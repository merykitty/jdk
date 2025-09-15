/*
 * Copyright (c) 2025, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#ifndef SHARE_OPTO_RANGEINFERENCE_HPP
#define SHARE_OPTO_RANGEINFERENCE_HPP

#include "utilities/globalDefinitions.hpp"
#include "utilities/ostream.hpp"

#include <limits>
#include <type_traits>

class outputStream;
class Type;
class TypeInt;
class TypeLong;

// A simple range in the signed or unsigned domain
template <class T>
class RangeInt {
public:
  T _lo;
  T _hi;
};

/**
 * Bits that are known to be 0 or 1. A value v satisfies this constraint iff
 * (v & zeros) == 0 && (v & ones) == ones. I.e, any bit that is 1 in zeros must
 * be 0 in v, and any bit that is 1 in ones must be 1 in v.
 *
 * I.e, for each bit position from 0 to sizeof(U) - 1, the corresponding bits
 * of zeros, ones and the allowed bit in v must follow:
 *
 * zeros    ones    allowed bits
 * 0        0       0 or 1
 * 1        0       0
 * 0        1       1
 * 1        1       none (impossible state)
 *
 * E.g:
 * zeros: 00110100
 * ones:  10000010
 * Then:  10001010 would satisfy the bit constraints
 * while: 10011000 would not since the bit at the 4th position violates
 * zeros and the bit at the 7th position violates ones
 *
 * A KnownBits is sane if there is no position at which a bit must be both set
 * and unset at the same time. That is (zeros & ones) == 0.
 */
template <class U>
class KnownBits {
  static_assert(U(-1) > U(0), "bit info should be unsigned");

public:
  U _zeros;
  U _ones;

  bool is_satisfied_by(U v) const {
    return (v & _zeros) == U(0) && (v & _ones) == _ones;
  }
};

// All the information needed to construct a TypeInt/TypeLong, the constraints
// here may be arbitrary and need to be canonicalized to construct a
// TypeInt/TypeLong
template <class S, class U>
class TypeIntPrototype {
public:
  static_assert(S(-1) < S(0), "");
  static_assert(U(-1) > U(0), "");
  static_assert(sizeof(S) == sizeof(U), "");

  RangeInt<S> _srange;
  RangeInt<U> _urange;
  KnownBits<U> _bits;

private:
  friend class TypeInt;
  friend class TypeLong;

  template <class T1, class T2>
  friend class TypeIntMirror;

  template <class T1, class T2>
  friend void test_canonicalize_constraints_exhaustive();

  template <class T1, class T2>
  friend void test_canonicalize_constraints_simple();

  template <class T1, class T2>
  friend void test_canonicalize_constraints_random();

  // A canonicalized version of a TypeIntPrototype, if the prototype represents
  // an empty type, _present is false, otherwise, _data is canonical
  class CanonicalizedTypeIntPrototype {
  public:
    bool _present; // whether this is an empty set
    TypeIntPrototype<S, U> _data;

    bool empty() const {
      return !_present;
    }

    static CanonicalizedTypeIntPrototype make_empty() {
      return {false, {}};
    }
  };

  CanonicalizedTypeIntPrototype canonicalize_constraints() const;
  int normalize_widen(int w) const;
#ifdef ASSERT
  bool contains(S v) const;
  void verify_constraints() const;
#endif // ASSERT
};

// Various helper functions for TypeInt/TypeLong operations
class TypeIntHelper {
public:
  // Calculate the cardinality of a TypeInt/TypeLong ignoring the bits
  // constraints, the return value is the cardinality minus 1 to not overflow
  // with the bottom type
  template <class S, class U>
  static U cardinality_from_bounds(const RangeInt<S>& srange, const RangeInt<U>& urange) {
    static_assert(S(-1) < S(0), "");
    static_assert(U(-1) > U(0), "");
    static_assert(sizeof(S) == sizeof(U), "");

    if (U(srange._lo) == urange._lo) {
      // srange is the same as urange
      assert(U(srange._hi) == urange._hi, "");
      // The cardinality is (hi - lo + 1), we return the result minus 1
      return urange._hi - urange._lo;
    }

    // srange intersects with urange in 2 intervals [srange._lo, urange._hi]
    // and [urange._lo, srange._hi]
    // The cardinality is (uhi - lo + 1) + (hi - ulo + 1), we return the result
    // minus 1
    return (urange._hi - U(srange._lo)) + (U(srange._hi) - urange._lo) + U(1);
  }

  template <class CT>
  static const Type* int_type_xmeet(const CT* i1, const Type* t2);

  template <class CT>
  static bool int_type_is_equal(const CT* t1, const CT* t2) {
    return t1->_lo == t2->_lo && t1->_hi == t2->_hi &&
           t1->_ulo == t2->_ulo && t1->_uhi == t2->_uhi &&
           t1->_bits._zeros == t2->_bits._zeros && t1->_bits._ones == t2->_bits._ones;
  }

  template <class CT>
  static bool int_type_is_subset(const CT* super, const CT* sub) {
    return super->_lo <= sub->_lo && super->_hi >= sub->_hi &&
           super->_ulo <= sub->_ulo && super->_uhi >= sub->_uhi &&
           // All bits that are known in super must also be known to be the same
           // value in sub, &~ (and not) is the same as a set subtraction on bit
           // sets
           (super->_bits._zeros &~ sub->_bits._zeros) == 0 && (super->_bits._ones &~ sub->_bits._ones) == 0;
  }

  template <class CT>
  static const Type* int_type_widen(const CT* new_type, const CT* old_type, const CT* limit_type);

  template <class CT>
  static const Type* int_type_narrow(const CT* new_type, const CT* old_type);

#ifndef PRODUCT
  static const char* intname(char* buf, size_t buf_size, jint n);
  static const char* uintname(char* buf, size_t buf_size, juint n);
  static const char* longname(char* buf, size_t buf_size, jlong n);
  static const char* ulongname(char* buf, size_t buf_size, julong n);

  template <class U>
  static const char* bitname(char* buf, size_t buf_size, U zeros, U ones);

  static void int_type_dump(const TypeInt* t, outputStream* st, bool verbose);
  static void int_type_dump(const TypeLong* t, outputStream* st, bool verbose);
#endif // PRODUCT
};

// This class contains methods for inferring the Type of the result of several arithmetic
// operations from those of the corresponding inputs. For example, given a, b such that the Type of
// a is [0, 1] and the Type of b is [-1, 3], then the Type of the sum a + b is [-1, 4].
// The methods in this class receive one or more template parameters which are often TypeInt* or
// TypeLong*, or they can be special helper classes which behave similar to TypeInt* and TypeLong*.
// This allows us to verify the correctness of the implementation without coupling with the
// hotspot compiler allocation infrastructure. 
class RangeInference {
private:
  // If CTP is a pointer, get the underlying type. For the test helper classes, using the struct
  // directly allows straightfoward equality comparison.
  template <class CTP>
  using CT = std::conditional_t<std::is_pointer_v<CTP>, std::remove_pointer_t<CTP>, CTP>;

  // The type of CT::_lo, should be jint for TypeInt* and jlong for TypeLong*
  template <class CTP>
  using S = std::remove_const_t<decltype(CT<CTP>::_lo)>;

  // The type of CT::_ulo, should be juint for TypeInt* and julong for TypeLong*
  template <class CTP>
  using U = std::remove_const_t<decltype(CT<CTP>::_ulo)>;

public:
  template <class CTP>
  static CTP infer_and(CTP t1, CTP t2) {
    S<CTP> lo = std::numeric_limits<S<CTP>>::min();
    S<CTP> hi = std::numeric_limits<S<CTP>>::max();
    U<CTP> ulo = std::numeric_limits<U<CTP>>::min();
    U<CTP> uhi = MIN2(t1->_uhi, t2->_uhi);
    U<CTP> zeros = t1->_bits._zeros | t2->_bits._zeros;
    U<CTP> ones = t1->_bits._ones & t2->_bits._ones;
    return CT<CTP>::make(TypeIntPrototype<S<CTP>, U<CTP>>{{lo, hi}, {ulo, uhi}, {zeros, ones}}, MAX2(t1->_widen, t2->_widen));
  }
};

#endif // SHARE_OPTO_RANGEINFERENCE_HPP
