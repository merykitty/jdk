/*
 * Copyright (c) 1999, 2026, Oracle and/or its affiliates. All rights reserved.
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

#ifndef SHARE_CI_CIINSTANCEKLASS_HPP
#define SHARE_CI_CIINSTANCEKLASS_HPP

#include "ci/ciConstantPoolCache.hpp"
#include "ci/ciFlags.hpp"
#include "ci/ciKlass.hpp"
#include "ci/ciSymbol.hpp"
#include "classfile/classFileParser.hpp"
#include "oops/instanceKlass.hpp"

// ciInstanceKlass
//
// This class represents a Klass* in the HotSpot virtual machine
// whose Klass part is an InstanceKlass.  It may or may not
// be loaded.
class ciInstanceKlass : public ciKlass {
  CI_PACKAGE_ACCESS
  friend class ciBytecodeStream;
  friend class ciEnv;
  friend class ciExceptionHandler;
  friend class ciMethod;
  friend class ciField;
  friend class ciReplay;
  friend class CompileTrainingData;

private:
  enum SubklassValue { subklass_unknown, subklass_false, subklass_true };

  jobject                _loader;

  InstanceKlass::ClassState _init_state;           // state of class
  bool                   _is_shared;
  bool                   _has_finalizer;
  bool                   _has_nonstatic_fields;
  bool                   _has_nonstatic_concrete_methods;
  bool                   _is_hidden;
  bool                   _is_record;
  bool                   _trust_final_fields;
  bool                   _has_trusted_loader;

  ciFlags                _flags;
  ciInstanceKlass*       _super;
  ciInstance*            _java_mirror;  // Lazy fields get filled in only upon request.

  ciConstantPoolCache*   _field_cache;  // cached map index->field

  // Fields declared in the bytecode (without nested fields in flat fields),
  // ordered in JavaFieldStream order, with superclasses first (i.e. from lang.java.Object
  // to most derived class).
  const GrowableArray<ciField*>* _declared_nonstatic_fields;

  // Fields laid out in memory (flat fields are expanded into their components). The ciField object
  // for each primitive component has the holder being this ciInstanceKlass or one of its
  // superclasses.
  // Fields are in the same order as in _declared_nonstatic_fields, but flat fields are replaced by
  // the list of their own fields, ordered the same way (hierarchy traversed top-down, in
  // JavaFieldStream order).
  const GrowableArray<ciField*>* _nonstatic_fields;

  int _has_injected_fields; // any non static injected fields? lazily initialized.
  GrowableArray<ciInstanceKlass*>* _transitive_interfaces;

  // CHA related fields need to be cached so that the compiler has a consistent view of the class
  // hierarchy. The first concern is that multiple calls on the same ciInstanceKlass should return
  // the same value. Otherwise, different nodes may have different types even if their declared
  // types in the classfile are the same. The second concern is that the value should be consistent
  // with the state of other ciInstanceKlasses. For example, the view is inconsistent if a
  // ciInstanceKlass says that it has no subklass, but there is another ciInstanceKlass which says
  // that it has the former as its super. Another example is if a ciInstanceKlass says that it has
  // a unique concrete subklass, but there are multiple concrete ciInstanceKlasses inherit it.
  // Inconsistency is dangerous as it is easy for the compiler to get strange failures.
  // Since they need to be consistent, these fields can only be computed after parsing (and
  // inlining) has finished, and we do not encounter more code.
  bool _cha_info_computed;

  // Whether this ciInstanceKlass has a proper subklass (a subklass that is not itself) that is not
  // an interface
  SubklassValue _has_subklass;

  // _implementor is the result of trying to find the LCA of all concrete subklasses of a class or
  // interface. The possible values fall into following 2 cases:
  //   == nullptr: no concrete subklass (including itself)
  //   != nullptr: each concrete subklass of this must be a subklass of this value
  ciInstanceKlass* _implementor;

  void compute_injected_fields();
  bool compute_injected_fields_helper();
  GrowableArray<ciInstanceKlass*>* compute_transitive_interfaces(Arena* arena, InstanceKlass* ik);

  ciField* get_nonstatic_field_by_offset(int field_offset);

  void compute_cha_info();
  bool check_cha_consistency(InstanceKlass* ik);
  void update_cha_info_upon_creation();

protected:
  ciInstanceKlass(Klass* k);
  ciInstanceKlass(ciSymbol* name, jobject loader, BasicType bt = T_OBJECT); // for unloaded klasses

  InstanceKlass* get_instanceKlass() const {
    return InstanceKlass::cast(get_Klass());
  }

  oop loader();
  jobject loader_handle();

  const char* type_string() { return "ciInstanceKlass"; }

  bool is_in_package_impl(const char* packagename, int len);

  void print_impl(outputStream* st);

  ciConstantPoolCache* field_cache();

  bool is_shared() { return _is_shared; }

  InstanceKlass::ClassState compute_init_state();
  bool compute_shared_has_subklass();
  void compute_nonstatic_fields();
  void compute_nonstatic_fields_impl(const GrowableArray<ciField*>* super_declared_fields, const GrowableArray<ciField*>* super_fields);
  bool compute_has_trusted_loader();

  static InstanceKlass::ClassState compute_init_state(InstanceKlass* ik);

public:
  // Has this klass been initialized?
  bool                   is_initialized() {
    InstanceKlass::ClassState state = compute_init_state();
    return state == InstanceKlass::fully_initialized;
  }
  bool                   is_not_initialized() {
    InstanceKlass::ClassState state = compute_init_state();
    return state < InstanceKlass::being_initialized;
  }
  // Is this klass being initialized?
  bool                   is_being_initialized() {
    InstanceKlass::ClassState state = compute_init_state();
    return state == InstanceKlass::being_initialized;
  }
  // Has this klass been linked?
  bool                   is_linked() {
    InstanceKlass::ClassState state = compute_init_state();
    return state >= InstanceKlass::linked;
  }
  // Is this klass in error state?
  bool                   is_in_error_state() {
    InstanceKlass::ClassState state = compute_init_state();
    return state == InstanceKlass::initialization_error;
  }

  // General klass information.
  ciFlags                flags()          {
    assert(is_loaded(), "must be loaded");
    return _flags;
  }

  // Fetch Klass::access_flags.
  jint                   access_flags() { return flags().as_int(); }

  bool                   has_finalizer()  {
    assert(is_loaded(), "must be loaded");
    return _has_finalizer; }

  jint                   layout_helper_size_in_bytes()  {
    return Klass::layout_helper_size_in_bytes(layout_helper());
  }
  jint                   size_helper()  {
    return (Klass::layout_helper_size_in_bytes(layout_helper())
            >> LogHeapWordSize);
  }
  jint                   has_nonstatic_fields()  {
    assert(is_loaded(), "must be loaded");
    return _has_nonstatic_fields;
  }

  ciInstanceKlass*       super() const {
    return _super;
  }

  bool has_nonstatic_concrete_methods()  {
    assert(is_loaded(), "must be loaded");
    return _has_nonstatic_concrete_methods;
  }

  bool is_hidden() const {
    return _is_hidden;
  }

  bool is_record() const {
    return _is_record;
  }

  bool trust_final_fields() const {
    return _trust_final_fields;
  }

  ciInstanceKlass* get_canonical_holder(int offset);
  ciField* get_field_by_offset(int field_offset, bool is_static);
  ciField* get_field_by_name(ciSymbol* name, ciSymbol* signature, bool is_static);
  // Get field descriptor at field_offset ignoring flattening
  ciField* get_non_flat_field_by_offset(int field_offset);
  // Get the index of the declared field that contains this offset
  int field_index_by_offset(int offset);

  // Total number of nonstatic fields (including inherited)
  int nof_declared_nonstatic_fields() {
    if (_declared_nonstatic_fields == nullptr) {
      compute_nonstatic_fields();
    }
    return _declared_nonstatic_fields->length();
  }
  ciField* get_injected_instance_field_by_name(ciSymbol* name, ciSymbol* signature);
  BasicType get_field_type_by_offset(int field_offset, bool is_static);

  int nof_nonstatic_fields() {
    if (_nonstatic_fields == nullptr) {
      compute_nonstatic_fields();
    }
    return _nonstatic_fields->length();
  }

  bool has_injected_fields() {
    if (_has_injected_fields == -1) {
      compute_injected_fields();
    }
    return _has_injected_fields > 0 ? true : false;
  }

  bool has_object_fields() const;

  ciField* declared_nonstatic_field_at(int i) {
    assert(_declared_nonstatic_fields != nullptr, "should be initialized");
    return _declared_nonstatic_fields->at(i);
  }

  ciField* nonstatic_field_at(int i) {
    assert(_nonstatic_fields != nullptr, "");
    return _nonstatic_fields->at(i);
  }

  int number_of_oop_entries_in_acmp_map() const;
  int number_of_nonoop_entries_in_acmp_map() const;
  AcmpMapSegment get_nonoop_segment_of_acmp_map(int i) const;

  bool has_finalizable_subclass();

  bool has_class_initializer();

  bool contains_field_offset(int offset) const;

  // Get the instance of java.lang.Class corresponding to
  // this klass.  This instance is used for locking of
  // synchronized static methods of this klass.
  ciInstance*            java_mirror();

  // Java access flags
  bool is_public      () { return flags().is_public(); }
  bool is_final       () { return flags().is_final(); }
  bool is_interface   () { return flags().is_interface(); }
  bool is_abstract    () { return flags().is_abstract(); }
  bool is_abstract_value_klass() { return is_abstract() && !flags().is_identity(); }

  ciMethod* find_method(ciSymbol* name, ciSymbol* signature);
  // Note:  To find a method from name and type strings, use ciSymbol::make,
  // but consider adding to vmSymbols.hpp instead.

  virtual bool can_be_value_klass(bool is_exact = false);

  // Is the defining class loader of this class the default loader?
  bool uses_default_loader() const;

  bool is_java_lang_Object() const;

  BasicType box_klass_type() const;
  bool is_box_klass() const;
  bool is_boxed_value_offset(int offset) const;

  // Is this klass in the given package?
  bool is_in_package(const char* packagename) {
    return is_in_package(packagename, (int) strlen(packagename));
  }
  bool is_in_package(const char* packagename, int len);

  // What kind of ciObject is this?
  bool is_instance_klass() const { return true; }

  virtual ciKlass* exact_klass() {
    if (is_loaded() && is_final() && !is_interface()) {
      return this;
    }
    return nullptr;
  }

  bool can_be_instantiated() {
    assert(is_loaded(), "must be loaded");
    return !is_interface() && !is_abstract();
  }

  bool has_trusted_loader() const {
    return _has_trusted_loader;
  }

  GrowableArray<ciInstanceKlass*>* transitive_interfaces() const;

  // CHA related methods
  // These methods are pessimistic, they ensure the consistency in the compiler's view of the class
  // hierarchy (e.g. if a klass says that it has no subklass, no ciKlass can be created as its
  // child). These methods can be used for static type inference such as general type information
  // of the nodes the graph. Class loading is still racy, but these methods ensure the compiler can
  // work properly without encountering strange issues. Assumption violation will invalidate the
  // compiled method, but it only happens after the compilation has finished.
  bool has_subklass_checked();
  ciInstanceKlass* unique_concrete_subklass_checked();
  ciInstanceKlass* unique_implementor_checked();

  // These methods are optimistic, they don't care about the raciness with the class loading
  // mechanism and can result in inconsistencies. These methods can be used for speculative type
  // inference that does not affect the relationship of different nodes in the graph such as when
  // optimizing a subtype check. It is generally unsafe to optimize the type information of a node
  // using the unchecked methods because when IGVN replaces it with another node in the graph, the
  // consistency can be exposed.
  bool has_subklass_unchecked();
  bool is_leaf_type_unchecked();
  ciInstanceKlass* unique_concrete_subklass_unchecked();
  ciInstanceKlass* unique_implementor_unchecked();

  // Replay support

  // Dump the current state of this klass for compilation replay.
  virtual void dump_replay_data(outputStream* out);

  static void dump_replay_instanceKlass(outputStream* out, InstanceKlass* ik);


  // Return stable class name suitable for replay file.
  const char *replay_name() const;

#ifdef ASSERT
  bool debug_final_field_at(int offset);
  bool debug_stable_field_at(int offset);
#endif
};

#endif // SHARE_CI_CIINSTANCEKLASS_HPP
