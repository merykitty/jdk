package java.math;

import java.util.function.LongUnaryOperator;
import jdk.internal.vm.annotation.Stable;

@jdk.internal.ValueBased
public class PreparedLongUnsignedDivision implements LongUnaryOperator {
    public static PreparedLongUnsignedDivision of(long divisor) {
        if (divisor == 0) {
            throw new ArithmeticException("division by zero");
        }

        long d = divisor;
        int m = Long.SIZE - 1 - Long.numberOfLeadingZeros(d);
        if (d == 1L << m) {
            return new PreparedLongUnsignedDivision(-1, 1, m);
        }

        // Calculate floor(2**(m + n) / d) from 2**n / d using induction
        long t = Long.divideUnsigned(-d, d) + 1;
        long tr = Long.remainderUnsigned(-d, d);
        for (int i = 0; i < m; i++) {
            long newTr = tr * 2;
            if (Long.compareUnsigned(newTr, tr) < 0 || Long.compareUnsigned(tr, d) >= 0) {
                t = t * 2 + 1;
                tr = newTr - d;
            } else {
                t = t * 2;
                tr = newTr;
            }
        }

        long r = (t + 1) * d;
        long a, b;
        if (r <= 1L << m) {
            a = t + 1;
            b = 0;
        } else {
            a = t;
            b = 1;
        }
        return new PreparedLongUnsignedDivision(a, b, m);
    }

    @Override
    public long applyAsLong(long dividend) {
        long prod;
        long b = other >>> B_SHIFT;
        int m = other;
        if (dividend == -1 && b == 1) {
            prod = a;
        } else {
            prod = Math.unsignedMultiplyHigh(dividend + b, a);
        }
        return prod >>> m;
    }

    private static final int B_SHIFT = Byte.SIZE;

    @Stable
    private final long a;

    @Stable
    private final short other;

    private PreparedLongUnsignedDivision(long a, long b, int m) {
        this.a = a;
        this.other = (short)(m | b << B_SHIFT);
    }
}
