package java.math;

import java.util.function.IntUnaryOperator;
import jdk.internal.vm.annotation.Stable;

@jdk.internal.ValueBased
public final class PreparedIntUnsignedDivision implements IntUnaryOperator {
    public static PreparedIntUnsignedDivision of(int divisor) {
        if (divisor == 0) {
            throw new ArithmeticException("division by zero");
        }
        long d = Integer.toUnsignedLong(divisor);
        int m = Long.SIZE - 1 - Long.numberOfLeadingZeros(d);
        int s = m + Integer.SIZE;
        long t = Long.divideUnsigned(1L << s, d);
        long r = Integer.toUnsignedLong((int)((t + 1) * d));
        long a, b;
        if (Long.compareUnsigned(r, 1L << m) <= 0) {
            a = t + 1;
            b = 0;
        } else {
            a = t;
            b = 1;
        }
        return new PreparedIntUnsignedDivision(a, b, s);
    }

    @Override
    public int applyAsInt(int dividend) {
        long b = other >>> B_SHIFT;
        int s = other;
        long prod = ((Integer.toUnsignedLong(dividend) + b) * a);
        return (int)(prod >>> s);
    }

    private static final int B_SHIFT = Byte.SIZE;

    @Stable
    private final long a;

    @Stable
    private final short other;

    private PreparedIntUnsignedDivision(long a, long b, int s) {
        this.a = a;
        this.other = (short)(s | (b << B_SHIFT));
    }
}
