package java.math;

import java.util.function.IntUnaryOperator;
import jdk.internal.vm.annotation.Stable;

@jdk.internal.ValueBased
public class PreparedIntSignedDivision implements IntUnaryOperator {
    public static PreparedIntSignedDivision of(int divisor) {
        if (divisor == 0) {
            throw new ArithmeticException("division by zero");
        }

        boolean neg = divisor < 0;
        int d = Math.abs(divisor);
        if ((d & (d - 1)) == 0) {
            int m = Integer.SIZE - 1 - Integer.numberOfLeadingZeros(d);
            return new PreparedIntSignedDivision(0x80000001L, m + Integer.SIZE - 1, neg);
        }

    }

    @Override
    public int applyAsInt(int dividend) {
        int s = other;
        boolean neg = (s & NEG_MASK) != 0;
        long prod = dividend * a;
        int q0 = (int)(prod >> s);
        int res = q0 + dividend >>> (Integer.SIZE - 1);
        return neg ? -res : res;
    }

    private static final int NEG_MASK = 1 << Byte.SIZE;

    @Stable
    private final long a;

    @Stable
    private final int other;

    private PreparedIntSignedDivision(long a, int s, boolean neg) {
        this.a = a;
        this.other = s | (neg ? NEG_MASK : 0);
    }
}
