package compiler.loopopts;

import compiler.lib.ir_framework.Run;
import compiler.lib.ir_framework.Test;
import compiler.lib.ir_framework.TestFramework;
import java.util.Arrays;
import jdk.test.lib.Asserts;

/*
 * @test
 * @bug 8390046
 * @summary PhaseIdealLoop::get_late_ctrl must compute anti-dependencies of memory load intrinsics
 * @library /test/lib /
 * @run driver ${test.main.class}
 */
public class TestIntrinsicsAntiDependence {
    public static void main(String[] args) {
        var framework = new TestFramework();
        framework.start();
    }

    @Test
    private static boolean testArrayEquals(byte[] a, byte[] b) {
        boolean r = false;
        for (int i = 0; i < 32; i++) {
            r = Arrays.equals(a, b);
            a[i] = 1;
        }
        // Arrays::equals sinks down here because of missing anti-dependency computation which
        // allows it to bypass the store in the loop, and produces the wrong result.
        return r;
    }

    @Run(test = "testArrayEquals")
    public void runArrayEquals() {
        byte[] a = new byte[32];
        byte[] b = new byte[32];
        Arrays.fill(b, (byte) 1);
        Asserts.assertEQ(false, testArrayEquals(a, b));
    }

    @Test
    private static int testArrayHashCode(byte[] a) {
        int r = 0;
        for (int i = 0; i < 32; i++) {
            r = Arrays.hashCode(a);
            a[i] = 1;
        }
        // Arrays::hashCode sinks down here because of missing anti-dependency computation which
        // allows it to bypass the store in the loop, and produces the wrong result.
        return r;
    }

    @Run(test = "testArrayHashCode")
    public void runArrayHashCode() {
        byte[] verify = new byte[32];
        for (int i = 0; i < 31; i++) {
            verify[i] = 1;
        }
        byte[] test = new byte[32];
        Asserts.assertEQ(Arrays.hashCode(verify), testArrayHashCode(test));
    }
}
