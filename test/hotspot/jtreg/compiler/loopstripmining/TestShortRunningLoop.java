/*
 * Copyright (c) 2026, Oracle and/or its affiliates. All rights reserved.
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

package compiler.loopstripmining;

import compiler.lib.ir_framework.*;

/*
 * @test
 * @summary 
 * @library /test/lib /
 * @run driver ${test.main.class}
 */
public class TestShortRunningLoop {
    private static final int[] ARRAY = new int[4000];

    public static void main(String[] args) {
        TestFramework.runWithFlags("-XX:LoopUnrollLimit=0");
    }

    @Test
    @Warmup(0)
    @IR(failOn = {IRNode.SHORT_RUNNING_LOOP_TRAP, IRNode.OUTER_STRIP_MINED_LOOP})
    @IR(counts = {IRNode.COUNTED_LOOP, "> 0"})
    public int staticShortIntLoop1() {
        int sum = 0;
        for (int i = 0; i < 100; i++) {
            sum += ARRAY[i * 2];
        }
        return sum;
    }

    @Test
    @IR(failOn = IRNode.OUTER_STRIP_MINED_LOOP)
    @IR(counts = {IRNode.SHORT_RUNNING_LOOP_TRAP, "1", IRNode.COUNTED_LOOP, "> 0"})
    public int profileShortIntLoop(int start, int limit) {
        int sum = 0;
        for (int i = start; i < limit; i++) {
            sum += ARRAY[i * 2];
        }
        return sum;
    }

    @Run(test = "profileShortIntLoop")
    public int runProfileShortIntLoop() {
        // Trip count computed from the profile can be incorrect due to floating-point error
        return profileShortIntLoop(0, 90);
    }

    @Test
    @IR(failOn = {IRNode.SHORT_RUNNING_LOOP_TRAP, IRNode.OUTER_STRIP_MINED_LOOP})
    @IR(counts = {IRNode.COUNTED_LOOP, "> 0"})
    public int staticShortIntLoop2(int start, int limit) {
        // Huge increment means that the counted loop never runs too many iterations
        int sum = 0;
        for (int i = start; i < limit; i += Integer.MIN_VALUE >>> 2) {
            sum += i;
        }
        return sum;
    }

    @Run(test = "staticShortIntLoop2")
    @Warmup(0)
    public int runStaticShortIntLoop2() {
        return staticShortIntLoop2(Integer.MIN_VALUE, Integer.MIN_VALUE >>> 1);
    }

    @Test
    @Warmup(0)
    @IR(failOn = IRNode.SHORT_RUNNING_LOOP_TRAP)
    @IR(counts = {IRNode.OUTER_STRIP_MINED_LOOP, "1", IRNode.COUNTED_LOOP, "> 0"})
    public int staticLongIntLoop() {
        int sum = 0;
        for (int i = 0; i < 2000; i++) {
            sum += ARRAY[i * 2];
        }
        return sum;
    }

    @Test
    @IR(failOn = IRNode.SHORT_RUNNING_LOOP_TRAP)
    @IR(counts = {IRNode.OUTER_STRIP_MINED_LOOP, "1", IRNode.COUNTED_LOOP, "> 0"})
    public int profileLongIntLoop(int start, int limit) {
        int sum = 0;
        for (int i = start; i < limit; i++) {
            sum += ARRAY[i * 2];
        }
        return sum;
    }

    @Run(test = "profileLongIntLoop")
    public int runProfileLongIntLoop() {
        return profileLongIntLoop(0, 200);
    }

    @Test
    @Warmup(0)
    @IR(failOn = {IRNode.SHORT_RUNNING_LONG_LOOP_TRAP, IRNode.SHORT_RUNNING_LOOP_TRAP, IRNode.OUTER_STRIP_MINED_LOOP})
    @IR(counts = {IRNode.COUNTED_LOOP, "> 0"})
    public int staticShortLongLoop() {
        int sum = 0;
        for (long i = 0; i < 100; i++) {
            sum += ARRAY[(int)i * 2];
        }
        return sum;
    }

    @Test
    @IR(failOn = IRNode.OUTER_STRIP_MINED_LOOP)
    @IR(counts = {IRNode.SHORT_RUNNING_LONG_LOOP_TRAP, "1", IRNode.SHORT_RUNNING_LOOP_TRAP, "1", IRNode.COUNTED_LOOP, "> 0"})
    public int profileShortLongLoop(long start, long limit) {
        int sum = 0;
        for (long i = start; i < limit; i++) {
            sum += ARRAY[(int)i * 2];
        }
        return sum;
    }

    @Run(test = "profileShortLongLoop")
    public int runProfileShortLongLoop() {
        // Trip count computed from the profile can be incorrect due to floating-point error
        return profileShortLongLoop(0, 90);
    }

    @Test
    @Warmup(0)
    @IR(failOn = {IRNode.SHORT_RUNNING_LONG_LOOP_TRAP, IRNode.SHORT_RUNNING_LOOP_TRAP})
    @IR(counts = {IRNode.OUTER_STRIP_MINED_LOOP, "1", IRNode.COUNTED_LOOP, "> 0"})
    public int staticLongLongLoop() {
        int sum = 0;
        for (long i = 0; i < 2000; i++) {
            sum += ARRAY[(int)i * 2];
        }
        return sum;
    }

    @Test
    @IR(failOn = IRNode.SHORT_RUNNING_LOOP_TRAP)
    @IR(counts = {IRNode.SHORT_RUNNING_LONG_LOOP_TRAP, "1", IRNode.OUTER_STRIP_MINED_LOOP, "1", IRNode.COUNTED_LOOP, "> 0"})
    public int profileLongLongLoop(long start, long limit) {
        int sum = 0;
        for (long i = start; i < limit; i++) {
            sum += ARRAY[(int)i * 2];
        }
        return sum;
    }

    @Run(test = "profileLongLongLoop")
    public int runProfileLongLongLoop() {
        return profileLongLongLoop(0, 200);
    }
}
