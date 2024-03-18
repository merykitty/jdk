/*
 * Copyright (c) 2024, Oracle and/or its affiliates. All rights reserved.
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
 */

package compiler.regalloc;

import compiler.lib.ir_framework.*;

/*
 * @test
 * @bug 8322101
 * @summary Verify that pre-ra scheduler can arrange nodes in a way that
 *          minimizes spilling
 * @library /test/lib /
 * @run driver compiler.regalloc.LCMMinimizeSpilling
 */
public class LCMMinimizeSpilling {
    private static double out;
    public static void main(String[] args) {
        var test = new TestFramework(LCMMinimizeSpilling.class);
        test.addFlags("-XX:-UseFPUForSpilling");
        test.start();
    }

    // x + y should be scheduled before the call
    @Test
    @IR(counts = {IRNode.SPILL_COPY, "2"}, applyIfPlatform = {"x64", "true"})
    @Arguments(values = {Argument.NUMBER_42, Argument.NUMBER_42})
    public static double acrossCall1(double x, double y) {
        double res = Math.cos(x);
        out = x + y;
        return res;
    }

    // x * x + x should be scheduled after the call
    @Test
    @IR(counts = {IRNode.SPILL_COPY, "2"}, applyIfPlatform = {"x64", "true"})
    @Arguments(values = Argument.NUMBER_42)
    public static double acrossCall2(double x) {
        double res = Math.cos(x);
        out = x * x + x;
        return res;
    }

    // x + y + z should be scheduled before the call while t * t + t should be
    // scheduled after
    @Test
    @IR(counts = {IRNode.SPILL_COPY, "2"}, applyIfPlatform = {"x64", "true"})
    @Arguments(values = {Argument.NUMBER_42, Argument.NUMBER_42, Argument.NUMBER_42})
    public static double acrossCall3(double x, double y, double z) {
        double res = Math.cos(x);
        double t = x + y + z;
        out = t * t + t;
        return res;
    }

    @Test
    @IR(failOn = IRNode.MEM_TO_REG_SPILL_COPY, applyIfPlatform = {"x64", "true"})
    @Arguments(values = {Argument.NUMBER_42, Argument.NUMBER_42})
    public static int basicScheduling(int sum, int idx) {
        sum += 2 * idx * idx; idx++; sum += 2 * idx * idx; idx++;
        sum += 2 * idx * idx; idx++; sum += 2 * idx * idx; idx++;
        sum += 2 * idx * idx; idx++; sum += 2 * idx * idx; idx++;
        sum += 2 * idx * idx; idx++; sum += 2 * idx * idx; idx++;
        sum += 2 * idx * idx; idx++; sum += 2 * idx * idx; idx++;
        sum += 2 * idx * idx; idx++; sum += 2 * idx * idx; idx++;
        sum += 2 * idx * idx; idx++; sum += 2 * idx * idx; idx++;
        sum += 2 * idx * idx; idx++; sum += 2 * idx * idx;
        return sum;
    }

    @Test
    @IR(failOn = IRNode.MEM_TO_REG_SPILL_COPY, applyIfPlatform = {"x64", "true"})
    @Arguments(values = {Argument.NUMBER_42, Argument.RANDOM_EACH, Argument.DEFAULT})
    public static int flagScheduling(int sum, int idx, int mask) {
        mask++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum; idx++;
        sum = (idx & mask) == 0 ? sum + 1 : sum;
        return sum;
    }
}
