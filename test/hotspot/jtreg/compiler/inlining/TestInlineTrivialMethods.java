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
 */
package compiler.inlining;

import java.io.IOException;
import jdk.test.lib.process.OutputAnalyzer;
import jdk.test.lib.process.ProcessTools;

/*
 * @test
 * @bug 8372634
 * @summary 8372634
 * @library /test/lib /
 * @requires vm.flagless
 * @requires vm.debug == true
 * @run main ${test.main.class}
 */
public class TestInlineTrivialMethods {
    public static class TrivialInlining {
        static abstract class P {
            abstract int get();
        }

        // The only concrete implementor of P
        static class C1 extends P {
            @Override
            int get() {
                return 1;
            }

            static final C1 INSTANCE = new C1();
        }

        static class C2 extends P {
            @Override
            int get() {
                return 2;
            }

            static final C2 INSTANCE = new C2();
        }

        public static void main(String[] args) {
            for (int i = 0; i < 10; i++) {
                test1();
                test2(0, 1);
                test3();
                test4();
                test5("");
                test6("");
                test7(0, 5);
                test8(0, 5);
                test9(0);
                test10(false);
                test11();
                test12();
                test13();
                test14(C1.INSTANCE);
                test15(C2.INSTANCE);
            }
        }

        private static void test1() {
            emptyMethod();
        }

        private static void emptyMethod() {}

        // A simple calculation, add can be considered trivial if TrivialMethodNodeLimit is
        // sufficient
        private static int test2(int x, int y) {
            return add(1, x, y, 4);
        }

        private static int add(int x, int y, int z, int t) {
            return add(add(x, y), add(z, t));
        }

        private static int add(int x, int y) {
            return x + y;
        }

        static final Integer IMMUTABLE_INT = 1;

        // Load a constant, immutableHolderValue can be considered trivial even if
        // TrivialMethodNodeLimit = 0
        private static int test3() {
            return immutableHolderValue();
        }

        private static int immutableHolderValue() {
            return immutableHolder();
        }

        private static Integer immutableHolder() {
            return IMMUTABLE_INT;
        }

        static class MutableInt {
            int v;
        }

        static final MutableInt MUTABLE_INT = new MutableInt();

        // A simple load, mutableHolderValue can be considered trivial if TrivialMethodNodeLimit is
        // sufficient
        private static int test4() {
            return mutableHolderValue();
        }

        private static int mutableHolderValue() {
            return mutableHolder().v;
        }

        private static MutableInt mutableHolder() {
            return MUTABLE_INT;
        }

        // nullCheck1 cannot be considered trivial because of the conditional jump
        private static Object test5(Object o) {
            return nullCheck1(o);
        }

        private static Object nullCheck1(Object o) {
            if (o == null) {
                throw new NullPointerException();
            } else {
                return o;
            }
        }

        // nullCheck2 can be considered trivial because o is known not to be null, allowing the
        // conditional jump to be folded
        private static Object test6(Object o) {
            if (o != null) {
                return nullCheck2(nullCheck2(o));
            } else {
                return "default";
            }
        }

        private static Object nullCheck2(Object o) {
            if (o == null) {
                throw new NullPointerException();
            } else {
                return o;
            }
        }

        // maybePrint1 cannot be considered trivial because of the conditional jump
        private static void test7(int x, int y) {
            maybePrint1(x, y);
        }

        private static void maybePrint1(int x, int y) {
            if (x <= y) {
                return;
            }

            System.out.println("Something");
        }

        // x is provably less than y, allowing the conditional jump to be folded
        private static void test8(int x, int y) {
            x = Math.min(x, 3);
            y = Math.max(y, 4);
            maybePrint2(x, y);
        }

        private static void maybePrint2(int x, int y) {
            if (x <= y) {
                return;
            }

            System.out.println("Something");
        }

        // maybePrint3 can detect that it is called from test9 with the same value for both
        // arguments, allowing the conditional jump to be folded
        private static void test9(int x) {
            maybePrint3(x, x);
        }

        private static void maybePrint3(int x, int y) {
            if (x <= y) {
                return;
            }

            System.out.println("Something");
        }

        // cutOff will trap, so inlining it allows the compiler to discover that the path is a
        // dead-end
        private static void test10(boolean b) {
            if (b) {
                cutoff(null);
            }
        }

        private static int cutoff(Integer v) {
            int x = v;
            return x + MUTABLE_INT.v;
        }

        // loop is not trivial because it has a loop
        private static int test11() {
            return loop(2);
        }

        private static int loop(int limit) {
            int sum = 0;
            for (int i = 0; i < limit; i++) {
                sum += i;
            }
            return sum;
        }

        // recursiveCall is not trivial because it calls itself recursively, note that the
        // recursion depth passed here should be sufficiently large, or recursiveCall can be
        // considered trivial when we inline some level of recursion and only the last one is left
        private static int test12() {
            return recursiveCall(5);
        }

        private static int recursiveCall(int n) {
            if (n == 0) {
                return 0;
            } else {
                return n + recursiveCall(n - 1);
            }
        }

        static class MutableIntHolder {
            MutableInt v;
        }

        static MutableIntHolder nonConIntHolder = new MutableIntHolder();
        static {
            nonConIntHolder.v = MUTABLE_INT;
        }

        // nonConIntHolder is nullable, nonConIntHolder.v is also nullable. As a result,
        // loadAndNullCheckALot is only considered trivial for a fairly large value of
        // TrivialMethodNodeLimit
        private static int test13() {
            return loadAndNullCheckALot();
        }

        private static int loadAndNullCheckALot() {
            return nonConIntHolder.v.v;
        }

        // devirtualizeCall1 can be considered trivial because we know that v is a C1
        private static int test14(C1 v) {
            return devirtualizeCall1(v);
        }

        private static int devirtualizeCall1(P v) {
            return v.get();
        }

        // devirtualizeCall2 cannot be considered trivial because we can't devirtualize the call
        // v.get()
        private static int test15(P v) {
            return devirtualizeCall2(v);
        }

        private static int devirtualizeCall2(P v) {
            return v.get();
        }
    }

    private static ProcessBuilder processBuilder(int trivialLimit) {
        return ProcessTools.createLimitedTestJavaProcessBuilder(
                "-XX:-TieredCompilation", "-XX:-UseOnStackReplacement", "-XX:-BackgroundCompilation",
                "-XX:CompileThreshold=2", "-XX:MaxInlineSize=0", "-XX:FreqInlineSize=0", "-XX:+PrintCompilation",
                "-XX:CompileCommand=quiet", "-XX:+PrintInlining", "-XX:TrivialMethodNodeLimit=" + trivialLimit,
                TrivialInlining.class.getName()
        );
    }

    public static void main(String[] args) throws IOException {
        // Only methods that do not generate any non-constant node can be considered trivial
        ProcessBuilder pb = processBuilder(0);
        OutputAnalyzer analyzer = new OutputAnalyzer(pb.start());
        analyzer.shouldHaveExitValue(0);
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::emptyMethod (1 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::immutableHolderValue (7 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::immutableHolder (4 bytes)   trivial");
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::add (14 bytes)   trivial");
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::add (4 bytes)   trivial");
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::mutableHolderValue (7 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::mutableHolder (4 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::nullCheck2 (14 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::maybePrint2 (15 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::maybePrint3 (15 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::cutoff (14 bytes)   trivial");
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::devirtualizeCall1 (5 bytes)   trivial");

        // The default value of TrivialMethodNodeLimit allows simple functions to be considered
        // trivial
        pb = processBuilder(10);
        analyzer = new OutputAnalyzer(pb.start());
        analyzer.shouldHaveExitValue(0);
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::add (14 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::add (4 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::mutableHolderValue (7 bytes)   trivial");
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::loadAndNullCheckALot (10 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::devirtualizeCall1 (5 bytes)   trivial");

        // Even with a large value of TrivialMethodNodeLimit, functions with conditional jumps
        // cannot be considered trivial
        pb = processBuilder(100);
        analyzer = new OutputAnalyzer(pb.start());
        analyzer.shouldHaveExitValue(0);
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::nullCheck1 (14 bytes)   trivial");
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::maybePrint1 (15 bytes)   trivial");
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::loop (21 bytes)   trivial");
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::recursiveCall (15 bytes)   trivial");
        analyzer.shouldContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::loadAndNullCheckALot (10 bytes)   trivial");
        analyzer.shouldNotContain("compiler.inlining.TestInlineTrivialMethods$TrivialInlining::devirtualizeCall2 (5 bytes)   trivial");
    }
}
