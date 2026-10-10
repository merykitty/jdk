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
package compiler.types;

/*
 * @test
 * @bug 8394225
 * @summary TypeOopPtr::make_from_klass_common should not try_for_exact with abstract klasses
 * @enablePreview
 * @run main ${test.main.class}
 * @run main/othervm -Xbatch -XX:-TieredCompilation -XX:CompileOnly=${test.main.class}::test
 *                   ${test.main.class}
 */
public class TestTryExactAbstractKlass {
    private static abstract value class A {}

    public static void main(String[] args) {
        A[] array = new A[1];
        for (int i = 0; i < 20000; i++) {
            test(array);
        }
    }

    private static A test(A[] array) {
        return array[0];
    }
}
