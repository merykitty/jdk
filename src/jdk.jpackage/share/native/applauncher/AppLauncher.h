/*
 * Copyright (c) 2020, 2024, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
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


#ifndef AppLauncher_h
#define AppLauncher_h

#include "tstrings.h"

class Jvm;
class CfgFile;

class AppLauncher {
public:
    AppLauncher();

    AppLauncher& setImageRoot(const tstring& v) {
        imageRoot = v;
        return *this;
    }

    AppLauncher& setDefaultRuntimePath(const tstring& v) {
        defaultRuntimePath = v;
        return *this;
    }

    AppLauncher& addCfgFileLookupDir(const tstring& v) {
        cfgFileLookupDirs.push_back(v);
        return *this;
    }

    AppLauncher& setAppDir(const tstring& v) {
        appDirPath = v;
        return *this;
    }

    AppLauncher& setLibEnvVariableName(const tstring& v) {
        libEnvVarName = v;
        return *this;
    }

    AppLauncher& setInitJvmFromCmdlineOnly(bool v) {
        initJvmFromCmdlineOnly = v;
        return *this;
    }

    AppLauncher& addJvmLibName(const tstring& v) {
        jvmLibNames.push_back(v);
        return *this;
    }

    AppLauncher& setCfgFile(const CfgFile* v) {
        externalCfgFile = v;
        return *this;
    }

    bool libEnvVariableContainsAppDir() const;

    Jvm* createJvmLauncher() const;

    void launch() const;

    CfgFile* createCfgFile() const;

private:
    tstring getCfgFilePath() const;

private:
    tstring_array args;
    tstring launcherPath;
    tstring defaultRuntimePath;
    tstring appDirPath;
    tstring libEnvVarName;
    tstring imageRoot;
    tstring_array jvmLibNames;
    tstring_array cfgFileLookupDirs;
    bool initJvmFromCmdlineOnly;
    const CfgFile* externalCfgFile;
};

#endif // AppLauncher_h
