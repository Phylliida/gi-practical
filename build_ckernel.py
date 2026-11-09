#!/usr/bin/env python3
"""Build the optional compiled kernel gi/_ckernel.c in place.

    python3 build_ckernel.py            # optimized build next to gi/_ckernel.c
    python3 build_ckernel.py --asan     # AddressSanitizer + UBSan build (see below)
    python3 build_ckernel.py --clean    # remove the built module

Headers and the extension suffix come from the interpreter that runs this
script, never from `python3-config` on PATH (on NixOS that can belong to a
different Python), so run it with the Python that will import the module. It
only needs a C compiler (`gcc` on PATH, or $CC) and writes only gi/_ckernel*.so.

The sanitizer build has to be run with the sanitizer runtime preloaded, because
the interpreter itself is not instrumented:

    LD_PRELOAD=$(gcc -print-file-name=libasan.so) ASAN_OPTIONS=detect_leaks=0 \\
        PYTHONMALLOC=malloc python3 -m pytest -q tests/test_ckernel.py
"""
import argparse
import glob
import hashlib
import os
import shlex
import subprocess
import sys
import sysconfig

ROOT = os.path.dirname(os.path.abspath(__file__))
SRC = os.path.join(ROOT, "gi", "_ckernel.c")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--asan", action="store_true", help="AddressSanitizer + UBSan build")
    ap.add_argument("--clean", action="store_true", help="remove the built module")
    args = ap.parse_args()
    suffix = sysconfig.get_config_var("EXT_SUFFIX")
    out = os.path.join(ROOT, "gi", "_ckernel" + suffix)
    if args.clean:
        for f in glob.glob(os.path.join(ROOT, "gi", "_ckernel*.so")):
            os.remove(f)
            print("removed", f)
        return
    with open(SRC, "rb") as f:
        digest = hashlib.sha256(f.read()).hexdigest()
    cc = shlex.split(os.environ.get("CC", "gcc"))
    flags = ["-std=gnu11", "-fPIC", "-shared", "-Wall", "-Wextra", "-Wno-unused-parameter",
             "-fno-strict-overflow", f'-DCK_SOURCE_HASH="{digest}"',
             "-I" + sysconfig.get_paths()["include"]]
    if args.asan:
        flags += ["-O1", "-g", "-fno-omit-frame-pointer", "-fsanitize=address,undefined",
                  "-fno-sanitize-recover=undefined"]
    else:
        flags += ["-O3", "-DNDEBUG"]
    cmd = cc + flags + [SRC, "-o", out]
    print(" ".join(shlex.quote(c) for c in cmd))
    subprocess.run(cmd, check=True)
    # The module must load in this interpreter, and must be the source just built.
    check = ("import importlib.machinery as m, importlib.util as u, sys;"
             f"l = m.ExtensionFileLoader('_ckernel', {out!r});"
             "s = u.spec_from_loader('_ckernel', l);"
             "k = u.module_from_spec(s); l.exec_module(k);"
             f"assert k.SOURCE_HASH == {digest!r}; print('built', k.__file__)")
    env = None
    if args.asan:                       # (the runtime must come first in the process)
        lib = subprocess.run(cc + ["-print-file-name=libasan.so"], check=True,
                             capture_output=True, text=True).stdout.strip()
        env = dict(os.environ, LD_PRELOAD=lib, ASAN_OPTIONS="detect_leaks=0")
    subprocess.run([sys.executable, "-c", check], check=True, env=env)


if __name__ == "__main__":
    main()
