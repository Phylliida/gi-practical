"""Loader of the optional compiled kernel (gi/_ckernel.c; docs/w16-ckernel.md).

`ck` is the extension module, or None when it is not built or GI_NO_CKERNEL is
set to anything but "" or "0". The pure-Python code in gi/perm.py, gi/group.py
and gi/refine.py is the fallback and the reference, so nothing else depends on
whether the module is present.

A module built from a different version of the source is ignored, with a
warning: running it would mean testing or benchmarking code that is not the
code in the tree.
"""
import hashlib
import os
import warnings

API_VERSION = 1

ck = None


def _load():
    if os.environ.get("GI_NO_CKERNEL", "") not in ("", "0"):
        return None
    try:
        from . import _ckernel as module
    except ImportError:
        return None
    src = os.path.join(os.path.dirname(os.path.abspath(__file__)), "_ckernel.c")
    try:
        with open(src, "rb") as f:
            digest = hashlib.sha256(f.read()).hexdigest()
    except OSError:                     # (an installed copy without the source)
        digest = module.SOURCE_HASH
    if module.API_VERSION != API_VERSION or module.SOURCE_HASH != digest:
        warnings.warn("gi/_ckernel is stale (rebuild with build_ckernel.py); using pure Python",
                      RuntimeWarning, stacklevel=2)
        return None
    return module


ck = _load()


def active():
    """Whether the compiled kernel is in use."""
    return ck is not None
