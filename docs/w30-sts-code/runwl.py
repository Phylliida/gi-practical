import struct, subprocess, sys, os, tempfile
BIN = os.environ.get("WLBIN", "/tmp/claude-1000/-home-bepis-math/117a2777-2472-4276-845a-e0dfeb712755/scratchpad/w30/wl")
def wl(Q, which=3):
    n = len(Q)
    with tempfile.NamedTemporaryFile(delete=False, suffix=".sts", dir=os.path.dirname(BIN)) as f:
        f.write(struct.pack("<i", n))
        f.write(struct.pack(f"<{n*n}i", *[v for row in Q for v in row]))
        path = f.name
    try:
        out = subprocess.run([BIN, path, str(which)], capture_output=True, text=True, timeout=600).stdout
    finally:
        os.unlink(path)
    res = {}
    for line in out.splitlines():
        p = line.split()
        if p[0] == "sig":
            res["sig"] = tuple(p[1:])
        else:
            res[p[0]] = (int(p[2]), [int(v) for v in p[4:]])
    return res
