import subprocess, sys, os, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
def hub_check(G, path=None):
    """Write graph and run hub4 (C checker). Returns dict with valid, nA, nB, maxdeg."""
    os.makedirs(os.path.join(HERE, "tmp"), exist_ok=True)
    fd, p = tempfile.mkstemp(suffix=".edges", dir=os.path.join(HERE, "tmp")) if path is None else (None, path)
    if fd is not None: os.close(fd)
    G.write(p)
    out = subprocess.run([os.path.join(HERE, "hub4"), p], capture_output=True, text=True, timeout=600).stdout
    if path is None: os.remove(p)
    kv = dict(x.split("=") for x in out.split()[1:] if "=" in x)
    return dict(valid=int(kv.get("valid", 0)), nA=int(kv.get("nA", -1)), nB=int(kv.get("nB", -1)),
                maxdeg=int(kv.get("maxdeg", -1)), bad=int(kv.get("bad", -1)), n=int(kv.get("n", -1)))
