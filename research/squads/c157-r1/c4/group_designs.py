#!/usr/bin/env python3
"""Group route (construction B of make_designs.py) for K where Z_K has no difference cover of size 8.
Enumerates metacyclic groups Z_m x|_r Z_k (m*k = K, r^k = 1 mod m), writes each multiplication table to a scratch file,
runs ./group_exh (exhaustive search, C source group_exh.c) for D with |D| = 8, and writes hgK.hg from the first hit.
Usage: python3 group_designs.py K [K ...]     (needs ./group_exh compiled: gcc -O2 -o group_exh group_exh.c)
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from checker import check_file  # noqa: E402
from make_designs import write_hg  # noqa: E402


def metacyclic(m, k, r):
    """Group on indices g = j*m + x (x in Z_m, j in Z_k), (x,j)(y,l) = (x + r^j y, j + l)."""
    K = m * k
    rp = [pow(r, j, m) for j in range(k)]
    mul = [[0] * K for _ in range(K)]
    for g in range(K):
        x, j = g % m, g // m
        for h in range(K):
            y, l = h % m, h // m
            mul[g][h] = ((j + l) % k) * m + (x + rp[j] * y) % m
    return mul


def groups(K):
    out = []
    for m in range(2, K + 1):
        if K % m:
            continue
        k = K // m
        if k < 2:
            continue
        for r in range(1, m):
            if __import__("math").gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    return out


def run(K, s=8):
    binpath = os.path.join(HERE, "group_exh")
    for (m, k, r) in groups(K):
        mul = metacyclic(m, k, r)
        with tempfile.NamedTemporaryFile("w", suffix=".tab", delete=False, dir=os.environ.get("SCRATCH", None)) as f:
            f.write(f"{K} 0\n")
            for row in mul:
                f.write(" ".join(map(str, row)) + "\n")
            tab = f.name
        out = subprocess.run([binpath, tab, str(s), "1"], capture_output=True, text=True, timeout=900).stdout
        os.unlink(tab)
        last = out.strip().splitlines()[-1] if out.strip() else "no output"
        sols = [line for line in out.splitlines() if line.startswith("sol:")]
        print(f"K={K} group Z_{m} x|_{r} Z_{k}: {last}", flush=True)
        if sols:
            D = [int(x) for x in sols[0].split()[1:]]
            edges = [(g, mul[g][d]) for g in range(K) for d in D]
            path = os.path.join(HERE, f"hg{K}.hg")
            write_hg(path, K, edges)
            ok, info = check_file(path)
            print(f"   D={D} written to {path}: {'PASS' if ok else 'FAIL'} m={info['m']} maxdeg={info['maxdeg']}", flush=True)
            if ok:
                return True
    return False


if __name__ == "__main__":
    for arg in sys.argv[1:]:
        run(int(arg))
