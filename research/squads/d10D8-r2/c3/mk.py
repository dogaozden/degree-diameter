#!/usr/bin/env python3
"""r2-c3: explicit voltage rules for lifts of GH(q) (incidence graph of H(q)) + 2 point->line matchings.

Writes lift3 solution files (format of research/d10D8/hex/lift2.c save()) and evaluates them with
research/d10D8/hex/lift3 IN=... ITERS=0 (fullcost 0 = DIAMETER_OK at D=8).
Nothing here is annealed: every voltage and matching is a fixed formula of the hexgen2 data
(point ids, line table, PG(6,q) coordinates).
"""
import struct, subprocess, sys, os, re, time

HEXDIR = "/home/user/degree-diameter/research/d10D8/hex"
OUTDIR = "/home/user/degree-diameter/research/squads/d10D8-r2/c3/sols"

def load_hex(q):
    data = open(os.path.join(HEXDIR, "hex", "hex_q%d.bin" % q), "rb").read()
    qq, N, L = struct.unpack_from("<3i", data, 0)
    assert qq == q and L == N
    Q1 = q + 1
    pl = list(struct.unpack_from("<%di" % (N * Q1), data, 12))   # pl[l*Q1+k] = k-th point of line l
    off = 12 + 4 * N * Q1
    coords = [tuple(data[off + 7 * i: off + 7 * i + 7]) for i in range(N)]
    return N, Q1, pl, coords

def write_sol(path, q, J, m, gspec, sigs, mvs, hv, cost=0):
    with open(path, "w") as f:
        f.write("%d %d %d %d %d\n%s\n" % (q, J, m, 8, cost, gspec))
        for s in sigs: f.write(" ".join(map(str, s)) + "\n")
        for v in mvs: f.write(" ".join(map(str, v)) + "\n")
        f.write(" ".join(map(str, hv)) + "\n")

def evaluate(q, solpath, gspec, J=2):
    """Run lift3 (ITERS=0) on a solution file. Returns fullcost (int) or None."""
    env = dict(os.environ, IN=solpath, ITERS="0", GROUP=gspec, J=str(J), D="8")
    r = subprocess.run(["timeout", "120", "nice", "-n", "19", "./lift3", str(q)], cwd=HEXDIR,
                       env=env, capture_output=True, text=True)
    m = re.search(r"fullcost (\d+)", r.stdout)
    return int(m.group(1)) if m else None
