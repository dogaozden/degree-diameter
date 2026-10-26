#!/usr/bin/env python3
"""c5 helper: hexgen2 data loader, solution-file writer and lift3 evaluator (all files stay in this folder).
Lift vertices: points 0..N-1, lines N..2N-1; hexagon flag (p, l) voltage hv[l*(q+1)+k] (p = k-th point of line l),
matching t: point p -- line sig_t[p] with voltage mv_t[p] (direction point -> line). Group Z_m (cyc m)."""
import os, re, struct, subprocess

HERE = os.path.dirname(os.path.abspath(__file__))

def load_hex(q):
    data = open(os.path.join(HERE, "hex", "hex_q%d.bin" % q), "rb").read()
    qq, N, L = struct.unpack_from("<3i", data, 0)
    assert qq == q and L == N
    Q1 = q + 1
    pl = list(struct.unpack_from("<%di" % (N * Q1), data, 12))
    off = 12 + 4 * N * Q1
    coords = [tuple(data[off + 7 * i: off + 7 * i + 7]) for i in range(N)]
    lines_of = [[] for _ in range(N)]          # lines through each point, in line order
    for l in range(N):
        for k in range(Q1):
            lines_of[pl[l * Q1 + k]].append((l, k))
    return dict(q=q, N=N, Q1=Q1, pl=pl, coords=coords, lines_of=lines_of)

def write_sol(path, q, m, sigs, mvs, hv, D=8):
    with open(path, "w") as f:
        f.write("%d %d %d %d %d\ncyc %d\n" % (q, len(sigs), m, D, 0, m))
        for s in sigs: f.write(" ".join(map(str, s)) + "\n")
        for v in mvs: f.write(" ".join(map(str, v)) + "\n")
        f.write(" ".join(map(str, hv)) + "\n")

def evaluate(q, m, sigs, mvs, hv, tag="tmp", D=8):
    """Write solution file and run lift3 (ITERS=0). Returns fullcost (int) or None."""
    sol = os.path.join(HERE, "sols", "%s_q%d_m%d.sol" % (tag, q, m))
    os.makedirs(os.path.join(HERE, "sols"), exist_ok=True)
    write_sol(sol, q, m, sigs, mvs, hv, D)
    env = dict(os.environ, IN=sol, ITERS="0", GROUP="cyc %d" % m, J=str(len(sigs)), D=str(D))
    r = subprocess.run(["timeout", "120", "nice", "-n", "19", "./lift3", str(q)], cwd=HERE,
                       env=env, capture_output=True, text=True)
    mm = re.search(r"fullcost (\d+)", r.stdout)
    return int(mm.group(1)) if mm else None
