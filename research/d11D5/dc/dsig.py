"""Replace sigma of a DM base by delta o C (C a random collineation of PG(3,8), delta the polarity of W(8));
new points (ids >= 585) keep sigma(x) = x-th new line.  usage: dsig.py base.in seed out.in [frob]"""
import sys, json, random
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5")
import os; here=os.getcwd(); os.chdir("/home/user/degree-diameter/research/d11D5")
from dcover import load
n0, L, d_pt, d_ln, inv = load(8); W = json.load(open("w8.json")); os.chdir(here)
from w8 import field
mul, finv = field(8)
pts = [tuple(v) for v in W["points"]]; idx = {v: i for i, v in enumerate(pts)}
def norm(v):
    for c in v:
        if c: s = finv[c]; return tuple(mul[s][x] for x in v)
def det_nonzero(M):
    # gaussian elimination over GF(8)
    A = [r[:] for r in M]
    for c in range(4):
        piv = next((r for r in range(c, 4) if A[r][c]), None)
        if piv is None: return False
        A[c], A[piv] = A[piv], A[c]
        iv = finv[A[c][c]]
        for r in range(c + 1, 4):
            if A[r][c]:
                f = mul[A[r][c]][iv]
                A[r] = [A[r][k] ^ mul[f][A[c][k]] for k in range(4)]
    return True
def randC(rng):
    while True:
        M = [[rng.randrange(8) for _ in range(4)] for _ in range(4)]
        if det_nonzero(M): return M
def apply(M, v, fr):
    if fr: 
        for _ in range(fr): v = tuple(mul[x][x] for x in v)
    return norm(tuple(mul[M[i][0]][v[0]] ^ mul[M[i][1]][v[1]] ^ mul[M[i][2]][v[2]] ^ mul[M[i][3]][v[3]] for i in range(4)))
if __name__ == "__main__":
    base, seed, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]; fr = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    t = open(base).read().split(); n, dg = int(t[0]), int(t[1])
    rng = random.Random(seed); M = randC(rng)
    Cp = [idx[apply(M, p, fr)] for p in pts]
    sig = [d_pt[Cp[p]] for p in range(n0)] + list(range(n0, n))
    assert sorted(sig) == list(range(n))
    with open(out, "w") as f:
        f.write(f"{n} {dg}\n")
        for l in range(n): f.write(" ".join(t[2 + l*dg: 2 + l*dg + dg]) + "\n")
        for s in sig: f.write(f"{s}\n")
