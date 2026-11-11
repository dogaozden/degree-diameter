import re, glob, os, sys
E = "/home/user/degree-diameter/research/squads/raise_d8b/r3/e13"
# name: (family, p, n, k, AG_t, AR, fixed_f, m)  AG = [[0,-1],[1,t]] as printed in the source log
STATES = {
 # name: (family, p, n, k, t = d-entry of printed alpha mat(0,p-1,1,t), AR = z multiplier, f)
 "d01_a.sol.best":      ("sl",  41, 311,  5, 6, 6, 2),
 "d02_start.sol.best":  ("psl", 89, 61,   5, 9, 9, 2),
 "d05_a.sol.best":      ("sl",  31, 1091, 5, 12, 93, 3),
 "d06_d06.sol.best":    ("psl", 97, 71,   7, 25, 20, 4),
 "d07_a.sol.best":      ("psl", 131, 41, 5, 11, 10, 4),
 "d09_a.sol.best":      ("psl", 89, 131,  5, 9, 53, 4),
 "d10_a.sol.best":      ("psl", 59, 451,  5, 25, 16, 4),
 "d11_a.sol.best.orb":  ("sl",  79, 131,  5, 29, 53, 0),
 "d12_a.sol.best.orb":  ("psl", 61, 571,  5, 17, 106, 0),
 "d13_a.sol.best.orb":  ("psl", 109, 101, 5, 10, 36, 0),
}
# AG = [[0,-1],[1,t]] for the printed alpha: matrix mat(0,p-1,1,t)
def mm(A, B, p):
    return ((A[0]*B[0]+A[1]*B[2]) % p, (A[0]*B[1]+A[1]*B[3]) % p,
            (A[2]*B[0]+A[3]*B[2]) % p, (A[2]*B[1]+A[3]*B[3]) % p)
def norm(M, p, psl):
    if not psl: return M
    neg = tuple((-x) % p for x in M)
    return min(M, neg)
def proj_order(M, p, psl):
    I = (1, 0, 0, 1); negI = (p-1, 0, 0, p-1); X = M; o = 1
    while not (X == I or (psl and X == negI) or (X == negI and not psl and False)):
        X = mm(X, M, p); o += 1
        if o > 10**6: return None
    return o
report = []
tsv = ["state\tcost\tidx\tmatrix(a,b,c,d)\tz\talpha_fixed\tz0\tproj_order\tin_alpha_torus(commutes up to sign)\talpha_orbit_size"]
summary = []
for name, (fam, p, n, k, t, AR, f) in STATES.items():
    assert all(True for _ in [0])
    psl = fam == "psl"
    AG = (0, p-1, 1, t % p)
    AGI = (t % p, 1, p-1, 0)          # inverse of [[0,-1],[1,t]] (det 1)
    assert mm(AG, AGI, p) == (1, 0, 0, 1)
    def alpha(key):
        M, z = key
        M2 = norm(mm(mm(AG, M, p), AGI, p), p, psl)
        return (M2, (AR * z) % n)
    Xk = AG; ordA = 1
    while not (Xk in [(1,0,0,1), (p-1,0,0,p-1)]): Xk = mm(Xk, AG, p); ordA += 1
    assert ordA == k, (name, ordA, k)
    holes = []
    for line in open(os.path.join(E, "eval_" + name + ".txt")):
        m = re.match(r"uncovered (\d+) mat\((\d+),(\d+),(\d+),(\d+)\) z=(\d+)", line)
        if m:
            idx = int(m.group(1)); M = tuple(int(m.group(i)) % p for i in (2, 3, 4, 5)); z = int(m.group(6))
            holes.append((idx, norm(M, p, psl), z))
    cost_line = open(os.path.join(E, "eval_" + name + ".txt")).read()
    cost = int(re.search(r"cost=(\d+)", cost_line).group(1))
    if f == 0:   # EVAL reports holes of T = S s0^-1; the S-form hole is h_S = h_T * s0 (B side), S alpha-invariant
        fl = [l for l in open(os.path.join(E, "states", name)) if "mat(" in l][0]
        mm0 = re.search(r"mat\((\d+),(\d+),(\d+),(\d+)\) z=(\d+)", fl)
        M0 = tuple(int(mm0.group(i)) % p for i in (1, 2, 3, 4)); z0s = int(mm0.group(5))
        holes = [(idx, norm(mm(M, M0, p), p, psl), (z + z0s) % n) for idx, M, z in holes]
        print("   f=0: holes mapped from T-form to S-form with s0 =", M0, z0s)
    keyset = {(h[1], h[2]) for h in holes}
    def apow(key, j):
        for _ in range(j): key = alpha(key)
        return key
    assert all(apow(key, k) == key for key in keyset)
    assert len(holes) == cost == len(keyset), (name, len(holes), cost)
    closed = all(alpha(key) in keyset for key in keyset)
    nfix = 0; norb = 0; orbsz = {}
    rows = []
    for idx, M, z in holes:
        key = (M, z)
        o = [key]; X = alpha(key)
        while X != key and len(o) < 1000:
            o.append(X); X = alpha(X)
        size = len(o)
        fixed = size == 1
        z0 = z == 0
        po = proj_order(M, p, psl)
        # torus of alpha: projective centralizer of AG, i.e. M AG = +-AG M
        c1 = mm(M, AG, p); c2 = mm(AG, M, p)
        torus = (c1 == c2) or (c1 == tuple((-x) % p for x in c2))
        nfix += fixed; norb += (not fixed)
        orbsz[size] = orbsz.get(size, 0) + 1
        rows.append((name, cost, idx, M, z, fixed, z0, po, torus, size))
        tsv.append("%s\t%d\t%d\t%s\t%d\t%s\t%s\t%s\t%s\t%d" % (name, cost, idx, str(M).replace(' ', ''), z,
                   'Y' if fixed else 'N', 'Y' if z0 else 'N', po, 'Y' if torus else 'N', size))
    summary.append((name, fam, p, n, k, cost, nfix, norb, orbsz, closed, rows))
    print("%-22s %-4s p=%-4d n=%-5d k=%d cost=%2d fixed=%d orbit_holes=%d orbit_sizes=%s alpha_closed=%s" %
          (name, fam, p, n, k, cost, nfix, norb, dict(sorted(orbsz.items())), closed))
open(os.path.join(E, "holes.tsv"), "w").write("\n".join(tsv) + "\n")
print("---- per hole ----")
for s in summary:
    for r in s[10]:
        print("%-22s idx=%-9d M=%-22s z=%-5d fixed=%-5s z0=%-5s ord=%-4s torus=%-5s orbit=%d" %
              (r[0], r[2], str(r[3]), r[4], r[5], r[6], r[7], r[8], r[9]))
