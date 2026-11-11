# Referee check: for each f = 0 file, solve alpha(s0) s0^-1 = tau and verify alpha(T s0) = T s0 with the stated cycles.
# Run from this folder: python3 s0check.py
import sys, re, numpy as np
sys.argv = [sys.argv[0]]
from refcheck import Mat, factor_of
S = '/home/user/degree-diameter/research/frontier/sols/'
# (file, factor specs, g per factor, r, c per factor, c_z) from orbit_check logs
cases = [
 ('d6D8_psl_11_24_orb2f0_s1.txt', [('psl',11,None)], [(6,10,4,5)], 11, [(0,4,8,5)], 0, 2),
 ('d9D8_psl_19_79_orb3_s1.txt', [('psl',19,None)], [(1,3,6,0)], 23, [(5,4,0,4)], 21, 3),
 ('d15D8_sl_109_7_orb3f0_s1.txt', [('sl',109,None)], [(46,0,37,64)], 2, [(78,40,108,54)], 0, 3),
 ('d6D9_sl_17_13_orb3f0_s2.txt', [('sl',17,None)], [(5,16,4,13)], 3, [(2,16,4,7)], 3, 3),
 ('d12D9_sl_41_247_orb3f0_s1.txt', [('sl',41,None)], [(5,2,10,37)], 68, [(6,21,1,31)], 59, 3),
 ('d15D9_sl_79_211_orb3f0_s1.txt', [('sl',79,None)], [(40,1,19,40)], 14, [(54,52,76,22)], 9, 3),
 ('d9D10_psl_71_67_orb3f0_s1.txt', [('psl',71,None)], [(2,41,31,68)], 29, [(6,57,49,16)], 53, 3),
 ('d12D10_sl_107_133_orb3f0_s1.txt', [('sl',107,None)], [(66,72,53,40)], 11, [(33,22,40,4)], 80, 3),
 ('d15D10_sl_149_373_orb3f0_s1.txt', [('sl',149,None)], [(0,148,1,1)], 88, [(105,144,40,35)], 161, 3),
 ('d9D9_prod_psl_7_sl_7_31_orb3f0_s1.txt', [('psl',7,None),('sl',7,None)], [(3,2,4,3),(3,0,6,5)], 5, [(3,6,5,1),(6,4,6,3)], 26, 3),
 ('d6D10_prod_sl_5_psl_7_13_orb3f0_s1.txt', [('sl',5,None),('psl',7,None)], [(2,2,1,4),(0,3,2,1)], 3, [(0,4,1,1),(3,5,2,6)], 8, 3),
]
def mul(F, X, Y):   # X, Y arrays (m,4)
    A, M = F.A, F.M
    return np.stack([A[M[X[:,0],Y[:,0]], M[X[:,1],Y[:,2]]], A[M[X[:,0],Y[:,1]], M[X[:,1],Y[:,3]]],
                     A[M[X[:,2],Y[:,0]], M[X[:,3],Y[:,2]]], A[M[X[:,2],Y[:,1]], M[X[:,3],Y[:,3]]]], 1)
for fn, specs, gs, r, cs, cz, k in cases:
    lines = open(S + fn).read().splitlines()
    n = int(lines[0].split()[lines[0].split().index('n') + 1])
    T = []
    for ln in lines[1:]:
        mats = [tuple(map(int, m)) for m in re.findall(r'mat\((\d+),(\d+),(\d+),(\d+)\)', ln)]
        if mats: T.append((mats, int(re.search(r'z=(\d+)', ln).group(1))))
    facs = [factor_of(kd, q, pl) for kd, q, pl in specs]
    # solve g s g^-1 s^-1 = c in each factor:  g s = c s g
    sols = []
    for F, g, c in zip(facs, gs, cs):
        E = F.E
        G = np.tile(np.array(g), (len(E), 1)); C = np.tile(np.array(c), (len(E), 1))
        lhs = F.canon(mul(F, G, E)); rhs = F.canon(mul(F, mul(F, C, E), G))
        sols.append(E[lhs == rhs])
    # z part: (r-1) z = cz mod n
    zs = [z for z in range(n) if ((r - 1) * z - cz) % n == 0]
    print(fn, '#solutions per factor', [len(s) for s in sols], 'z solutions', zs[:3], len(zs))
    if not all(len(s) for s in sols) or not zs:
        print('   NO s0'); continue
    s0 = ([tuple(s[0]) for s in sols], zs[0])
    # S = T s0 ; check alpha(S) = S and cycle sizes
    def m1(F, x, y): return tuple(mul(F, np.array([x]), np.array([y]))[0])
    def can(F, x): return int(F.canon(np.array([x]))[0])
    def inv(F, x): a,b,c_,d = x; return (d, int(F.neg[b]), int(F.neg[c_]), a)
    Sset = []
    for mats, t in T:
        Sset.append((tuple(m1(F, x, y) for F, x, y in zip(facs, mats, s0[0])), (t + s0[1]) % n))
    key = lambda el: (tuple(can(F, x) for F, x in zip(facs, el[0])), el[1])
    keys = {key(el): i for i, el in enumerate(Sset)}
    def alpha(el):
        return (tuple(m1(F, m1(F, g, x), inv(F, g)) for F, g, x in zip(facs, gs, el[0])), (r * el[1]) % n)
    perm = []
    for el in Sset:
        kk = key(alpha(el))
        perm.append(keys.get(kk, -1))
    if -1 in perm:
        print('   alpha(S) != S'); continue
    seen = set(); cyc = []
    for i in range(len(perm)):
        if i in seen: continue
        j = i; L = 0
        while j not in seen: seen.add(j); j = perm[j]; L += 1
        cyc.append(L)
    print('   s0 found; alpha(S)=S, cycle sizes', sorted(cyc))
