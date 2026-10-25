import numpy as np, sys, itertools, time
sys.path.insert(0, '/home/user/degree-diameter/research/d10D7/ovoid')
from subgeo import *
ids217 = [int(x) for x in open('/home/user/degree-diameter/research/d10D7/sets/P8_r5c4_217.txt').read().split()]
U, Uinv, spids = special_basis(ids217)
def perm_of_sigma(sig): M = perm_matrix(sig); return perm_from_c_map(U, Uinv, lambda c, M=M: matvec(M, c))
frob = perm_from_c_map(U, Uinv, lambda c: MT[c, c])
Mt = np.eye(6, dtype=np.int64)
for j in range(6): Mt[:, j] ^= 1      # tau: u_j -> u_j + (u_0+...+u_5); S8 = <S7, tau>
tau = perm_from_c_map(U, Uinv, lambda c: matvec(Mt, c))
def sig_from_cycles(*cyc):
    s = list(range(7))
    for c in cyc:
        for a, b in zip(c, c[1:] + c[:1]): s[a] = b
    return s
fano = [sorted([i, (i + 1) % 7, (i + 3) % 7]) for i in range(7)]
def fano_auts():
    L = set(tuple(l) for l in fano); out = []
    for p in itertools.permutations(range(7)):
        if all(tuple(sorted(p[x] for x in l)) in L for l in L): out.append(list(p))
    return out
groups = {
  'S7': [sig_from_cycles((0, 1)), sig_from_cycles((0, 1, 2, 3, 4, 5, 6))],
  'A7': [sig_from_cycles((0, 1, 2)), sig_from_cycles((1, 2, 3, 4, 5, 6, 0))[:]],
  'S6': [sig_from_cycles((0, 1)), sig_from_cycles((0, 1, 2, 3, 4, 5))],
  'L32': None,
  '7:6': [sig_from_cycles((0, 1, 2, 3, 4, 5, 6)), [ (3 * x) % 7 for x in range(7)]],
  '7:3': [sig_from_cycles((0, 1, 2, 3, 4, 5, 6)), [ (2 * x) % 7 for x in range(7)]],
  'S5xS2': [sig_from_cycles((0, 1)), sig_from_cycles((0, 1, 2, 3, 4)), sig_from_cycles((5, 6))],
  'S4xS3': [sig_from_cycles((0, 1)), sig_from_cycles((0, 1, 2, 3)), sig_from_cycles((4, 5)), sig_from_cycles((4, 5, 6))],
}
FA = fano_auts(); groups['L32'] = FA[1:4] + FA[10:13]
want = sys.argv[1:] if len(sys.argv) > 1 else list(groups)
for name in want:
    for withF in (False, True):
        for withT in ((False, True) if name == 'S7' else (False,)):
            gens = [perm_of_sigma(s) for s in groups[name]] + ([frob] if withF else []) + ([tau] if withT else [])
            t0 = time.time(); lab = orbits(gens)
            sizes, members, S, A = orbit_graph(lab)
            w = sizes[S]
            if len(S) == 0: print('%-6s frob=%d S8=%d orbits %d selfcompat 0' % (name, withF, withT, len(sizes)), flush=True); continue
            bw, cl, exact = max_weight_clique(A, w.tolist(), time_limit=120)
            print('%-6s frob=%d S8=%d orbits %d selfcompat %d  best union %d (%s) orbits %s  [%.0fs]' % (name, withF, withT,
                  len(sizes), len(S), bw, 'exact' if exact else 'time limit', sorted(w[cl].tolist()), time.time() - t0), flush=True)
