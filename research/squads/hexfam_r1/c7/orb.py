import sys, time, numpy as np
from base import *
sys.path.insert(0, '/home/user/degree-diameter/research/projects/hexagon-family/tools')
from mwc import max_weight_clique
pm = np.load('/home/user/degree-diameter/research/squads/hexfam_r1/c7/permM.npy')
def power_perm(p, k):
    r = np.arange(N)
    for _ in range(k): r = p[r]
    return r
def orbit_labels(perms):
    from scipy.sparse import coo_matrix
    from scipy.sparse.csgraph import connected_components
    rows = np.concatenate([np.arange(N)] * len(perms)); cols = np.concatenate([pp for pp in perms])
    A = coo_matrix((np.ones(len(rows)), (rows, cols)), shape=(N, N))
    nc, lab = connected_components(A, directed=True, connection='weak')
    return nc, lab
def analyse(d, tlimit=120, verbose=True):
    gen = power_perm(pm, 513 // d)
    nc, lab = orbit_labels([gen])
    sizes = np.bincount(lab, minlength=nc)
    # internal validity
    members = [[] for _ in range(nc)]
    for i in range(N): members[lab[i]].append(i)
    valid = []
    for o in range(nc):
        x = members[o][0]
        r = w_row(P[x])
        ms = np.array(members[o])
        if all(r[y] != 0 for y in ms if y != x): valid.append(o)
    vidx = {o: k for k, o in enumerate(valid)}
    nv = len(valid)
    adj = [0] * nv
    for a, o1 in enumerate(valid):
        x = members[o1][0]
        r = w_row(P[x])
        orth = (r == 0)
        cnt = np.bincount(lab[orth], minlength=nc)
        for b, o2 in enumerate(valid):
            if b == a: continue
            if cnt[o2] == 0: adj[a] |= (1 << b)
    dens = sum(bin(x).count('1') for x in adj) / max(1, nv * (nv - 1))
    if verbose: print('d', d, 'orbits', nc, 'sizes', set(sizes.tolist()), 'valid', nv, 'density %.3f' % dens, flush=True)
    if nv == 0: return 0, []
    w = [d] * nv
    t0 = time.time()
    best, verts, done = max_weight_clique(w, adj, tlimit)
    sel = [valid[v] for v in verts]
    pts = sorted(i for o in sel for i in members[o])
    if verbose: print('  clique orbits', len(verts), 'points', best, 'exact', done, 'time %.1f' % (time.time()-t0), flush=True)
    return best, pts
if __name__ == '__main__':
    d = int(sys.argv[1]); tl = float(sys.argv[2]) if len(sys.argv) > 2 else 120
    best, pts = analyse(d, tl)
    if pts:
        from base import P
        ok = all(w_pair(P[a], P[b]) != 0 for i, a in enumerate(pts) for b in pts[i+1:])
        print('verified pairwise', ok, len(pts))
        open('/home/user/degree-diameter/research/squads/hexfam_r1/c7/orb_d%d_%d.txt' % (d, len(pts)), 'w').write(' '.join(map(str, pts)) + '\n')
