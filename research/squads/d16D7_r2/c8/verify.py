import numpy as np, sys, time
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d16D7_r2/c8')
from load import *
from geo import *
t0 = time.time()
q, N, L, LP, X = load_hex()
gp = load_perm(D+'data/g13o61_pts.bin'); gl = load_perm(D+'data/g13o61_lines.bin')
PL = build_PL(LP, N)            # lines through each point (N,14)
PLl = build_PL(LP, N)           # placeholder
orbit_p, orbs_p = orbits_of(gp)
orbit_l, orbs_l = orbits_of(gl)
print('orbits', len(orbs_p), len(orbs_l), 'time', round(time.time()-t0,1), flush=True)
np.save('orbit_pts.npy', orbit_p); np.save('orbit_lines.npy', orbit_l)
def geo_adj(kind):
    # collinear elements of each element: points -> points sharing a line; lines -> lines sharing a point
    orbit_e = orbit_p if kind == 'pts' else orbit_l
    orbs = orbs_p if kind == 'pts' else orbs_l
    M, E, rep, nb = load_og(D+('og_pts.txt' if kind == 'pts' else 'og_lines.txt'))
    NO = len(orbs)
    # reps as orbit indices
    vid = {int(orbit_e[rep[i]]): i for i in range(M)}
    selfc = set(); pairs_list = []
    for o, cyc in enumerate(orbs):
        pass
    # for each vertex orbit, its elements' neighbour orbits
    res = {}
    cyc_arr = {}
    vert_orbits = np.array(sorted(vid.keys()))
    edges = set()
    selfcol = np.zeros(NO, bool)
    chunk = 400
    for c0 in range(0, len(vert_orbits), chunk):
        ob = vert_orbits[c0:c0+chunk]
        elems = np.array([orbs[o] for o in ob], dtype=np.int64)  # (c,61)
        flat = elems.ravel()
        if kind == 'pts':
            lines = PL[flat]                       # (k,14)
            nbrs = LP[lines].reshape(len(flat), -1)  # (k,196) includes self
        else:
            pts = LP[flat]                         # (k,14)
            nbrs = PL[pts].reshape(len(flat), -1)   # (k,196)
        owner = np.repeat(np.arange(len(ob)), 61)
        no = orbit_e[nbrs]                         # orbit ids of neighbours
        own = np.repeat(ob, 61)[:, None]
        same = (no == own)
        # self-collinear: neighbour (not the element itself) in same orbit
        selfflag = same & (nbrs != flat[:, None])
        if selfflag.any():
            for o in np.unique(own[selfflag.any(axis=1)]): selfcol[o] = True
        sel = (~same)
        a = np.repeat(ob, 61)[:, None].repeat(nbrs.shape[1], axis=1)[sel]
        b = no[sel]
        key = np.unique(a * NO + b)
        for k in key: edges.add(int(k))
    print(kind, 'self-collinear orbits', int(selfcol.sum()), 'vertex orbits', len(vert_orbits), 'selfcol among vertices', int(selfcol[vert_orbits].sum()), flush=True)
    mism = 0
    nbset = {}
    for k in edges:
        a, b = divmod(k, NO)
        nbset.setdefault(a, set()).add(b)
    for i in range(M):
        o = int(orbit_e[rep[i]])
        g_nb = set(vid[x] for x in nbset.get(o, set()) if x in vid)
        if g_nb != set(nb[i].tolist()): mism += 1
    print(kind, 'mismatched vertices', mism, 'of', M, 'time', round(time.time()-t0,1), flush=True)
    return selfcol
s1 = geo_adj('pts')
s2 = geo_adj('lines')
