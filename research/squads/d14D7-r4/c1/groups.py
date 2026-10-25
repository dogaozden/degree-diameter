# c1 (r4): for each commuting pair (g,h) of c3's isometries, enumerate all subgroups H of <g,h>, compute the
# H-orbits of E (q = 11), keep the independent ones ("usable"), and write each H's cycle permutation
# (cycles = H-orbits) to permH_<tag>.txt for orbitclique. Prints one summary line per subgroup.
import glob, os, sys, json
from collections import Counter
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r4/c1')
from survey import load, group_closure, orbits_of_gens

D = '/home/user/degree-diameter/research/cell147/data/'
OUT = '/home/user/degree-diameter/research/squads/d14D7-r4/c1/'
p = 11
rows = np.loadtxt(D + 'E11.map', dtype=np.int64)
pid, sline = rows[:, 0], rows[:, 1]
X = rows[:, 2:9] % p
n = len(X)
M7 = np.zeros((7, 7), dtype=np.int64)
M7[0, 4] = M7[4, 0] = 1; M7[1, 5] = M7[5, 1] = 1; M7[2, 6] = M7[6, 2] = 1; M7[3, 3] = -2
def Bm(A, Bv):
    return (A @ M7 @ Bv.T) % p

def pairs_for(name_pair):
    return name_pair

if __name__ == '__main__':
    files = sorted(glob.glob(D + 'perms_q11/*.txt'))
    P = {os.path.basename(f)[:-4]: load(f) for f in files}
    commuting = json.load(open(OUT + 'survey.json'))['commuting']
    summary = []
    tagn = 0
    seen_groups = set()
    for (x, y) in commuting:
        G = group_closure([P[x], P[y]], n)
        # index the group elements
        idx = {g.tobytes(): i for i, g in enumerate(G)}
        Gl = G
        def mul(i, j):
            return idx[Gl[i][Gl[j]].tobytes()]
        # subgroups by closure: each subgroup stored as (frozenset of ids, generator ids)
        triv = frozenset([idx[np.arange(n, dtype=np.int64).tobytes()]])
        subs = {triv: []}
        frontier = [triv]
        while frontier:
            nf = []
            for H in frontier:
                gens = subs[H]
                for g in range(len(Gl)):
                    if g in H: continue
                    # closure of H with g
                    S = set(H) | {g}
                    changed = True
                    while changed:
                        changed = False
                        for a in list(S):
                            for b in list(S):
                                c = mul(a, b)
                                if c not in S:
                                    S.add(c); changed = True
                    Sf = frozenset(S)
                    if Sf not in subs:
                        subs[Sf] = gens + [g]; nf.append(Sf)
            frontier = nf
        for H, gens in sorted(subs.items(), key=lambda t: len(t[0])):
            if len(H) == 1: continue
            gperms = [Gl[i] for i in gens]
            mem = orbits_of_gens(gperms, n)
            usable = []
            for mi, m in enumerate(mem):
                if len(m) == 1: usable.append(mi); continue
                Gm = Bm(X[m], X[m]); np.fill_diagonal(Gm, 1)
                if np.all(Gm != 0): usable.append(mi)
            sz = Counter(len(mem[mi]) for mi in usable)
            ucount = sum(len(mem[mi]) for mi in usable)
            key = tuple(sorted(H))
            tag = f"{x.replace('elems_o4_','').replace('seed1_d4','seedd4')}__{y.replace('elems_o4_','').replace('seed1_d4','seedd4')}__H{len(H)}_{tagn}"
            tagn += 1
            perm = np.arange(n, dtype=np.int64)
            for mi in usable:
                m = mem[mi]
                for k in range(len(m)):
                    perm[m[k]] = m[(k + 1) % len(m)]
            # the perm for orbitclique: cycles = usable orbits only (non-usable points are fixed points)
            # but orbitclique needs all points in cycles; non-usable orbits are cycled too (they're excluded anyway)
            perm = np.arange(n, dtype=np.int64)
            for mi in range(len(mem)):
                m = mem[mi]
                for k in range(len(m)):
                    perm[m[k]] = m[(k + 1) % len(m)]
            fn = OUT + f"permH_{tag}.txt"
            np.savetxt(fn, perm, fmt='%d')
            line = dict(tag=tag, g=x, h=y, order=len(H), gens=[x, y] if False else None, norb=len(mem),
                        usable_orbits=len(usable), usable_points=ucount, usable_sizes=dict(sorted(sz.items())),
                        perm=fn)
            summary.append(line)
            print(f"{tag:55s} |H|={len(H):3d} orbits={len(mem):5d} usable={len(usable):5d} usable_pts={ucount:5d} sizes={dict(sorted(sz.items()))}", flush=True)
    json.dump(summary, open(OUT + 'groups_summary.json', 'w'), indent=1)
