"""c4: quotient of the 168 lift (2+2 base over G=SmallGroup(42,2)) by a subgroup H, plus gadget starts.
Usage: quot.py H_ORDER SEED NGADGET   -> writes H<h>_base.sol (no gadget, verification) and H<h>_g<seed>.sol
Vertex (u,g)=u*42+g; base edge (u,v,a) gives (u,g)~(v,g*a). H acts by left multiplication.
Quotient vertex = H-orbit of (u,g); lift over H: (O,i) = H_list[i]*rep(O), edge (O1,i)~(O2,i*b)."""
import sys, random, itertools

GT = "/home/user/degree-diameter/research/d3D7/groups/g42.txt"
BASE = [(0,2),(0,2),(0,3),(1,2),(1,3),(1,3)]
VOLT = [0,21,0,0,5,2]
NG = 42

def read_group(path, gid):
    tok = open(path).read().split(); i = 0
    while i < len(tok):
        N, g = int(tok[i+1]), int(tok[i+2]); i += 4
        if g == gid:
            return N, [list(map(int, tok[i+r*N:i+(r+1)*N])) for r in range(N)]
        i += N*N
    raise SystemExit("no group")

N, M = read_group(GT, 2)
assert N == NG
inv = [next(b for b in range(N) if M[a][b] == 0) for a in range(N)]

def closure(gens):
    S = {0}
    frontier = [0]
    while frontier:
        new = []
        for x in frontier:
            for g in gens:
                y = M[x][g]
                if y not in S: S.add(y); new.append(y)
        frontier = new
    return frozenset(S)

def subgroup_of_order(h):
    cands = set()
    for x in range(N):
        for y in range(N):
            S = closure([x, y])
            if len(S) == h: cands.add(S)
    return sorted(cands, key=lambda S: sorted(S))

def canon_map(H):
    """canonical rep of each element g: min over h of M[h][g] (as element index)"""
    return [min(M[h][g] for h in H) for g in range(N)]

def build_quotient(H, edges_base, volts):
    """returns (H_list, reps (list of (u,r)), qedges [(iO1, iO2, hidx)], plus map)"""
    H_list = sorted(H, key=lambda x: (x != 0, x))  # identity first
    hidx = {x: i for i, x in enumerate(H_list)}
    h = len(H_list)
    canon = canon_map(H)
    reps = []  # (u, r)
    oid = {}  # (u, g) -> orbit index
    for u in range(4):
        seen = {}
        for g in range(N):
            c = canon[g]
            if c not in seen:
                seen[c] = len(reps); reps.append((u, c))
            oid[(u, g)] = seen[c]
    # per-orbit: u, rep r. lifted vertex (O,i) = H_list[i]*r
    qedges = []
    for O, (u, r) in enumerate(reps):
        if u not in (0, 1): continue
        for (uu, v), a in zip(edges_base, volts):
            if uu != u: continue
            y = M[r][a]  # r*a
            O2 = oid[(v, y)]
            _, g2 = reps[O2]
            # y = h0 * g2  => h0 = y * g2^{-1}
            h0 = M[y][inv[g2]]
            assert h0 in H, "voltage not in H"
            qedges.append((O, O2, hidx[h0]))
    # group table of H reindexed
    T = [[hidx[M[a][b]] for b in H_list] for a in H_list]
    return H_list, reps, oid, qedges, T

def lift_edges(nv, qedges, h, T):
    """lift to explicit edge list over H with (O,i)->O*h+i; returns set of frozenset edges"""
    E = set()
    for (O1, O2, b) in qedges:
        for i in range(h):
            j = T[i][b]
            E.add(frozenset((O1*h+i, O2*h+j)))
    return E

def original_edges():
    E = set()
    for (u, v), a in zip(BASE, VOLT):
        for g in range(N):
            E.add(frozenset((u*N+g, v*N+M[g][a])))
    return E

if __name__ == "__main__":
    h = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    subs = subgroup_of_order(h)
    H = subs[0]
    print("subgroups of order", h, ":", len(subs), "using", sorted(H), file=sys.stderr)
    H_list, reps, oid, qedges, T = build_quotient(H, BASE, VOLT)
    nq = len(reps); assert nq == 168 // h, (nq, h)
    # verify: lift of quotient equals original graph under (O,i)->H_list[i]*rep(O)
    lifted = lift_edges(nq, qedges, h, T)
    mapped = set()
    for e in lifted:
        a, b = tuple(e)
        def tomap(x):
            O, i = divmod(x, h)
            u, r = reps[O]
            return u*N + M[H_list[i]][r]
        mapped.add(frozenset((tomap(a), tomap(b))))
    orig = original_edges()
    print("lift == original graph:", mapped == orig, len(mapped), len(orig), file=sys.stderr)
    assert mapped == orig
    # write base .sol (no gadget): whites 0..nw-1 as in quotient (white orbits first), blacks after
    # quotient vertices: whites are orbits with u in {0,1}, blacks u in {2,3}
    whites = [O for O, (u, r) in enumerate(reps) if u in (0, 1)]
    blacks = [O for O, (u, r) in enumerate(reps) if u in (2, 3)]
    p = len(whites)
    newidx = {}
    for k_, O in enumerate(whites): newidx[O] = k_
    for k_, O in enumerate(blacks): newidx[O] = p + k_
    # write group table file for H
    gname = f"/home/user/degree-diameter/research/squads/d3D7-r1/c4/H{h}.txt"
    with open(gname, "w") as f:
        f.write(f"G {h} 1 H{h}\n")
        for row in T: f.write(" ".join(map(str, row)) + "\n")
    E = [(newidx[O1], newidx[O2], b) for (O1, O2, b) in qedges]
    # gadget: optionally
    import os
    out = f"/home/user/degree-diameter/research/squads/d3D7-r1/c4/H{h}_base.sol"
    with open(out, "w") as f:
        f.write(f"{h} 1 {p}\n")
        for (a, b, c) in E: f.write(f"{a} {b} {c}\n")
    print("base written", out, "p=", p, "edges", len(E), file=sys.stderr)
