# c6_struct.py FLAGS GHFILE: structure of a packing: distance-4 pairs (points and lines), pointing, components ("chains")
import sys, collections, itertools
flagsfile, ghfile = sys.argv[1], sys.argv[2]
with open(ghfile) as f:
    P, q = map(int, f.readline().split())
    lines = [list(map(int, f.readline().split())) for _ in range(P)]
pl = collections.defaultdict(list)
for l, pts in enumerate(lines):
    for p in pts: pl[p].append(l)
flags = [tuple(map(int, s.split())) for s in open(flagsfile) if s.strip()]
n = len(flags)
def mid_point(p, p2):   # midpoint x and lines M1=(p,x), M2=(x,p2) for points at distance 4
    for M in pl[p]:
        for x in lines[M]:
            if x == p: continue
            for N in pl[x]:
                if N != M and p2 in lines[N]:
                    return x, M, N
    return None
pt_pairs = []; ln_pairs = []
for i, j in itertools.combinations(range(n), 2):
    p, l = flags[i]; p2, l2 = flags[j]
    r = mid_point(p, p2)
    if r is not None:
        x, M1, M2 = r
        pt_pairs.append((i, j, M1 == l, M2 == l2))   # pointing: flag i's line is the first geodesic line, or flag j's
    # line side: lines l, l2 at distance 4 iff not concurrent and joined by path l - x - K - y - l2
    if set(lines[l]) & set(lines[l2]): continue
    found = None
    for x in lines[l]:
        for K in pl[x]:
            if K == l: continue
            for y in lines[K]:
                if y != x and l2 in pl[y]:
                    found = (x, K, y)
    if found is not None:
        x, K, y = found
        ln_pairs.append((i, j, x == p, y == p2))  # flag i's point on the geodesic, or flag j's point
print("point distance-4 pairs:", len(pt_pairs), " pointing ok:", all(a or b for _, _, a, b in pt_pairs),
      " both-point-toward:", sum(1 for _, _, a, b in pt_pairs if a and b))
print("line distance-4 pairs:", len(ln_pairs), " pointing ok:", all(a or b for _, _, a, b in ln_pairs),
      " both-point-toward:", sum(1 for _, _, a, b in ln_pairs if a and b))
# components of the point distance-4 graph
adj = collections.defaultdict(set)
for i, j, _, _ in pt_pairs: adj[i].add(j); adj[j].add(i)
seen = set(); comps = []
for s in range(n):
    if s in seen or s not in adj: continue
    st = [s]; comp = []; seen.add(s)
    while st:
        v = st.pop(); comp.append(v)
        for w in adj[v]:
            if w not in seen: seen.add(w); st.append(w)
    comps.append(len(comp))
print("point distance-4 graph: degrees", sorted(len(adj[v]) for v in adj), " components (sizes)", sorted(comps, reverse=True))
print("isolated flags (all pairs opposite on points):", n - len(adj))
