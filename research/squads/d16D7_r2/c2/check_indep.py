import sys
# independent check: symmetric adjacency, and every pair of solution vertices tested in both directions
g, s = sys.argv[1], sys.argv[2]
with open(g) as f:
    M, E = map(int, f.readline().split())
    nb = [set() for _ in range(M)]
    cnt = 0
    for line in f:
        a = list(map(int, line.split()))
        if not a: continue
        nb[a[0]] = set(a[3:3 + a[2]])
        cnt += a[2]
asym = sum(1 for v in range(M) for w in nb[v] if v not in nb[w])
selfloops = sum(1 for v in range(M) if v in nb[v])
sol = [int(x) for x in open(s) if x.strip() and not x.startswith('#')]
S = set(sol)
bad = [(a, b) for a in sol for b in sol if a < b and (b in nb[a] or a in nb[b])]
print('M=%d E=%d sumdeg=%d asym_arcs=%d selfloops=%d |sol|=%d distinct=%d bad_pairs=%d'
      % (M, E, cnt, asym, selfloops, len(sol), len(S), len(bad)))
