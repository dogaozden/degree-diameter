import collections, sys
exec(open('dbg.py').read().split("# walks of length exactly 4")[0])
# lift BFS from (0,0) depth 5
n = 6 * 1152
L_adj = collections.defaultdict(list)
for (u, v, g) in base:
    for h in range(6):
        L_adj[6*u+h].append(6*v+(h+g)%6)
        L_adj[6*v+(h+g)%6].append(6*u+h)
dist = {0: 0}; fr = [0]
for d in range(1, 6):
    nf = []
    for x in fr:
        for y in L_adj[x]:
            if y not in dist:
                dist[y] = d; nf.append(y)
    fr = nf
unreached = [x for x in range(n) if x not in dist]
pts_unreached = [x for x in unreached if x//6 < 512]
print("unreached total", len(unreached), "point-targets unreached", len(pts_unreached))
print("colour-0 point targets unreached (h even):", sum(1 for x in pts_unreached if (x%6)%2==0))
print("sample:", pts_unreached[:12])
# dist histogram of point targets with h even
hist = collections.Counter(dist.get(6*u+h, -1) for u in range(512) for h in (0,2,4))
print("dist histogram of colour-0 point lift vertices:", sorted(hist.items()))
