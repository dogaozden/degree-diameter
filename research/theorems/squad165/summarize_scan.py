import sys, collections
sys.argv = ['x', 'none']
import weyl_graphs as wg
res = wg.scan(minorder=int(sys.stdin.readline() or 20000), maxD=4, show_near=9)
best = {}
for r in res:
    k = (r[2], r[3], r[4])
    if k not in best or (r[0], -r[1]) < (best[k][0], -best[k][1]):
        best[k] = r
print('\n== best D per (building, I, J) ==')
for k, r in sorted(best.items(), key=lambda kv: (kv[1][0], -kv[1][1])):
    print(r)
