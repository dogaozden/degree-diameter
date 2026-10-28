"""BFS-verify every balanced K in [lo,hi] reached by gen_hubs.generate (windows and clique table) at delta,
and sample unbalanced pairs from the windows. Prints a compact summary."""
import sys, json
sys.path.insert(0, '.')
from gen_hubs import generate, window_graph
from check import hub_check
delta, lo, hi = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
use_cliques = len(sys.argv) > 4 and sys.argv[4] == 'cliques'
ok, fail, src = [], [], {}
for K in range(lo, hi + 1):
    G, label = window_graph(K, K, delta)
    if G is None and use_cliques:
        G, label = generate(K, K, delta)
    if G is None:
        fail.append(K); continue
    r = hub_check(G)
    if r['valid'] and r['nA'] == K and r['nB'] == K:
        ok.append(K); src.setdefault(label.split(' ')[0], []).append(K)
    else:
        fail.append(K)
print("delta", delta, "balanced verified:", len(ok), "failed/uncovered:", fail[:40], len(fail))
for k, v in src.items():
    print("  ", k, "range", min(v), max(v), "count", len(v))
# first uncovered K from lo
first_gap = next((K for K in range(lo, hi + 1) if K in fail), None)
print("first uncovered balanced K:", first_gap)
