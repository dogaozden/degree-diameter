"""Hub capacity: lab model K_A+K_B = min_j out_j + min_j in_j (B-hubs on A-slots, A-hubs on B-slots)
vs mixed model: a hub may use an A-slot or a B-slot in each level, so K <= min_j (out_j + in_j)."""
import itertools, sys
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
from layouts import regular_tournaments
def run(n, a, b, c):
    T = regular_tournaments(n)
    best_lab = (-1, None); best_mix = (-1, None)
    for arcs in T:
        for types in itertools.product('HD', repeat=n):
            out = [0]*n; inn = [0]*n; tot = [0]*n
            for (u, v) in arcs:
                if types[u] == 'H' and types[v] == 'D': w = a
                elif types[u] == 'D' and types[v] == 'H': w = b
                else: w = c
                out[u] += w; inn[v] += w; tot[u] += w; tot[v] += w
            lab = min(out) + min(inn); mix = min(tot)
            if lab > best_lab[0]: best_lab = (lab, ''.join(types), sorted(arcs))
            if mix > best_mix[0]: best_mix = (mix, ''.join(types), sorted(arcs))
    return best_lab[0], best_lab[1], best_mix[0], best_mix[1]
for (a, b, c) in [(122, 111, 0), (122, 111, 2), (122, 111, 10), (9, 7, 0), (10, 8, 0), (5,4,0)]:
    for n in (3, 5, 7):
        print('a=%d b=%d c=%d n=%d' % (a, b, c, n), 'lab K_A+K_B=%d types=%s' % run(n, a, b, c)[:2], ' mixed bound=%d types=%s' % run(n, a, b, c)[2:])
