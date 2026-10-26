"""Caps: D->H arcs carry a spread of lines (size a = q^2+1); H->D arcs carry a partial ovoid of points (size b); c = 0.
Mixed-hub bound K = min_j (out_j + in_j); lab bound min_j out_j + min_j in_j."""
import itertools, random, sys
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c17')
from tourn import arcs_random
def bounds(arcs, n, a, b, c=0):
    best_mix = (-1, ''); best_lab = (-1, '')
    for types in itertools.product('HD', repeat=n):
        out = [0]*n; inn = [0]*n; tot = [0]*n
        for (u, v) in arcs:
            if types[u] == 'D' and types[v] == 'H': w = a
            elif types[u] == 'H' and types[v] == 'D': w = b
            else: w = c
            out[u] += w; inn[v] += w; tot[u] += w; tot[v] += w
        m = min(tot); l = min(out) + min(inn)
        if m > best_mix[0]: best_mix = (m, ''.join(types))
        if l > best_lab[0]: best_lab = (l, ''.join(types))
    return best_mix, best_lab
if __name__ == '__main__':
    rng = random.Random(7)
    Ts = [arcs_random(7, rng) for _ in range(30)]
    for (a, b) in [(26, 21), (26, 16), (122, 111), (122, 100)]:
        best = max(((bounds(T, 7, a, b), T) for T in Ts), key=lambda x: x[0][0][0])
        print('a=%d b=%d: mixed K<=%d types %s | lab %d %s' % (a, b, best[0][0][0], best[0][0][1], best[0][1][0], best[0][1][1]))
