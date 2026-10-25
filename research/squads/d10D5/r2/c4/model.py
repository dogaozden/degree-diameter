"""model.py: hub-graph demand model. Flags = (p_i, l_i) in GQ(7); needs A (points opposite) and B (lines not concurrent).
e(i,m) = edges needed by the direct-witness model: max(Hi,Hm) if both needs, min(Hi,Hm) if one, 0 if free."""
import sys
sys.path.insert(0, '.')
from gq import load, perp, lperp
q, N, lines, lof = load('gq/gq_q7.bin')
def collinear(p, r): return any(r in lines[l] for l in lof[p])
def concurrent(l, m): return bool(set(lines[l]) & set(lines[m])) or l == m
def flags_from(free, sig):
    return [(p, sig[p]) for p in free]
def demand(flags, H):
    k = len(flags); tot = 0; kinds = {'free': 0, 'A': 0, 'B': 0, 'AB': 0}
    for i in range(k):
        for m in range(i + 1, k):
            (p, l), (r, n) = flags[i], flags[m]
            needA = not collinear(p, r); needB = not concurrent(l, n)
            hi, hm = H[i], H[m]
            if needA and needB: e = max(hi, hm); kinds['AB'] += 1
            elif needA: e = min(hi, hm); kinds['A'] += 1
            elif needB: e = min(hi, hm); kinds['B'] += 1
            else: e = 0; kinds['free'] += 1
            tot += e
    return tot, kinds
if __name__ == '__main__':
    rows = [ln.split() for ln in open(sys.argv[1]) if ln.strip()]
    sig = list(map(int, rows[2])) if len(rows) > 2 else None
    free = list(map(int, open(sys.argv[2]).read().split()))
    sig = list(map(int, [r for r in rows if r[0] not in ('7','cyc') and len(r) == N][0]))
    flags = flags_from(free, sig)
    H = [2] * len(flags)
    tot, kinds = demand(flags, H)
    print('k', len(flags), 'edges needed (model)', tot, 'slots', 4 * sum(H), 'pair kinds', kinds)
    print('free points collinear pairs', sum(collinear(a, b) for i, (a, _) in enumerate(flags) for b, _ in flags[i+1:]),
          'concurrent line pairs', sum(concurrent(l, m) for i, (_, l) in enumerate(flags) for _, m in flags[i+1:]))
