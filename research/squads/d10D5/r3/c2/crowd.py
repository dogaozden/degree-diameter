"""crowd.py SOLFILE: crowding of the freed flags of a dmhub .sol and candidate opposite flags."""
import sys, itertools
sys.path.insert(0, '.')
from gq import load, perp, lperp
q, N, lines, lof = load('gq/gq_q7.bin')
rows = {}
for ln in open(sys.argv[1]):
    t = ln.split()
    if t and t[0] not in rows: rows[t[0]] = t[1:]
free = list(map(int, rows['free'])); sig = list(map(int, rows['sigma']))
Lf = {p: sig[p] for p in free}
PER = {p: perp(lines, lof, p) for p in range(N)}      # incl. p
LPER = {l: lperp(lines, lof, l) for l in range(N)}    # incl. l
print('freed flags (p, l=sigma(p), p on l):', [(p, Lf[p], p in lines[Lf[p]]) for p in free])
print('point-flag incidences all points:', sum(1 for x in range(N) if x in lines[sig[x]]), 'of', N)
for p in free:
    col = [p2 for p2 in free if p2 != p and p2 in PER[p]]
    conc = [p2 for p2 in free if p2 != p and Lf[p2] in LPER[Lf[p]]]
    print(f'p={p:3d} l={Lf[p]:3d} collinear_freed={col} concurrent_lines_freed={conc} crowd={len(col)+len(conc)}')
# which freed points are collinear with each other (point graph among freed)
pairs = [(a, b) for a, b in itertools.combinations(free, 2) if b in PER[a]]
lpairs = [(a, b) for a, b in itertools.combinations(free, 2) if Lf[b] in LPER[Lf[a]]]
print('collinear freed pairs:', pairs)
print('concurrent freed-line pairs:', [(a, b) for a, b in lpairs])
