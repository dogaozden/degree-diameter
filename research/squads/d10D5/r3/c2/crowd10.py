"""crowd10.py 'p1 p2 ...' 'p:l ...': collinear freed pairs and concurrent freed-line pairs for a FREE set with FORCE flags."""
import sys, itertools
sys.path.insert(0, '.')
from gq import load, perp, lperp
q, N, lines, lof = load('gq/gq_q7.bin')
rows = {}
for ln in open('k9_valid.sol'):
    t = ln.split()
    if t and t[0] not in rows: rows[t[0]] = t[1:]
sig = list(map(int, rows['sigma']))
free = list(map(int, sys.argv[1].split()))
for tok in sys.argv[2].split():
    p, l = map(int, tok.split(':')); sig[p] = l
L = {p: sig[p] for p in free}
PER = {p: perp(lines, lof, p) for p in range(N)}
LPER = {l: lperp(lines, lof, l) for l in range(N)}
col = [(a, b) for a, b in itertools.combinations(free, 2) if b in PER[a]]
con = [(a, b) for a, b in itertools.combinations(free, 2) if L[b] in LPER[L[a]]]
print('flags', [(p, L[p], p in lines[L[p]]) for p in free])
print('collinear pairs', len(col), col)
print('concurrent-line pairs', len(con), con)
print('total crowd pairs', len(col) + len(con))
