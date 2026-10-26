"""Filter cands_all.tsv for the c5 card: no meta inside products; n <= NMAXN; n = 1 or Z_n has a nontrivial
k-th root of unity (so alpha can act on Z_n).  usage: python3 filt_groups.py K NMAXN < cands_all.tsv > cands_k.tsv"""
import sys, math
K, NMAXN = int(sys.argv[1]), int(sys.argv[2])
def has_root(n, k):
    if n == 1: return True
    return any(pow(r, k, n) == 1 for r in range(2, n) if math.gcd(r, n) == 1)
rows = []
for line in sys.stdin:
    N, tag, spec = line.rstrip('\n').split('\t')
    toks = spec.split()
    n = int(toks[-1])
    if n > NMAXN: continue
    if toks[0] == 'prod' and 'meta' in toks: continue
    if not has_root(n, K): continue
    rows.append((int(N), tag, spec))
for N, tag, spec in sorted(rows): print('%d\t%s\t%s' % (N, tag, spec))
