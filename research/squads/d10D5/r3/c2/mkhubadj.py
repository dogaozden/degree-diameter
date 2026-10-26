"""mkhubadj.py X.sol: print HUBADJ="i:j ..." (flag-level pairs from the hubgraph line of a dmhub .sol), as PRINTHUBADJ does."""
import sys
H = 2
for ln in open(sys.argv[1]):
    t = ln.split()
    if t and t[0] == 'hubgraph':
        v = list(map(int, t[1:])); seen = []
        for a, b in zip(v[0::2], v[1::2]):
            p = (a // H, b // H)
            if p not in seen: seen.append(p)
        print('HUBADJ="' + ' '.join(f'{i}:{j}' for i, j in seen) + '"')
