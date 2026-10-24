"""Write H(q) as text: q N, then N lines (points of line k)."""
import sys
import gh
q = int(sys.argv[1])
H = gh.load(q)
with open(sys.argv[2], 'w') as fh:
    fh.write(f'{q} {H.N}\n')
    for k in range(H.N):
        fh.write(' '.join(str(int(p)) for p in H.lines[k]) + '\n')
print('wrote', sys.argv[2], H.N)
