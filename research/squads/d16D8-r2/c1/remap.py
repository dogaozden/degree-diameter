# remap.py IN OUT NEWM MODE: change the Z_m header of a base file to Z_NEWM. MODE id keeps each voltage c as is;
# MODE scale maps c -> floor(c*NEWM/m) (keeps the voltage order and spread). Used for warm starts.
import sys
fi, fo, newm, mode = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4]
with open(fi) as f:
    V, m, E = map(int, f.readline().split())
    rows = [list(map(int, f.readline().split())) for _ in range(E)]
if mode == 'scale':
    for r in rows:
        if r[3] >= 1:
            r[2] = r[2] * newm // m
for r in rows:
    assert r[2] < newm
with open(fo, 'w') as f:
    f.write('%d %d %d\n' % (V, newm, E))
    f.write(''.join('%d %d %d %d\n' % tuple(r) for r in rows))
