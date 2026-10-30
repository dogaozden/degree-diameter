import sys, glob, os
# usage: grp_stats.py ORDER -> prints id, invol, order4 count, abelian flag, name
def load(path):
    with open(path) as f:
        tok = f.read().split()
    m = int(tok[0])
    mul = [list(map(int, tok[1 + i*m:1 + (i+1)*m])) for i in range(m)]
    return m, mul
order = sys.argv[1]
rows = []
for p in sorted(glob.glob(f"/home/user/degree-diameter/research/squads/bh5b-r2/c7/grp/sg_{order}_*.txt")):
    i = int(p.rsplit('_', 1)[1].split('.')[0])
    m, mul = load(p)
    inv = sum(1 for x in range(1, m) if mul[x][x] == 0)
    ab = all(mul[x][y] == mul[y][x] for x in range(m) for y in range(m))
    name = open(p[:-4] + ".name").read().strip() if os.path.exists(p[:-4] + ".name") else "?"
    rows.append((inv, i, ab, name))
rows.sort(reverse=True)
for r in rows: print(r[0], r[1], "abelian" if r[2] else "nonab", r[3][:70])
