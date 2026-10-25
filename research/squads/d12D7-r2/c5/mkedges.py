# c5: apply an edit list ("- u v" / "+ u v") to g.edges and write the edge list for srccheck (one pass, streaming).
import sys
src, opsf, out = sys.argv[1], sys.argv[2], sys.argv[3]
rem, add = set(), []
for line in open(opsf):
    p = line.split()
    if len(p) != 3: continue
    op, u, v = p[0], int(p[1]), int(p[2])
    key = (min(u, v), max(u, v))
    if op == "-": rem.add(key)
    else: add.append(key)
removed = set()
with open(src) as fi, open(out, "w") as fo:
    n = fi.readline(); fo.write(n)
    for line in fi:
        a, b = line.split()
        key = (min(int(a), int(b)), max(int(a), int(b)))
        if key in rem and key not in removed:
            removed.add(key); continue
        fo.write(line)
    for key in add: fo.write("%d %d\n" % key)
print("removed", len(removed), "of", len(rem), "requested; added", len(add), file=sys.stderr)
