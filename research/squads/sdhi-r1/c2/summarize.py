import glob, os, re
OUT = "/home/user/degree-diameter/research/squads/sdhi-r1/c2/out"
rows = []
for f in sorted(glob.glob(os.path.join(OUT, "g_*.txt"))):
    txt = open(f, errors="replace").read().splitlines()
    name = os.path.basename(f)
    _, N, m, k, r = re.match(r"(g)_(\d+)_(\d+)_(\d+)_(\d+)\.txt", name).groups()
    best = None; bestline = None; sols = 0
    for ln in txt:
        mt = re.match(r"(TABU|ENUM) (\S+).*?best (-?\d+)", ln)
        if mt and int(mt.group(3)) >= 0:
            b = int(mt.group(3))
            if best is None or b < best:
                best = b; bestline = ln.split(" sols")[0]
        if ln.startswith("SOL"):
            sols += 1
    rows.append((int(N), int(m), int(k), int(r), best, bestline, sols))
print("N m k r best sols | best-line")
for row in rows:
    print(*row[:5], row[6], "|", row[5])
ok = [r for r in rows if r[4] is not None]
if ok:
    g = min(ok, key=lambda r: r[4])
    print("OVERALL best", g[4], "at N", g[0], "m", g[1], "k", g[2], "r", g[3])
print("groups with output:", len(rows), "total SOL:", sum(r[6] for r in rows))
