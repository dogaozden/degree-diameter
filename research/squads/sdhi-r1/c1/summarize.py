import glob, re, os, sys
OUT = "/home/user/degree-diameter/research/squads/sdhi-r1/c1/out"
rows = []
for f in sorted(glob.glob(os.path.join(OUT, "N*.txt"))):
    txt = open(f, errors="replace").read().splitlines()
    name = os.path.basename(f)
    m = re.match(r"N(\d+)_m(\d+)_k(\d+)_r(\d+)\.txt", name)
    N, mm, kk, rr = map(int, m.groups())
    psi = None; best = None; bestpsi = None; sols = 0; nlines = 0; per_psi = {}
    cur = None
    for ln in txt:
        if ln.startswith("PSI "):
            cur = ln.split("]")[0] + "]"
            pm = re.match(r"PSI (\d+) \[.*u0=\((\d+),(\d+)\)\]", ln)
            cur = (int(pm.group(1)), pm.group(2) + "," + pm.group(3)) if pm else (ln[:12], "?")
        mt = re.match(r"(TABU|ENUM) (\S+).*?best (-?\d+)", ln)
        if mt:
            b = int(mt.group(3))
            if b >= 0:
                nlines += 1
                if cur is not None:
                    per_psi[cur] = min(per_psi.get(cur, 10**9), b)
                if best is None or b < best:
                    best = b; bestpsi = (cur, mt.group(1), mt.group(2))
        if ln.startswith("SOL"):
            sols += 1
    done = any(l.startswith("DONE") for l in txt)
    rows.append((N, mm, kk, rr, best, bestpsi, sols, done, per_psi))
print("N\tm\tk\tr\tbest\tpsi(idx,u0)\tmode/type\tsols\tdone")
for N, mm, kk, rr, best, bp, sols, done, pp in rows:
    bpsi = "%s,%s" % (bp[0][0], bp[0][1]) if bp else "-"
    print("%d\t%d\t%d\t%d\t%s\t%s\t%s\t%d\t%s" % (N, mm, kk, rr, best, bpsi, (bp[1]+" "+bp[2]) if bp else "-", sols, done))
# overall
ok = [r for r in rows if r[4] is not None]
if ok:
    g = min(ok, key=lambda r: r[4])
    print("OVERALL best", g[4], "at N", g[0], "m", g[1], "k", g[2], "r", g[3], "psi", g[5][0] if g[5] else None)
    nu = [r for r in ok if r[5] and r[5][0][1] != "0,0"]
    if nu:
        g2 = min(nu, key=lambda r: r[4])
        print("OVERALL best with u0!=(0,0)", g2[4], "at N", g2[0], "m", g2[1], "k", g2[2], "r", g2[3], "psi", g2[5][0])
print("groups with output:", len(rows), " total SOL lines:", sum(r[6] for r in rows))
