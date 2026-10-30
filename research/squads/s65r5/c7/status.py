import os, re, sys, time
ROOT = "/home/user/degree-diameter/research"
SRC = ["squads/s65r3", "squads/s65r4", "s65/haar"]
now = time.time()
pat = re.compile(r"^h(\d+)_(\d+)(_resume)?\.log$")
logs = {}
for src in SRC:
    for dp, dn, fn in os.walk(os.path.join(ROOT, src)):
        for f in fn:
            m = pat.match(f)
            if m:
                logs.setdefault((int(m.group(1)), int(m.group(2))), []).append(os.path.join(dp, f))
cands = []
for line in open(os.path.join(ROOT, "s65/haar/remaining_r4.txt")):
    s = line.strip()
    if s and not s.startswith("#"):
        o, i = s.split("_"); cands.append((int(o), int(i)))
for line in open(os.path.join(ROOT, "s65/haar/next_361_380.txt")):
    s = line.split()
    if s and "_" in s[0]:
        o, i = s[0].split("_"); cands.append((int(o), int(i)))
seen = set(); out = []
for c in cands:
    if c in seen: continue
    seen.add(c)
    files = logs.get(c, [])
    P = None; ivs = []; recent = []; valid = 0; minA = None; sets = 0; aside = 0; info = []
    for fp in files:
        mt = os.path.getmtime(fp)
        if now - mt < 600: recent.append(os.path.basename(fp))
        lines = open(fp, errors="replace").read().splitlines()
        if not lines: continue
        m = re.match(r"N=(\d+) automorphism generators=(\d+) pair classes=(\d+), doing (\d+)\.\.(\d+)", lines[0])
        if not m: continue
        Pl = int(m.group(3)); P = Pl if P is None else P
        p0 = int(m.group(4)); lastpair = None; done = None
        for l in lines:
            if l.startswith("PAIR "):
                lastpair = int(l.split()[1])
            elif l.startswith("DONE"):
                mm = re.search(r"pairs=(\d+)\.\.(\d+) sets=(\d+) Acovered=(\d+) valid=(\d+) minA=(\d+)", l)
                if mm:
                    done = (int(mm.group(1)), int(mm.group(2)))
                    sets += int(mm.group(3)); aside += int(mm.group(4)); valid += int(mm.group(5))
                    mA = int(mm.group(6)); minA = mA if minA is None else min(minA, mA)
            elif l.startswith("VALID"):
                info.append(l)
            elif l.startswith("ASIDE"):
                info.append(l)
        if done: ivs.append(done)
        elif lastpair is not None: ivs.append((p0, lastpair + 1)); info.append("killed-after-pair-%d" % lastpair)
        else: ivs.append((p0, p0))
    # union coverage
    covered = False
    if P is not None:
        cur = 0
        for a, b in sorted(ivs):
            if a <= cur: cur = max(cur, b)
        covered = cur >= P
    cov = []
    if P is not None:
        cur = 0
        for a, b in sorted(ivs):
            if a <= cur: cur = max(cur, b)
        cov_s = "0..%d of %d" % (cur, P)
    else:
        cov_s = "none"
    status = "DONE" if covered else ("RECENT" if recent else ("PARTIAL" if files else "TODO"))
    out.append((c, status, cov_s, P, ";".join(os.path.relpath(f, ROOT) for f in files), recent, valid, minA, aside, info))
for o in out:
    c, status, cov_s, P, fl, recent, valid, minA, aside, info = o
    print("%d_%d %s cov=%s P=%s valid=%s minA=%s aside=%s recent=%s files=%s %s" % (c[0], c[1], status, cov_s, P, valid, minA, aside, recent, fl, info[:2]))
