import os, re, glob
C = "/home/user/degree-diameter/research/squads/s65r5/c7"
PRIOR = {  # earlier partial logs (other folders) for the two resumed groups
    "360_100": "/home/user/degree-diameter/research/squads/s65r3/c2/h360_100.log",
    "352_169": "/home/user/degree-diameter/research/squads/s65r3/c3/h352_169.log",
}
def parse(path):
    d = dict(P=None, ivs=[], sets=0, valid=0, minA=None, aside=0, bunc=None, lastpair=None, nVALID=0, struct=None)
    if not os.path.exists(path): return None
    lines = open(path, errors="replace").read().splitlines()
    if not lines: return None
    m = re.match(r"N=(\d+) automorphism generators=(\d+) pair classes=(\d+), doing (\d+)\.\.(\d+)", lines[0])
    if not m: return None
    d["P"] = int(m.group(3)); p0 = int(m.group(4)); d["N"] = int(m.group(1))
    done = None
    for l in lines:
        if l.startswith("PAIR "):
            p = int(l.split()[1]); d["lastpair"] = p
            mm = re.search(r"minA=(\d+)", l)
            if mm: d["minA"] = int(mm.group(1)) if d["minA"] is None else min(d["minA"], int(mm.group(1)))
        elif l.startswith("DONE"):
            mm = re.search(r"pairs=(\d+)\.\.(\d+) sets=(\d+) Acovered=(\d+) valid=(\d+) minA=(\d+)", l)
            done = (int(mm.group(1)), int(mm.group(2)))
            d["sets"] += int(mm.group(3)); d["aside"] += int(mm.group(4)); d["valid"] += int(mm.group(5))
            v = int(mm.group(6)); d["minA"] = v if d["minA"] is None else min(d["minA"], v)
        elif l.startswith("VALID"): d["nVALID"] += 1; d["valid_line"] = l
        elif l.startswith("ASIDE"):
            b = int(re.search(r"Bunc=(\d+)", l).group(1))
            d["bunc"] = b if d["bunc"] is None else min(d["bunc"], b)
    d["aside"] = d.get("aside", 0)
    if done: d["ivs"].append(done); d["done"] = True
    elif d["lastpair"] is not None: d["ivs"].append((p0, d["lastpair"] + 1)); d["done"] = False
    else: d["ivs"].append((p0, p0)); d["done"] = False
    return d
rows = []
for f in sorted(glob.glob(C + "/h*.log")):
    name = os.path.basename(f)
    m = re.match(r"h(\d+)_(\d+)(_resume)?\.log$", name)
    if not m: continue
    key = "%s_%s" % (m.group(1), m.group(2))
    rows.append((key, f))
print(len(rows), "logs")
groups = {}
for key, f in rows: groups.setdefault(key, []).append(f)
out = []
for key in sorted(groups, key=lambda k: (int(k.split("_")[0]), int(k.split("_")[1]))):
    ps = [parse(f) for f in groups[key]]
    ps = [p for p in ps if p]
    if key in PRIOR and os.path.exists(PRIOR[key]):
        pr = parse(PRIOR[key])
        if pr: ps.append(pr)
    ivs = []; P = None; sets = 0; valid = 0; minA = None; aside = 0; bunc = None; nV = 0; vl = []
    for d in ps:
        P = d["P"] if P is None else P
        ivs += d["ivs"]; sets += d["sets"]; valid += d["valid"]; nV += d["nVALID"]
        if d.get("valid_line"): vl.append(d["valid_line"])
        if d["minA"] is not None: minA = d["minA"] if minA is None else min(minA, d["minA"])
        aside += d["aside"]
        if d["bunc"] is not None: bunc = d["bunc"] if bunc is None else min(bunc, d["bunc"])
    cur = 0
    for a, b in sorted(ivs):
        if a <= cur: cur = max(cur, b)
    st = ""
    ex = C + "/exp_%s.out" % key
    if os.path.exists(ex):
        mm = re.search(r"\|Aut\|=(\d+) gens=\d+ (.*)$", open(ex).read(), re.M)
        if mm: st = "%s, Aut %s" % (mm.group(2).strip(), mm.group(1))
    status = "DONE" if (P and cur >= P) else "PARTIAL %d/%d" % (cur, P or 0)
    out.append("%s | %s | %s | %s | %s | %s | %s | %s" % (key, st or "-", status, sets, valid + nV, minA, bunc if bunc is not None else "-", ("aside %d" % aside)))
    if vl: out.append("   VALID: " + " ; ".join(vl))
open(C + "/table_summary.txt", "w").write("\n".join(out) + "\n")
print("\n".join(out))
