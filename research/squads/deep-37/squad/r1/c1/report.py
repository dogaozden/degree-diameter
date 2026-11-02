"""c1 report: per-group summary of runs.tsv. A G-set is COMPLETE if it ran to DONE (or EXCL_TWIN, checked by a PROBE run
printing EXCLUDED_TWIN), or if all 16 shards ran to DONE; UNRESOLVED if the shard budget ran out; TIMEOUT rows without shards
are followed by their shard rows."""
import os, re, subprocess, glob, collections
W = "/home/user/degree-diameter/research/squads/deep-37"; os.chdir(W)
rows = [l.rstrip("\n").split("\t") for l in open("squad/r1/c1/runs.tsv") if l.strip()]
rows = [r for r in rows if len(r) >= 9 and r[0] != "file"]
zero = sorted({r[0] for r in rows if r[3] == "DONE" and r[4] == "0" and r[7] == "-"})
excl = {}
for f in zero:
    o = subprocess.run(["bin/orbdfs", f, "7"], capture_output=True, text=True, env=dict(os.environ, PROBE="1")).stdout
    excl[f] = "EXCLUDED_TWIN" in o
def status(rr):
    plain = [r for r in rr if r[7] == "-"]
    shards = [r for r in rr if r[7] not in ("-", "budget")]
    if any(r[3] == "UNRESOLVED" for r in rr): return "UNRESOLVED"
    if plain and plain[-1][3] in ("DONE", "EXCL_TWIN", "MAXSOL"):
        if plain[-1][3] == "DONE" and plain[-1][4] == "0" and excl.get(plain[-1][0]): return "EXCL_TWIN"
        return plain[-1][3]
    if shards:
        if all(r[3] in ("DONE", "EXCL_TWIN") for r in shards) and len(shards) == 16 and len({r[7] for r in shards}) == 16:
            return "SHARDS_COMPLETE"
        return "SHARDS_PARTIAL"
    return "TIMEOUT"
groups = collections.OrderedDict()
for g in sorted(glob.glob("squad/r1/c1/gs/n168/g*/est.txt"), key=lambda p: (int(re.search(r"/g(\d+)_", p).group(1)), int(re.search(r"/g\d+_(\d+)/", p).group(1)))):
    tag = re.search(r"/(g\d+_\d+)/est.txt", g).group(1)
    ests = [l.split(None, 2) for l in open(g) if l.strip()]
    big = sum(1 for p in ests if p[1] == "PROBE_TIMEOUT" or float(p[1]) >= 3e7)
    groups[tag] = (len(ests), big, [r for r in rows if r[1] == "n168_" + tag])
out = ["| group | G-sets listed | est >= 3e7 (not run) | complete (DONE / EXCL_TWIN / sharded complete) | incomplete (MAXSOL / partial shards / UNRESOLVED / TIMEOUT) | solution hits (sum of runs) |",
       "|---|---|---|---|---|---|"]
tot = collections.Counter()
for tag, (ns, big, rs) in groups.items():
    byf = collections.OrderedDict()
    for r in rs: byf.setdefault(r[0], []).append(r)
    st = collections.Counter(status(rr) for rr in byf.values())
    comp = st["DONE"] + st["EXCL_TWIN"] + st["SHARDS_COMPLETE"]
    inc = sum(v for k, v in st.items() if k not in ("DONE", "EXCL_TWIN", "SHARDS_COMPLETE"))
    sols = sum(int(r[5]) for r in rs if r[5].isdigit())
    out.append(f"| {tag} | {ns} | {big} | {comp} | {inc} ({', '.join(f'{k}:{v}' for k, v in st.items() if k not in ('DONE','EXCL_TWIN','SHARDS_COMPLETE')) or '-'}) | {sols} |")
    tot.update({"sets": ns, "big": big, "comp": comp, "inc": inc, "sols": sols})
out.append(f"| TOTAL | {tot['sets']} | {tot['big']} | {tot['comp']} | {tot['inc']} | {tot['sols']} |")
open("squad/r1/c1/group_summary.md", "w").write("\n".join(out) + "\n")
print("\n".join(out))
