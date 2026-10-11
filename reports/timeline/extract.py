"""Extract the 10 Oct 2026 progress timeline from git: every candidate's time and case values, from all runs.

Writes four CSVs next to this file:
  progress.csv   - each time a target case's best-so-far improved (all runs combined)
  programs.csv   - Haiku-written programs per 10-minute bin, Mac vs cloud, with a running total
  records.csv    - the cases where we beat the table, with when and where
  milestones.csv - the day's milestones (from commit times and session events)
Run from the repo root after `git fetch --all`.
"""
import csv, json, subprocess, sys
from datetime import datetime, timezone, timedelta
from pathlib import Path

OUT = Path(__file__).resolve().parent
TARGETS = {  # case: (label, table record, wiki upper bound, old record holder)
    "d4D5": ("Δ=4, D=5", 160, 236, "Hafner; Loz"),
    "d5D5": ("Δ=5, D=5", 336, 676, "Loz, Pérez-Rosés, Pineda-Villavicencio"),
    "d6D5": ("Δ=6, D=5", 684, 1556, "Loz, Pérez-Rosés, Pineda-Villavicencio"),
    "d7D5": ("Δ=7, D=5", 1134, 3106, "Loz, Pérez-Rosés, Pineda-Villavicencio"),
    "d7D4": ("Δ=7, D=4", 346, 518, "Delorme and Farhi"),
    "d11D4": ("Δ=11, D=4", 1734, 2222, "Delorme and Farhi"),
    "d11D3": ("Δ=11, D=3", 190, 220, "Feria-Purón, Miller, Pineda-Villavicencio; Araujo-Pardo, López"),
    "d13D3": ("Δ=13, D=3", 274, 314, "Araujo-Pardo and López"),
    "d15D3": ("Δ=15, D=3", 374, 422, "Araujo-Pardo and López"),
    "d16D3": ("Δ=16, D=3", 394, 482, "Delorme and Farhi"),
}
ISLANDS = ["island-1", "spec-d4d5", "spec-d5d5", "spec-d6d5", "spec-d7d5", "spec-d7d4", "spec-d11d4", "spec-d3fam",
           "spec-d16d3", "c-d4d5", "c-d5d5", "c-d6d5", "c-d7d5", "c-d7d4", "c-d11d4", "c-d3fam", "c-d16d3"]
ISLANDS += [i + "-w2" for i in ISLANDS]  # wave 2 twins


def git(*a):
    return subprocess.run(["git", *a], capture_output=True, text=True, check=True).stdout


def freshest(run_id):
    best = None
    for line in git("for-each-ref", "--format=%(refname:short) %(committerdate:unix)", f"refs/remotes/origin/{run_id}",
                    f"refs/remotes/origin/claude/{run_id}-evolve-run-*").splitlines():
        ref, t = line.rsplit(" ", 1)
        if best is None or int(t) > best[1]:
            best = (ref, int(t))
    return best[0]


def engine(run_id):
    if run_id.startswith("c-"): return "C island"
    if run_id.startswith("spec-"): return "Python island"
    if run_id == "island-1": return "Generalist island"
    return {"pilot-001": "Mac pilot", "run-002": "Mac run 2"}[run_id]


runs = [("pilot-001", "origin/master"), ("run-002", "origin/master")] + [(r, freshest(r)) for r in ISLANDS]
# Collect blob ids for every candidate's meta.json and result.json, then read them all through one cat-file process.
want = []
for run_id, ref in runs:
    for line in git("ls-tree", "-r", ref, f"runs/{run_id}/candidates/").splitlines():
        meta, path = line.split("\t")
        if path.endswith(("/meta.json", "/result.json")):
            want.append((run_id, path.split("/")[3], path.rsplit("/", 1)[1], meta.split()[2]))
proc = subprocess.run(["git", "cat-file", "--batch"], input="\n".join(w[3] for w in want) + "\n",
                      capture_output=True, text=True, check=True)
out, pos, blobs = proc.stdout, 0, []
for _ in want:
    header_end = out.index("\n", pos)
    size = int(out[pos:header_end].split()[2])
    raw = out[header_end + 1: header_end + 1 + size]
    blobs.append(raw)
    pos = header_end + 1 + size + 1
cands = {}
for (run_id, cid, kind, _), raw in zip(want, blobs):
    cands.setdefault((run_id, cid), {})[kind] = json.loads(raw)

rows = []  # (time, run_id, cid, haiku_written, {case: value})
for (run_id, cid), files in cands.items():
    meta, res = files.get("meta.json", {}), files.get("result.json", {})
    t = datetime.fromisoformat(meta["created"]) if meta.get("created") else None
    if t is None:
        continue
    calls = (meta.get("mutator") or {}).get("calls", 0) or 0
    vals = {c: v["value"] for c, v in (res.get("cases") or {}).items() if v.get("valid") and c in TARGETS}
    rows.append((t, run_id, cid, calls > 0, vals))
rows.sort(key=lambda r: r[0])
print(f"{len(rows)} candidates from {len(runs)} runs; {sum(r[3] for r in rows)} written by Haiku", file=sys.stderr)

# progress.csv: improvements of the best-so-far per target case
best, prog = {}, []
for t, run_id, cid, _, vals in rows:
    for case, v in vals.items():
        if v > best.get(case, 0):
            best[case] = v
            label, rec, ub, _ = TARGETS[case]
            prog.append({"time": t.astimezone(timezone.utc).isoformat(timespec="seconds"), "case": case, "label": label,
                         "value": int(v), "record": rec, "ratio": round(v / rec, 5), "run_id": run_id, "cid": cid,
                         "engine": engine(run_id)})
with open(OUT / "progress.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(prog[0]), lineterminator="\n"); w.writeheader(); w.writerows(prog)

# programs.csv: Haiku-written programs per 10-minute bin (Mac runs vs cloud islands)
start = rows[0][0].replace(minute=rows[0][0].minute // 10 * 10, second=0, microsecond=0)
bins = {}
for t, run_id, _, haiku, _ in rows:
    if not haiku: continue
    k = start + timedelta(minutes=(t - start) // timedelta(minutes=10) * 10)
    b = bins.setdefault(k, {"mac": 0, "cloud": 0})
    b["mac" if run_id in ("pilot-001", "run-002") else "cloud"] += 1
total, prows = 0, []
k = start
while k <= max(bins):
    b = bins.get(k, {"mac": 0, "cloud": 0}); total += b["mac"] + b["cloud"]
    prows.append({"bin_start": k.astimezone(timezone.utc).isoformat(timespec="seconds"), "mac": b["mac"], "cloud": b["cloud"],
                  "total": b["mac"] + b["cloud"], "cumulative": total})
    k += timedelta(minutes=10)
with open(OUT / "programs.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(prows[0]), lineterminator="\n"); w.writeheader(); w.writerows(prows)

# records.csv: cases where our best beats the table, with the first time it did and the current best
recs = []
for case, (label, rec, ub, holder) in TARGETS.items():
    beat = [p for p in prog if p["case"] == case and p["value"] > rec]
    if not beat: continue
    first, last = beat[0], beat[-1]
    recs.append({"case": case, "label": label, "table": rec, "ours": last["value"], "gain": last["value"] - rec,
                 "upper_bound": ub, "first_beaten": first["time"], "first_value": first["value"],
                 "best_found": last["time"], "run_id": last["run_id"], "cid": last["cid"], "engine": last["engine"],
                 "old_holder": holder})
with open(OUT / "records.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(recs[0]), lineterminator="\n"); w.writeheader(); w.writerows(recs)
print(json.dumps({"progress_rows": len(prog), "program_bins": len(prows), "programs_total": total,
                  "records": [(r["case"], r["ours"], r["first_beaten"]) for r in recs]}, ensure_ascii=False), file=sys.stderr)
