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
BASE_ISLANDS = list(ISLANDS)
ISLANDS = ISLANDS + [i + s for s in ("-w2", "-w3", "-w3b") for i in BASE_ISLANDS]  # waves 2 and 3


def git(*a):
    return subprocess.run(["git", *a], capture_output=True, text=True, check=True).stdout


def freshest(run_id):
    best = None
    # Cloud sessions name their branches freely, so take any branch whose name contains the id
    # and that carries this island's run folder.
    for line in git("for-each-ref", "--format=%(refname:short) %(committerdate:unix)", "refs/remotes/origin/").splitlines():
        ref, t = line.rsplit(" ", 1)
        if run_id not in ref or subprocess.run(["git", "cat-file", "-e", f"{ref}:runs/{run_id}/status.md"]).returncode:
            continue
        if best is None or int(t) > best[1]:
            best = (ref, int(t))
    return best[0] if best else None


def engine(run_id):
    if run_id.startswith("c-"): return "C island"
    if run_id.startswith("spec-"): return "Python island"
    if run_id == "island-1": return "Generalist island"
    return {"pilot-001": "Mac pilot", "run-002": "Mac run 2"}[run_id]


runs = [("pilot-001", "origin/master"), ("run-002", "origin/master")] + [(r, f) for r in ISLANDS if (f := freshest(r))]
# Collect blob ids for every candidate's meta.json and result.json, then read them all through one cat-file process.
want = []
for run_id, ref in runs:
    for line in git("ls-tree", "-r", ref, f"runs/{run_id}/candidates/").splitlines():
        meta, path = line.split("\t")
        if path.endswith(("/meta.json", "/result.json")):
            want.append((run_id, path.split("/")[3], path.rsplit("/", 1)[1], meta.split()[2]))
# Candidate files can be large (meta.json holds the whole Haiku prompt and reply), so keep only the few fields
# we need, cached by blob id, and stream just the new blobs through one `git cat-file --batch`.
CACHE = OUT / ".blobcache.json"
cache = json.loads(CACHE.read_text()) if CACHE.exists() else {}


def slim(kind, raw):
    d = json.loads(raw)
    if kind == "meta.json":
        return {"created": d.get("created"), "calls": (d.get("mutator") or {}).get("calls", 0) or 0}
    return {"cases": {c: {"valid": v.get("valid"), "value": v.get("value")} for c, v in (d.get("cases") or {}).items()}}


new_ids = sorted({w[3] for w in want if w[3] not in cache})
if new_ids:
    kinds = {w[3]: w[2] for w in want}
    proc = subprocess.Popen(["git", "cat-file", "--batch"], stdin=subprocess.PIPE, stdout=subprocess.PIPE)
    import threading
    threading.Thread(target=lambda: (proc.stdin.write(("\n".join(new_ids) + "\n").encode()), proc.stdin.close()), daemon=True).start()
    for sha in new_ids:
        header = proc.stdout.readline().split()
        size = int(header[2])
        raw = proc.stdout.read(size); proc.stdout.read(1)
        try:
            cache[sha] = slim(kinds[sha], raw)
        except ValueError:
            cache[sha] = {}
    proc.wait()
    CACHE.write_text(json.dumps(cache, separators=(",", ":")))
cands = {}
for run_id, cid, kind, sha in want:
    cands.setdefault((run_id, cid), {})[kind] = cache.get(sha, {})

rows = []  # (time, run_id, cid, haiku_written, {case: value})
for (run_id, cid), files in cands.items():
    meta, res = files.get("meta.json", {}), files.get("result.json", {})
    t = datetime.fromisoformat(meta["created"]) if meta.get("created") else None
    if t is None:
        continue
    calls = meta.get("calls", 0) or 0
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

# fleet.csv: one row per cloud island, for the live view
import re
as_of = datetime.now(timezone.utc)
STATUS_ROW = re.compile(r"^\| (d\d+D\d+) \| target \| (\d+) \| (\d+) \| (\d+)( NEW| =)? \|", re.M)
fleet = []
for run_id in ISLANDS:
    base = run_id.split("-w")[0]
    wave = 3 if "-w3" in run_id else 2 if run_id.endswith("-w2") else 1
    row = {"run_id": run_id, "base": base, "engine": engine(base), "wave": wave, "status": "booting",
           "minutes_since_push": "", "generation": "", "cells": "", "best": "", "beats": 0, "as_of": as_of.isoformat(timespec="seconds")}
    ref = freshest(run_id)
    if ref:
        t = int(git("log", "-1", "--format=%ct", ref)); subj = git("log", "-1", "--format=%s", ref)
        age = (as_of.timestamp() - t) / 60
        status_md = subprocess.run(["git", "show", f"{ref}:runs/{run_id}/status.md"], capture_output=True, text=True).stdout
        g = re.search(r"Generations done: (\d+)", status_md)
        cells = STATUS_ROW.findall(status_md)
        stopped = re.search(r"usage limit|EXIT=|exit \d|final", subj, re.I)
        row.update(minutes_since_push=round(age), generation=g.group(1) if g else "",
                   status="stopped" if stopped else "running" if age <= 25 else "quiet",
                   cells=" ".join(c[0] for c in cells), best=" ".join(c[3] for c in cells),
                   beats=sum(int(c[3]) > int(c[1]) for c in cells))
        if not cells:
            row["status"] = "booting" if not stopped else row["status"]
    fleet.append(row)
with open(OUT / "fleet.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(fleet[0]), lineterminator="\n"); w.writeheader(); w.writerows(fleet)

# lean.csv: what the Lean proof covers versus our best now
lean_ref = "origin/master"
records_src = subprocess.run(["git", "show", f"{lean_ref}:lean/BipartiteDD/Records.lean"], capture_output=True, text=True).stdout
axioms = subprocess.run(["git", "show", f"{lean_ref}:lean/Axioms.out.txt"], capture_output=True, text=True).stdout
in_lean = {f"d{a}D{b}": (int(n), name) for name, n, a, b in
           re.findall(r"^theorem (nb_\w+) : \u2203 G : SimpleGraph \(Fin (\d+)\), BipartiteDD.IsBipartiteDegDiam G (\d+) (\d+)", records_src, re.M)}
lean_rows = []
for r in recs:
    proved = in_lean.get(r["case"])
    mode = ""
    if proved:
        line = next((l for l in axioms.splitlines() if l.startswith(f"'{proved[1]}'")), "")
        mode = "fast mode" if "native_decide" in line else "strict (kernel)" if line else "unknown"
    lean_rows.append({"case": r["case"], "label": r["label"], "best_now": r["ours"], "in_lean": proved[0] if proved else "",
                      "mode": mode, "state": "current" if proved and proved[0] >= int(r["ours"]) else "older graph" if proved else "not yet"})
with open(OUT / "lean.csv", "w", newline="") as f:
    w = csv.DictWriter(f, fieldnames=list(lean_rows[0]), lineterminator="\n"); w.writeheader(); w.writerows(lean_rows)
print(f"fleet: {sum(r['status'] == 'running' for r in fleet)} running, {sum(r['status'] == 'stopped' for r in fleet)} stopped, "
      f"{sum(r['status'] == 'booting' for r in fleet)} booting, {sum(r['status'] == 'quiet' for r in fleet)} quiet; "
      f"lean: {[(r['case'], r['state']) for r in lean_rows]}", file=sys.stderr)
