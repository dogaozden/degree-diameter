#!/usr/bin/env python3
"""Calibration of research/frontier/haarcheck_gen.c.  Run from the repo root:
    python3 research/frontier/runs/cloudcheck/haarcheck_gen_calibrate.py MAXN > haarcheck_gen_calibration.txt
Part 1: every file in research/frontier/sols (sl / psl / prod families) that has a report in runs/cloudcheck and
        N <= MAXN: haarcheck_gen must say VALID and its BFS level sizes (from (e,A) and (e,B)) must equal those of the
        first earlier report that lists them (check_haar_indep.py / bigcheck_indep.c).
Part 2: deliberately corrupted files (runs/cloudcheck/haarcheck_gen_calib_files): haarcheck_gen --full must say INVALID;
        the true eccentricity and level sizes are compared with check_haar_indep.py, and the verdict with build_haar2.py.
Part 3: malformed files must be rejected (exit 2)."""
import glob, os, re, subprocess, sys, time
EXE = "/tmp/haarcheck_gen"
maxN = int(sys.argv[1]) if len(sys.argv) > 1 else 45_000_000
FR = "research/frontier"
def run(cmd, **kw):
    t = time.time(); p = subprocess.run(cmd, capture_output=True, text=True, **kw); return p, time.time() - t
def levels(txt):   # haarcheck_gen format "from (e,A): ... level sizes [..]" and check_haar_indep format "BFS from A: ... level sizes [..]"
    return {s: l for s, l in re.findall(r"(?:from \(e,|BFS from )([AB])(?:\)|):.*?level sizes \[([\d, ]+)\]", txt)}
print("# haarcheck_gen calibration  (date %s)" % time.strftime("%Y-%m-%dT%H:%MZ", time.gmtime()))
p, _ = run(["gcc", "-O3", "-fopenmp", "-Wall", "-Wextra", "-o", EXE, f"{FR}/haarcheck_gen.c"])
print("build: gcc -O3 -fopenmp -Wall -Wextra -o haarcheck_gen haarcheck_gen.c  -> exit", p.returncode, p.stderr.strip() or "(no warnings)")
print(run(["bash", "-c", "nproc; free -g | head -2; gcc --version | head -1"])[0].stdout)
print("=" * 100, "\nPART 1: known-good files (same families), N <= %d" % maxN)
n_ok = n_tot = 0
for rep in sorted(glob.glob(f"{FR}/runs/cloudcheck/d*.txt")):
    stem = os.path.basename(rep)[:-4]; sol = f"{FR}/sols/{stem}.txt"
    if not os.path.exists(sol): continue
    h = open(sol).readline().split()
    if h[2] not in ("sl", "psl", "prod") or "meta" in h or "pgl" in h: continue
    N = int(h[h.index("N") + 1])
    if N > maxN: continue
    rtxt = open(rep).read()
    refvalid = bool(re.search(r"^(RESULT )?VALID ", rtxt, re.M)) and not re.search(r"^(RESULT )?INVALID", rtxt, re.M)
    reflv = {}
    for s, l in re.findall(r"BFS from ([AB]): ecc=\d+ reached .*? level sizes \[([\d, ]+)\]", rtxt): reflv.setdefault(s, l)
    p, dt = run([EXE, sol]); mine = levels(p.stdout)
    last = p.stdout.strip().splitlines()[-1] if p.stdout.strip() else p.stderr.strip()
    ok = p.returncode == 0 and last.startswith("VALID") and refvalid and bool(reflv) and mine == reflv
    n_tot += 1; n_ok += ok
    print(f"[{'MATCH' if ok else 'MISMATCH'}] {stem}  ({dt:.0f}s)  earlier-report={'VALID' if refvalid else 'NOT VALID'}  levels-equal={mine == reflv if reflv else 'no earlier levels'}")
    print("    " + last)
# the file named in the brief that has no cloudcheck report: its earlier results (build_haar2.py, check_haar_indep.py) are in runs/harvest_check_2026-10-31.txt
stem = "d10D10_psl_81_121_orb5f0_s3"; sol = f"{FR}/sols/{stem}.txt"
sec = open(f"{FR}/runs/harvest_check_2026-10-31.txt").read().split("== " + stem)[1].split("\n== ")[0]
reflv = levels(sec); p, dt = run([EXE, sol]); mine = levels(p.stdout); last = p.stdout.strip().splitlines()[-1]
ok = p.returncode == 0 and last.startswith("VALID") and "\nVALID d=10 D=10" in sec and mine == reflv and bool(reflv)
n_tot += 1; n_ok += ok
print(f"[{'MATCH' if ok else 'MISMATCH'}] {stem}  ({dt:.0f}s)  earlier results (build_haar2.py VALID, check_haar_indep.py VALID, runs/harvest_check_2026-10-31.txt)  levels-equal={mine == reflv}")
print("    " + last)
print(f"PART 1 SUMMARY: {n_ok}/{n_tot} files: haarcheck_gen VALID, level sizes from both start vertices identical to the earlier report")
print("=" * 100, "\nPART 2: deliberately corrupted files (one generator changed, or D lowered by 1)")
for f in sorted(glob.glob(f"{FR}/runs/cloudcheck/haarcheck_gen_calib_files/c*.txt")):
    print("-" * 100); print("file:", f); print("header:", open(f).readline().strip())
    p, dt = run([EXE, f, "--full"]); print(p.stdout.strip().split("selftest group")[-1].split("\n", 1)[1].strip()); print(f"[haarcheck_gen exit {p.returncode}, {dt:.0f}s]")
    mine = levels(p.stdout)
    q, dt = run(["python3", f"{FR}/check_haar_indep.py", f]); ind = levels(q.stdout)
    res = [l for l in q.stdout.splitlines() if l.startswith("RESULT")]
    print(f"check_haar_indep.py: {res[0] if res else q.stderr[-200:]}   [{dt:.0f}s]  levels identical to haarcheck_gen --full: {ind == mine}")
    if os.path.getsize(f) < 100000 and "c3_" not in f:
        q, dt = run(["python3", f"{FR}/build_haar2.py", f]); res = [l for l in q.stdout.splitlines() if "INVALID" in l or l.startswith("VALID") or l.startswith("ecc")]
        print("build_haar2.py: " + " | ".join(res) + f"   [{dt:.0f}s]")
print("=" * 100, "\nPART 3: malformed inputs must be rejected (exit 2, no VALID line)")
for f in sorted(glob.glob(f"{FR}/runs/cloudcheck/haarcheck_gen_calib_files/r*.txt")):
    p, _ = run([EXE, f]); print(f"{os.path.basename(f)}: exit {p.returncode}; stderr: {p.stderr.strip()}; VALID line printed: {'VALID' in p.stdout.splitlines()[-1] if p.stdout.strip() else False}")
