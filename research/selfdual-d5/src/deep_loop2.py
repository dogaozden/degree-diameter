#!/usr/bin/env python3
"""deep_loop2.py K DIR...: keep running long sdtabu2 runs (ENDG=3, NB=96, STALL=2000, SECS each, env) on the near misses
(best <= THR) found in the sweep folders DIR (each with fmeta/, gapf/ or tabu/ outputs) for groups of order above
logs/K$K/RECORD_N, smallest best first, each (group, record, type) once per seed in SEEDS (comma list, default 11).
Deep outputs go to logs/K$K/deep/; done keys in logs/K$K/deep/done2.txt.  Stops when logs/K$K/deep/STOP2 exists.
env: THR (default 3), SECS (default 600), SEEDS."""
import glob, os, subprocess, sys, time

K = sys.argv[1]; dirs = sys.argv[2:]
THR = int(os.environ.get("THR", 3)); SECS = os.environ.get("SECS", "600")
SEEDS = os.environ.get("SEEDS", "11").split(",")
os.chdir(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
D = f"logs/K{K}/deep"; os.makedirs(D, exist_ok=True)
env = dict(os.environ, K=K, TABU="sdtabu2", ENDG=os.environ.get("ENDG", "3"), NB=os.environ.get("NB", "96"),
           STALL=os.environ.get("STALL", "2000"))


def tabu_lines(f):
    for l in open(f):
        t = l.split()
        if t and t[0] == "TABU":
            yield int(t[t.index("best") + 1]), t[2], t[t.index("f") + 1], t[t.index("m") + 1]


def cands():
    rec = int(open(f"logs/K{K}/RECORD_N").read())
    rows = []
    for d in dirs:
        for f in glob.glob(f"{d}/fmeta/*.out"):
            m, k, r = os.path.basename(f)[:-4].split("_"); n = int(m) * int(k)
            if n <= rec: continue
            for b, rr, ff, mm in tabu_lines(f):
                if b <= THR:
                    sk = "1" if os.path.exists(f[:-4] + ".skipa1") else ""
                    rows.append((b, n, ["env", f"SKIPA1={sk}", "src/deep_fmeta.sh", m, k, r, rr, ff, mm], f"f{m}_{k}_{r}{'a' if sk else ''}_r{rr}_f{ff}"))
        for f in glob.glob(f"{d}/tabu/*.out"):
            n, i = os.path.basename(f)[:-4].split("_")
            if int(n) <= rec: continue
            for b, rr, ff, mm in tabu_lines(f):
                if b <= THR:
                    rows.append((b, int(n), ["src/deep_tabu.sh", "sg", n, i, rr, ff, mm], f"{n}_{i}_r{rr}_f{ff}"))
        for f in glob.glob(f"{d}/gapf/*.out"):
            tag = os.path.basename(f)[:-4]; a = f[:-4] + ".args"
            if not os.path.exists(a): continue
            pre, args = open(a).read().strip().split("|")
            n = None
            for l in open(f):
                if l.startswith("GROUP"): n = int(l.split()[3]); break
            if n is None or n <= rec: continue
            for b, rr, ff, mm in tabu_lines(f):
                if b <= THR:
                    rows.append((b, n, ["src/deep_gapf.sh", tag, pre, args, rr, ff, mm], f"{tag}_r{rr}_f{ff}"))
    rows.sort(key=lambda r: (r[0], r[1]))
    return rows


donef = f"{D}/done2.txt"
done = set(l.strip() for l in open(donef)) if os.path.exists(donef) else set()
while not os.path.exists(f"{D}/STOP2"):
    todo = [(r, s) for s in SEEDS for r in cands() if f"{r[3]}_s{s}" not in done]
    if not todo: time.sleep(60); continue
    (b, n, args, key), seed = min(todo, key=lambda x: (x[0][0], SEEDS.index(x[1]), x[0][1]))
    print(time.strftime("%H:%M"), "deep", key, "best", b, "seed", seed, flush=True)
    subprocess.run(args + [SECS, seed], env=env)
    done.add(f"{key}_s{seed}"); open(donef, "a").write(f"{key}_s{seed}\n")
