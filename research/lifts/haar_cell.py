"""Haar graphs (= lifts of the dipole) for one cell with haar_gen3: screen candidate groups, anneal the best.

Usage: python3 haar_cell.py d D NLO NHI --bin HAAR_GEN3 --tag TAG [--screen 200] [--top 12] [--secs 300] [--seeds 2]

Candidates come from research/frontier/sizelaw/small_cands.py (metacyclic x Z_n plus the matrix / affine / product
families of cands_gen.py), group orders N in [NLO, NHI]. Each is screened with RANDSAMPLE (cost quantiles of random
connection sets); the score is (p10 + median) / mu(N), mu(N) = N exp(-W/N) as in SIZE_LAW.md. The best --top are
annealed in order of increasing N (once an order is solved, its other candidates are skipped).
Solutions: sols/haar/TAG_*.txt (haar_gen3 format; convert with haar2lift.py). Log: runs/TAG.tsv.
"""
import argparse
import math
import os
import subprocess
import time

HERE = os.path.dirname(os.path.abspath(__file__))
SIZELAW = os.path.join(HERE, "..", "frontier", "sizelaw")


def W(d, D):
    if D % 2 == 0:
        return d * sum((d - 1) ** (2 * i) for i in range(D // 2))
    return 1 + sum(d * (d - 1) ** (2 * i - 1) for i in range(1, (D - 1) // 2 + 1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("d", type=int)
    ap.add_argument("D", type=int)
    ap.add_argument("nlo", type=int)
    ap.add_argument("nhi", type=int)
    ap.add_argument("--bin", required=True)
    ap.add_argument("--tag", required=True)
    ap.add_argument("--screen", type=int, default=200)
    ap.add_argument("--top", type=int, default=12)
    ap.add_argument("--secs", type=float, default=300)
    ap.add_argument("--seeds", type=int, default=2)
    a = ap.parse_args()
    out = subprocess.run(["python3", "small_cands.py", str(a.nlo), str(a.nhi)], cwd=SIZELAW, capture_output=True,
                         text=True).stdout
    cands = [(int(l.split("|")[1]), l.split("|")[0]) for l in out.splitlines() if "|" in l]
    w = W(a.d, a.D)
    log = open(os.path.join(HERE, "runs", f"{a.tag}.tsv"), "a")
    scored = []
    for N, spec in cands:
        env = dict(os.environ, RANDSAMPLE=str(a.screen))
        try:
            r = subprocess.run([a.bin, str(a.d), str(a.D), "1", "1", "8", "/dev/null"] + spec.split(), env=env,
                               capture_output=True, text=True, timeout=300).stdout
            kv = dict(x.split("=", 1) for x in r.split() if "=" in x)
            p10, med, mn = int(kv["p10"]), int(kv["median"]), int(kv["min"])
        except Exception:
            continue
        mu = N * math.exp(-w / N)
        sc = (p10 + med) / mu
        scored.append((sc, N, spec, mn, p10, med))
        log.write(f"screen\t{N}\t{spec}\tmin={mn}\tp10={p10}\tmedian={med}\tmu={mu:.1f}\tscore={sc:.2f}\n")
        log.flush()
    scored.sort()
    chosen = sorted(scored[: a.top], key=lambda t: (t[1], t[0]))
    print(f"{a.tag}: {len(cands)} candidates screened, annealing {len(chosen)}", flush=True)
    solved = set()
    for sc, N, spec, mn, p10, med in chosen:
        if N in solved:
            continue
        for s in range(1, a.seeds + 1):
            tag = f"{a.tag}_{spec.replace(' ', '_')}_s{s}"
            sol = os.path.join(HERE, "sols", "haar", tag + ".txt")
            t0 = time.time()
            try:
                r = subprocess.run([a.bin, str(a.d), str(a.D), str(a.secs), str(s), "8", sol] + spec.split(),
                                   capture_output=True, text=True, timeout=a.secs + 120).stdout
            except subprocess.TimeoutExpired:
                r = ""
            best = next((x.split("=")[1] for l in r.splitlines() if l.startswith("RESULT") for x in l.split()
                         if x.startswith("best=")), "?")
            ok = "full diameter check: OK" in r
            line = f"run\t{N}\t{spec}\tseed={s}\tbest={best}\tcheck={'OK' if ok else '-'}\t{time.time() - t0:.0f}s"
            log.write(line + "\n")
            log.flush()
            if best == "0" and ok:
                print("SOLVED", line, sol, flush=True)
                solved.add(N)
                break
    print(f"{a.tag}: done; solved N = {sorted(solved)}", flush=True)


if __name__ == "__main__":
    main()
