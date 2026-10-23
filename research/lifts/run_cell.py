"""Driver: try lifts (base x group) for one cell (Delta, D) over a range of orders, in parallel, with time limits.

Usage: python3 run_cell.py --delta d --D D --orders LO:HI[:STEP] [--hs 1,2,3] [--secs 10] [--workers 4]
                           [--budget SECONDS] [--tag TAG] [--maxbases B] [--maxgroups G] [--seed S] [--K 4]
                           [--stop-on-solve] [--maxmult m] [--groups "spec;spec"]

For every even order n in the range and every h in --hs with 2h | n, the group order is N = n/(2h); bases are the
connected d-regular bipartite multigraphs on h+h vertices (enum_bases.py, cached in bases/enum/), groups come from
groups.py (or --groups). Jobs (base, group) are sampled (at most B bases x G groups per (n, h)) and run with
`lift search` for --secs seconds each. Results go to runs/TAG.tsv; solutions to sols/TAG_n{n}_*.txt and are
re-checked with `lift check`.
"""
import argparse
import os
import random
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import groups  # noqa: E402


def bases_for(h, d, maxmult):
    if h == 1:
        p = os.path.join(HERE, "bases", f"dipole{d}.txt")
        if not os.path.exists(p):
            with open(p, "w") as f:
                f.write("k 2\n" + "e 0 1\n" * d)
        return [p]
    sub = f"b{h}_{d}" + (f"_m{maxmult}" if maxmult else "")
    dd = os.path.join(HERE, "bases", "enum", sub)
    if not os.path.isdir(dd):
        tmp = dd + ".tmp"
        if h <= 5 or (h == 6 and d == 3):   # complete list up to isomorphism (larger lists take too long)
            cmd = [sys.executable, os.path.join(HERE, "enum_bases.py"), str(h), str(d), tmp]
            if maxmult:
                cmd += ["--maxmult", str(maxmult)]
            subprocess.run(cmd, check=True, stdout=subprocess.DEVNULL)
        else:        # too many to enumerate: 200 random connected d-regular bipartite multigraphs
            os.makedirs(tmp, exist_ok=True)
            for s in range(200):
                with open(os.path.join(tmp, f"r{h}_{d}_{s}.txt"), "w") as f:
                    subprocess.run([sys.executable, os.path.join(HERE, "bases.py"), "random", str(2 * h), str(d), str(s)],
                                   check=True, stdout=f)
        os.rename(tmp, dd)
    return sorted(os.path.join(dd, f) for f in os.listdir(dd) if f.endswith(".txt"))


def run_job(job, secs, K, seed, tag):
    n, h, base, spec = job
    bname = os.path.splitext(os.path.basename(base))[0]
    gname = spec.replace(" ", "")
    out = os.path.join(HERE, "sols", f"{tag}_n{n}_{bname}_{gname}_s{seed}.txt")
    cmd = [os.path.join(HERE, "lift"), "search", base, str(args.D), str(secs), str(seed), str(K), out] + spec.split()
    t0 = time.time()
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=secs + 60)
        txt = r.stdout
    except subprocess.TimeoutExpired:
        txt = ""
    best, evals = None, None
    for line in txt.splitlines():
        if line.startswith("RESULT"):
            kv = dict(w.split("=", 1) for w in line.split()[1:] if "=" in w)
            best, evals = int(kv["best"]), int(kv["evals"])
    ok = None
    if best == 0 and os.path.exists(out):
        c = subprocess.run([os.path.join(HERE, "lift"), "check", out], capture_output=True, text=True)
        ok = "VALID" in c.stdout
    return dict(n=n, h=h, base=bname, group=spec, best=best, evals=evals, secs=round(time.time() - t0, 1),
                sol=out if best == 0 else "", check=ok)


def main():
    global args
    ap = argparse.ArgumentParser()
    ap.add_argument("--delta", type=int, required=True)
    ap.add_argument("--D", type=int, required=True)
    ap.add_argument("--orders", required=True)
    ap.add_argument("--hs", default="1,2,3,4,5,6")
    ap.add_argument("--secs", type=float, default=10)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--budget", type=float, default=600)
    ap.add_argument("--tag", default=None)
    ap.add_argument("--maxbases", type=int, default=6)
    ap.add_argument("--maxgroups", type=int, default=6)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--K", type=int, default=4)
    ap.add_argument("--maxmult", type=int, default=0)
    ap.add_argument("--stop-on-solve", action="store_true")
    ap.add_argument("--groups", default=None)
    ap.add_argument("--extra-bases", default="", help="comma-separated base files tried in addition (any k)")
    ap.add_argument("--rich", action="store_true", help="groups.specs_rich: also products of two non-abelian factors")
    ap.add_argument("--screen", type=int, default=0, help="screen every job with M random assignments first")
    ap.add_argument("--top", type=int, default=8, help="with --screen: anneal the best T jobs per order")
    args = ap.parse_args()
    tag = args.tag or f"d{args.delta}D{args.D}"
    lo, hi, *st = map(int, args.orders.split(":"))
    step = st[0] if st else 2
    rng = random.Random(args.seed)
    jobs = []
    for n in range(lo, hi + 1, step):
        for h in map(int, args.hs.split(",")):
            if n % (2 * h):
                continue
            N = n // (2 * h)
            bs = bases_for(h, args.delta, args.maxmult)
            gs = args.groups.split(";") if args.groups else (groups.specs_rich(N) if args.rich else groups.specs(N))
            gs = [g for g in gs if g]
            rng.shuffle(bs)
            rng.shuffle(gs)
            for b in bs[: args.maxbases]:
                for g in gs[: args.maxgroups]:
                    jobs.append((n, h, b, g))
    for b in filter(None, args.extra_bases.split(",")):
        k = int(next(l.split()[1] for l in open(b) if l.startswith("k ")))
        for n in range(lo, hi + 1, step):
            if n % k:
                continue
            gs = args.groups.split(";") if args.groups else (groups.specs_rich(n // k) if args.rich else groups.specs(n // k))
            gs = [g for g in gs if g]
            rng.shuffle(gs)
            for g in gs[: args.maxgroups]:
                jobs.append((n, k // 2, b, g))
    jobs.sort(key=lambda j: j[0])
    if args.screen:
        # cheap screening: cost quantiles of random voltage assignments, keep the best --top jobs per order
        def scr(job):
            n, h, b, g = job
            cmd = [os.path.join(HERE, "lift"), "sample", b, str(args.D), str(args.screen)] + g.split()
            try:
                out = subprocess.run(cmd, capture_output=True, text=True, timeout=600).stdout
                kv = dict(w.split("=", 1) for w in out.split() if "=" in w)
                return (int(kv["min"]), int(kv["p10"]), int(kv["median"]))
            except Exception:
                return (10 ** 18, 10 ** 18, 10 ** 18)
        with ThreadPoolExecutor(args.workers) as ex:
            scores = list(ex.map(scr, jobs))
        slog = open(os.path.join(HERE, "runs", f"{tag}.screen.tsv"), "a")
        for j, sc in zip(jobs, scores):
            slog.write("\t".join(map(str, (j[0], j[1], os.path.basename(j[2]), j[3]) + sc)) + "\n")
        slog.close()
        byn = {}
        for j, sc in zip(jobs, scores):
            byn.setdefault(j[0], []).append((sc[0] + sc[1] + sc[2], j))
        jobs = [j for n in sorted(byn) for _, j in sorted(byn[n], key=lambda t: t[0])[: args.top]]
    print(f"{tag}: {len(jobs)} jobs, {args.secs}s each, {args.workers} workers, budget {args.budget}s", flush=True)
    os.makedirs(os.path.join(HERE, "runs"), exist_ok=True)
    os.makedirs(os.path.join(HERE, "sols"), exist_ok=True)
    log = open(os.path.join(HERE, "runs", f"{tag}.tsv"), "a")
    t0 = time.time()
    solved = set()
    with ThreadPoolExecutor(args.workers) as ex:
        it = iter(jobs)
        pending = set()

        def submit():
            for job in it:
                if args.stop_on_solve and job[0] in solved:
                    continue
                if time.time() - t0 > args.budget:
                    return
                pending.add(ex.submit(run_job, job, args.secs, args.K, args.seed, tag))
                return

        for _ in range(args.workers):
            submit()
        while pending:
            done = next(as_completed(pending))
            pending.remove(done)
            r = done.result()
            line = "\t".join(str(r[k]) for k in ("n", "h", "base", "group", "best", "evals", "secs", "check", "sol"))
            log.write(line + "\n")
            log.flush()
            if r["best"] == 0:
                solved.add(r["n"])
                print("SOLVED", line, flush=True)
            submit()
    print(f"{tag}: done in {time.time() - t0:.0f}s; solved orders {sorted(solved)}", flush=True)


if __name__ == "__main__":
    main()
