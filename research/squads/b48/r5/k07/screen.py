# Screen (base, parity pattern, meta group) triples with plift (parity-aware lift annealer), short runs.
import json, math, os, random, subprocess, sys, time
from enum_bases import *   # noqa
K7 = "/home/user/degree-diameter/research/squads/b48/r5/k07"
T = "/home/user/degree-diameter/research/squads/b48/tools"

def base_file(path, b, items):
    with open(path, "w") as f:
        f.write(f"{b} {len(items)}\n")
        for t, u, v in items:
            f.write(f"{u} {v}" + (" s" if t == "s" else "") + "\n")

def groups_for(b, rng, count, need_semi, lo_b=801, hi_b=900):
    Nlo = -(-lo_b // b); Nhi = -(-hi_b // b)
    cands = []
    for N in range(Nlo, Nhi + 1):
        for m in range(3, N + 1):
            if N % m: continue
            k = N // m
            if k % 2: continue
            if need_semi and k % 4 != 2: continue
            for r in range(2, m):
                if math.gcd(r, m) != 1: continue
                if pow(r, k, m) != 1 % m: continue
                cands.append((m, k, r))
    rng.shuffle(cands)
    return cands[:count]

def run(b, items, pat, m, k, r, secs, seed):
    N = m * k
    bf = f"{K7}/tmp_base_{b}.txt"
    base_file(bf, b, items)
    gs = f"meta:{m}:{k}:{r}"
    env = dict(os.environ, THREADS="1", NOTREE="1", BIP="0", QUIET="1", MS=str(m),
               PAR="".join(str(x) for x in pat))
    cmd = ["timeout", "120", "nice", "-n", "10", f"{K7}/plift", bf, gs, "3", "10", str(secs), str(seed), "8"]
    p = subprocess.run(cmd, env=env, capture_output=True, text=True)
    line = [l for l in p.stdout.splitlines() if l.startswith("RESULT")]
    if not line: return None, p.stdout + p.stderr
    best = int(line[0].split("best=")[1].split()[0])
    return best, line[0]

if __name__ == "__main__":
    # usage: screen.py B GCOUNT SECS OUT [ONE]   (ONE: only the first pattern per base)
    bb_want = int(sys.argv[1]); gcount = int(sys.argv[2]); secs = float(sys.argv[3]); out = sys.argv[4]
    one = len(sys.argv) > 5
    rng = random.Random(7)
    bases = [json.loads(l) for l in open(f"{K7}/bases.jsonl")]
    fo = open(out, "a")
    for bb in bases:
        if bb["b"] != bb_want: continue
        items = [tuple(x) for x in bb["items"]]
        has_semi = any(t == "s" for t, _, _ in items)
        grps = groups_for(bb["b"], rng, gcount, has_semi)
        pats = bb["patterns"][-1:] if one else bb["patterns"]
        for pat in pats:
            for (m, k, r) in grps:
                best, info = run(bb["b"], items, pat, m, k, r, secs, 1)
                rec = {"b": bb["b"], "items": items, "pat": "".join(map(str, pat)), "m": m, "k": k, "r": r, "best": best}
                fo.write(json.dumps(rec) + "\n"); fo.flush()
    fo.close()
