#!/usr/bin/env python3
"""Fine ladder (brief docs/d5-fine-brief.md on research-diam4): groups just above each current best, one shard.

Pool per Δ: every non-abelian name groups.py can build (sl, psl, pgl, gl, agl, aff, heis, z2 diag/singer, meta,
and base x cyc_k) with order in (THRESHOLD[Δ], 1.08 * THRESHOLD[Δ]]. Ranked by (Δ, order, name); the first QUOTA
non-duplicates per Δ are kept (duplicates by h4_plan.fingerprint, built only as far as needed). The 48 picks are
numbered in (Δ, order) order; shard S takes the picks with index % 2 == S (0-based; shard 1 = odd indices).

Usage:
  python3 fine_plan.py                  list the picks for shard 1 (builds the tables it needs)
  python3 fine_plan.py --write 1        write fine_jobs_s1.txt: 2 seeds x shard picks, 30 min, K 20
"""
import os
import sys
from math import gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import groups  # noqa: E402
import h4_plan  # noqa: E402

THRESHOLD = {5: 177, 6: 342, 7: 576, 8: 882, 9: 1331, 10: 2000}  # current bests from the brief; order must exceed
WINDOW = 1.08
QUOTA = 8
SEEDS = (1, 2)
SECS = 1800
K = 20


def window(d):
    return THRESHOLD[d], int(WINDOW * THRESHOLD[d])


def pool(d):
    """All (name, order) in the window, not abelian-checked yet."""
    lo, hi = window(d)
    primes = [p for p in h4_plan.primes(hi) if p >= 2]
    qs = h4_plan.prime_powers(hi)
    bases = []  # (name, order), all non-abelian candidates' bases and the groups themselves
    for kind in ("sl", "psl", "pgl", "gl"):
        for q in qs:
            o = h4_plan.base_order(kind, q)
            if o <= hi and o >= 6:
                bases.append((f"{kind}_{q}", o))
    for q in qs:
        if q >= 3 and q * (q - 1) <= hi:
            bases.append((f"agl_{q}", q * (q - 1)))
        for k in range(2, q - 1):
            if (q - 1) % k == 0 and q * k <= hi:
                bases.append((f"aff_{q}_{k}", q * k))
    for p in primes:
        if p ** 3 <= hi:
            bases.append((f"heis_{p}", p ** 3))
    for p in primes:
        for k in range(2, hi // (p * p) + 1):
            if p * p * k <= hi and (p * p - 1) % k == 0:
                bases.append((f"z2_{p}_{k}_singer", p * p * k))
            for x in range(1, p):
                for y in range(x, p):
                    ox, oy = order_mod(p, x), order_mod(p, y)
                    if lcm(ox, oy) == k and p * p * k <= hi:
                        bases.append((f"z2_{p}_{k}_diag_{x}_{y}", p * p * k))
    for m in range(3, hi // 2 + 1):
        for k in range(2, hi // m + 1):
            if m * k > hi:
                break
            for lam in range(2, m):
                if gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    bases.append((f"meta_{m}_{k}_{lam}", m * k))
    # direct products with cyclic groups; the bases are non-abelian, so every product is non-abelian
    out = []
    for name, o in bases:
        if lo < o <= hi:
            out.append((name, o))
        for k in range(2, hi // o + 1):
            if lo < o * k <= hi:
                out.append((f"{name}__x__cyc_{k}", o * k))
    return sorted(set(out), key=lambda c: (c[1], c[0]))


def order_mod(p, x):
    o, y = 1, x % p
    while y != 1:
        y = y * x % p
        o += 1
    return o


def lcm(a, b):
    return a * b // gcd(a, b)


def picks(d, verbose=False):
    chosen, seen = [], {}
    for name, o in pool(d):
        if len(chosen) == QUOTA:
            break
        table = groups.build(name)
        if table is None or len(table) != o:
            raise RuntimeError(f"{name}: built order {len(table)} != {o}")
        if fingerprint_abelian(table):
            continue
        fp = h4_plan.fingerprint(table)
        if fp in seen:
            if verbose:
                print(f"  drop {name}: same fingerprint as {seen[fp]}")
            continue
        seen[fp] = name
        groups.check_table(table)
        os.makedirs(groups.TABLE_DIR, exist_ok=True)
        groups.write_table(os.path.join(groups.TABLE_DIR, name + ".txt"), table)
        chosen.append((name, o))
    return chosen


def fingerprint_abelian(table):
    """A group is abelian iff the table is symmetric."""
    N = len(table)
    return all(table[g][h] == table[h][g] for g in range(N) for h in range(g + 1, N))


def all_picks():
    out = []
    for d in sorted(THRESHOLD):
        for name, o in picks(d, verbose=True):
            out.append((d, name, o))
    return out


def main(argv):
    if argv[:1] == ["--write"]:
        shard = int(argv[1])
        plan = all_picks()
        mine = [p for i, p in enumerate(plan) if i % 2 == shard]
        lines = [f"# fine ladder shard {shard}: d table secs seed K  (30 min, K=20, seeds 1-2)"]
        for seed in SEEDS:
            for d, name, _ in mine:
                lines.append(f"{d} {name} {SECS} {seed} {K}")
        path = os.path.join(HERE, f"fine_jobs_s{shard}.txt")
        with open(path, "w") as f:
            f.write("\n".join(lines) + "\n")
        for i, (d, name, o) in enumerate(plan):
            print(f"{i:2d} {'*' if i % 2 == shard else ' '} d={d} order={o:5d} {name}")
        print(f"wrote {path}: {len(mine)} groups x {len(SEEDS)} seeds")
        return 0
    shard = 1
    plan = all_picks()
    for i, (d, name, o) in enumerate(plan):
        print(f"{i:2d} {'*' if i % 2 == shard else ' '} d={d} order={o:5d} {name}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
