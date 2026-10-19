#!/usr/bin/env python3
"""Round 4 plan: near-miss jobs (Part A), ladder jobs (Part B), and the climb rule.

Candidates are groups.py names: a base group G, or G x Z_k (k >= 2), with order in (threshold, 1.08 * threshold].
Abelian groups are left out. Small non-abelian bases (order 6 and up) are allowed but ranked last, so a large
non-abelian part is always preferred. Duplicates (same group under two names) are dropped with a fingerprint: element-order counts
plus the centre size. Two non-isomorphic groups with the same fingerprint would be dropped by mistake; none is known.

Usage:
  python3 h4_plan.py                 print the Part B candidates per Δ with their fingerprints
  python3 h4_plan.py --write         build the tables needed, write h4_jobs.txt
  python3 h4_plan.py --next NAME D   print the next larger same-family name for degree D (climb rule)
"""
import os
import sys
from collections import Counter
from math import gcd

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import groups  # noqa: E402

THRESHOLD = {5: 177, 6: 342, 7: 570, 8: 864, 9: 1320, 10: 2000}  # order must exceed this
WINDOW = 1.08
MIN_BASE = 6
# Part B jobs per Δ (fingerprint duplicates are dropped before counting). Total 48 = 24 job-hours at 30 min.
QUOTA = {5: 8, 6: 8, 7: 8, 8: 8, 9: 8, 10: 8}
# Part A: the five near misses from slice 1, each with 3 seeds and K = 1 or 20.
NEAR_MISS = [(6, "sl_5__x__cyc_3"), (7, "agl_25"), (8, "heis_5__x__cyc_7"),
             (8, "agl_7__x__cyc_21"), (9, "heis_11")]
SEEDS = (1, 2, 3)
KS = (1, 20)
PART_A_SECS = 7200
PART_B_SECS = 1800
PART_B_K = 20
PART_B_SEED = 1
CLIMB_MAX = 2800  # largest order a climb may queue (tables are Python lists, so N^2 stays small)


def prime_powers(limit):
    out = []
    for q in range(2, limit + 1):
        p = next(p for p in range(2, q + 1) if q % p == 0)
        r = q
        while r % p == 0:
            r //= p
        if r == 1:
            out.append(q)
    return out


def primes(limit):
    return [p for p in prime_powers(limit) if all(p % r for r in range(2, p))]


def base_order(kind, q):
    if kind == "sl":
        return q * (q * q - 1)
    if kind == "psl":
        return q * (q * q - 1) // gcd(2, q - 1)
    if kind == "pgl":
        return q * (q * q - 1)
    if kind == "gl":
        return (q * q - 1) * (q * q - q)
    if kind == "agl":
        return q * (q - 1)
    if kind == "heis":
        return q ** 3
    raise ValueError(kind)


def split(name):
    """'psl_9__x__cyc_6' -> ('psl', 9, 6); 'agl_25' -> ('agl', 25, 1)."""
    base, _, k = name.partition("__x__cyc_")
    kind, q = base.split("_")
    return kind, int(q), int(k) if k else 1


def join(kind, q, k):
    return f"{kind}_{q}" + (f"__x__cyc_{k}" if k > 1 else "")


def order(name):
    kind, q, k = split(name)
    return base_order(kind, q) * k


def base_names(kind, limit=60):
    if kind == "heis":
        return primes(13)
    return [q for q in prime_powers(limit) if base_order(kind, q) >= MIN_BASE
            and (kind != "agl" or q >= 3)]


def candidates(d):
    """(name, order) in the window, largest non-abelian part first."""
    lo = THRESHOLD[d]
    hi = int(WINDOW * lo)
    out = []
    for kind in ("sl", "psl", "pgl", "gl", "agl", "heis"):
        for q in base_names(kind):
            g = base_order(kind, q)
            if g < MIN_BASE:
                continue
            for k in range(1, hi // g + 1):
                if lo < g * k <= hi:
                    out.append((join(kind, q, k), g * k))
    return sorted(out, key=lambda c: (-(c[1] // split(c[0])[2]), c[0]))


def fingerprint(table):
    N = len(table)
    hist = Counter()
    for g in range(N):
        x, k = g, 1
        while x != 0:
            x = table[x][g]
            k += 1
        hist[k] += 1
    centre = sum(1 for z in range(N) if all(table[z][h] == table[h][z] for h in range(N)))
    return (N, tuple(sorted(hist.items())), centre)


def part_b(d, verbose=False):
    """Pick QUOTA[d] non-duplicate candidates for Δ = d, building (and checking) tables as needed."""
    picked, seen = [], {}
    for name, o in candidates(d):
        if len(picked) == QUOTA[d]:
            break
        if name in ("agl_25", "heis_11", "sl_5__x__cyc_3", "heis_5__x__cyc_7", "agl_7__x__cyc_21"):
            continue  # Part A near misses already run at 2 h
        path = os.path.join(groups.TABLE_DIR, name + ".txt")
        if not os.path.exists(path):
            table = groups.build(name)
            groups.check_table(table)
            groups.write_table(path, table)
        else:
            with open(path) as f:
                N = int(f.readline())
                table = [list(map(int, f.readline().split())) for _ in range(N)]
        fp = fingerprint(table)
        if fp in seen:
            if verbose:
                print(f"  drop {name}: same fingerprint as {seen[fp]}")
            continue
        seen[fp] = name
        picked.append((name, o))
    return picked


def next_larger(name, d):
    """Climb rule: same base family and same Z_k factor, smallest order above the current one, at most CLIMB_MAX."""
    kind, q, k = split(name)
    current = order(name)
    best = None
    for q2 in base_names(kind, limit=200):
        o = base_order(kind, q2) * k
        if current < o <= CLIMB_MAX and (best is None or o < best[1]):
            best = (join(kind, q2, k), o)
    if best is None:
        return None
    return best[0]


def main(argv):
    if argv[:1] == ["--next"]:
        print(next_larger(argv[1], int(argv[2])))
        return 0
    write = "--write" in argv
    plan = {}
    for d in sorted(THRESHOLD):
        plan[d] = part_b(d, verbose=not write)
        lo, hi = THRESHOLD[d], int(WINDOW * THRESHOLD[d])
        print(f"d={d} window ({lo}, {hi}]: {len(plan[d])} jobs")
        for name, o in plan[d]:
            print(f"  {o:5d}  {name}")
    if not write:
        return 0
    lines = ["# d table secs seed K   (Part B: 30 min, K=20; Part A: 2 h, K=1 or 20, seeds 1-3)",
             "# Part B first (threshold < order <= 1.08 x threshold), then Part A seed by seed."]
    for d in sorted(plan):
        for name, _ in plan[d]:
            lines.append(f"{d} {name} {PART_B_SECS} {PART_B_SEED} {PART_B_K}")
    for seed in SEEDS:
        for d, name in NEAR_MISS:
            for k in KS:
                lines.append(f"{d} {name} {PART_A_SECS} {seed} {k}")
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "h4_jobs.txt")
    with open(path, "w") as f:
        f.write("\n".join(lines) + "\n")
    print(f"wrote {path}: {sum(1 for l in lines if l and l[0] != '#')} jobs")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
