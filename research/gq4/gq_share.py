"""Diameter 4, degree q+2, one step past gq_clones.py: copied lines may share ovoid points.

Q(4,q) + a clone z_a of every ovoid point a (on all lines through a; that fills every old line). Each clone keeps one
spare link, and so does every old point. A line clone y_L needs one stand-in for each point of L: for a non-ovoid
point p that is p itself; for the ovoid point a on L it is a OR z_a (z_a sees exactly the points a sees, so every
distance stays within 4). So the copied lines must be pairwise disjoint away from the ovoid, and at most two of them
may pass through any one ovoid point (one takes a, the other z_a). Counting non-ovoid points: at most q^2+1 lines,
against Tallini's q^2-q+1 for disjoint lines.

Order 2(q+1)(q^2+1) + (q^2+1) + t, t = number of copied lines.
Usage: python3 gq_share.py q seconds
"""
import json
import random
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from gq_clones import q4, lib  # noqa: E402


def search(lines, ovoid, seconds, seed=0):
    rng = random.Random(seed)
    O = set(ovoid)
    ov_of = [next(iter(L & O)) for L in lines]                 # the one ovoid point on each line
    rest = [L - O for L in lines]
    best = []
    t_end = time.time() + seconds
    while time.time() < t_end:
        order = list(range(len(lines)))
        rng.shuffle(order)
        used, cnt, chosen = set(), {}, []
        for j in order:
            if rest[j] & used or cnt.get(ov_of[j], 0) >= 2:
                continue
            chosen.append(j); used |= rest[j]; cnt[ov_of[j]] = cnt.get(ov_of[j], 0) + 1
        # local improvement: try to swap one chosen line out for two that fit
        improved = True
        while improved and time.time() < t_end:
            improved = False
            rng.shuffle(chosen)
            for j in list(chosen):
                chosen.remove(j); used -= rest[j]; cnt[ov_of[j]] -= 1
                cand = [k for k in range(len(lines)) if k not in chosen and not (rest[k] & used) and cnt.get(ov_of[k], 0) < 2]
                rng.shuffle(cand)
                got = []
                for k in cand:
                    if not (rest[k] & used) and cnt.get(ov_of[k], 0) < 2:
                        got.append(k); chosen.append(k); used |= rest[k]; cnt[ov_of[k]] = cnt.get(ov_of[k], 0) + 1
                if len(got) >= 2:
                    improved = True
                    break
                for k in got:
                    chosen.remove(k); used -= rest[k]; cnt[ov_of[k]] -= 1
                chosen.append(j); used |= rest[j]; cnt[ov_of[j]] = cnt.get(ov_of[j], 0) + 1
        if len(chosen) > len(best):
            best = list(chosen)
    return best, ov_of


def build(q, seconds):
    pts, lines, ovoid = q4(q)
    chosen, ov_of = search(lines, ovoid, seconds)
    P, L = len(pts), len(lines)
    edges = [(p, P + k) for k, Ln in enumerate(lines) for p in Ln]
    base = P + L
    through = {}
    for k, Ln in enumerate(lines):
        for p in Ln:
            through.setdefault(p, []).append(k)
    zid = {a: base + i for i, a in enumerate(ovoid)}            # z_a: on every line through a
    for a in ovoid:
        edges += [(zid[a], P + k) for k in through[a]]
    taken = set()
    for i, k in enumerate(chosen):
        y = base + len(ovoid) + i
        for p in lines[k]:
            if p == ov_of[k]:
                stand = p if p not in taken else zid[p]          # first line through a takes a, the second z_a
                taken.add(p)
                edges.append((stand, y))
            else:
                edges.append((p, y))
    n = base + len(ovoid) + len(chosen)
    return n, edges, len(chosen)


if __name__ == '__main__':
    q, secs = int(sys.argv[1]), float(sys.argv[2])
    t0 = time.time()
    n, edges, t = build(q, secs)
    ok = lib.is_valid(n, edges, q + 2, 4)
    print(f'q={q}: GQ {2*(q+1)*(q*q+1)} + ovoid clones {q*q+1} + copied lines {t} (bound {q*q+1}) = {n}, '
          f'degree {q+2}, diameter 4, valid={ok} ({time.time()-t0:.0f}s)', flush=True)
    if ok:
        out = Path(__file__).resolve().parent / 'graphs' / f'gqshare_q{q}_n{n}.json'
        out.write_text(json.dumps({'case': f'd{q+2}D4', 'value': n, 'output': [n, edges]}))
