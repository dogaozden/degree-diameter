"""Search for a large multiset of lines of Q(4,q) in which every point lies on at most 2 chosen lines.

A line may be chosen twice. The multiset size is the number of line clones that from_cover2.py adds.
Upper bound: 2*(q^2+1) (every point covered exactly twice, each line has q+1 points).

Method: simulated annealing on multiplicities m_L in {0,1,2}. Energy = -sum(m) + lam * excess, where excess is
sum over points of max(0, load_p - 2). Moves change one m_L by +-1. The best state with zero excess is kept,
then greedily filled. Starts: empty, spread (the doubled partial spread in spreads/), random (greedy),
sections (greedy union of hyperbolic quadric sections Q+(3,q), each 28 lines covering 196 points twice for q=13).

Usage:
  python3 twocover_search.py run Q SECONDS SEED START [LAM] [T0] [T1] [CYCLE]
      START in {empty, spread, random, sections}. Writes runs_2cover/q{Q}_{START}_s{SEED}_best.json after every
      cycle, so a killed run still leaves its best.
  python3 twocover_search.py collect Q
      Re-checks every runs_2cover/q{Q}_*_best.json and saves the largest as spreads/cover2_q{Q}_t{size}.json
      (a JSON list of line indices, a repeated index means the line is chosen twice).
"""
import glob
import itertools
import json
import math
import random
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from gq_clones import q4  # noqa: E402

RUNS = HERE / 'runs_2cover'
SPREADS = HERE / 'spreads'


def load_geometry(q):
    pts, lines, ovoid = q4(q)
    return pts, [tuple(sorted(L)) for L in lines], ovoid


def expand(m):
    return [k for k, mk in enumerate(m) for _ in range(mk)]


def check_cover2(lines, multiset):
    """Independent check: every point lies on at most 2 chosen lines (repeats count), indices in range."""
    assert all(0 <= k < len(lines) for k in multiset), 'line index out of range'
    count = {}
    for k in multiset:
        for p in lines[k]:
            count[p] = count.get(p, 0) + 1
    return max(count.values(), default=0) <= 2


def fill(m, lines, load, rng):
    """Greedily add any line (or second copy) whose points all still have load < 2."""
    order = list(range(len(lines)))
    rng.shuffle(order)
    for k in order:
        while m[k] < 2 and all(load[p] < 2 for p in lines[k]):
            m[k] += 1
            for p in lines[k]:
                load[p] += 1
    return m


def hyperbolic_sections(q, pts, lines):
    """Lists of 2(q+1) line indices: the lines inside a hyperplane section Q+(3,q) (prime q only)."""
    import numpy as np
    assert all(q % d for d in range(2, int(q ** 0.5) + 1)), 'sections need prime q here'
    P = np.array(pts, dtype=np.int64)
    LP = np.array(lines, dtype=np.int64)
    sections = []
    for h in itertools.product(range(q), repeat=5):
        if not any(h) or h[next(i for i, x in enumerate(h) if x)] != 1:
            continue  # one normal vector per hyperplane
        on = (P @ np.array(h, dtype=np.int64)) % q == 0
        if on.sum() != (q + 1) ** 2:
            continue
        inside = np.nonzero(on[LP].all(axis=1))[0].tolist()
        if len(inside) == 2 * (q + 1):
            sections.append(inside)
    return sections


def start_state(q, start, lines, pts, rng):
    L = len(lines)
    m = [0] * L
    load = [0] * len(pts)

    def add(k):
        if m[k] < 2 and all(load[p] < 2 for p in lines[k]):
            m[k] += 1
            for p in lines[k]:
                load[p] += 1

    if start == 'empty':
        pass
    elif start == 'spread':
        files = sorted(SPREADS.glob(f'spread_q{q}_s*.json'), key=lambda f: -len(json.loads(f.read_text())))
        assert files, f'no spread file for q={q}'
        spread = json.loads(files[0].read_text())
        spread = spread['lines'] if isinstance(spread, dict) else spread
        for k in spread:  # the doubled spread: every chosen line taken twice (disjoint, so always fits)
            m[k] = 2
            for p in lines[k]:
                load[p] += 2
        print(f'start: doubled spread {files[0].name}, size {2 * len(spread)}', flush=True)
    elif start == 'random':
        order = list(range(L))
        rng.shuffle(order)
        for k in order:
            add(k)
            add(k)
    elif start == 'sections':
        secs = hyperbolic_sections(q, pts, lines)
        print(f'start: {len(secs)} hyperbolic sections found', flush=True)
        rng.shuffle(secs)
        for sec in secs:
            for k in sec:
                add(k)
    else:
        raise SystemExit(f'unknown start {start}')
    return m, load


def anneal(q, pts, lines, seconds, seed, start, lam, t0, t1, cycle):
    rng = random.Random(seed)
    m, load = start_state(q, start, lines, pts, rng)
    L = len(lines)
    S = sum(m)
    V = sum(max(0, c - 2) for c in load)
    if V:
        raise SystemExit('start state infeasible')
    fill(m, lines, load, rng)
    S = sum(m)
    best_S, best_m = S, m[:]
    print(f'init: size {S}, bound {2 * (q * q + 1)}', flush=True)
    out = RUNS / f'q{q}_{start}_s{seed}_best.json'
    t_end = time.time() + seconds
    cyc = 0
    ratio = t1 / t0
    rand = rng.random
    randrange = rng.randrange
    exp = math.exp
    while time.time() < t_end:
        cyc += 1
        for step in range(cycle):
            T = t0 * ratio ** (step / cycle)
            k = randrange(L)
            mk = m[k]
            if mk == 0:
                d = 1
            elif mk == 2:
                d = -1
            else:
                d = 1 if rand() < 0.5 else -1
            lk = lines[k]
            if d > 0:
                dv = 0
                for p in lk:
                    if load[p] >= 2:
                        dv += 1
            else:
                dv = 0
                for p in lk:
                    if load[p] > 2:
                        dv -= 1
            dE = -d + lam * dv
            if dE <= 0 or rand() < exp(-dE / T):
                m[k] = mk + d
                for p in lk:
                    load[p] += d
                S += d
                V += dv
                if V == 0 and S > best_S:
                    best_S, best_m = S, m[:]
            if time.time() > t_end:
                break
        # Save the best found so far, greedily filled, after every cycle.
        bl = [0] * len(pts)
        bm = best_m[:]
        for k in range(L):
            for p in lines[k]:
                bl[p] += bm[k]
        fill(bm, lines, bl, rng)
        best_S, best_m = sum(bm), bm
        print(f'cycle {cyc}: best {best_S}, current {S} (excess {V}), T_end {t0 * ratio ** ((step + 1) / cycle):.3f}, '
              f'elapsed {seconds - (t_end - time.time()):.0f}s', flush=True)
        ms = expand(best_m)
        assert check_cover2(lines, ms), 'internal error: best state violates the cap'
        RUNS.mkdir(exist_ok=True)
        out.write_text(json.dumps({'q': q, 'start': start, 'seed': seed, 'size': len(ms), 'lines': ms}))
    print(f'done: best {best_S} (bound {2 * (q * q + 1)}), wrote {out}', flush=True)
    return best_S


def collect(q):
    _, lines, _ = load_geometry(q)
    best = None
    for f in sorted(glob.glob(str(RUNS / f'q{q}_*_best.json'))):
        d = json.loads(Path(f).read_text())
        ok = check_cover2(lines, d['lines'])
        print(f'{Path(f).name}: size {len(d["lines"])}, valid={ok}')
        if ok and (best is None or len(d['lines']) > len(best)):
            best = d['lines']
    assert best is not None, 'no valid runs'
    out = SPREADS / f'cover2_q{q}_t{len(best)}.json'
    out.write_text(json.dumps(sorted(best)))
    print(f'saved {out} size {len(best)}')
    return out


if __name__ == '__main__':
    cmd = sys.argv[1]
    if cmd == 'run':
        q, secs, seed, start = int(sys.argv[2]), float(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
        lam = float(sys.argv[6]) if len(sys.argv) > 6 else 1.0
        t0 = float(sys.argv[7]) if len(sys.argv) > 7 else 0.5
        t1 = float(sys.argv[8]) if len(sys.argv) > 8 else 0.05
        cycle = int(sys.argv[9]) if len(sys.argv) > 9 else 2_000_000
        pts, lines, ovoid = load_geometry(q)
        print(f'q={q} points {len(pts)} lines {len(lines)} lam={lam} T={t0}->{t1} cycle={cycle}', flush=True)
        anneal(q, pts, lines, secs, seed, start, lam, t0, t1, cycle)
    elif cmd == 'collect':
        collect(int(sys.argv[2]))
    else:
        raise SystemExit(__doc__)
