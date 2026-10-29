"""Extend R_L (all lines through the 756 pairwise opposite points R_0 of H(11)) to a larger dual segment set.

A set G of lines is a dual segment set if for every line in G the other lines of G meeting it all pass through one of
its points.  Lines through distinct points of a partial ovoid never meet, so the pencils of R_0 (9,072 lines) form a
dual segment set, and a line can be added only if it has no point on a pencil line ("free" line).  Among the free lines
we search (randomized greedy with segment bookkeeping, then a simple 1-out-2-in local search) for a large set in which
every line meets the other chosen lines in at most one of its points.  Output: the chosen extra line ids (one per line),
checked again from scratch.
Usage: python extend_RL.py SEEDS SECONDS OUT"""
import sys
import time
import numpy as np

seeds, secs, out = int(sys.argv[1]), float(sys.argv[2]), sys.argv[3]
b = open('/home/user/degree-diameter/research/p4/d6/hex/hex_q11.bin', 'rb').read()
q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32))
Q1 = q + 1
LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
order = np.lexsort((flat_l, flat_p)); PL = flat_l[order].reshape(N, Q1)
mt = open('d14D7_hex11_mirror768_n1774632.sol').read().split('\n')
R0 = np.array([int(v) for v in mt[1].split()[1:]], dtype=np.int64)[:756]
RL = np.zeros(Lc, bool); RL[PL[R0].reshape(-1)] = True
cov = np.zeros(N, bool); cov[LP[RL].reshape(-1)] = True
free = np.nonzero(~cov[LP].any(axis=1))[0]
isfree = np.zeros(Lc, bool); isfree[free] = True
pts_of = {int(L): [int(p) for p in LP[L]] for L in free}
lines_at = {}
for L in free:
    for p in LP[L]:
        lines_at.setdefault(int(p), []).append(int(L))
print(f'{len(free)} free lines', flush=True)


def check(S):
    """dual segment set check of S (extra lines) on its own (they meet no pencil line by construction)."""
    cnt = {}
    for L in S:
        for p in pts_of[L]:
            cnt[p] = cnt.get(p, 0) + 1
    return all(sum(1 for p in pts_of[L] if cnt[p] >= 2) <= 1 for L in S)


def greedy(rng, start=()):
    chosen = set(start)
    cnt = {}
    seg = {}            # chosen line -> its segment point (or None)
    for L in chosen:
        for p in pts_of[L]:
            cnt[p] = cnt.get(p, 0) + 1
    for L in chosen:
        sp = [p for p in pts_of[L] if cnt[p] >= 2]
        seg[L] = sp[0] if sp else None
    for L in rng.permutation(free):
        L = int(L)
        if L in chosen:
            continue
        meet = [p for p in pts_of[L] if cnt.get(p, 0) >= 1]
        if len(meet) > 1:
            continue
        if meet:
            z = meet[0]
            ok = all(seg[M] in (None, z) for M in lines_at[z] if M in chosen)
            if not ok:
                continue
            for M in lines_at[z]:
                if M in chosen:
                    seg[M] = z
            seg[L] = z
        else:
            seg[L] = None
        chosen.add(L)
        for p in pts_of[L]:
            cnt[p] = cnt.get(p, 0) + 1
    return chosen


best = set()
t0 = time.time()
s = 0
while time.time() - t0 < secs and s < seeds:
    rng = np.random.default_rng(s)
    S = greedy(rng)
    # perturb: drop 5% and refill, keep if not worse
    for it in range(30):
        keep = set(L for L in S if rng.random() > 0.05)
        S2 = greedy(rng, keep)
        if len(S2) >= len(S):
            S = S2
    assert check(S)
    if len(S) > len(best):
        best = S
        print(f'seed {s}: {len(S)} extra lines (t={time.time() - t0:.0f}s)', flush=True)
    s += 1
assert check(best) and all(isfree[L] for L in best)
open(out, 'w').write('\n'.join(str(L) for L in sorted(best)) + '\n')
print(f'best {len(best)} -> R_L = {RL.sum() + len(best)}, K = {RL.sum() + len(best) + 768}, '
      f'n = {10 * N + 2 * (RL.sum() + len(best) + 768)}; wrote {out}')
