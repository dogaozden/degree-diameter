#!/usr/bin/env python3
"""Card c6: adversarial check of claim (1). Simulated annealing over (regular tournament, typing) on 9 and 11
levels, maximising the worst violation margin of claim (1) over all six parameter sets (normalised by P).
A positive best value would be a counterexample to claim (1)."""
import math
import random
import sys
import numpy as np

sys.path.insert(0, "/home/user/degree-diameter/research/squads/d7thm-r1/c6")
from check_thm33 import PARAMS, eval_counts, bounds, rotational  # noqa: E402


def margin(A, T, k):
    c = eval_counts(A[None], T[None, None])
    best = -math.inf
    for pname, P, Lam, m in PARAMS:
        alpha = c["aP"] * P + c["aL"] * Lam + c["am"] * m
        beta = c["bP"] * P + c["bL"] * Lam + c["bm"] * m
        minA = int(alpha.min())
        minB = int(beta.min())
        bA, bB, bS = bounds(k, P, Lam, m)
        mv = max(minA - bA, minB - bB)
        if bS is not None:
            mv = max(mv, (minA + minB) - bS)
        best = max(best, mv / P)
    return best


def run(L, restarts, steps, seed):
    k = (L - 1) // 2
    rng = random.Random(seed)
    overall = (-math.inf, None)
    for r in range(restarts):
        A = rotational(L).tolist()
        # random start: walk away from rotational
        for _ in range(300 + 50 * r):
            i, j, c = rng.randrange(L), rng.randrange(L), rng.randrange(L)
            if len({i, j, c}) == 3 and A[i][j] and A[j][c] and A[c][i]:
                A[i][j] = A[j][c] = A[c][i] = False
                A[j][i] = A[c][j] = A[i][c] = True
        T = [rng.random() < 0.5 for _ in range(L)]

        def state_arr():
            return np.array(A, dtype=bool), np.array(T, dtype=bool)

        cur = margin(*state_arr(), k)
        best = (cur, [row[:] for row in A], T[:])
        for s in range(steps):
            temp = 0.02 * (1 - s / steps) + 1e-6
            if rng.random() < 0.3:
                v = rng.randrange(L)
                T[v] = not T[v]
                new = margin(*state_arr(), k)
                if new >= cur or rng.random() < math.exp((new - cur) / temp):
                    cur = new
                else:
                    T[v] = not T[v]
            else:
                i, j, c = rng.randrange(L), rng.randrange(L), rng.randrange(L)
                if len({i, j, c}) < 3 or not (A[i][j] and A[j][c] and A[c][i]):
                    continue
                A[i][j] = A[j][c] = A[c][i] = False
                A[j][i] = A[c][j] = A[i][c] = True
                new = margin(*state_arr(), k)
                if new >= cur or rng.random() < math.exp((new - cur) / temp):
                    cur = new
                else:
                    A[i][j] = A[j][c] = A[c][i] = True
                    A[j][i] = A[c][j] = A[i][c] = False
            if cur > best[0]:
                best = (cur, [row[:] for row in A], T[:])
        print("L=%d restart %d: best normalised margin %.6g (<=0 means claim (1) holds)" % (L, r, best[0]))
        sys.stdout.flush()
        if best[0] > overall[0]:
            overall = (best[0], best)
    return overall


if __name__ == "__main__":
    for L in (9, 11):
        val, (score, Ab, Tb) = run(L, restarts=3, steps=12000, seed=100 + L)
        print("L=%d overall best normalised margin %.6g; best tournament has in/out-degree %s"
              % (L, val, sorted(set(sum(r) for r in Ab))))
        sys.stdout.flush()
