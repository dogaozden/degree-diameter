#!/usr/bin/env python3
"""Independent points-only checker for a colouring of the points of H(q) (card e12, squad polylev r2).

Usage: check_points.py HEXBIN COLFILE K

Reads the hexagon directly from the raw int32 file (header q, N, L; then L*(q+1) int32 point ids, one row per line)
and builds the point-line incidence itself. It does not use hexlib.py, domlocal.c or domcheck.py.

For every point p, its 2-ball is p together with the points on the q+1 lines through p: 1 + q(q+1) = 57 points for
q = 7. The colouring (int32 per point, -1 = uncoloured) is valid for K colours when every 2-ball contains every
colour 0..K-1. Only the POINT side is checked; the line side is not part of this card.

Prints PASS/FAIL with the number of balls missing some colour, and the class sizes.
"""
import sys
import numpy as np


def main():
    hexpath, colpath, K = sys.argv[1], sys.argv[2], int(sys.argv[3])
    data = np.fromfile(hexpath, dtype=np.int32)
    q, N, L = int(data[0]), int(data[1]), int(data[2])
    Q1 = q + 1
    assert L == N, "expected as many lines as points"
    lines = data[3:3 + L * Q1].reshape(L, Q1).astype(np.int64)
    assert lines.min() >= 0 and lines.max() < N, "point id out of range"

    # point -> lines through it (each point must lie on exactly q+1 lines, each line has q+1 distinct points)
    pts = lines.ravel()
    lns = np.repeat(np.arange(L, dtype=np.int64), Q1)
    order = np.argsort(pts, kind="stable")
    cnts = np.bincount(pts, minlength=N)
    assert (cnts == Q1).all(), "every point must lie on q+1 lines"
    PL = lns[order].reshape(N, Q1)
    for l in range(L):
        assert len(set(lines[l].tolist())) == Q1, "a line has repeated points"

    # the 2-ball of every point: the points of its q+1 lines (q+1 lines x q+1 points, p repeated q+1 times)
    ball_idx = lines[PL].reshape(N, Q1 * Q1)           # (N, 64) point ids
    s = np.sort(ball_idx, axis=1)
    distinct = 1 + (np.diff(s, axis=1) != 0).sum(axis=1)
    assert (distinct == 1 + q * Q1).all(), "2-ball size is not 1 + q(q+1)"
    assert (ball_idx == np.arange(N)[:, None]).any(axis=1).all(), "a point is not in its own 2-ball"

    col = np.fromfile(colpath, dtype=np.int32).astype(np.int64)
    assert col.shape[0] == N, f"colour file has {col.shape[0]} entries, expected {N}"
    assert col.max() < K and col.min() >= -1, "colour outside range -1..K-1"

    CB = col[ball_idx]                                  # (N, 64) colours seen in each ball (-1 = uncoloured)
    present = np.zeros((N, K), dtype=bool)
    for k in range(K):
        present[:, k] = (CB == k).any(axis=1)
    miss = ~present
    balls_missing = int(miss.any(axis=1).sum())
    sizes = np.bincount(col[col >= 0], minlength=K)[:K]
    coloured = int((col >= 0).sum())
    status = "PASS" if balls_missing == 0 else "FAIL"
    print(f"{status} points-only k={K} q={q} N={N}: balls missing a colour {balls_missing} / {N}; "
          f"missing colour-slots {int(miss.sum())}; coloured points {coloured}; "
          f"class sizes min {int(sizes.min())} max {int(sizes.max())}")
    if balls_missing == 0:
        print(f"VERIFIED k={K}")
    return 0 if balls_missing == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
