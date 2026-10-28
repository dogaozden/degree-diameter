#!/usr/bin/env python3
"""Independent certifier for card e03 (polylev r2): checks a file of lines of Q(6,13).

File format (written by greedy.c): int32 q, int32 count, then count*(q+1)*7 uint8 normalised coordinates.
Checks, in pure Python (no code shared with the search):
  1. header q (13 for this card) and file size matches count;
  2. every coordinate vector is nonzero, entries in 0..12, first nonzero entry equal to 1 (normalised);
  3. every point lies on Q(6,13): x0x4 + x1x5 + x2x6 - x3^2 = 0 (mod 13);
  4. each line: its 14 points are distinct, have rank 2 over F_13 (so they are exactly the 14 points of a projective
     line), and are pairwise orthogonal for b(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 (so the line is totally singular);
  5. lines are pairwise disjoint (no point on two lines).
Usage: certify.py FILE
"""
import sys
import struct

P = 13  # set from the file header in main(); the card is q = 13


def b(x, y):
    return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % P


def quad(x):
    return (x[0] * x[4] + x[1] * x[5] + x[2] * x[6] - x[3] * x[3]) % P


def rank_mod_p(vectors):
    rows = [list(v) for v in vectors]
    r = 0
    ncols = len(rows[0])
    for c in range(ncols):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][c] % P:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], P - 2, P)
        rows[r] = [(a * inv) % P for a in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] % P:
                f = rows[i][c]
                rows[i] = [(a - f * bb) % P for a, bb in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def main():
    path = sys.argv[1]
    data = open(path, 'rb').read()
    q, count = struct.unpack('<ii', data[:8])
    global P
    assert q in (3, 5, 7, 11, 13), f"q={q}"
    P = q
    pts_per_line = q + 1
    expect = 8 + count * pts_per_line * 7
    assert len(data) == expect, f"size {len(data)} != {expect}"
    body = data[8:]
    seen = {}
    errors = 0
    for li in range(count):
        line_pts = []
        base = li * pts_per_line * 7
        for s in range(pts_per_line):
            v = tuple(body[base + s * 7: base + s * 7 + 7])
            line_pts.append(v)
        # 2. normalisation / range
        for v in line_pts:
            if not any(v) or any(a >= P for a in v):
                errors += 1
                continue
            k = next(i for i, a in enumerate(v) if a)
            if v[k] != 1:
                errors += 1
        # 3. on the quadric
        for v in line_pts:
            if quad(v) != 0:
                errors += 1
        # 4. distinct, rank 2, pairwise orthogonal
        if len(set(line_pts)) != pts_per_line:
            errors += 1
        if rank_mod_p(line_pts) != 2:
            errors += 1
        for i in range(pts_per_line):
            for j in range(i + 1, pts_per_line):
                if b(line_pts[i], line_pts[j]) != 0:
                    errors += 1
        # 5. disjointness
        for v in line_pts:
            if v in seen:
                errors += 1
            else:
                seen[v] = li
    status = "VALID" if errors == 0 else f"INVALID ({errors} errors)"
    print(f"file {path}: q={q} lines={count} points_covered={len(seen)} -> {status}")
    return 0 if errors == 0 else 1


if __name__ == '__main__':
    sys.exit(main())
