"""check_pts.py: independent check of a POINT colouring for the D = 9 ball lift, straight from the raw hexagon file.

Reads hex_q5.bin directly (int32 q, N, L; then L*(q+1) int32 point ids per line), builds the collinearity
(points on a common line) from the lines only, and for every point p takes its 2-ball = p plus the points on the
q+1 lines through p (q(q+1)+1 = 31 points). Colour file: int32 per point, -1 = free.
k = number of colours c (0..max) that occur in EVERY 2-ball, counting only colours used. Also checks that
every ball has at least one point of each colour and reports the class sizes.
Usage: python3 check_pts.py HEXBIN COLOURFILE
"""
import sys
import numpy as np


def main():
    hexbin, colfile = sys.argv[1], sys.argv[2]
    raw = np.fromfile(hexbin, dtype=np.int32)
    q, N, L = int(raw[0]), int(raw[1]), int(raw[2])
    lines = raw[3:3 + L * (q + 1)].reshape(L, q + 1).astype(np.int64)
    assert lines.min() >= 0 and lines.max() < N, 'point ids out of range'
    assert N == (q ** 6 - 1) // (q - 1), f'N={N} is not (q^6-1)/(q-1) for q={q}'
    col = np.fromfile(colfile, dtype=np.int32).astype(np.int64)
    assert col.shape[0] == N, f'colour file has {col.shape[0]} entries, expected {N}'

    # lines through each point
    through = [[] for _ in range(N)]
    for l in range(L):
        for p in lines[l]:
            through[p].append(l)
    assert all(len(t) == q + 1 for t in through), 'every point must lie on q+1 lines'

    colours = sorted(set(col[col >= 0].tolist()))
    good = {c: True for c in colours}
    for p in range(N):
        ball = {p}
        for l in through[p]:
            ball.update(lines[l].tolist())
        assert len(ball) == q * q + q + 1, f'ball of point {p} has size {len(ball)}'
        present = set(col[list(ball)].tolist())
        for c in colours:
            if good[c] and c not in present:
                good[c] = False
    k = sum(good.values())
    sizes = {c: int((col == c).sum()) for c in colours}
    print(f'q={q} N={N} colours used={len(colours)} good (in every 2-ball)={k} '
          f'min class={min(sizes.values())} max class={max(sizes.values())} free={int((col < 0).sum())}')
    print(f'SCORE k={k}' if k == len(colours) else f'NOT all used colours good: k={k} of {len(colours)}')


if __name__ == '__main__':
    main()
