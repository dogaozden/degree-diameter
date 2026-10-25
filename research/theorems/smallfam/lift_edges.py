"""Edge list of a regular voltage lift of a small base over SmallGroup(n, i), for an independent check with apsp.

Base file as for lx.c / lanneal.c: first line k, then one line per edge "w b" (free voltage) or "w b = e" (identity).
Free voltages are element indices in AsSSortedList(SmallGroup(n, i)) (0-based), in the order of the free edges in the
file, exactly as lx / lanneal print them.  Lift: (w, g) ~ (b, a_e * g); vertex (u, g) gets id u * n + g.
Usage: SCRATCH=dir python3 lift_edges.py n i BASE OUT v1 v2 ...   then   verify/apsp OUT 3 D
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from screen import export_table  # noqa: E402


def main():
    n, i, base, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], sys.argv[4]
    volts = [int(x) for x in sys.argv[5:]]
    struct, tab = export_table(n, i)
    with open(tab) as f:
        N, e = map(int, f.readline().split())
        T = [list(map(int, f.readline().split())) for _ in range(N)]
    os.remove(tab)
    lines = [l.split() for l in open(base) if l.strip() and not l.startswith('#')]
    k = int(lines[0][0])
    edges = []
    fi = 0
    for l in lines[1:]:
        w, b = int(l[0]), int(l[1])
        if len(l) > 2:
            a = e
        else:
            a = volts[fi]
            fi += 1
        edges.append((w, b, a))
    assert fi == len(volts), f'{len(volts)} voltages given, base has {fi} free edges'
    with open(out, 'w') as f:
        f.write(f'{k * N}\n')
        for (w, b, a) in edges:
            for g in range(N):
                f.write(f'{w * N + g} {b * N + T[a][g]}\n')
    print(f'# lift of {base} over SmallGroup({n},{i}) = {struct}: {k * N} vertices, {len(edges) * N} edges -> {out}')


if __name__ == '__main__':
    main()
