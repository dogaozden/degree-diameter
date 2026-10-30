#!/usr/bin/env python3
"""Build the full lift edge list from a vl solution file and a group table.
usage: export_lift.py SOL GROUP OUT_EDGES
Lift vertex (v, h) has index v*m + h; base edge (a, b, g) gives (a, h) ~ (b, h*g)."""
import sys

def read_group(path):
    with open(path) as f:
        tok = f.read().split()
    m = int(tok[0])
    mul = [list(map(int, tok[1 + i * m:1 + (i + 1) * m])) for i in range(m)]
    return m, mul

def read_sol(path):
    with open(path) as f:
        lines = [l for l in f if l.strip() and not l.startswith('#')]
    b, E = map(int, lines[0].split())
    side = list(map(int, lines[1].split()))
    edges = [tuple(map(int, l.split()[:3])) for l in lines[2:2 + E]]
    return b, side, edges

def main():
    sol, grp, out = sys.argv[1:4]
    m, mul = read_group(grp)
    b, side, edges = read_sol(sol)
    with open(out, 'w') as f:
        f.write(f"{b * m}\n")
        for (a, c, g) in edges:
            for h in range(m):
                f.write(f"{a * m + h} {c * m + mul[h][g]}\n")
    print(f"wrote {out}: n={b * m} edges={len(edges) * m}")

if __name__ == '__main__':
    main()
