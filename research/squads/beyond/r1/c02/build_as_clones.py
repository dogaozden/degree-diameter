"""Corollary A1 (POLISHED.md section 4, Theorem A) for odd prime q.

AS(q) = Payne derivation P(W(q), x), built by research/gq4x/as_gq.py (points (a,b,c) = vector (a,1,b,c);
lines = 'lines' of that module). Elliptic quadrics E1: 2 X0 X1 = X2^2 - eps X3^2 and
E2: 2 eps X0 X1 = X2^2 - eps X3^2 (eps the least non-square mod q). Affinely, E_kappa \\ {x} is the set of
points (a,b,c) with a = kappa*(b^2 - eps*c^2), kappa = 1/2 (E1) and kappa = 1/(2 eps) (E2).
Clones: one per point of E1\\{x} and one per point of E2\\{x} (e = (0,0,0) gets two). A clone is adjacent to the
q+2 lines of AS(q) through its base point. The result is bipartite: (old points + clones) vs lines.

Vertices: old points 0..q^3-1, clones next, lines last. Usage: python3 build_as_clones.py q out.edges
"""
import sys
from pathlib import Path

REPO = Path('/home/user/degree-diameter')
sys.path.insert(0, str(REPO / 'research' / 'gq4x'))
import as_gq  # noqa: E402

q = int(sys.argv[1])
out = sys.argv[2]
F, pts, lines = as_gq.build(q)
P = len(pts)                      # q^3
assert P == q ** 3 and len(lines) == (q + 2) * q * q
idx = {p: i for i, p in enumerate(pts)}

eps = next(e for e in range(2, q) if pow(e, (q - 1) // 2, q) == q - 1)   # least non-square
inv = lambda x: pow(x % q, q - 2, q)
kappas = [inv(2), inv(2 * eps)]    # E1, E2

clone_base = []                   # base point index of each clone
for kap in kappas:
    for (a, b, c) in pts:
        # E_kappa \ {x} is the affine set a = kappa*(b^2 - eps c^2); each point gets one clone
        if a == (kap * (b * b - eps * c * c)) % q:
            clone_base.append(idx[(a, b, c)])
assert len(clone_base) == 2 * q * q, len(clone_base)

# sanity: each base point lies on the quadric equations 2 kappa^-1 ... checked via the affine form above
N_old = P
N_cl = len(clone_base)
line_off = N_old + N_cl
n = line_off + len(lines)
edges = []
on_line = [[] for _ in range(P)]
for j, L in enumerate(lines):
    for p in L:
        edges.append((p, line_off + j))
        on_line[p].append(j)
for k, p in enumerate(clone_base):
    assert len(on_line[p]) == q + 2
    for j in on_line[p]:
        edges.append((N_old + k, line_off + j))
with open(out, 'w') as f:
    f.write(f'{n}\n')
    f.write(''.join(f'{u} {v}\n' for u, v in edges))
deg = [0] * n
for u, v in edges:
    deg[u] += 1; deg[v] += 1
print(f'q={q} eps={eps} kappas={kappas} points={P} clones={N_cl} lines={len(lines)} n={n} edges={len(edges)} '
      f'degrees min={min(deg)} max={max(deg)}')
