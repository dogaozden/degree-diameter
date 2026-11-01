#!/usr/bin/env python3
"""Card c6 of squad lean-cyc-r1: independent check of lean/BipartiteDD/Haar/CycLift/N497042.lean.

Claimed: the (4,14) Haar graph of Z_2731 x| Z_91 (R = 2400), 497042 vertices, written as a
Z_2731-lift of a 182-vertex base graph. Checks follow research/squads/lean-cyc-r1/SPEC.md:
  1. parse outA from the Lean text; build the lift; no loops; every vertex has exactly 4 neighbours
  2. Haar numbering: map every edge of the edge file by the claimed map; mapped set == lift edge set;
     the map is a bijection on vertices
  3. bipartite: explicit 2-colouring verified on every edge (edge-file graph and lift)
  4. diameter: BFS from vertex 0 and vertex N of the edge-file graph; max must be exactly 14;
     BFS from 50 random other vertices all <= 14
Nothing from gen_cyclift.py / gen_cychaar.py is used.
"""
import gzip
import json
import os
import random
import re
import resource
import time

import numpy as np

LEAN = '/home/user/degree-diameter/lean/BipartiteDD/Haar/CycLift/N497042.lean'
EDGES = ('/home/user/degree-diameter/research/frontier/beyond/graphs/'
         'd4D14_n497042_meta2731_91_2400.edges.gz')
HERE = os.path.dirname(os.path.abspath(__file__))

N = 497042        # vertices
M = 2731          # lift modulus
K = 91            # Haar second coordinate range (side size of base = K per side)
R = 2400          # Haar multiplier
B = 182           # base vertices = 2K
DEG = 4
DIAM = 14
HALF = M * K      # 248521 = Haar N; side B starts here in the edge file

T0 = time.time()
fails = []
lines = []


def check(name, ok, info=''):
    ok = bool(ok)
    line = f'[{"PASS" if ok else "FAIL"}] {name}' + (f'  ({info})' if info else '')
    print(line, flush=True)
    lines.append(line)
    if not ok:
        fails.append(name)


# ---------------------------------------------------------------- 0. Lean text
text = open(LEAN, encoding='utf-8').read()
def_at = text.index('def outA497042')
end_at = text.index('/-- Side A')
block = text[def_at:end_at]
rows = []
for rt in re.findall(r'\[([^\[\]]*)\]', block):
    rows.append([(int(a), int(b)) for a, b in re.findall(r'\(\s*(\d+)\s*,\s*(\d+)\s*\)', rt)])

lift_call = re.search(r'G497042 : SimpleGraph \(Fin (\d+)\) := liftGraph (\d+) (\d+) outA(\d+)', text)
thm = re.search(r'theorem G497042_isBipartiteDegDiam : IsBipartiteDegDiam G497042 (\d+) (\d+)', text)
p_b = re.search(r'isBipartiteDegDiam_of_srcs \(b := (\d+)\)', text)
p_mu = re.search(r"\(μ := (\d+)\) \(μ' := (\d+)\) \(K := (\d+)\)", text)
p_sides = re.search(r'side497042 \[0, 91\] rfl', text)

check('lean: theorem statement is IsBipartiteDegDiam G497042 4 14',
      thm and int(thm.group(1)) == DEG and int(thm.group(2)) == DIAM)
check('lean: liftGraph n m outA with n = 497042, m = 2731, table outA497042',
      lift_call and int(lift_call.group(1)) == N and int(lift_call.group(2)) == N
      and int(lift_call.group(3)) == M and int(lift_call.group(4)) == N)
check('lean: isBipartiteDegDiam_of_srcs params b = 182, mu = 33, mu\' = 2400, K = 91',
      p_b and int(p_b.group(1)) == B and p_mu
      and (int(p_mu.group(1)), int(p_mu.group(2)), int(p_mu.group(3))) == (33, R, K)
      and p_sides is not None)
check('lean: outA has b = 182 rows, each with 4 arcs',
      len(rows) == B and all(len(r) == DEG for r in rows), f'rows={len(rows)}')
check('lean: b*m = n', B * M == N, f'{B}*{M}={B * M}')
check('lean: voltages u < b and beta < m',
      all(u < B and be < M for r in rows for (u, be) in r))

# ---------------------------------------------------------------- 1. the lift
xs = np.arange(M, dtype=np.int64)
src_parts, dst_parts = [], []
for w in range(B):
    for u, beta in rows[w]:
        src_parts.append(w * M + xs)                       # vertex v = w*m + x
        dst_parts.append((u * M + (xs + beta) % M) % N)     # (u*m + (x+beta)%m) % n
src = np.concatenate(src_parts)
dst = np.concatenate(dst_parts)
arc_loops = int((src == dst).sum())
check('lift: no loops among the arcs', arc_loops == 0, f'loops={arc_loops}')

keep = src != dst
lo = np.minimum(src, dst)[keep]
hi = np.maximum(src, dst)[keep]
lift_codes = np.unique(lo * N + hi)          # symmetric closure, simple, as a set of edges
lift_lo = lift_codes // N
lift_hi = lift_codes % N
lift_deg = np.bincount(lift_lo, minlength=N) + np.bincount(lift_hi, minlength=N)
directed_unique = len(np.unique(src * N + dst))
check('lift: 497042 vertices, every vertex has exactly 4 distinct neighbours',
      (lift_deg == DEG).all() and N == 497042,
      f'min deg={int(lift_deg.min())} max deg={int(lift_deg.max())} undirected edges={len(lift_codes)}')
check('lift: arc set is symmetric (2*|E| == number of distinct directed arcs)',
      2 * len(lift_codes) == directed_unique, f'{directed_unique} directed arcs')

# ---------------------------------------------------------------- 1b. the edge file
with gzip.open(EDGES, 'rt') as f:
    toks = f.read().split()
n_file = int(toks[0])
E = np.array(list(map(int, toks[1:])), dtype=np.int64).reshape(-1, 2)
del toks
check('file: header n = 497042 and 994084 edge lines',
      n_file == N and E.shape[0] == N * DEG // 2, f'n={n_file} edges={E.shape[0]}')
check('file: all endpoints in [0, n)', E.min() >= 0 and E.max() < N)
file_loops = int((E[:, 0] == E[:, 1]).sum())
f_lo = np.minimum(E[:, 0], E[:, 1])
f_hi = np.maximum(E[:, 0], E[:, 1])
file_codes = np.unique(f_lo * N + f_hi)
file_deg = np.bincount(f_lo, minlength=N) + np.bincount(f_hi, minlength=N)
check('file: no loops, no repeated edges, every vertex degree exactly 4',
      file_loops == 0 and len(file_codes) == E.shape[0] and (file_deg == DEG).all(),
      f'loops={file_loops} distinct={len(file_codes)}')

# ---------------------------------------------------------------- 2. Haar map
Rinv = pow(R, -1, M)
check('Haar: mu = R^-1 mod m is 33, and R^K = 1 mod m (group is well defined)',
      Rinv == 33 and pow(R, K, M) == 1, f'R^-1={Rinv} R^K mod m={pow(R, K, M)}')
fac = np.array([pow(Rinv, j, M) for j in range(K)], dtype=np.int64)   # R^(-j) mod m


def haar_to_lift(v):
    """Edge-file index v (side A: v < M*K, side B: v >= M*K, v = a*K + j within a side)
    -> lift vertex. Side A: (a, j) -> j*M + (R^-j * a mod M); side B: (a, j) -> (K+j)*M + ..."""
    v = np.asarray(v, dtype=np.int64)
    side = v // HALF
    g = v % HALF
    a = g // K
    j = g % K
    x = (fac[j] * a) % M
    return (K * side + j) * M + x


img = haar_to_lift(np.arange(N, dtype=np.int64))
bij_ok = bool(img.min() >= 0 and img.max() < N and (np.bincount(img, minlength=N) == 1).all())
check('Haar: claimed vertex map is a bijection on 0..n-1', bij_ok)

sides_ok = bool(((img[:HALF] // M) < K).all() and ((img[HALF:] // M) >= K).all()
                and ((img[HALF:] // M) < B).all())
check('Haar: side A goes to base rows < 91, side B to base rows >= 91 (as in side497042)', sides_ok)

ma = img[E[:, 0]]
mb = img[E[:, 1]]
m_loops = int((ma == mb).sum())
m_codes = np.unique(np.minimum(ma, mb) * N + np.maximum(ma, mb))
same_set = (m_loops == 0 and len(m_codes) == len(lift_codes)
            and np.array_equal(m_codes, lift_codes))
check('Haar: mapped edge set == lift edge set (exact equality of the undirected edge sets)',
      same_set, f'mapped distinct={len(m_codes)} lift={len(lift_codes)} loops={m_loops}')


# ---------------------------------------------------------------- 3/4. graph search tools
def csr(a, b, n):
    u = np.concatenate([a, b])
    v = np.concatenate([b, a])
    order = np.argsort(u, kind='stable')
    indices = v[order]
    deg = np.bincount(u, minlength=n).astype(np.int64)
    indptr = np.zeros(n + 1, dtype=np.int64)
    np.cumsum(deg, out=indptr[1:])
    return indptr, indices, deg


def bfs(g, src):
    indptr, indices, deg = g
    n = len(deg)
    dist = np.full(n, -1, dtype=np.int32)
    dist[src] = 0
    frontier = np.array([src], dtype=np.int64)
    d = 0
    while frontier.size:
        c = deg[frontier]
        tot = int(c.sum())
        if tot == 0:
            break
        starts = indptr[frontier]
        offs = np.concatenate(([0], np.cumsum(c)[:-1])).astype(np.int64)
        pos = np.repeat(starts - offs, c) + np.arange(tot, dtype=np.int64)
        nb = indices[pos]
        nb = nb[dist[nb] < 0]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        d += 1
        dist[nb] = d
        frontier = nb
    return dist


def two_colouring_ok(dist, a, b):
    """dist from one source; parity is a candidate 2-colouring; verify it on every edge."""
    if (dist < 0).any():
        return False
    col = dist % 2
    return bool((col[a] != col[b]).all())


# ---------------------------------------------------------------- 3. bipartite
lift_g = csr(lift_lo, lift_hi, N)
file_g = csr(f_lo, f_hi, N)
lift_d0 = bfs(lift_g, 0)
file_d0 = bfs(file_g, 0)
check('bipartite: lift has a 2-colouring (BFS parity, verified on all edges), connected',
      two_colouring_ok(lift_d0, lift_lo, lift_hi))
check('bipartite: edge-file graph has a 2-colouring (BFS parity, verified on all edges), connected',
      two_colouring_ok(file_d0, f_lo, f_hi))
lean_side = (np.arange(N) // M) >= K       # side497042: w >= 91 is side B
check('bipartite: Lean side497042 is a proper 2-colouring of the lift',
      bool((lean_side[lift_lo] != lean_side[lift_hi]).all()))

# ---------------------------------------------------------------- 4. diameter
d_file_0 = file_d0
d_file_N = bfs(file_g, HALF)
conn = bool((d_file_0 >= 0).all() and (d_file_N >= 0).all())
e0 = int(d_file_0.max())
eN = int(d_file_N.max())
check('diameter: edge-file graph connected from vertex 0 and vertex N', conn)
check('diameter: max eccentricity over sources 0 and N is exactly 14', conn and max(e0, eN) == DIAM,
      f'ecc(0)={e0} ecc(N)={eN}')

rng = random.Random(6)
pool = [v for v in range(N) if v not in (0, HALF)]
samples = rng.sample(pool, 50)
sample_eccs = []
sample_ok = True
for s in samples:
    d = bfs(file_g, s)
    if (d < 0).any():
        sample_ok = False
        break
    sample_eccs.append(int(d.max()))
sample_ok = sample_ok and all(e <= DIAM for e in sample_eccs)
check('diameter sanity: 50 random BFS sources all reach every vertex with ecc <= 14', sample_ok,
      f'max sampled ecc={max(sample_eccs) if sample_eccs else None} '
      f'min={min(sample_eccs) if sample_eccs else None}')

# extra: the lift itself, from the images of file vertices 0 and N (an isomorphism, so same ecc)
lift_eN = bfs(lift_g, int(img[HALF]))
check('extra: lift BFS from image of file vertex N gives ecc 14 (matches the edge file)',
      bool((lift_eN >= 0).all()) and int(lift_eN.max()) == DIAM, f'ecc={int(lift_eN.max())}')

# ---------------------------------------------------------------- summary
score = 1 if not fails else 0
maxrss_mb = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0
summary = {
    'card': 'c6', 'graph': 'N497042.lean', 'score': score,
    'failed_checks': fails,
    'ecc_file_0': e0, 'ecc_file_N': eN,
    'sampled_ecc_range': [min(sample_eccs), max(sample_eccs)] if sample_eccs else None,
    'max_rss_mb': round(maxrss_mb, 1), 'seconds': round(time.time() - T0, 1),
}
print(json.dumps(summary), flush=True)
with open(os.path.join(HERE, 'result.json'), 'w') as f:
    json.dump({'summary': summary, 'log': lines}, f, indent=1)
