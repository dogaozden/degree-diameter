import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3), with deletions.
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Optionally delete a matching R of point-line incidences. A deleted incidence
# frees one slot on its point and one on its line. Every old vertex then has
# capacity cap = d - (q+1) + (number of its deleted incidences).
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Each line L may hold at most capL[L] SA points.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Each point P may lie on at most capP[P] SB lines.
#
# Every candidate is checked with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

_LS_ITERS = 12000


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, caps, nbr):
    """True if every target t is hit by <= caps[t] elements of S, where element x hits nbr[x]."""
    m = len(caps)
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return all(load[t] <= caps[t] for t in range(m))


def _greedy_side(m, caps, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target t is hit by <= caps[t] chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < caps[t] for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, caps, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the capacitated set problem."""
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= caps[t]:
                if not cur:
                    ok = False
                    break
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _best_side(m, caps, nbr, rng, deadline, seeds):
    """Best capacitated set found by greedy, supplied seeds, then local search."""
    cands = [_greedy_side(m, caps, nbr, rng, 12, deadline)]
    for S in seeds:
        if _loads_ok(S, caps, nbr):
            cands.append(list(S))
    start = max(cands, key=len)
    return _local_search(m, caps, nbr, start, rng, deadline, _LS_ITERS)


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _pick_deletions(edges, m, r, rng):
    """Random matching of up to r PG incidences, as (point, line) pairs with line index 0..m-1."""
    inc = [(u, v - m) for u, v in edges]
    rng.shuffle(inc)
    usedP, usedL, R = set(), set(), []
    for P, L in inc:
        if len(R) >= r:
            break
        if P in usedP or L in usedL:
            continue
        usedP.add(P)
        usedL.add(L)
        R.append((P, L))
    return R


def _arc_graph(m, edges, R, point_lines, line_points, SA, SB):
    """PG incidence minus deleted matching R, plus one new A-vertex per SA point and one B-vertex per SB line."""
    Rset = set(R)
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = [(u, v) for u, v in edges if (u, v - m) not in Rset]
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d, largest first."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * (s + 1) * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        q_deadline = now + (deadline - now) / (len(qs) - idx)
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        conic = _conic_set(q, index, lib.GF(q)) if s >= 0 else []
        rs = [0, max(1, m // 12), max(1, m // 6), max(1, m // 4)]
        trial = 0
        while time.monotonic() < q_deadline:
            r = rs[trial] if trial < len(rs) else rng.choice(rs)
            trial += 1
            R = _pick_deletions(edges, m, r, rng) if r > 0 else []
            delP = [0] * m
            delL = [0] * m
            for P, L in R:
                delP[P] += 1
                delL[L] += 1
            capL = [s + delL[L] for L in range(m)]
            capP = [s + delP[P] for P in range(m)]
            seeds = [conic] if not R else []
            SA = _best_side(m, capL, point_lines, rng, q_deadline, seeds)
            SB = _best_side(m, capP, line_points, rng, q_deadline, seeds)
            if not (_loads_ok(SA, capL, point_lines) and _loads_ok(SB, capP, line_points)):
                continue
            out.append(_arc_graph(m, edges, R, point_lines, line_points, SA, SB))
            if trial > 40:
                break
    out.sort(key=lambda t: -t[0])
    return out[:30]


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Simulated annealing over bi-Cayley voltage lifts (for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# C engine: grow-and-repair annealing at fixed bipartition.
#
# Keeps a valid bipartite graph with max degree d and diameter <= D. When it is
# valid it saves the graph and adds one isolated vertex. The penalty is the
# number of vertex pairs at distance > D. It is computed with bitset ball
# expansion: each vertex's radius-r ball is an N-bit row, expanded by OR-ing
# neighbour rows, which is much faster than per-source BFS.
# Moves: degree-preserving bipartite 2-switches, edge additions between a
# deficient pair, and "steals" that attach a deficient vertex to a full vertex
# by rerouting one of the latter's edges.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1200
#define MAXD 40
#define MAXE 40000
#define WMAX ((MAXN + 63) / 64)

static int d, D, N, M;
static int col[MAXN], deg[MAXN];
static int adj[MAXN][MAXD];
static int EA[MAXE], EB[MAXE];
static int RU[MAXE], RV[MAXE];
static int SAv[MAXE], SBv[MAXE];
static int bestN = 0, bestM = 0, haveBest = 0;
static uint64_t rs;
static uint64_t RA[MAXN][WMAX], RB[MAXN][WMAX];
static int candbuf[MAXN];
static int qbuf[MAXN];

static uint64_t rnd64(void) {
  rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
  return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc(uint64_t x) {
  x = x - ((x >> 1) & 0x5555555555555555ULL);
  x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
  x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
  return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
  for (int k = 0; k < deg[u]; k++) if (adj[u][k] == v) return 1;
  return 0;
}
static void adj_remove(int u, int v) {
  for (int k = 0; k < deg[u]; k++)
    if (adj[u][k] == v) { adj[u][k] = adj[u][deg[u] - 1]; deg[u]--; return; }
}
static void adj_add(int u, int v) { adj[u][deg[u]++] = v; }

/* Replace edge e (EA = colour-0 end, EB = colour-1 end) by (na, nb). */
static void replace_edge(int e, int na, int nb) {
  adj_remove(EA[e], EB[e]);
  adj_remove(EB[e], EA[e]);
  EA[e] = na; EB[e] = nb;
  adj_add(na, nb);
  adj_add(nb, na);
}
/* Append edge (a colour-0, b colour-1). */
static void add_edge(int a, int b) {
  EA[M] = a; EB[M] = b; M++;
  adj_add(a, b); adj_add(b, a);
}
/* Remove the most recently added edge. */
static void remove_last_edge(void) {
  M--;
  adj_remove(EA[M], EB[M]);
  adj_remove(EB[M], EA[M]);
}

/* Penalty = number of unordered pairs at distance > D (bitset ball expansion). */
static long long eval_cost(void) {
  int Wn = (N + 63) >> 6;
  uint64_t (*cur)[WMAX] = RA;
  uint64_t (*nx)[WMAX] = RB;
  for (int v = 0; v < N; v++) {
    for (int w = 0; w < Wn; w++) cur[v][w] = 0;
    cur[v][v >> 6] |= 1ULL << (v & 63);
  }
  for (int r = 0; r < D; r++) {
    for (int v = 0; v < N; v++) {
      for (int w = 0; w < Wn; w++) nx[v][w] = cur[v][w];
      for (int k = 0; k < deg[v]; k++) {
        int u = adj[v][k];
        for (int w = 0; w < Wn; w++) nx[v][w] |= cur[u][w];
      }
    }
    uint64_t (*t)[WMAX] = cur;
    cur = nx;
    nx = t;
  }
  long long cnt = 0;
  for (int v = 0; v < N; v++)
    for (int w = 0; w < Wn; w++) cnt += popc(cur[v][w]);
  return ((long long)N * N - cnt) / 2;
}

static int color_graph(void) {
  for (int v = 0; v < N; v++) col[v] = -1;
  for (int s = 0; s < N; s++) {
    if (col[s] != -1) continue;
    col[s] = 0;
    int h = 0, t = 0;
    qbuf[t++] = s;
    while (h < t) {
      int u = qbuf[h++];
      for (int k = 0; k < deg[u]; k++) {
        int w = adj[u][k];
        if (col[w] == -1) { col[w] = 1 - col[u]; qbuf[t++] = w; }
        else if (col[w] == col[u]) return 0;
      }
    }
  }
  return 1;
}

static void save_best(void) {
  bestN = N; bestM = M;
  for (int i = 0; i < M; i++) { SAv[i] = EA[i]; SBv[i] = EB[i]; }
  haveBest = 1;
}

static void grow(void) {
  col[N] = (int)(rnd64() & 1ULL);
  deg[N] = 0;
  N++;
}

static int accept_move(long long delta, double T) {
  if (delta <= 0) return 1;
  return rnd01() < exp(-(double)delta / T);
}

int main(int argc, char **argv) {
  if (argc < 5) return 1;
  d = atoi(argv[1]);
  D = atoi(argv[2]);
  uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
  double tl = atof(argv[4]);
  rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
  if (rs == 0) rs = 1;

  if (d < 1 || d > MAXD - 2 || D < 1) { printf("0 0\n"); return 0; }
  int n, m;
  if (scanf("%d %d", &n, &m) != 2) { printf("0 0\n"); return 0; }
  if (n < 1 || n > MAXN - 2 || m < 0 || m > MAXE - 2) { printf("0 0\n"); return 0; }

  N = n; M = 0;
  memset(deg, 0, sizeof(deg));
  int ok = 1;
  for (int i = 0; i < m; i++) {
    int u, v;
    if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
    if (u < 0 || u >= n || v < 0 || v >= n || u == v) { ok = 0; break; }
    if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) { ok = 0; break; }
    adj_add(u, v); adj_add(v, u);
    RU[i] = u; RV[i] = v;
  }
  if (!ok || !color_graph()) { printf("0 0\n"); return 0; }
  M = m;
  for (int i = 0; i < m; i++) {
    if (col[RU[i]] == 0) { EA[i] = RU[i]; EB[i] = RV[i]; }
    else { EA[i] = RV[i]; EB[i] = RU[i]; }
  }

  long long cost = eval_cost();
  const double T0 = 2.0, Tmin = 0.12;
  double T = T0;
  long long newc = 0;
  clock_t t0 = clock();

  while (1) {
    if ((double)(clock() - t0) / CLOCKS_PER_SEC > tl) break;
    if (cost == 0) {
      save_best();
      if (N >= MAXN - 2) break;
      grow();
      cost = eval_cost();
      T = T0;
      continue;
    }
    T *= 0.9997;
    if (T < Tmin) T = T0;

    if (rnd01() < 0.55) {
      /* degree-preserving bipartite 2-switch */
      if (M < 2) continue;
      int i = rndint(M), j = rndint(M);
      if (i == j) continue;
      int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
      if (a1 == a2 || b1 == b2) continue;
      if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
      replace_edge(i, a1, b2);
      replace_edge(j, a2, b1);
      newc = eval_cost();
      if (accept_move(newc - cost, T)) cost = newc;
      else { replace_edge(j, a2, b2); replace_edge(i, a1, b1); }
    } else {
      /* attach a deficient vertex u to a random opposite-colour vertex v */
      int nc = 0;
      for (int v = 0; v < N; v++) if (deg[v] < d) candbuf[nc++] = v;
      if (nc == 0) continue;
      int u = candbuf[rndint(nc)];
      int v = rndint(N);
      if (v == u || col[v] == col[u] || has_edge(u, v)) continue;
      int a = (col[u] == 0) ? u : v;
      int b = (col[u] == 0) ? v : u;
      if (deg[v] < d) {
        if (M >= MAXE - 2) continue;
        add_edge(a, b);
        newc = eval_cost();
        if (accept_move(newc - cost, T)) cost = newc;
        else remove_last_edge();
      } else {
        if (deg[v] == 0) continue;
        int w = adj[v][rndint(deg[v])];
        int e = -1;
        for (int k = 0; k < M; k++)
          if ((EA[k] == v && EB[k] == w) || (EA[k] == w && EB[k] == v)) { e = k; break; }
        if (e < 0) continue;
        int oa = EA[e], ob = EB[e];
        replace_edge(e, a, b);
        newc = eval_cost();
        if (accept_move(newc - cost, T)) cost = newc;
        else replace_edge(e, oa, ob);
      }
    }
  }

  if (!haveBest) { printf("0 0\n"); return 0; }
  printf("%d %d\n", bestN, bestM);
  for (int i = 0; i < bestM; i++) printf("%d %d\n", SAv[i], SBv[i]);
  return 0;
}
"""


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Construction phase budget: about 30% of the time limit.
    arc_deadline = start + 0.3 * time_limit

    if D >= 3:
        cands = _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d))
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)
                if best_n >= n_c:
                    break

    if D >= 4 and time.monotonic() < arc_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if D >= 4:
        ks = [1, 2, 2, 3, 4]
        while time.monotonic() < arc_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, arc_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Grow-and-repair C search from the best construction found so far.
    # Skip when the start already meets the Moore bound (cannot be beaten).
    if best_n < lib.moore_bound(d, D):
        elapsed = time.monotonic() - start
        budget = (time_limit - elapsed) * 0.85 - 2.0
        if budget >= 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                 stdin_graph=best, timeout=budget + 15.0)
                n2, e2 = lib.parse_graph_text(text)
                if n2 > best_n and lib.is_valid(n2, e2, d, D):
                    best = (n2, e2)
                    best_n = n2
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
