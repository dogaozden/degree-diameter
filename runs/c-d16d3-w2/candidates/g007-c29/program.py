import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bitset-ball annealing that grows a valid bipartite graph.
#
# Start from a valid graph with N vertices. Add one isolated vertex at a time
# and anneal edge moves (add, delete, endpoint rewire, degree-preserving double
# swap) on the N+1 vertex graph. The cost is the number of vertex pairs at
# distance > D, computed exactly with 64-bit bitset balls. Every move keeps
# bipartiteness (edges only join opposite colours) and the degree cap. When the
# cost reaches zero, the graph is saved and another vertex is added.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXW (MAXN / 64)
#define MAXDEG 64
#define MAXE 40000

static int N, d, D, W;
static int col[MAXN];
static int deg[MAXN];
static int nb[MAXN][MAXDEG];
static uint64_t bufA[MAXN][MAXW], bufB[MAXN][MAXW];
static uint64_t (*R)[MAXW] = bufA;
static uint64_t (*Q)[MAXW] = bufB;

static int bestN = 0, bestM = 0, bestValid = 0;
static int bestE[MAXE][2];

static uint64_t rng_state = 88172645463325252ULL;

static uint64_t rnd64(void) {
  rng_state ^= rng_state << 13;
  rng_state ^= rng_state >> 7;
  rng_state ^= rng_state << 17;
  return rng_state;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int popc64(uint64_t x) {
  x = x - ((x >> 1) & 0x5555555555555555ULL);
  x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
  x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
  return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
  for (int i = 0; i < deg[a]; i++)
    if (nb[a][i] == b) return 1;
  return 0;
}

static void raw_add(int a, int b) { nb[a][deg[a]++] = b; }

static void raw_del(int a, int b) {
  for (int i = 0; i < deg[a]; i++) {
    if (nb[a][i] == b) {
      nb[a][i] = nb[a][--deg[a]];
      return;
    }
  }
}

typedef struct {
  int nrem, nadd;
  int rem[2][2];
  int add[2][2];
} Move;

static void m_add(Move *m, int a, int b) {
  raw_add(a, b);
  raw_add(b, a);
  m->add[m->nadd][0] = a;
  m->add[m->nadd][1] = b;
  m->nadd++;
}

static void m_del(Move *m, int a, int b) {
  raw_del(a, b);
  raw_del(b, a);
  m->rem[m->nrem][0] = a;
  m->rem[m->nrem][1] = b;
  m->nrem++;
}

static void m_undo(Move *m) {
  for (int i = 0; i < m->nadd; i++) {
    raw_del(m->add[i][0], m->add[i][1]);
    raw_del(m->add[i][1], m->add[i][0]);
  }
  for (int i = 0; i < m->nrem; i++) {
    raw_add(m->rem[i][0], m->rem[i][1]);
    raw_add(m->rem[i][1], m->rem[i][0]);
  }
  m->nadd = 0;
  m->nrem = 0;
}

static long long cost_eval(void) {
  W = (N + 63) / 64;
  for (int v = 0; v < N; v++) {
    for (int w = 0; w < W; w++) R[v][w] = 0;
    R[v][v >> 6] |= 1ULL << (v & 63);
  }
  for (int r = 0; r < D; r++) {
    for (int v = 0; v < N; v++) {
      for (int w = 0; w < W; w++) Q[v][w] = R[v][w];
      for (int i = 0; i < deg[v]; i++) {
        int u = nb[v][i];
        for (int w = 0; w < W; w++) Q[v][w] |= R[u][w];
      }
    }
    uint64_t (*t)[MAXW] = R;
    R = Q;
    Q = t;
  }
  long long miss = 0;
  for (int v = 0; v < N; v++) {
    int c = 0;
    for (int w = 0; w < W; w++) c += popc64(R[v][w]);
    miss += N - c;
  }
  return miss / 2;
}

static int move_add(Move *m) {
  if (N < 2) return 0;
  for (int tries = 0; tries < 60; tries++) {
    int a = rndint(N);
    if (deg[a] >= d) continue;
    int b = rndint(N);
    if (col[b] == col[a] || deg[b] >= d || has_edge(a, b)) continue;
    m_add(m, a, b);
    return 1;
  }
  return 0;
}

static int move_del(Move *m) {
  if (N < 2) return 0;
  for (int tries = 0; tries < 60; tries++) {
    int a = rndint(N);
    if (deg[a] == 0) continue;
    int b = nb[a][rndint(deg[a])];
    m_del(m, a, b);
    return 1;
  }
  return 0;
}

static int move_rewire(Move *m) {
  if (N < 2) return 0;
  for (int tries = 0; tries < 60; tries++) {
    int a = rndint(N);
    if (deg[a] == 0) continue;
    int b = nb[a][rndint(deg[a])];
    int e = rndint(N);
    if (e == a || e == b || col[e] != col[b] || deg[e] >= d || has_edge(a, e)) continue;
    m_del(m, a, b);
    m_add(m, a, e);
    return 1;
  }
  return 0;
}

static int move_swap(Move *m) {
  if (N < 2) return 0;
  for (int tries = 0; tries < 60; tries++) {
    int a = rndint(N);
    if (deg[a] == 0) continue;
    int b = nb[a][rndint(deg[a])];
    int c = rndint(N);
    if (c == a || col[c] != col[a] || deg[c] == 0) continue;
    int e = nb[c][rndint(deg[c])];
    if (e == b) continue;
    if (has_edge(a, e) || has_edge(c, b)) continue;
    m_del(m, a, b);
    m_del(m, c, e);
    m_add(m, a, e);
    m_add(m, c, b);
    return 1;
  }
  return 0;
}

static void color_graph(void) {
  static int stk[MAXN];
  for (int v = 0; v < N; v++) col[v] = -1;
  for (int s = 0; s < N; s++) {
    if (col[s] >= 0) continue;
    col[s] = 0;
    int sp = 0;
    stk[sp++] = s;
    while (sp > 0) {
      int u = stk[--sp];
      for (int i = 0; i < deg[u]; i++) {
        int v = nb[u][i];
        if (col[v] < 0) {
          col[v] = 1 - col[u];
          stk[sp++] = v;
        }
      }
    }
  }
}

static void snapshot(void) {
  bestN = N;
  bestM = 0;
  for (int v = 0; v < N; v++) {
    for (int i = 0; i < deg[v]; i++) {
      int u = nb[v][i];
      if (u > v && bestM < MAXE) {
        bestE[bestM][0] = v;
        bestE[bestM][1] = u;
        bestM++;
      }
    }
  }
}

static void add_vertex(void) {
  col[N] = (int)(rnd64() & 1ULL);
  deg[N] = 0;
  N++;
}

int main(int argc, char **argv) {
  if (argc < 5) return 1;
  d = atoi(argv[1]);
  D = atoi(argv[2]);
  unsigned long long seed = strtoull(argv[3], NULL, 10);
  double limit = atof(argv[4]);
  if (d < 1) d = 1;
  if (d > MAXDEG - 2) d = MAXDEG - 2;

  rng_state ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
  if (rng_state == 0) rng_state = 1;
  for (int i = 0; i < 16; i++) rnd64();

  int n = 0, m = 0;
  if (scanf("%d %d", &n, &m) != 2) {
    n = 0;
    m = 0;
  }
  if (n < 0 || n > MAXN - 2) n = 0;
  N = n;
  for (int i = 0; i < m; i++) {
    int u, v;
    if (scanf("%d %d", &u, &v) != 2) break;
    if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
    if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
    raw_add(u, v);
    raw_add(v, u);
  }
  color_graph();

  clock_t t0 = clock();
  long long cost = cost_eval();
  snapshot();
  bestValid = (cost == 0);

  long long iter = 0;
  for (;;) {
    if (cost == 0) {
      if (!bestValid || N > bestN) {
        snapshot();
        bestValid = 1;
      }
      if (N >= MAXN - 1) break;
      add_vertex();
      cost = cost_eval();
      continue;
    }
    if ((iter & 255) == 0) {
      double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
      if (el > limit) break;
    }
    iter++;

    long long ph = iter % 20000;
    double T = 1.2 * (1.0 - (double)ph / 20000.0) + 0.05;

    Move mv;
    mv.nadd = 0;
    mv.nrem = 0;
    double r = rnd01();
    int ok;
    if (r < 0.35) ok = move_add(&mv);
    else if (r < 0.70) ok = move_swap(&mv);
    else if (r < 0.90) ok = move_rewire(&mv);
    else ok = move_del(&mv);
    if (!ok) continue;

    long long c2 = cost_eval();
    long long delta = c2 - cost;
    if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
      cost = c2;
    } else {
      m_undo(&mv);
    }
  }

  printf("%d %d\n", bestN, bestM);
  for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[i][0], bestE[i][1]);
  return 0;
}
'''


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, S, line_points):
    """Build the extended graph: old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, S, line_points)
        out.append((n_c, e_c))
    return out


# ----------------------------------------------------------------------------
# Spare-capacity fill (diameter 3), exact validity check on every addition.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """2-colouring of a bipartite graph given by adjacency lists."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _fill(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods cover the opposite side; return (n, edges)."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 400:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        deg = [len(a) for a in adj]
        col = _bipartition(n, adj)
        c = rng.randrange(2)
        uncovered = {v for v in range(n) if col[v] == 1 - c}
        cand = [v for v in range(n) if col[v] == c and deg[v] < d]
        chosen = []
        chosen_set = set()
        while uncovered and len(chosen) < d:
            best_v = None
            best_key = None
            for v in cand:
                if v in chosen_set:
                    continue
                g = 0
                for u in adj[v]:
                    if u in uncovered:
                        g += 1
                if g == 0:
                    continue
                key = (g, rng.random())
                if best_key is None or key > best_key:
                    best_key = key
                    best_v = v
            if best_v is None:
                break
            chosen.append(best_v)
            chosen_set.add(best_v)
            for u in adj[best_v]:
                uncovered.discard(u)
        if uncovered:
            fails += 1
            continue
        new_edges = edges + [(v, n) for v in chosen]
        if lib.is_valid(n + 1, new_edges, d, D):
            edges = new_edges
            n += 1
            fails = 0
        else:
            fails += 1
    return n, edges


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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
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
# Glue: run the C growth engine from the best graph found so far.
# ----------------------------------------------------------------------------

def _c_grow(d, D, graph, seed, budget):
    """Run the C engine from `graph` for about `budget` CPU seconds; return (n, edges)."""
    text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                     stdin_graph=graph, timeout=budget + 4.0)
    return lib.parse_graph_text(text)


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

    # Arc-extended projective plane graphs (diameter 3).
    if D >= 3:
        cands = _arc_extensions(d, start + 0.15 * time_limit, random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    # Greedy spare-degree fill (diameter 3), kept short; the C engine does the heavy work.
    if D >= 3 and best_n > 2:
        n_f, e_f = _fill(best_n, best[1], d, D, start + 0.25 * time_limit,
                         random.Random(seed * 104729 + d))
        consider(n_f, e_f)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Short voltage-lift search for D >= 4.
    if D >= 4:
        ks = [1, 2, 2, 3, 4]
        vdeadline = start + 0.3 * time_limit
        while time.monotonic() < vdeadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, vdeadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # Main search: C engine grows the best graph by one vertex at a time.
    elapsed = time.monotonic() - start
    budget = 0.85 * time_limit - elapsed - 2.0
    if budget >= 1.0 and best_n >= 2 and d <= 60 and best_n < lib.moore_bound(d, D):
        try:
            n_c, e_c = _c_grow(d, D, best, seed, budget)
            consider(n_c, e_c)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
