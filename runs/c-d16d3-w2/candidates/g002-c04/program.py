import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: "ball-cover insertion + degree-preserving annealing".
#
# State: a bipartite graph with max degree d. The cost is the number of
# unordered vertex pairs at distance > D. Moves:
#   - bipartite 2-switch (keeps all degrees),
#   - delete a random edge (creates spare degree),
#   - insert a new vertex on a side whose neighbours' radius-(D-1) balls cover
#     the whole graph (this never increases the cost).
# Simulated annealing accepts or rejects moves on the cost. Whenever the cost is
# zero, the largest valid graph seen is kept. The C program prints it.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXN 1600
#define MAXDEG 40
#define MAXW (MAXN / 64)

typedef struct {
  int n;
  int deg[MAXN];
  int adj[MAXN][MAXDEG];
  int col[MAXN];
} State;

static int n, d, D, W;
static int deg[MAXN], adj[MAXN][MAXDEG], col[MAXN];
static uint64_t ball[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;
static State snap, bst;
static int qb[MAXN], db[MAXN];

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int m) { return (int)(rnd() % (uint64_t)m); }

static int adjacent(int u, int v) {
  for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
  return 0;
}
static void add_edge(int u, int v) { adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
static void drop_half(int u, int v) {
  for (int i = 0; i < deg[u]; i++)
    if (adj[u][i] == v) { adj[u][i] = adj[u][--deg[u]]; return; }
}
static void del_edge(int u, int v) { drop_half(u, v); drop_half(v, u); }

static void save_state(State *s) {
  s->n = n;
  memcpy(s->deg, deg, sizeof deg);
  memcpy(s->adj, adj, sizeof adj);
  memcpy(s->col, col, sizeof col);
}
static void load_state(const State *s) {
  n = s->n;
  W = (n + 63) / 64;
  memcpy(deg, s->deg, sizeof deg);
  memcpy(adj, s->adj, sizeof adj);
  memcpy(col, s->col, sizeof col);
}

/* number of vertices within distance R of s; the reached list is left in qb[0..t) */
static int bfs_count(int s, int R) {
  int h = 0, t = 0;
  for (int i = 0; i < n; i++) db[i] = -1;
  qb[t++] = s;
  db[s] = 0;
  while (h < t) {
    int u = qb[h++];
    if (db[u] >= R) continue;
    for (int i = 0; i < deg[u]; i++) {
      int v = adj[u][i];
      if (db[v] < 0) { db[v] = db[u] + 1; qb[t++] = v; }
    }
  }
  return t;
}

static void compute_balls(int R) {
  W = (n + 63) / 64;
  for (int s = 0; s < n; s++) {
    int t = bfs_count(s, R);
    for (int w = 0; w < W; w++) ball[s][w] = 0;
    for (int i = 0; i < t; i++) {
      int v = qb[i];
      ball[s][v >> 6] |= 1ULL << (v & 63);
    }
  }
}

static long bad_pairs(void) {
  long tot = 0;
  for (int s = 0; s < n; s++) tot += n - bfs_count(s, D);
  return tot / 2;
}

static int used[MAXN], cand[MAXN];

/* add a new vertex of colour c if its neighbours (colour 1-c, spare degree)
   have radius-(D-1) balls covering all vertices; greedy set cover */
static int try_insert(int c) {
  if (n + 2 >= MAXN) return 0;
  compute_balls(D - 1);
  int nc = 0;
  for (int u = 0; u < n; u++) if (col[u] == 1 - c && deg[u] < d) cand[nc++] = u;
  if (nc == 0) return 0;
  for (int i = nc - 1; i > 0; i--) {
    int j = rndi(i + 1);
    int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
  }
  uint64_t cov[MAXW];
  for (int w = 0; w < W; w++) cov[w] = 0;
  memset(used, 0, sizeof(int) * (size_t)n);
  int chosen[MAXDEG], nch = 0, covered = 0;
  while (covered < n && nch < d) {
    int bi = -1, bg = 0;
    for (int i = 0; i < nc; i++) {
      int u = cand[i];
      if (used[u]) continue;
      int g = 0;
      for (int w = 0; w < W; w++) g += __builtin_popcountll(ball[u][w] & ~cov[w]);
      if (g > bg) { bg = g; bi = u; }
    }
    if (bi < 0) break;
    used[bi] = 1;
    chosen[nch++] = bi;
    covered = 0;
    for (int w = 0; w < W; w++) {
      cov[w] |= ball[bi][w];
      covered += __builtin_popcountll(cov[w]);
    }
  }
  if (covered < n) return 0;
  int w = n;
  n++;
  W = (n + 63) / 64;
  deg[w] = 0;
  col[w] = c;
  for (int k = 0; k < nch; k++) add_edge(chosen[k], w);
  return 1;
}

/* add edges between spare-degree vertices of opposite colours (only lowers the cost) */
static void fill_spare(void) {
  static int A[MAXN], B[MAXN];
  int na = 0, nb = 0;
  for (int u = 0; u < n; u++)
    if (deg[u] < d) { if (col[u] == 0) A[na++] = u; else B[nb++] = u; }
  for (int i = na - 1; i > 0; i--) { int j = rndi(i + 1); int t = A[i]; A[i] = A[j]; A[j] = t; }
  for (int i = nb - 1; i > 0; i--) { int j = rndi(i + 1); int t = B[i]; B[i] = B[j]; B[j] = t; }
  for (int i = 0; i < na; i++)
    for (int j = 0; j < nb; j++) {
      int u = A[i], v = B[j];
      if (deg[u] >= d) break;
      if (deg[v] < d && !adjacent(u, v)) add_edge(u, v);
    }
}

/* bipartite 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1); degrees unchanged */
static void two_switch(void) {
  for (int tr = 0; tr < 60; tr++) {
    int a1 = rndi(n), a2 = rndi(n);
    if (col[a1] != 0 || col[a2] != 0 || deg[a1] == 0 || deg[a2] == 0 || a1 == a2) continue;
    int b1 = adj[a1][rndi(deg[a1])];
    int b2 = adj[a2][rndi(deg[a2])];
    if (b1 == b2) continue;
    if (adjacent(a1, b2) || adjacent(a2, b1)) continue;
    del_edge(a1, b1);
    del_edge(a2, b2);
    add_edge(a1, b2);
    add_edge(a2, b1);
    return;
  }
}

static void remove_random(void) {
  for (int tr = 0; tr < 60; tr++) {
    int u = rndi(n);
    if (deg[u] == 0) continue;
    int v = adj[u][rndi(deg[u])];
    del_edge(u, v);
    return;
  }
}

static void grow_once(void) {
  int c = rndi(2);
  if (!try_insert(c)) try_insert(1 - c);
}

int main(int argc, char **argv) {
  if (argc < 5) return 1;
  d = atoi(argv[1]);
  D = atoi(argv[2]);
  rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
  if (rs == 0) rs = 1;
  double tl = atof(argv[4]);

  int N, M;
  if (scanf("%d %d", &N, &M) != 2 || N < 1 || N > MAXN - 4 || M < 0 || d < 1 || d > MAXDEG || D < 2) {
    printf("1 0\n");
    return 0;
  }
  n = N;
  for (int u = 0; u < n; u++) { deg[u] = 0; col[u] = -1; }
  for (int i = 0; i < M; i++) {
    int u, v;
    if (scanf("%d %d", &u, &v) != 2) { printf("1 0\n"); return 0; }
    if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjacent(u, v) || deg[u] >= d || deg[v] >= d) {
      printf("1 0\n");
      return 0;
    }
    add_edge(u, v);
  }
  /* 2-colour, and reject odd cycles */
  for (int s = 0; s < n; s++) {
    if (col[s] >= 0) continue;
    col[s] = 0;
    int h = 0, t = 0;
    qb[t++] = s;
    while (h < t) {
      int u = qb[h++];
      for (int i = 0; i < deg[u]; i++) {
        int v = adj[u][i];
        if (col[v] < 0) { col[v] = 1 - col[u]; qb[t++] = v; }
        else if (col[v] == col[u]) { printf("1 0\n"); return 0; }
      }
    }
  }
  long cost = bad_pairs();
  if (cost != 0) { printf("1 0\n"); return 0; }

  save_state(&bst);
  int best_n = n;
  clock_t t0 = clock();
  long it = 0;
  while (1) {
    double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (el >= tl) break;
    it++;
    save_state(&snap);
    int r = rndi(100);
    if (r < 70) two_switch();
    else if (r < 85) remove_random();
    else grow_once();
    fill_spare();
    long c2 = bad_pairs();
    double T = 0.08 + 0.7 * (1.0 - (double)(it % 3000) / 3000.0);
    int acc = (c2 <= cost);
    if (!acc) {
      double p = exp(-(double)(c2 - cost) / T);
      acc = ((double)(rnd() % 1000000) / 1000000.0) < p;
    }
    if (acc) {
      cost = c2;
      if (cost == 0 && n > best_n) { best_n = n; save_state(&bst); }
    } else {
      load_state(&snap);
    }
  }

  load_state(&bst);
  int E = 0;
  for (int u = 0; u < n; u++)
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] > u) E++;
  printf("%d %d\n", n, E);
  for (int u = 0; u < n; u++)
    for (int i = 0; i < deg[u]; i++)
      if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
  return 0;
}
"""


# ----------------------------------------------------------------------------
# Python: projective-plane arc extensions (D = 3).
# ----------------------------------------------------------------------------

def _loads_ok(S, s, m, pl, lp):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q):
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, pl, lp, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        for L in pl[P]:
            E.append((2 * m + t, m + L))
    for t, j in enumerate(S):
        for Q in lp[j]:
            E.append((Q, 2 * m + k + t))
    return n, E


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        s = d - q - 1
        if s < 1 or not lib.is_prime_power(q) or time.monotonic() > deadline:
            continue
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        pl = [[] for _ in range(m)]
        lp = [[] for _ in range(m)]
        for u, v in edges:
            pl[u].append(v - m)
            lp[v - m].append(u)
        cands = [_greedy_arc(m, s, pl, lp, rng, 40, deadline)]
        if s >= 2:
            cands.append(_conic_set(q))
        S = max(cands, key=len)
        if S and _loads_ok(S, s, m, pl, lp):
            out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Python: cyclic Haar graphs from difference covers (D = 3).
# ----------------------------------------------------------------------------

def _diff_counts(S, m):
    cnt = [0] * m
    k = len(S)
    for i in range(k):
        for j in range(k):
            if i != j:
                cnt[(S[i] - S[j]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)
    return cnt, zeros


def _move(S, cnt, i, y, m, zeros):
    k = len(S)
    old = S[i]
    for j in range(k):
        if j != i:
            t = S[j]
            for a in ((old - t) % m, (t - old) % m):
                cnt[a] -= 1
                if cnt[a] == 0:
                    zeros += 1
    S[i] = y
    for j in range(k):
        if j != i:
            t = S[j]
            for a in ((y - t) % m, (t - y) % m):
                if cnt[a] == 0:
                    zeros -= 1
                cnt[a] += 1
    return zeros


def _cover_search(k, m, deadline, rng):
    if k > m or k * (k - 1) + 1 < m:
        return None
    S = rng.sample(range(m), k)
    cnt, zeros = _diff_counts(S, m)
    T = 0.3
    moves = 0
    while zeros > 0:
        moves += 1
        if moves % 512 == 0 and time.monotonic() > deadline:
            return None
        if moves % 200000 == 0:
            S = rng.sample(range(m), k)
            cnt, zeros = _diff_counts(S, m)
            continue
        i = rng.randrange(k)
        y = rng.randrange(m)
        if y in S:
            continue
        old = S[i]
        z = _move(S, cnt, i, y, m, zeros)
        delta = z - zeros
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            zeros = z
        else:
            _move(S, cnt, i, old, m, z)
    return sorted(S)


def _difference_graph(d, deadline, rng):
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best_m, best_S = 0, None
    cur = max(k + 1, int(0.8 * cap))
    fails = 0
    while time.monotonic() < deadline and cur <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
        S = _cover_search(k, cur, slice_end, rng)
        if S is not None:
            best_m, best_S = cur, S
            cur += 1
            fails = 0
        else:
            fails += 1
            if best_S is None:
                cur = max(k + 1, cur - 3)
            elif fails >= 3:
                break
    if best_S is None:
        return None
    return lib.haar_graph(best_m, best_S)


# ----------------------------------------------------------------------------
# Python glue: run the C annealer on the best graph found so far.
# ----------------------------------------------------------------------------

def _c_improve(graph, d, D, seed, budget):
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=graph, timeout=budget + 5.0)
        return lib.parse_graph_text(text)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(c):
        nonlocal best
        if c is not None and c[0] > best[0] and lib.is_valid(c[0], c[1], d, D):
            best = c

    if D == 3:
        arcs = _arc_candidates(d, start + 0.06 * time_limit, random.Random(seed * 7919 + d))
        for c in sorted(arcs, key=lambda t: -t[0])[:3]:
            consider(c)
        consider(_difference_graph(d, start + 0.30 * time_limit, rng))

    # Main search: C annealer that inserts vertices and keeps diameter <= D.
    budget = start + 0.88 * time_limit - time.monotonic() - 2.5
    if budget >= 1.0 and 2 <= d <= 40:
        consider(_c_improve(best, d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
