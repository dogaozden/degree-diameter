import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing on bipartite graphs with a fixed vertex set.
# Cost = number of unordered pairs at distance > D (unreachable counts as bad).
# Moves keep max degree <= d and bipartiteness (sides are fixed per vertex).
# Moves are focused: most rewire/add moves start at a vertex that is part of
# some bad pair, so search effort goes where the defects are.
# Whenever the cost reaches 0 the engine saves the graph and appends one more
# isolated vertex, so it grows the order while staying valid. It always prints
# a graph; Python re-checks it with lib.is_valid.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1600
#define MAXW 25
#define DCAP 64
#define MAXE (MAXN * DCAP)

static int n, d, D;
static int nb[MAXN][DCAP];
static int deg[MAXN];
static int side[MAXN];
static unsigned char adjm[MAXN][MAXN];
static uint64_t RA[MAXN][MAXW];
static uint64_t RB[MAXN][MAXW];
static int bestU[MAXE], bestV[MAXE];
static int best_n = 0, best_m = 0;
static uint64_t rs = 1;
static int vis[MAXN];

/* vertices involved in at least one bad pair: tmp from the last bad_pairs call,
   cur for the accepted state. */
static int tmpbadv[MAXN], ntmp = 0;
static int curbadv[MAXN], ncurbadv = 0;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static int popc(uint64_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }

static void add_edge(int u, int v) {
    nb[u][deg[u]++] = v;
    nb[v][deg[v]++] = u;
    adjm[u][v] = 1; adjm[v][u] = 1;
}
static void rm_one(int u, int v) {
    for (int i = 0; i < deg[u]; i++) {
        if (nb[u][i] == v) { nb[u][i] = nb[u][deg[u] - 1]; deg[u]--; return; }
    }
}
static void del_edge(int u, int v) {
    rm_one(u, v); rm_one(v, u);
    adjm[u][v] = 0; adjm[v][u] = 0;
}

static int bad_pairs(void) {
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        memset(RA[v], 0, sizeof(uint64_t) * (size_t)W);
        RA[v][v >> 6] |= 1ULL << (v & 63);
    }
    uint64_t (*cur)[MAXW] = RA;
    uint64_t (*nxt)[MAXW] = RB;
    for (int t = 0; t < D; t++) {
        for (int v = 0; v < n; v++) {
            memcpy(nxt[v], cur[v], sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *s = cur[nb[v][i]];
                for (int w = 0; w < W; w++) nxt[v][w] |= s[w];
            }
        }
        uint64_t (*tmp)[MAXW] = cur;
        cur = nxt;
        nxt = tmp;
    }
    long bad = 0;
    ntmp = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(cur[v][w]);
        int miss = n - c;
        bad += miss;
        if (miss > 0) tmpbadv[ntmp++] = v;
    }
    return (int)(bad / 2);
}

/* Make the most recent bad_pairs() result the accepted state's defect list. */
static void adopt(void) {
    memcpy(curbadv, tmpbadv, sizeof(int) * (size_t)ntmp);
    ncurbadv = ntmp;
}

static void save_best(void) {
    int m = 0;
    for (int u = 0; u < n; u++) {
        for (int i = 0; i < deg[u]; i++) {
            if (nb[u][i] > u && m < MAXE) {
                bestU[m] = u; bestV[m] = nb[u][i]; m++;
            }
        }
    }
    best_n = n; best_m = m;
}

static int color_graph(void) {
    static int queue[MAXN];
    int iso = 0;
    for (int v = 0; v < n; v++) vis[v] = 0;
    for (int s = 0; s < n; s++) {
        if (vis[s]) continue;
        if (deg[s] == 0) { vis[s] = 1; side[s] = (iso++) & 1; continue; }
        vis[s] = 1; side[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = nb[u][i];
                if (!vis[v]) { vis[v] = 1; side[v] = 1 - side[u]; queue[qt++] = v; }
                else if (side[v] == side[u]) return 0;
            }
        }
    }
    return 1;
}

/* Pick a vertex: with good probability one that is part of a bad pair. */
static int pick_vertex(void) {
    if (ncurbadv > 0 && rdbl() < 0.6) {
        return curbadv[rint_(ncurbadv)];
    }
    return rint_(n);
}

/* a -- b  becomes  a -- w, where w is on the same side as b. */
static int move_rewire(int *ua, int *ub, int *uw) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = pick_vertex();
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    int w = -1;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != b && side[c] == side[b] && deg[c] < d && !adjm[a][c]) { w = c; break; }
    }
    if (w < 0) return 0;
    del_edge(a, b);
    add_edge(a, w);
    *ua = a; *ub = b; *uw = w;
    return 1;
}

static int move_add(int *ua, int *ub) {
    int x = -1, y = -1;
    for (int t = 0; t < 64; t++) {
        int c = pick_vertex();
        if (deg[c] < d) { x = c; break; }
    }
    if (x < 0) return 0;
    for (int t = 0; t < 64; t++) {
        int c = rint_(n);
        if (c != x && side[c] != side[x] && deg[c] < d && !adjm[x][c]) { y = c; break; }
    }
    if (y < 0) return 0;
    add_edge(x, y);
    *ua = x; *ub = y;
    return 1;
}

static int move_remove(int *ua, int *ub) {
    int a = -1;
    for (int t = 0; t < 64 && a < 0; t++) {
        int c = rint_(n);
        if (deg[c] > 0) a = c;
    }
    if (a < 0) return 0;
    int b = nb[a][rint_(deg[a])];
    del_edge(a, b);
    *ua = a; *ub = b;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 12345ULL);
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    clock_t t0 = clock();

    int m0 = 0;
    if (scanf("%d %d", &n, &m0) != 2 || n < 0 || m0 < 0) { printf("0 0\n"); return 0; }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (!iu || !iv) return 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { m0 = i; break; }
    }

    int ok = (n >= 2 && n <= MAXN - 256 && d >= 1 && d <= DCAP && D >= 1);
    if (ok) {
        for (int i = 0; i < m0 && ok; i++) {
            int u = iu[i], v = iv[i];
            if (u < 0 || v < 0 || u >= n || v >= n || u == v || adjm[u][v] ||
                deg[u] >= d || deg[v] >= d) {
                ok = 0;
            } else {
                add_edge(u, v);
            }
        }
    }
    if (ok) ok = color_graph();
    if (!ok) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }

    int cur_bad = bad_pairs();
    adopt();
    int have_best = 0;
    if (cur_bad == 0) { save_best(); have_best = 1; }

    long it = 0;
    for (;;) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;

        if (cur_bad == 0) {
            save_best();
            have_best = 1;
            if (n >= MAXN - 2) break;
            side[n] = n & 1;
            deg[n] = 0;
            n++;
            cur_bad = bad_pairs();
            adopt();
            continue;
        }

        double phase = (double)(it % 60000) / 60000.0;
        double T = 0.15 + 1.2 * (1.0 - phase) * (1.0 - phase);

        int kind = 0, ua = 0, ub = 0, uw = 0, applied = 0;
        int r = rint_(100);
        if (r < 55) { kind = 0; applied = move_rewire(&ua, &ub, &uw); }
        else if (r < 90) { kind = 1; applied = move_add(&ua, &ub); }
        else { kind = 2; applied = move_remove(&ua, &ub); }
        if (!applied) continue;

        int nbad = bad_pairs();
        int delta = nbad - cur_bad;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur_bad = nbad;
            adopt();
        } else {
            if (kind == 0) { del_edge(ua, uw); add_edge(ua, ub); }
            else if (kind == 1) { del_edge(ua, ub); }
            else { add_edge(ua, ub); }
        }
    }

    if (!have_best) {
        printf("%d %d\n", n, m0);
        for (int i = 0; i < m0; i++) printf("%d %d\n", iu[i], iv[i]);
        return 0;
    }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bestU[i], bestV[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# NEW: asymmetric clone extensions of PG(2, q) (diameter 3).
#
# Let s = d - q - 1 be the spare degree of every vertex of PG(2, q).
# A "point clone" x_P is a new point-side vertex joined to the q+1 lines
# through a point P; a "line clone" y_j is a new line-side vertex joined to
# the q+1 points on a line j. Both have degree q+1 <= d.
#
# Clones only add degree to the originals on the other side, so the only
# constraints are:
#   * each line L: #{P in S_A : P on L} <= s          (point clones)
#   * each point Q: #{j in S_B : Q on j} <= s         (line clones)
# The two sets S_A and S_B are chosen INDEPENDENTLY (the parent forced
# S_A = S_B). Distances stay <= 3 for every choice, so only the degree
# constraints matter. Each set is a maximum-size "load-s" set found by a
# swap-based local search, seeded with a conic when q is odd.
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, pl, lp): points and lines of PG(2, q) indexed 0..m-1.

    pl[P] = indices of lines through point P; lp[L] = indices of points on line L.
    """
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _conic_seed(q):
    """Point indices of a conic (plus nucleus) for odd q; empty for even q."""
    if q % 2 == 0:
        return []
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    return S


def _max_load_set(m, s, pl, lp, rng, deadline, seed_set):
    """Largest set X of elements 0..m-1 such that every constraint L has |X & lp[L]| <= s.

    pl[x] lists the constraints touching element x; lp[L] lists the elements under constraint L.
    Local search with 1-for-1 swaps (always accepted) and occasional 2-for-1 drops.
    """
    inX = [False] * m
    cnt = [0] * m
    X = set()

    def add(x):
        inX[x] = True
        X.add(x)
        for L in pl[x]:
            cnt[L] += 1

    def drop(x):
        inX[x] = False
        X.discard(x)
        for L in pl[x]:
            cnt[L] -= 1

    for x in seed_set:
        if not inX[x] and all(cnt[L] < s for L in pl[x]):
            add(x)
    best = list(X)
    it = 0
    while True:
        it += 1
        if (it & 255) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inX[x]:
            continue
        tk = set()
        for L in pl[x]:
            if cnt[L] < s:
                continue
            if any(y in tk for y in lp[L]):
                continue
            cands = [y for y in lp[L] if inX[y]]
            tk.add(rng.choice(cands))
            if len(tk) > 2:
                break
        if len(tk) > 2:
            continue
        if len(tk) == 2 and rng.random() > 0.1:
            continue
        for y in tk:
            drop(y)
        add(x)
        if len(X) > len(best):
            best = list(X)
    return best


def _clone_graph(m, edges, pl, lp, SA, SB):
    """PG(2,q) incidence plus point clones (for SA) and line clones (for SB)."""
    E = list(edges)
    n = 2 * m + len(SA) + len(SB)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    base = 2 * m + len(SA)
    for t, j in enumerate(SB):
        y = base + t
        for Q in lp[j]:
            E.append((Q, y))
    return n, E


def _best_clone_graph(d, D, deadline, rng):
    """Best asymmetric clone extension over prime powers q with q + 1 <= d; (n, edges) or None."""
    qs = [q for q in range(min(d - 1, 23), 1, -1)
          if q + 1 <= d and lib.is_prime_power(q)]
    best = None
    for idx, q in enumerate(qs):
        now = time.monotonic()
        if now > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp = _pg(q)
        if s == 0:
            SA, SB = [], []
        else:
            share = (deadline - now) / (len(qs) - idx)
            seed_set = _conic_seed(q)
            SA = _max_load_set(m, s, pl, lp, rng, now + share / 2, seed_set)
            SB = _max_load_set(m, s, lp, pl, rng, now + share, seed_set)
        n, E = _clone_graph(m, edges, pl, lp, SA, SB)
        if (best is None or n > best[0]) and lib.is_valid(n, E, d, D):
            best = (n, E)
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.88 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], list(g[1]))

    # Asymmetric clone extensions of PG(2, q) (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        clone_deadline = time.monotonic() + 0.2 * (end - time.monotonic())
        cg = _best_clone_graph(d, D, clone_deadline, random.Random(seed * 7919 + d))
        if cg is not None:
            consider(cg)

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Focused annealing for D = 3: adds vertices to the best graph,
    # with moves aimed at vertices that take part in bad pairs.
    if D == 3:
        bound = lib.moore_bound(d, D)
        cbudget = end - time.monotonic()
        if best[0] < bound and cbudget > 3.0:
            try:
                start_graph = (best[0] + 1, list(best[1]))  # one extra isolated vertex
                out = lib.run_c(C_SOURCE, [d, D, seed, round(cbudget - 1.5, 2)],
                                stdin_graph=start_graph, timeout=cbudget + 5)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
