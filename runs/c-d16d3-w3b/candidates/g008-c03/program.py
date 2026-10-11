import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: greedy vertex insertion with ball-cover certificates (diameter D).
#
# Let R = D-1. A new vertex w joined to a set N of opposite-colour vertices is
# within distance D of every old vertex x that lies in the R-ball of some u in N.
# Adding vertices and cross edges never increases old distances, so validity is
# preserved. Each round:
#   1. compute R-balls as bitsets,
#   2. for each colour class, greedily cover all vertices with spare-degree
#      neighbours (randomized tie-breaks) and insert a vertex on success,
#   3. on failure add a random spare cross edge to change the spare pattern.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXD 64
#define MAXW (MAXN / 64)

static int n, d, D, W;
static int deg[MAXN];
static int adj[MAXN][MAXD];
static int col[MAXN];
static uint64_t reach[MAXN][MAXW];
static uint64_t nxt[MAXN][MAXW];
static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static int popc(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++) if (adj[u][i] == v) return 1;
    return 0;
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void compute_balls(int R) {
    for (int v = 0; v < n; v++) {
        for (int w = 0; w < W; w++) reach[v][w] = 0;
        reach[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < R; r++) {
        for (int v = 0; v < n; v++) {
            for (int w = 0; w < W; w++) nxt[v][w] = reach[v][w];
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                for (int w = 0; w < W; w++) nxt[v][w] |= reach[u][w];
            }
        }
        for (int v = 0; v < n; v++)
            for (int w = 0; w < W; w++) reach[v][w] = nxt[v][w];
    }
}

static int covers_all(const uint64_t *cov) {
    for (int w = 0; w < W; w++) {
        uint64_t want;
        if (w < W - 1) {
            want = ~0ULL;
        } else {
            int r = n - 64 * (W - 1);
            want = (r >= 64) ? ~0ULL : ((1ULL << r) - 1);
        }
        if ((cov[w] & want) != want) return 0;
    }
    return 1;
}

static int try_insert(int side) {
    static int cand[MAXN];
    int nc = 0;
    for (int u = 0; u < n; u++)
        if (col[u] == 1 - side && deg[u] < d) cand[nc++] = u;
    if (nc == 0) return 0;
    for (int i = nc - 1; i > 0; i--) {
        int j = (int)(rnd() % (uint32_t)(i + 1));
        int t = cand[i]; cand[i] = cand[j]; cand[j] = t;
    }
    static int used[MAXN];
    for (int i = 0; i < n; i++) used[i] = 0;
    uint64_t cov[MAXW];
    for (int w = 0; w < W; w++) cov[w] = 0;
    int chosen[MAXD];
    int nch = 0;
    while (nch < d && !covers_all(cov)) {
        int best = -1, bg = 0;
        for (int i = 0; i < nc; i++) {
            int u = cand[i];
            if (used[u]) continue;
            int g = 0;
            for (int w = 0; w < W; w++) g += popc(reach[u][w] & ~cov[w]);
            if (g > bg) { bg = g; best = u; }
        }
        if (best < 0) break;
        used[best] = 1;
        chosen[nch++] = best;
        for (int w = 0; w < W; w++) cov[w] |= reach[best][w];
    }
    if (!covers_all(cov)) return 0;
    int w = n;
    n++;
    col[w] = side;
    deg[w] = 0;
    for (int i = 0; i < nch; i++) add_edge(chosen[i], w);
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    int N0, M0;
    if (scanf("%d %d", &N0, &M0) != 2) { printf("0 0\n"); return 0; }
    if (N0 < 1 || N0 > MAXN) { printf("0 0\n"); return 0; }
    n = N0;
    W = (n + 63) >> 6;
    for (int i = 0; i < M0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) continue;
        if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
        add_edge(u, v);
    }

    static int queue[MAXN];
    for (int s = 0; s < n; s++) col[s] = -1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt) {
            int u = queue[qh++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u][i];
                if (col[v] < 0) {
                    col[v] = 1 - col[u];
                    queue[qt++] = v;
                }
            }
        }
    }

    clock_t t0 = clock();
    int fails = 0;
    const int maxfails = 400;
    while (fails < maxfails && n < MAXN) {
        if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) break;
        W = (n + 63) >> 6;
        compute_balls(D - 1);
        int sides[2] = {0, 1};
        if (rnd() & 1u) { sides[0] = 1; sides[1] = 0; }
        int ok = 0;
        for (int k = 0; k < 2 && !ok; k++) ok = try_insert(sides[k]);
        if (ok) { fails = 0; continue; }
        fails++;
        for (int t = 0; t < 50; t++) {
            int u = (int)(rnd() % (uint32_t)n);
            int v = (int)(rnd() % (uint32_t)n);
            if (u == v || col[u] == col[v]) continue;
            if (deg[u] >= d || deg[v] >= d || has_edge(u, v)) continue;
            add_edge(u, v);
            break;
        }
    }

    int m2 = 0;
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) m2++;
    printf("%d %d\n", n, m2);
    for (int u = 0; u < n; u++)
        for (int i = 0; i < deg[u]; i++)
            if (adj[u][i] > u) printf("%d %d\n", u, adj[u][i]);
    return 0;
}
"""


def _c_augment(graph, d, D, seed, budget):
    """Run the C insertion engine on graph; return (n, edges) or None on any failure."""
    if graph is None or budget < 0.5 or d > 64:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=(graph[0], graph[1]), timeout=budget + 5.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 1:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# C engine 2 (new, bold): bi-Cayley graphs over small groups for diameter D.
#
# Group G (cyclic Z_m, or semidirect Z_m x| Z_k), |S| = d with identity in S.
# Vertices A_x = x and B_y = G + y, edges A_x ~ B_{x s} for s in S.
# Left multiplication is an automorphism, so distances from A_e and B_e
# determine validity. Simulated annealing moves one element of S at a time,
# minimizing the number of vertices unreached within distance D from A_e and B_e.
# For D = 3 the condition is S S^-1 = G and S^-1 S = G, so |G| <= d(d-1)+1,
# which is the Moore-type ceiling for these graphs. Order 2|G| is the output.
# ----------------------------------------------------------------------------

BICAY_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXG 512
#define MAXDEG 64
#define MAXCAND 4096

typedef struct { int t, m, k, r; } Group;

static int d, D, G;
static int mulT[MAXG * MAXG];
static int invT[MAXG];
static int pw[MAXG];
static int S[MAXDEG], inS[MAXG], bestS[MAXDEG];
static int stampA[2 * MAXG], stampCur = 0, qbuf[2 * MAXG];
static Group cand[MAXCAND];
static int ncand = 0;
static Group bestGroup;
static int bestG = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t next64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd_int(int n) { return (int)((next64() >> 11) % (uint64_t)n); }

static double rnd_unit(void) { return (double)(next64() >> 11) / 9007199254740992.0; }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static double elapsed_since(clock_t t0) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC;
}

/* Build multiplication and inverse tables for the group g; sets global G. */
static void build_group(Group g) {
    int m = g.m, k = g.k;
    if (g.t == 0) {
        G = m;
        for (int x = 0; x < G; x++) {
            invT[x] = (G - x) % G;
            for (int y = 0; y < G; y++) mulT[x * G + y] = (x + y) % G;
        }
        return;
    }
    G = m * k;
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)(((long long)pw[b - 1] * g.r) % m);
    for (int x = 0; x < G; x++) {
        int a1 = x / k, b1 = x % k, nb = (k - b1) % k;
        invT[x] = ((m - (int)(((long long)pw[nb] * a1) % m)) % m) * k + nb;
        for (int y = 0; y < G; y++) {
            int a2 = y / k, b2 = y % k;
            int a = (a1 + (int)(((long long)pw[b1] * a2) % m)) % m;
            mulT[x * G + y] = a * k + (b1 + b2) % k;
        }
    }
}

/* Candidate groups of order Gt: cyclic, and Z_m x|_r Z_k for 2 <= k <= 12 with r^k = 1. */
static void enum_groups(int Gt) {
    ncand = 0;
    cand[ncand++] = (Group){0, Gt, 1, 0};
    for (int k = 2; k <= 12 && k <= Gt; k++) {
        if (Gt % k) continue;
        int m = Gt / k;
        if (m < 2) continue;
        for (int r = 1; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            long long p = 1 % m;
            for (int i = 0; i < k; i++) p = (p * r) % m;
            if (p != 1 % m) continue;
            if (ncand < MAXCAND) cand[ncand++] = (Group){1, m, k, r};
        }
    }
}

/* Number of vertices of the 2G-vertex graph not reached from src within D steps. */
static int bfs_unreached(int src) {
    stampCur++;
    int qh = 0, qt = 0, reached = 1;
    qbuf[qt++] = src;
    stampA[src] = stampCur;
    for (int depth = 0; depth < D && qh < qt; depth++) {
        int end = qt;
        while (qh < end) {
            int u = qbuf[qh++];
            if (u < G) {
                for (int i = 0; i < d; i++) {
                    int v = G + mulT[u * G + S[i]];
                    if (stampA[v] != stampCur) {
                        stampA[v] = stampCur;
                        qbuf[qt++] = v;
                        reached++;
                    }
                }
            } else {
                int y = u - G;
                for (int i = 0; i < d; i++) {
                    int v = mulT[y * G + invT[S[i]]];
                    if (stampA[v] != stampCur) {
                        stampA[v] = stampCur;
                        qbuf[qt++] = v;
                        reached++;
                    }
                }
            }
        }
    }
    return 2 * G - reached;
}

static void record(Group g) {
    memcpy(bestS, S, sizeof(S));
    bestGroup = g;
    bestG = G;
}

/* Annealing for one group within a CPU slice. Returns 1 on success (recorded). */
static int attempt(Group g, double slice) {
    build_group(g);
    if (G <= d || d < 2) return 0;
    memset(inS, 0, sizeof(int) * G);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < d; i++) {
        int y;
        do { y = rnd_int(G); } while (inS[y]);
        S[i] = y;
        inS[y] = 1;
    }
    int cur = bfs_unreached(0) + bfs_unreached(G);
    if (cur == 0) { record(g); return 1; }

    clock_t t0 = clock();
    const double T0 = 1.5, T1 = 0.05;
    double T = T0;
    for (long it = 1;; it++) {
        if ((it & 255) == 0) {
            double el = elapsed_since(t0);
            if (el >= slice) break;
            double f = el / slice;
            T = T0 * pow(T1 / T0, f);
        }
        int i = 1 + rnd_int(d - 1);
        int y;
        do { y = rnd_int(G); } while (inS[y]);
        int old = S[i];
        inS[old] = 0;
        S[i] = y;
        inS[y] = 1;
        int c2 = bfs_unreached(0) + bfs_unreached(G);
        int delta = c2 - cur;
        if (delta <= 0 || rnd_unit() < exp(-delta / T)) {
            cur = c2;
            if (cur == 0) { record(g); return 1; }
        } else {
            inS[y] = 0;
            S[i] = old;
            inS[old] = 1;
        }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) next64();

    if (d < 2 || d > MAXDEG || D < 2) { printf("0 0\n"); return 0; }

    /* Gmax = sum_{i<D} (d-1)^i, half the bipartite Moore bound. */
    double Gd = 0, p = 1;
    for (int i = 0; i < D; i++) {
        Gd += p;
        p *= (d - 1);
        if (Gd > MAXG) break;
    }
    int Gmax = (Gd > MAXG - 1) ? MAXG - 1 : (int)Gd;
    int Gmin = (int)(0.75 * Gmax);
    if (Gmin < d + 1) Gmin = d + 1;
    if (Gmin > Gmax) { printf("0 0\n"); return 0; }
    int numG = Gmax - Gmin + 1;
    double slice = budget / numG;
    if (slice < 0.05) slice = 0.05;
    if (slice > 3.0) slice = 3.0;

    clock_t tstart = clock();
    while (elapsed_since(tstart) < budget) {
        if (bestG >= Gmax) break;
        for (int G0 = Gmax; G0 >= Gmin && G0 > bestG; G0--) {
            double left = budget - elapsed_since(tstart);
            if (left <= 0.01) break;
            enum_groups(G0);
            Group g = cand[rnd_int(ncand)];
            double sl = slice < left ? slice : left;
            attempt(g, sl);
        }
    }

    if (bestG == 0) { printf("0 0\n"); return 0; }
    build_group(bestGroup);
    memcpy(S, bestS, sizeof(S));
    if (bfs_unreached(0) + bfs_unreached(G) != 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", 2 * G, G * d);
    for (int x = 0; x < G; x++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", x, G + mulT[x * G + S[i]]);
    return 0;
}
"""


def _bicayley(d, D, seed, budget):
    """Run the bi-Cayley annealing engine; return (n, edges) or None."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(BICAY_SOURCE, [d, D, seed, round(budget, 2)],
                        timeout=budget + 8.0)
        n2, e2 = lib.parse_graph_text(out)
    except Exception:
        return None
    if n2 < 2 or not e2:
        return None
    return n2, e2


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to the
#         q+1 lines through P. Each line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to the q+1
#         points on j. Each point lies on <= s lines of SB.
# ----------------------------------------------------------------------------

_LS_ITERS = 30000


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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the same load-constrained set problem."""
    if s < 1:
        return list(S)
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
            if len(cur) >= s:
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


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
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
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


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
# Driver.
#   All D >= 3: arc-extended PG graph as a safe, valid fallback (short deadline).
#   D == 3:     bi-Cayley difference-cover annealing (new), then insertion on best.
#   D >= 4:     GQ baseline, annealed group voltage lifts, then insertion on best.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def el():
        return time.monotonic() - start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.20 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs[:4]:
            consider(g)

    if D == 3:
        budget = 0.70 * time_limit - el()
        if budget >= 1.0:
            consider(_bicayley(d, D, seed, budget))

    if D >= 4:
        if el() < 0.50 * time_limit:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq)
        anneal_end = start + 0.70 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < anneal_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, anneal_end, iters=400)
            if res is not None:
                consider(res)

    if D >= 3:
        rem = 0.88 * time_limit - el()
        if rem >= 0.5:
            consider(_c_augment(best, d, D, seed + 1, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
