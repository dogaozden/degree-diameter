import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1: bi-Cayley voltage-lift annealing (new in this version).
#
# The group is Z_M x| Z_K2 with R^K2 = 1 mod M (K2 = 1 gives cyclic Z_M), coded
# as a*K2 + b, with (a,b)*(c,e) = (a + R^b c, b + e). Base has k vertices per side.
# Layer L (0..d-1) has, for each base vertex i, a target B-vertex P[L][i] (a
# permutation per layer, so every B base vertex gets one dart per layer) and a
# voltage V[L][i] in G. Dart (L,i) joins A_{i,g} to B_{P,g*V}.
# Every vertex then has degree d (duplicate darts are dropped at output time).
# Cost = number of (source, vertex) pairs not reached within D steps, summed
# over the 2k base sources. Zero cost gives a valid graph of order 2*k*G.
# Simulated annealing runs over voltages and per-layer permutation swaps.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXD 64
#define MAXG 1200
#define MAXN (2 * MAXK * MAXG)

static int d, D, k, M, K2, R, G, KG, N;
static int *MUL;
static int *INV;
static int POW[64];
static int V[MAXD][MAXK];
static int P[MAXD][MAXK];
static int PI[MAXD][MAXK];
static int stamp[MAXN];
static int curst = 0;
static int qbuf[MAXN];
static uint64_t rs = 1;

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static double urand(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int irand(int n) {
    return (int)(nextr() % (uint64_t)n);
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)POW[b] * c) % M;
    return (int)t * K2 + (b + e) % K2;
}

static int nbrs(int u, int *out) {
    int c = 0;
    if (u < KG) {
        int i = u / G, g = u % G;
        for (int L = 0; L < d; L++) {
            int j = P[L][i];
            int w = MUL[g * G + V[L][i]];
            out[c++] = KG + j * G + w;
        }
    } else {
        int x = u - KG, j = x / G, h = x % G;
        for (int L = 0; L < d; L++) {
            int i = PI[L][j];
            int g = MUL[h * G + INV[V[L][i]]];
            out[c++] = i * G + g;
        }
    }
    return c;
}

static int bfs(int src) {
    int nb[MAXD];
    curst++;
    int head = 0, tail = 0;
    qbuf[tail++] = src;
    stamp[src] = curst;
    int level_end = 1;
    for (int lev = 0; lev < D; lev++) {
        while (head < level_end) {
            int u = qbuf[head++];
            int c = nbrs(u, nb);
            for (int t = 0; t < c; t++) {
                int v = nb[t];
                if (stamp[v] != curst) {
                    stamp[v] = curst;
                    qbuf[tail++] = v;
                }
            }
        }
        level_end = tail;
        if (head == tail) break;
    }
    return tail;
}

static long long cost_all(void) {
    long long tot = 0;
    for (int i = 0; i < k; i++) tot += N - bfs(i * G);
    for (int j = 0; j < k; j++) tot += N - bfs(KG + j * G);
    return tot;
}

static int is_dup(int L, int i) {
    for (int L2 = 0; L2 < L; L2++)
        if (P[L2][i] == P[L][i] && V[L2][i] == V[L][i]) return 1;
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    M = atoi(argv[4]);
    K2 = atoi(argv[5]);
    R = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double budget = atof(argv[8]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || M < 2 || K2 < 1 || K2 > 64) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    if (G > MAXG) { printf("0 0\n"); return 0; }
    KG = k * G;
    N = 2 * KG;
    if (N > MAXN) { printf("0 0\n"); return 0; }

    POW[0] = 1 % M;
    for (int b = 1; b < K2; b++) POW[b] = (int)((long long)POW[b - 1] * R % M);
    if (((long long)POW[K2 - 1] * R) % M != 1 % M) { printf("0 0\n"); return 0; }

    MUL = malloc(sizeof(int) * (size_t)G * (size_t)G);
    INV = malloc(sizeof(int) * (size_t)G);
    if (!MUL || !INV) { printf("0 0\n"); return 0; }
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            MUL[x * G + y] = gmul(x, y);
    for (int x = 0; x < G; x++) {
        INV[x] = -1;
        for (int y = 0; y < G; y++)
            if (MUL[x * G + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) { printf("0 0\n"); return 0; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int t = 0; t < 8; t++) nextr();

    for (int L = 0; L < d; L++) {
        int perm[MAXK];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = irand(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            P[L][i] = perm[i];
            PI[L][perm[i]] = i;
            V[L][i] = irand(G);
        }
    }

    clock_t t0 = clock();
    long long cur = cost_all();
    double T = 1.5;
    long long it = 0;
    while (cur > 0) {
        if ((it & 127) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > budget) break;
            double f = el / budget;
            T = 1.5 * pow(0.05 / 1.5, f);
        }
        it++;
        if (k == 1 || (nextr() & 1)) {
            int L = irand(d), i = irand(k);
            int old = V[L][i];
            int nv = irand(G);
            if (nv == old) continue;
            V[L][i] = nv;
            long long c2 = cost_all();
            if (c2 <= cur || urand() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                V[L][i] = old;
            }
        } else {
            int L = irand(d), i1 = irand(k), i2 = irand(k);
            if (i1 == i2) continue;
            int a = P[L][i1], b = P[L][i2];
            P[L][i1] = b; P[L][i2] = a;
            PI[L][b] = i1; PI[L][a] = i2;
            long long c2 = cost_all();
            if (c2 <= cur || urand() < exp(-(double)(c2 - cur) / T)) {
                cur = c2;
            } else {
                P[L][i1] = a; P[L][i2] = b;
                PI[L][a] = i1; PI[L][b] = i2;
            }
        }
    }

    if (cur != 0) { printf("0 0\n"); return 0; }
    int m = 0;
    for (int L = 0; L < d; L++)
        for (int i = 0; i < k; i++)
            if (!is_dup(L, i)) m += G;
    printf("%d %d\n", N, m);
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < k; i++) {
            if (is_dup(L, i)) continue;
            int j = P[L][i];
            for (int g = 0; g < G; g++) {
                int w = MUL[g * G + V[L][i]];
                printf("%d %d\n", i * G + g, KG + j * G + w);
            }
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2: greedy vertex insertion with ball-cover certificates (unchanged).
#
# Let R = D-1. A new vertex w joined to a set N of vertices on the opposite
# colour class is within distance D of every old vertex x whenever x lies in
# the R-ball of some u in N. Adding a vertex never increases distances between
# old vertices, so the graph stays valid.
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
    int cand[MAXN];
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
    const int maxfails = 200;
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


def _lift_run(d, D, k, M, K2, R, seed, budget):
    """Run the C lift annealer for Z_M x| Z_K2 with k base vertices per side; (n, edges) or None."""
    try:
        out = lib.run_c(LIFT_SOURCE, [d, D, k, M, K2, R, seed, round(budget, 2)],
                        timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 2 or not e:
        return None
    return n, e


def _sample_group(G, rng):
    """Return (M, K2, R) with M*K2 = G and R^K2 = 1 mod M, gcd(R, M) = 1; prefers nonabelian options."""
    cyclic = None
    nonab = []
    for K2 in range(1, 13):
        if G % K2:
            continue
        M = G // K2
        if M < 2:
            continue
        if K2 == 1:
            cyclic = (M, 1, 1)
            continue
        for R in range(1, M):
            if math.gcd(R, M) == 1 and pow(R, K2, M) == 1 % M:
                nonab.append((M, K2, R))
    if cyclic is None and not nonab:
        return None
    if cyclic is not None and (not nonab or rng.random() < 0.4):
        return cyclic
    return rng.choice(nonab)


def _lift_search(d, D, deadline, rng, best_n):
    """Repeatedly search bi-Cayley lifts of order above the current best; return the valid finds."""
    found = []
    cur_n = best_n
    while True:
        left = deadline - time.monotonic()
        if left < 2.0:
            break
        k = rng.choice([1, 1, 2])
        G = cur_n // (2 * k) + 1 + rng.choice([0, 0, 1, 2])
        if G < 2:
            G = 2
        grp = _sample_group(G, rng)
        if grp is None:
            continue
        M, K2, R = grp
        slice_budget = min(left - 1.0, max(3.0, left / 5.0))
        if slice_budget < 0.5:
            break
        g = _lift_run(d, D, k, M, K2, R, rng.randrange(1, 2 ** 31), slice_budget)
        if g is not None and g[0] > cur_n and lib.is_valid(g[0], g[1], d, D):
            found.append(g)
            cur_n = g[0]
    return found


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence. Each old vertex has degree q+1, spare s = d-q-1.
# A-side: a set SA of points, each gets a new vertex joined to the q+1 lines
# through it; each line may hold at most s points of SA. B-side is dual.
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


def _loads_ok(S, s, m, nbr):
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice of elements so that every target is hit <= s times."""
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
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
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
# Driver. Time plan (fractions of time_limit):
#   0.00-0.08  arc-extended PG graphs (A and B sets chosen independently)
#   0.08      generalized quadrangle baseline (D >= 4)
#   0.08-0.80  bi-Cayley lift annealing (C) for orders above the current best
#   0.80-0.92  greedy C insertion on the best graph so far
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def elapsed():
        return time.monotonic() - start

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.08 * T, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for g in arcs:
            consider(g)

    if D >= 4 and elapsed() < 0.08 * T:
        consider(_best_gq(d))

    if D >= 3 and best_n < lib.moore_bound(d, D):
        found = _lift_search(d, D, start + 0.80 * T, rng, best_n)
        for g in found:
            consider(g)

    if D >= 3:
        rem = 0.92 * T - elapsed()
        if rem > 1.0:
            consider(_c_augment(best, d, D, seed + 1, rem))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
