"""Diameter-3 bipartite search with two stages.

Stage 1 (parent approach): arc-extended projective plane starts plus a C augmentation engine
that adds vertices joined to a greedy cover of spare vertices. Every addition keeps the graph valid.

Stage 2 (new, high-risk): cyclic voltage lifts. Take a base bipartite multigraph with R vertices per
side, where each base vertex has exactly d darts. Each dart (i, j) carries a voltage in Z_m, and the
lift has 2*R*m vertices. The C engine runs simulated annealing over voltages to minimise the number of
pairs at distance > D. Checking BFS from one representative per base vertex is enough, because Z_m acts
by automorphisms. The lift is simple and d-regular by construction. Python re-checks everything with
lib.is_valid and falls back to the best valid graph found so far.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 2048
#define WORDS (MAXN / 64)
#define MAXDEG 64

static int N, Dd, Dist, W;
static int deg[MAXN];
static int adj[MAXN][MAXDEG];
static int side[MAXN];
static uint64_t ball[MAXN][WORDS];
static int mark[MAXN], lev[MAXN], bq[MAXN];
static int stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }

static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Bitset of all vertices within distance r of src. */
static void ball_of(int src, int r, uint64_t *bits) {
    int head = 0, t = 0;
    stamp++;
    for (int i = 0; i < W; i++) bits[i] = 0;
    bq[t++] = src;
    mark[src] = stamp;
    lev[src] = 0;
    while (head < t) {
        int u = bq[head++];
        bits[u >> 6] |= 1ULL << (u & 63);
        if (lev[u] >= r) continue;
        for (int k = 0; k < deg[u]; k++) {
            int v = adj[u][k];
            if (mark[v] != stamp) {
                mark[v] = stamp;
                lev[v] = lev[u] + 1;
                bq[t++] = v;
            }
        }
    }
}

static void recompute_balls(void) {
    for (int v = 0; v < N; v++) ball_of(v, Dist - 1, ball[v]);
}

/* Try to add one new vertex on side X. Returns 1 if the graph grew. */
static int try_add(int X) {
    uint64_t U[WORDS];
    int sel[MAXN];
    int T[MAXDEG];
    int nt = 0;
    if (N + 1 >= MAXN) return 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(sel));
    while (nt < Dd) {
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 8 + rndint(8);
            if (sc > bestsc) {
                bestsc = sc;
                best = v;
            }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    for (int i = 0; i < W; i++)
        if (U[i]) return 0;
    if (nt == 0) return 0;
    int x = N;
    side[x] = X;
    deg[x] = nt;
    for (int k = 0; k < nt; k++) {
        int t = T[k];
        adj[x][k] = t;
        adj[t][deg[t]++] = x;
    }
    N++;
    W = (N + 63) / 64;
    recompute_balls();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    Dd = atoi(argv[1]);
    if (Dd > MAXDEG) Dd = MAXDEG;
    Dist = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) n = 0;
    if (n <= 0 || n > MAXN - 2 || Dist < 1) {
        printf("0 0\n");
        return 0;
    }
    N = n;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || u >= N || v < 0 || v >= N || u == v) continue;
        if (deg[u] >= MAXDEG || deg[v] >= MAXDEG) continue;
        adj[u][deg[u]++] = v;
        adj[v][deg[v]++] = u;
    }

    for (int v = 0; v < N; v++) side[v] = -1;
    for (int s = 0; s < N; s++) {
        if (side[s] >= 0) continue;
        side[s] = 0;
        int head = 0, t = 0;
        bq[t++] = s;
        while (head < t) {
            int u = bq[head++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[u][k];
                if (side[v] < 0) {
                    side[v] = 1 - side[u];
                    bq[t++] = v;
                }
            }
        }
    }

    W = (N + 63) / 64;
    recompute_balls();

    double t_end = elapsed() + budget;
    int fails = 0;
    while (elapsed() < t_end && N < MAXN - 2 && fails < 4000) {
        int X = rndint(2);
        if (try_add(X)) fails = 0;
        else fails++;
    }

    int M = 0;
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) M++;
    printf("%d %d\n", N, M);
    for (int v = 0; v < N; v++)
        for (int k = 0; k < deg[v]; k++)
            if (adj[v][k] > v) printf("%d %d\n", v, adj[v][k]);
    return 0;
}
"""

# Voltage-lift annealer: args = d D R mstart seed budget. Output: lifted graph or "0 0".
C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define MAXD 64
#define MAXR 8
#define MAXDARTS (MAXR * MAXD)

static int R, Dd, DI, M, NV, nd;
static int mult[MAXR][MAXR];
static int di[MAXDARTS], dj[MAXDARTS], dv[MAXDARTS];
static int adjv[MAXV][MAXD];
static int stampv[MAXV], lev[MAXV], qbuf[MAXV];
static int curstamp = 0;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

/* Vertex A(i,g) = i*M+g, B(j,h) = R*M + j*M + h. Dart k = (i,j,v) joins A(i,g) to B(j,(g+v)%M). */
static void build_adj(void) {
    int cnt[MAXV];
    memset(cnt, 0, sizeof(int) * NV);
    for (int k = 0; k < nd; k++) {
        int i = di[k], j = dj[k], v = dv[k];
        for (int g = 0; g < M; g++) {
            int a = i * M + g;
            int b = R * M + j * M + (g + v) % M;
            adjv[a][cnt[a]++] = b;
            adjv[b][cnt[b]++] = a;
        }
    }
}

/* Number of vertices within distance DI of src. */
static int reach_count(int src) {
    int head = 0, t = 0;
    curstamp++;
    qbuf[t++] = src;
    stampv[src] = curstamp;
    lev[src] = 0;
    while (head < t) {
        int u = qbuf[head++];
        if (lev[u] >= DI) continue;
        for (int k = 0; k < Dd; k++) {
            int w = adjv[u][k];
            if (stampv[w] != curstamp) {
                stampv[w] = curstamp;
                lev[w] = lev[u] + 1;
                qbuf[t++] = w;
            }
        }
    }
    return t;
}

/* Sum over base representatives of the number of vertices too far away. Zero iff valid. */
static long cost_all(void) {
    long bad = 0;
    for (int i = 0; i < R; i++) bad += NV - reach_count(i * M);
    for (int j = 0; j < R; j++) bad += NV - reach_count(R * M + j * M);
    return bad;
}

static void random_mult(void) {
    memset(mult, 0, sizeof(mult));
    int perm[MAXR];
    for (int t = 0; t < Dd; t++) {
        for (int i = 0; i < R; i++) perm[i] = i;
        for (int i = R - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[r];
            perm[r] = tmp;
        }
        for (int i = 0; i < R; i++) mult[i][perm[i]]++;
    }
}

static void init_darts(void) {
    nd = 0;
    for (int i = 0; i < R; i++)
        for (int j = 0; j < R; j++)
            for (int c = 0; c < mult[i][j]; c++) {
                di[nd] = i;
                dj[nd] = j;
                nd++;
            }
    for (int k = 0; k < nd; k++) {
        int x;
        for (;;) {
            x = rndint(M);
            int ok = 1;
            for (int k2 = 0; k2 < k; k2++)
                if (di[k2] == di[k] && dj[k2] == dj[k] && dv[k2] == x) {
                    ok = 0;
                    break;
                }
            if (ok) break;
        }
        dv[k] = x;
    }
}

/* Propose a new voltage for dart k keeping voltages distinct within its (i,j) group. */
static int propose(int k, int *newx) {
    for (int tries = 0; tries < 60; tries++) {
        int x = rndint(M);
        if (x == dv[k]) continue;
        int ok = 1;
        for (int k2 = 0; k2 < nd; k2++)
            if (k2 != k && di[k2] == di[k] && dj[k2] == dj[k] && dv[k2] == x) {
                ok = 0;
                break;
            }
        if (ok) {
            *newx = x;
            return 1;
        }
    }
    return 0;
}

static long anneal(long iters) {
    long cur = cost_all();
    const long P = 4000;
    for (long it = 0; it < iters && cur > 0; it++) {
        double phase = (double)(it % P) / (double)P;
        double T = 2.0 * exp(-6.0 * phase) + 0.05;
        int k = rndint(nd);
        int nx;
        if (!propose(k, &nx)) continue;
        int old = dv[k];
        dv[k] = nx;
        build_adj();
        long nc = cost_all();
        long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            dv[k] = old;
            build_adj();
        }
    }
    return cur;
}

static double deadline_s;

static int try_M(long iters_per, int max_restarts) {
    for (int r = 0; r < max_restarts && elapsed() < deadline_s; r++) {
        random_mult();
        init_darts();
        build_adj();
        if (anneal(iters_per) == 0) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    Dd = atoi(argv[1]);
    DI = atoi(argv[2]);
    R = atoi(argv[3]);
    int mstart = atoi(argv[4]);
    unsigned long seed = strtoul(argv[5], NULL, 10);
    double budget = atof(argv[6]);
    if (Dd < 2 || Dd > MAXD || DI < 2 || R < 1 || R > MAXR) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 987654321ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnd();
    deadline_s = budget;

    int have = 0, bestM = 0, bestnd = 0;
    static int bdi[MAXDARTS], bdj[MAXDARTS], bdv[MAXDARTS];
    M = mstart > Dd ? mstart : Dd;
    while (elapsed() < deadline_s) {
        NV = 2 * R * M;
        if (NV > MAXV) break;
        if (!try_M(30000, 1000000)) break;
        have = 1;
        bestM = M;
        bestnd = nd;
        memcpy(bdi, di, sizeof(int) * nd);
        memcpy(bdj, dj, sizeof(int) * nd);
        memcpy(bdv, dv, sizeof(int) * nd);
        M++;
    }
    if (!have) {
        printf("0 0\n");
        return 0;
    }
    int Mb = bestM;
    int n = 2 * R * Mb;
    int E = bestnd * Mb;
    printf("%d %d\n", n, E);
    for (int k = 0; k < bestnd; k++) {
        int i = bdi[k], j = bdj[k], v = bdv[k];
        for (int g = 0; g < Mb; g++)
            printf("%d %d\n", i * Mb + g, R * Mb + j * Mb + (g + v) % Mb);
    }
    return 0;
}
"""


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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
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
        m, edges, pl, lp, index, _pts = _pg_data(q)
        cands = [[]]
        if s >= 1:
            cands.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S = max(cands, key=len)
        if not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
# C drivers.
# ----------------------------------------------------------------------------

def _augment(n0, e0, d, D, seed, budget, timeout):
    """Run the augmentation C engine from the start graph (n0, e0) and parse its output."""
    text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                     stdin_graph=(n0, e0), timeout=timeout)
    return lib.parse_graph_text(text)


def _lift_run(d, D, R, mstart, seed, budget, timeout):
    """Run the voltage-lift annealer with R base vertices per side; returns (n, edges)."""
    text = lib.run_c(C_LIFT, [d, D, R, mstart, seed, f"{budget:.2f}"], timeout=timeout)
    return lib.parse_graph_text(text)


def _parent_build(d, D, seed, time_limit):
    """Stage 1: arc-extension starts plus augmentation. Returns a valid (n, edges)."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed * 7919 + d)

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))

    starts = []
    if D >= 3:
        starts.extend(_arc_extensions(d, t0 + 0.25 * time_limit, rng))
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            starts.append(gq)
    starts = [g for g in starts if lib.is_valid(g[0], g[1], d, D)]
    starts.sort(key=lambda g: -g[0])
    if lib.is_valid(fallback[0], fallback[1], d, D):
        starts.append(fallback)
    if not starts:
        return 1, []
    best = max(starts, key=lambda g: g[0])

    plan = starts[:3]
    for idx in range(len(plan) + 1):
        remaining = hard_end - time.monotonic()
        if remaining < 2.0:
            break
        if idx < len(plan):
            src = plan[idx]
            share = remaining / (len(plan) + 1 - idx)
        else:
            src = best
            share = remaining
        try:
            n1, e1 = _augment(src[0], src[1], d, D, seed * 31 + idx,
                              max(0.3, share - 1.0), share + 3.0)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best


def _lift_stage(d, D, seed, best, deadline):
    """Stage 2: voltage-lift annealing over several base sizes R. Keeps the best valid graph."""
    if d < 2 or D < 2:
        return best
    if best[0] >= lib.moore_bound(d, D):
        return best
    Rs = [2, 3, 1, 4]
    for idx, R in enumerate(Rs):
        remaining = deadline - time.monotonic()
        if remaining < 3.0:
            break
        share = remaining / (len(Rs) - idx)
        mstart = max(d, int(0.9 * best[0] / (2 * R)))
        if 2 * R * mstart > 4000:
            continue
        try:
            n1, e1 = _lift_run(d, D, R, mstart, seed * 97 + idx,
                               max(0.5, share - 1.5), share + 1.5)
        except Exception:
            continue
        if n1 > best[0] and lib.is_valid(n1, e1, d, D):
            best = (n1, e1)
    return best


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = lib.haar_graph(d, range(d))
    if not lib.is_valid(fallback[0], fallback[1], d, D):
        fallback = (1, [])

    try:
        best = _parent_build(d, D, seed, 0.35 * time_limit)
    except Exception:
        best = fallback
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback

    try:
        best = _lift_stage(d, D, seed, best, t0 + 0.80 * time_limit)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
