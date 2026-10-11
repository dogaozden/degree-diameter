"""Combined diameter-3 bipartite search.

Python builds the strongest closed-form or arc-extended starts it can (Moore graph, Araujo-Pardo-Lopez
when applicable, arc-extended projective planes, and W(q) for D >= 4), validates them, and hands the best
one to a C engine. The C engine keeps the graph valid at all times. It adds vertices with a randomized
multi-restart greedy cover (a new vertex on one side is joined to a set T on the other side, and every
existing vertex must lie within distance D-1 of T). When additions stall, it applies degree-preserving
double-edge swaps, keeping a swap only if the graph still has diameter <= D.
"""
import itertools
import random
import time

import lib

C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
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
static uint64_t RA[MAXN * WORDS], RB[MAXN * WORDS];
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

static double elapsed(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) return 1;
    return 0;
}

static void del_half(int u, int v) {
    for (int i = 0; i < deg[u]; i++)
        if (adj[u][i] == v) {
            adj[u][i] = adj[u][--deg[u]];
            return;
        }
}

static void add_edge(int u, int v) {
    adj[u][deg[u]++] = v;
    adj[v][deg[v]++] = u;
}

static void del_edge(int u, int v) {
    del_half(u, v);
    del_half(v, u);
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

/* Full diameter check by bitset propagation over Dist rounds. */
static int full_ok(void) {
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < Dist; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *s = cur + (size_t)adj[v][k] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(s[w]);
        if (c != N) return 0;
    }
    return 1;
}

/* Greedy cover of all vertices by balls of chosen vertices on side != X. */
static int greedy_cover(int X, int *T, int *ntp, int noise) {
    uint64_t U[WORDS];
    static int sel[MAXN];
    int nt = 0, covered = 0;
    for (int i = 0; i < W; i++) U[i] = ~0ULL;
    if (N & 63) U[W - 1] = (1ULL << (N & 63)) - 1ULL;
    memset(sel, 0, sizeof(int) * (size_t)N);
    for (;;) {
        int left = 0;
        for (int i = 0; i < W; i++) left += popc(U[i]);
        if (left == 0) { covered = 1; break; }
        if (nt >= Dd) break;
        int best = -1;
        long bestsc = -1;
        for (int v = 0; v < N; v++) {
            if (side[v] == X || deg[v] >= Dd || sel[v]) continue;
            int g = 0;
            for (int i = 0; i < W; i++) g += popc(ball[v][i] & U[i]);
            if (g <= 0) continue;
            long sc = (long)g * 4096 + rndint(noise);
            if (sc > bestsc) { bestsc = sc; best = v; }
        }
        if (best < 0) break;
        sel[best] = 1;
        T[nt++] = best;
        for (int i = 0; i < W; i++) U[i] &= ~ball[best][i];
    }
    *ntp = nt;
    return covered;
}

/* Add one vertex on side X, using the smallest cover found over several randomized greedy runs. */
static int try_add(int X, int restarts) {
    if (N + 1 >= MAXN) return 0;
    int bestT[MAXDEG];
    int bestn = 1 << 30;
    for (int r = 0; r < restarts; r++) {
        int T[MAXDEG];
        int nt = 0;
        int cov = greedy_cover(X, T, &nt, r == 0 ? 1024 : 4000);
        if (cov && nt >= 1 && nt < bestn) {
            bestn = nt;
            memcpy(bestT, T, sizeof(int) * (size_t)nt);
        }
    }
    if (bestn == (1 << 30)) return 0;
    int x = N;
    side[x] = X;
    deg[x] = bestn;
    for (int k = 0; k < bestn; k++) {
        int t = bestT[k];
        adj[x][k] = t;
        adj[t][deg[t]++] = x;
    }
    N++;
    W = (N + 63) / 64;
    recompute_balls();
    return 1;
}

static int pick_side(int s) {
    for (int tries = 0; tries < 2000; tries++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Random degree-preserving double-edge swaps, each kept only if the diameter stays <= Dist. */
static void kick(int K) {
    int changed = 0;
    for (int it = 0; it < K; it++) {
        int a = pick_side(0), c = pick_side(0);
        if (a < 0 || c < 0 || a == c) continue;
        int b = adj[a][rndint(deg[a])];
        int e = adj[c][rndint(deg[c])];
        if (b == e || has_edge(a, e) || has_edge(c, b)) continue;
        del_edge(a, b);
        del_edge(c, e);
        add_edge(a, e);
        add_edge(c, b);
        if (full_ok()) {
            changed = 1;
        } else {
            del_edge(a, e);
            del_edge(c, b);
            add_edge(a, b);
            add_edge(c, e);
        }
    }
    if (changed) recompute_balls();
}

static void complete_bipartite(void) {
    N = 2 * Dd;
    W = (N + 63) / 64;
    for (int v = 0; v < N; v++) { deg[v] = 0; side[v] = v >= Dd; }
    for (int a = 0; a < Dd; a++)
        for (int b = 0; b < Dd; b++) add_edge(a, Dd + b);
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
    for (int i = 0; i < 10; i++) rnd();

    double t_end = elapsed() + budget;
    if (Dd < 1 || Dist < 2) {
        printf("0 0\n");
        return 0;
    }

    int n = 0, m = 0;
    if (scanf("%d %d", &n, &m) != 2) { n = 0; m = 0; }
    if (n <= 0) {
        complete_bipartite();
    } else {
        if (n > MAXN - 2) { printf("0 0\n"); return 0; }
        N = n;
        W = (N + 63) / 64;
        for (int v = 0; v < N; v++) deg[v] = 0;
        int ok = 1;
        for (int e = 0; e < m && ok; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
            if (u < 0 || v < 0 || u >= N || v >= N || u == v) { ok = 0; break; }
            if (deg[u] >= Dd || deg[v] >= Dd || has_edge(u, v)) { ok = 0; break; }
            add_edge(u, v);
        }
        if (ok) {
            static int qq[MAXN];
            for (int v = 0; v < N; v++) side[v] = -1;
            for (int s = 0; s < N && ok; s++) {
                if (side[s] >= 0) continue;
                side[s] = 0;
                int head = 0, t = 0;
                qq[t++] = s;
                while (head < t && ok) {
                    int u = qq[head++];
                    for (int k = 0; k < deg[u]; k++) {
                        int v = adj[u][k];
                        if (side[v] < 0) {
                            side[v] = 1 - side[u];
                            qq[t++] = v;
                        } else if (side[v] == side[u]) {
                            ok = 0;
                            break;
                        }
                    }
                }
            }
        }
        if (ok && !full_ok()) ok = 0;
        if (!ok) {
            printf("0 0\n");
            return 0;
        }
    }

    recompute_balls();
    int fails = 0;
    while (elapsed() < t_end && N < MAXN - 2) {
        if (try_add(rndint(2), 8)) {
            fails = 0;
        } else {
            fails++;
            if (fails >= 30) {
                kick(150);
                fails = 0;
            }
        }
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


# ----------------------------------------------------------------------------
# Projective-plane based starts (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


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
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG(2,q) incidence plus, per element P of S, a new A-vertex on the lines through P
    and a new B-vertex on the points of line P. Diameter 3, max degree q+1+s."""
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
    """(n, edges) candidates from arc-extended projective planes, for each prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        try:
            m, edges, pl, lp, index = _pg_data(q)
            cands = [[], _greedy_arc(m, s, pl, lp, rng, 40, deadline)]
            if s >= 2:
                cs = _conic_set(q, index, lib.GF(q))
                if _loads_ok(cs, s, m, pl, lp):
                    cands.append(cs)
            S = max(cands, key=len)
            if S and _loads_ok(S, s, m, pl, lp):
                out.append(_arc_graph(m, edges, pl, lp, S))
        except Exception:
            continue
    return out


def known_start(d, D):
    """Closed-form graph for (d, D) when one is known, else None."""
    try:
        if D == 3 and lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    except Exception:
        return None
    return None


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
            try:
                return _gq_w(q)
            except Exception:
                return None
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        consider(known_start(d, D))
        rng = random.Random(seed * 7919 + d)
        for cand in sorted(_arc_extensions(d, t0 + 0.2 * time_limit, rng), key=lambda g: -g[0]):
            consider(cand)
    if D >= 4 and time.monotonic() < t0 + 0.25 * time_limit:
        consider(_best_gq(d))

    # Hand the best construction to C, which grows it while keeping it valid.
    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget > 0.5 and best[0] < lib.moore_bound(d, D):
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                             stdin_graph=best, timeout=budget + 10)
            n, e = lib.parse_graph_text(text)
            consider((n, e))
        except (RuntimeError, ValueError):
            pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
