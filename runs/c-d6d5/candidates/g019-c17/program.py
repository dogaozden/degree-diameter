import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: insert-and-repair search on bipartite graphs.
#
# State: a bipartite graph with max degree DEG, stored as an edge list (ea, eb),
# where ea is the A endpoint and eb the B endpoint of each edge. The only move
# is a double-edge swap (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keeps every
# degree and the bipartition. Cost = number of unordered vertex pairs at
# distance > DIAM, computed with bitset BFS.
#
# Loop:
#   1. Start from a valid graph (a given start, or a random regular bipartite
#      graph repaired by annealing).
#   2. Drift: random neutral swaps that keep the graph valid.
#   3. Grow: remove DEG edges (a_i,b_i) with distinct endpoints, add a new A
#      vertex x joined to every b_i and a new B vertex y joined to every a_i.
#      This keeps all degrees at most DEG and adds 2 vertices.
#   4. Anneal swaps to cost 0. On success, the graph is larger and valid; on
#      failure, restore the snapshot and retry.
#
# Output is the largest valid graph found. If nothing valid is found, it
# prints "0 0" and the Python side keeps its fallback.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define DRIFT 200
#define ANN 1500
#define T_HI 3.0
#define T_LO 0.15

static int DEG, DIAM;
static double DEADLINE;
static struct timespec T0;
static uint64_t rs[2];

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int N, M, MAXN, MAXM, WM;
static int *deg, *nb, *ea, *eb;
static uint64_t *bufA, *bufB;

static int sN, sM;
static int *s_deg, *s_nb, *s_ea, *s_eb;

static int bestN = 0, bestM = 0;
static int *b_ea, *b_eb;

static int has_edge(int a, int b) {
    const int *p = nb + (size_t)a * DEG;
    for (int k = 0; k < deg[a]; k++)
        if (p[k] == b) return 1;
    return 0;
}

static void repl(int v, int old, int nw) {
    int *p = nb + (size_t)v * DEG;
    for (int k = 0; k < deg[v]; k++)
        if (p[k] == old) { p[k] = nw; return; }
}

static void add_nb(int v, int w) {
    nb[(size_t)v * DEG + deg[v]] = w;
    deg[v]++;
}

static void rem_nb(int v, int w) {
    int *p = nb + (size_t)v * DEG;
    for (int k = 0; k < deg[v]; k++)
        if (p[k] == w) {
            p[k] = p[deg[v] - 1];
            deg[v]--;
            return;
        }
}

/* Swap edges e1=(a1,b1), e2=(a2,b2) into (a1,b2), (a2,b1). Applying it again undoes it. */
static void do_swap(int e1, int e2) {
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
    ea[e1] = a1; eb[e1] = b2;
    ea[e2] = a2; eb[e2] = b1;
}

static int swap_ok(int e1, int e2) {
    if (e1 == e2) return 0;
    int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    return 1;
}

static int pc64(uint64_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs count). */
static long long bad_count(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++)
        cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            memcpy(o, cur + (size_t)v * W, sizeof(uint64_t) * (size_t)W);
            const int *p = nb + (size_t)v * DEG;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *q = cur + (size_t)p[k] * W;
                for (int w = 0; w < W; w++) o[w] |= q[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long unc = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *o = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += pc64(o[w]);
        unc += N - c;
    }
    return unc / 2;
}

static long long anneal(int iters, long long cur) {
    if (cur == 0) return 0;
    for (int it = 0; it < iters; it++) {
        if ((it & 15) == 0 && elapsed() > DEADLINE) break;
        double T = T_HI * pow(T_LO / T_HI, (double)it / (double)iters);
        int e1 = rnd_int(M), e2 = rnd_int(M);
        if (!swap_ok(e1, e2)) continue;
        do_swap(e1, e2);
        long long c2 = bad_count();
        if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / T)) {
            cur = c2;
            if (cur == 0) return 0;
        } else {
            do_swap(e1, e2);
        }
    }
    return cur;
}

/* Neutral moves on a valid graph: keep only swaps that stay valid. */
static void drift(int steps) {
    for (int s = 0; s < steps; s++) {
        if ((s & 31) == 0 && elapsed() > DEADLINE) break;
        int e1 = rnd_int(M), e2 = rnd_int(M);
        if (!swap_ok(e1, e2)) continue;
        do_swap(e1, e2);
        if (bad_count() != 0) do_swap(e1, e2);
    }
}

static void snapshot(void) {
    sN = N;
    sM = M;
    memcpy(s_deg, deg, sizeof(int) * (size_t)N);
    memcpy(s_nb, nb, sizeof(int) * (size_t)N * DEG);
    memcpy(s_ea, ea, sizeof(int) * (size_t)M);
    memcpy(s_eb, eb, sizeof(int) * (size_t)M);
}

static void restore(void) {
    N = sN;
    M = sM;
    memcpy(deg, s_deg, sizeof(int) * (size_t)N);
    memcpy(nb, s_nb, sizeof(int) * (size_t)N * DEG);
    memcpy(ea, s_ea, sizeof(int) * (size_t)M);
    memcpy(eb, s_eb, sizeof(int) * (size_t)M);
}

static void save_best(void) {
    bestN = N;
    bestM = M;
    memcpy(b_ea, ea, sizeof(int) * (size_t)M);
    memcpy(b_eb, eb, sizeof(int) * (size_t)M);
}

/* Remove DEG edges with distinct endpoints, add two new vertices x (A) and y (B). */
static int grow(void) {
    if (N + 2 > MAXN || M + DEG > MAXM) return 0;
    int sel[64], Aa[64], Bb[64], ns = 0;
    for (int tries = 0; tries < 5000 && ns < DEG; tries++) {
        int e = rnd_int(M), ok = 1;
        for (int i = 0; i < ns; i++)
            if (sel[i] == e || ea[sel[i]] == ea[e] || eb[sel[i]] == eb[e]) { ok = 0; break; }
        if (ok) sel[ns++] = e;
    }
    if (ns < DEG) return 0;
    for (int i = 0; i < ns; i++) { Aa[i] = ea[sel[i]]; Bb[i] = eb[sel[i]]; }
    for (int i = 0; i < ns; i++) { rem_nb(Aa[i], Bb[i]); rem_nb(Bb[i], Aa[i]); }
    /* Sort selected indices descending, then delete by swapping with the last edge. */
    for (int i = 1; i < ns; i++) {
        int x = sel[i], j = i - 1;
        while (j >= 0 && sel[j] < x) { sel[j + 1] = sel[j]; j--; }
        sel[j + 1] = x;
    }
    for (int i = 0; i < ns; i++) {
        int idx = sel[i];
        ea[idx] = ea[M - 1];
        eb[idx] = eb[M - 1];
        M--;
    }
    int x = N, y = N + 1;
    deg[x] = 0;
    deg[y] = 0;
    N += 2;
    for (int i = 0; i < ns; i++) {
        add_nb(x, Bb[i]);
        add_nb(Bb[i], x);
        add_nb(Aa[i], y);
        add_nb(y, Aa[i]);
        ea[M] = x; eb[M] = Bb[i]; M++;
        ea[M] = Aa[i]; eb[M] = y; M++;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [K0]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int K0 = argc > 5 ? atoi(argv[5]) : 0;
    if (DEG < 2 || DEG > 60 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0) { n0 = 0; m0 = 0; }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &iu[i], &iv[i]) != 2) { m0 = i; break; }
    }

    int base;
    if (n0 > 0) {
        base = n0;
    } else {
        if (K0 < DEG + 1) K0 = DEG + 1;
        base = 2 * K0;
    }
    MAXN = base + 2500;
    MAXM = MAXN * DEG;
    WM = (MAXN + 63) / 64;

    int *side = malloc(sizeof(int) * (size_t)MAXN);
    int *q = malloc(sizeof(int) * (size_t)MAXN);
    deg = calloc((size_t)MAXN, sizeof(int));
    nb = malloc(sizeof(int) * (size_t)MAXN * DEG);
    ea = malloc(sizeof(int) * (size_t)MAXM);
    eb = malloc(sizeof(int) * (size_t)MAXM);
    bufA = malloc(sizeof(uint64_t) * (size_t)MAXN * WM);
    bufB = malloc(sizeof(uint64_t) * (size_t)MAXN * WM);
    s_deg = malloc(sizeof(int) * (size_t)MAXN);
    s_nb = malloc(sizeof(int) * (size_t)MAXN * DEG);
    s_ea = malloc(sizeof(int) * (size_t)MAXM);
    s_eb = malloc(sizeof(int) * (size_t)MAXM);
    b_ea = malloc(sizeof(int) * (size_t)MAXM);
    b_eb = malloc(sizeof(int) * (size_t)MAXM);

    M = 0;
    if (n0 > 0) {
        N = n0;
        int ok = 1;
        for (int v = 0; v < N; v++) deg[v] = 0;
        for (int i = 0; i < m0 && ok; i++) {
            int u = iu[i], v = iv[i];
            if (u < 0 || v < 0 || u >= N || v >= N || u == v ||
                deg[u] >= DEG || deg[v] >= DEG || has_edge(u, v)) ok = 0;
            else { add_nb(u, v); add_nb(v, u); }
        }
        for (int v = 0; v < N; v++) side[v] = -1;
        for (int s = 0; s < N && ok; s++) {
            if (side[s] >= 0) continue;
            side[s] = 0;
            int qh = 0, qt = 0;
            q[qt++] = s;
            while (qh < qt && ok) {
                int u = q[qh++];
                for (int k = 0; k < deg[u]; k++) {
                    int w = nb[(size_t)u * DEG + k];
                    if (side[w] < 0) { side[w] = 1 - side[u]; q[qt++] = w; }
                    else if (side[w] == side[u]) { ok = 0; break; }
                }
            }
        }
        if (!ok) {
            printf("0 0\n");
            return 0;
        }
        for (int i = 0; i < m0; i++) {
            int u = iu[i], v = iv[i];
            if (side[u] == 0) { ea[M] = u; eb[M] = v; }
            else { ea[M] = v; eb[M] = u; }
            M++;
        }
    } else {
        N = 2 * K0;
        int *perm = malloc(sizeof(int) * (size_t)K0);
        int ok = 1;
        for (int l = 0; l < DEG && ok; l++) {
            int tries = 0, good = 0;
            while (!good && tries < 200000) {
                tries++;
                for (int i = 0; i < K0; i++) perm[i] = i;
                for (int i = K0 - 1; i > 0; i--) {
                    int j = rnd_int(i + 1);
                    int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
                }
                good = 1;
                for (int i = 0; i < K0; i++)
                    if (has_edge(i, K0 + perm[i])) { good = 0; break; }
            }
            if (!good) { ok = 0; break; }
            for (int i = 0; i < K0; i++) {
                add_nb(i, K0 + perm[i]);
                add_nb(K0 + perm[i], i);
                ea[M] = i; eb[M] = K0 + perm[i]; M++;
            }
        }
        free(perm);
        if (!ok) {
            printf("0 0\n");
            return 0;
        }
    }

    long long cost = bad_count();
    while (cost > 0 && elapsed() < DEADLINE)
        cost = anneal(20000, cost);

    if (cost == 0) {
        save_best();
        while (elapsed() < DEADLINE) {
            drift(DRIFT);
            snapshot();
            if (!grow()) continue;
            long long c = bad_count();
            c = anneal(ANN, c);
            if (c == 0) {
                if (N > bestN) save_best();
            } else {
                restore();
            }
        }
    }

    if (bestN > 0) {
        printf("%d %d\n", bestN, bestM);
        for (int i = 0; i < bestM; i++)
            printf("%d %d\n", b_ea[i], b_eb[i]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
# Driver: baselines in Python, then the C insert-and-repair search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    # Reserve time for compile-free overhead, parsing and validation.
    remaining = 0.9 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
        # Random start size per side; the C side repairs it to diameter D, then grows it.
        k0 = max(d + 1, moore // 6)
        # Use the best structured baseline as the start only if it is large enough.
        use_stdin = best_n > 2 * k0
        stdin = best if use_stdin else None
        args = [d, D, seed, f"{remaining:.2f}", 0 if use_stdin else k0]
        try:
            out = lib.run_c(C_SOURCE, args, stdin_graph=stdin, timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
