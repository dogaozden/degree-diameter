import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New target search: voltage lifts over semidirect groups Z_m x| Z_k2, with the
# annealing done in C. The base is K left and K right vertices joined by DEG
# random permutation matchings (a DEG-regular bipartite multigraph). Each dart
# carries a voltage in the group G = m*k2. The lift has 2*K*G vertices and
# degree DEG. Cost = number of vertex pairs at distance > DIAM. Moves change
# one or two voltages. On cost 0 the lift is printed.
# ----------------------------------------------------------------------------

VOLT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXV 4096
#define WMAX ((MAXV + 63) / 64)
#define DMAX 16
#define MAXK 8
#define MAXD (MAXK * DMAX)
#define MAXG 2048
#define STALL 2500

static int DIAM, DEG, K, MOD, K2, RR, G;
static int *MT;
static int nd, dU[MAXD], dV[MAXD], dG[MAXD];
static int adjv[MAXV][DMAX];
static int deg[MAXV];
static uint64_t RA[MAXV * WMAX], RB[MAXV * WMAX];
static uint64_t rs = 1;
static long long pwv[64];

static uint64_t nextr(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rnd(int k) { return (int)(nextr() % (uint64_t)k); }

static double rnd01(void) {
    return (double)(nextr() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adjv[a][i] == b) return 1;
    return 0;
}

/* Build the lift of the current darts; returns its order 2*K*G. */
static int build_lift(void) {
    int n = 2 * K * G;
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int j = 0; j < nd; j++) {
        int u = dU[j], v = dV[j], g = dG[j];
        for (int x = 0; x < G; x++) {
            int a = u * G + x;
            int b = v * G + MT[x * G + g];
            if (deg[a] >= DEG || deg[b] >= DEG) continue;
            if (has_edge(a, b)) continue;
            adjv[a][deg[a]++] = b;
            adjv[b][deg[b]++] = a;
        }
    }
    return n;
}

static long long eval_cost(int n) {
    int W = (n + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB, *tmp;
    memset(RA, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++)
        cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                uint64_t *t = cur + (size_t)adjv[v][i] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < n; v++) {
        uint64_t *s = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(s[w]);
        bad += n - cnt;
    }
    return bad / 2;
}

static long long evaluate(void) {
    int n = build_lift();
    return eval_cost(n);
}

static void init_darts(void) {
    int perm[MAXK];
    nd = 0;
    for (int j = 0; j < DEG; j++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int t = rnd(i + 1);
            int x = perm[i];
            perm[i] = perm[t];
            perm[t] = x;
        }
        for (int i = 0; i < K; i++) {
            dU[nd] = i;
            dV[nd] = K + perm[i];
            dG[nd] = rnd(G);
            nd++;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    DIAM = atoi(argv[1]);
    DEG = atoi(argv[2]);
    K = atoi(argv[3]);
    MOD = atoi(argv[4]);
    K2 = atoi(argv[5]);
    RR = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double budget = atof(argv[8]);
    if (DIAM < 1 || DEG < 1 || DEG > DMAX || K < 1 || K > MAXK ||
        MOD < 1 || K2 < 1 || K2 > 12 || budget <= 0) {
        printf("0 0\n");
        return 0;
    }
    G = MOD * K2;
    if (G > MAXG || 2 * K * G > MAXV) {
        printf("0 0\n");
        return 0;
    }
    rs = seed * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) nextr();

    pwv[0] = 1 % MOD;
    for (int b = 1; b < K2; b++) pwv[b] = (pwv[b - 1] * (RR % MOD)) % MOD;

    MT = (int *)malloc(sizeof(int) * (size_t)G * (size_t)G);
    if (!MT) {
        printf("0 0\n");
        return 0;
    }
    /* Semidirect product: (a,b)*(c,d) = (a + r^b c, b + d), element coded a*K2+b. */
    for (int x = 0; x < G; x++) {
        int a = x / K2, b = x % K2;
        for (int y = 0; y < G; y++) {
            int c = y / K2, d = y % K2;
            MT[x * G + y] = (int)(((a + pwv[b] * c) % MOD) * K2 + (b + d) % K2);
        }
    }

    init_darts();
    long long cur = evaluate();
    long long best = cur;
    int found = (cur == 0);
    double t0 = (double)clock() / CLOCKS_PER_SEC;
    long stall = 0;

    while (!found) {
        double frac = ((double)clock() / CLOCKS_PER_SEC - t0) / budget;
        if (frac >= 1.0) break;
        if (stall > STALL) {
            for (int j = 0; j < nd; j++) dG[j] = rnd(G);
            cur = evaluate();
            best = cur;
            stall = 0;
            if (cur == 0) {
                found = 1;
                break;
            }
            continue;
        }
        double T = 0.3 + 2.0 * (1.0 - frac);
        int j1 = rnd(nd);
        int old1 = dG[j1];
        dG[j1] = rnd(G);
        int j2 = -1, old2 = 0;
        if (rnd01() < 0.3) {
            j2 = rnd(nd);
            old2 = dG[j2];
            dG[j2] = rnd(G);
        }
        long long c2 = evaluate();
        double dl = (double)(c2 - cur);
        if (dl <= 0 || rnd01() < exp(-dl / T)) {
            cur = c2;
        } else {
            if (j2 >= 0) dG[j2] = old2;
            dG[j1] = old1;
        }
        if (cur < best) {
            best = cur;
            stall = 0;
        } else {
            stall++;
        }
        if (cur == 0) found = 1;
    }

    if (!found) {
        printf("0 0\n");
        free(MT);
        return 0;
    }
    int n = build_lift();
    long long em = 0;
    for (int v = 0; v < n; v++) em += deg[v];
    printf("%d %lld\n", n, em / 2);
    for (int v = 0; v < n; v++)
        for (int i = 0; i < deg[v]; i++)
            if (v < adjv[v][i]) printf("%d %d\n", v, adjv[v][i]);
    free(MT);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q): degree q+1, diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _colors(n, edges):
    """Two-colouring of a bipartite graph given by an edge list."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for w in adj[u]:
                if col[w] == -1:
                    col[w] = 1 - col[u]
                    st.append(w)
    return col


def _saturate(n, edges, d, rng):
    """Add opposite-side edges between deficient vertices (keeps bipartiteness; distances only shrink)."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    col = _colors(n, edges)
    left = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, edges


def _sample_params(G, rng):
    """Random (m, k2, r) with m * k2 = G describing Z_m x| Z_k2, or None."""
    opts = []
    for k2 in range(1, min(12, G) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for _ in range(40):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
                break
    return rng.choice(opts) if opts else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Calibration: D = 3 with d - 1 a prime power is the Moore-optimal incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n0, e0, d, D):
            return n0, e0

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # D = 3: projective plane of the largest prime power q with q + 1 <= d.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    # D >= 4: generalized quadrangle W(q), saturated with the spare degree.
    if D >= 4 and d >= 5:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            consider(*_saturate(gq[0], gq[1], d, rng))

    # Main new search: voltage lifts over semidirect groups, annealed in C.
    # Each attempt targets a group order just above the current best / (2K).
    tl_end = start + 0.9 * tl - 2.0
    if 2 <= d <= 16 and D >= 2:
        K_list = [1, 2, 3, 4, 5, 6]
        attempt = 0
        while True:
            remaining = tl_end - time.monotonic()
            if remaining < 1.0:
                break
            K = K_list[attempt % len(K_list)]
            attempt += 1
            G = best_n // (2 * K) + 1 + rng.randrange(2)
            if G < 2 or K * G > 2048:
                continue
            par = _sample_params(G, rng)
            if par is None:
                continue
            m, k2, r = par
            budget = min(remaining - 0.5, max(2.0, 0.08 * tl))
            if budget < 0.5:
                break
            try:
                out = lib.run_c(VOLT_SOURCE,
                                [D, d, K, m, k2, r, seed * 131 + attempt, f"{budget:.2f}"],
                                stdin_graph=None, timeout=budget + 6.0)
                consider(*lib.parse_graph_text(out))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
