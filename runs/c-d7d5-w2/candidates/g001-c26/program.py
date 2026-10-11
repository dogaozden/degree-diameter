import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C search engine: tabu search over the connection set of a bi-Cayley graph.
#
# Group G = Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b), |G| = G.
# Graph on 2G vertices: A_g (index g) and B_h (index G + h). Each of the DEG
# distinct voltages s_l gives the edges A_g -- B_{g*s_l} for all g.
# Left multiplication by any group element is an automorphism, so the graph
# is vertex-transitive on each side. Checking the BFS from A_e and B_e up to
# depth DIAM decides the diameter exactly.
#
# Cost = number of vertices not reached within DIAM from A_e plus from B_e.
# Cost 0 means the graph is valid.
#
# Search: tabu search. Each step samples random (layer, new voltage) moves,
# applies the best non-tabu move (aspiration if it beats the global best),
# and marks the displaced voltage as tabu for that layer. After a stall, the
# search restarts, either from random voltages or from the best state with
# two layers perturbed.
#
# Usage: prog d D m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXDEG 64
#define BIG (1 << 30)
#define SAMPLES 700
#define STALL_LIMIT 250
#define TENURE_BASE 4

static int DEG, DIAM, MM, K2, G, N, R;
static int POWR[64];
static int *S, *Sinv, *bestS, *tabu, *cur_buf, *nxt_buf;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* (a,b)*(c,d) = (a + r^b c, b + d) */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + d) % K2);
}

/* inverse of (a,b) is (-r^(-b) a, -b) */
static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)POWR[nb] * a) % MM;
    int ia = (int)((MM - t) % MM);
    return ia * K2 + nb;
}

static int inS_upto(int v, int n) {
    for (int i = 0; i < n; i++) if (S[i] == v) return 1;
    return 0;
}

/* Unreached vertices from A_e and B_e within DIAM steps. */
static int cost_fn(const int *s, const int *si) {
    int total = 0;
    for (int rep = 0; rep < 2; rep++) {
        int src = (rep == 0) ? 0 : G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *c = cur_buf, *x = nxt_buf;
        int fn = 1, reached = 1;
        c[0] = src;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = c[q];
                if (u < G) {
                    for (int l = 0; l < DEG; l++) {
                        int v = G + gmul(u, s[l]);
                        if (vis[v] != stamp) { vis[v] = stamp; x[nn++] = v; }
                    }
                } else {
                    int h = u - G;
                    for (int l = 0; l < DEG; l++) {
                        int v = gmul(h, si[l]);
                        if (vis[v] != stamp) { vis[v] = stamp; x[nn++] = v; }
                    }
                }
            }
            reached += nn;
            int *tmp = c; c = x; x = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage: prog d D m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    R = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DEG > MAXDEG || DIAM < 1 || MM < 1 || K2 < 1 || K2 > 60 || R < 0) {
        printf("0 0\n");
        return 0;
    }
    R %= MM;
    if (gcd_int(R, MM) != 1) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * R % MM);
    if (((long long)POWR[K2 - 1] * R) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    if (G < DEG || G > 100000) { printf("0 0\n"); return 0; }
    N = 2 * G;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    S = calloc(DEG, sizeof(int));
    Sinv = calloc(DEG, sizeof(int));
    bestS = calloc(DEG, sizeof(int));
    tabu = calloc((size_t)DEG * G, sizeof(int));
    vis = calloc(N, sizeof(uint32_t));
    cur_buf = calloc(N, sizeof(int));
    nxt_buf = calloc(N, sizeof(int));
    if (!S || !Sinv || !bestS || !tabu || !vis || !cur_buf || !nxt_buf) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIG;

    while (!found && elapsed(t0) < slice) {
        if (bestCost < BIG && rnd01() < 0.5) {
            /* Perturb the best state in two layers. */
            memcpy(S, bestS, sizeof(int) * DEG);
            for (int q = 0; q < 2; q++) {
                int l = rndint(DEG);
                int v;
                do { v = rndint(G); } while (inS_upto(v, DEG));
                S[l] = v;
            }
        } else {
            /* Random distinct voltages. */
            for (int l = 0; l < DEG; l++) {
                int v;
                do { v = rndint(G); } while (inS_upto(v, l));
                S[l] = v;
            }
        }
        for (int l = 0; l < DEG; l++) Sinv[l] = ginv(S[l]);

        int cc = cost_fn(S, Sinv);
        if (cc < bestCost) { bestCost = cc; memcpy(bestS, S, sizeof(int) * DEG); }
        memset(tabu, 0, sizeof(int) * (size_t)DEG * G);

        int stall = 0, step = 0;
        int localBest = cc;
        while (cc > 0 && stall < STALL_LIMIT) {
            if ((step & 15) == 0 && elapsed(t0) >= slice) break;
            step++;
            int ml = -1, mx = -1, mc = BIG, nt = 0;
            for (int k = 0; k < SAMPLES; k++) {
                int l = rndint(DEG);
                int x = rndint(G);
                if (inS_upto(x, DEG)) continue;
                int old = S[l];
                S[l] = x; Sinv[l] = ginv(x);
                int c = cost_fn(S, Sinv);
                S[l] = old; Sinv[l] = ginv(old);
                if (tabu[l * G + x] > step && c >= bestCost) continue;
                if (c < mc) { mc = c; ml = l; mx = x; nt = 1; }
                else if (c == mc) {
                    nt++;
                    if (rndint(nt) == 0) { ml = l; mx = x; }
                }
            }
            if (ml < 0) { stall++; continue; }
            int old = S[ml];
            tabu[ml * G + old] = step + TENURE_BASE + rndint(DEG + 1);
            S[ml] = mx; Sinv[ml] = ginv(mx);
            cc = mc;
            if (cc < bestCost) { bestCost = cc; memcpy(bestS, S, sizeof(int) * DEG); }
            if (cc < localBest) { localBest = cc; stall = 0; }
            else stall++;
        }
        if (bestCost == 0) found = 1;
    }

    if (found && bestCost == 0) {
        printf("%d %d\n", N, DEG * G);
        for (int l = 0; l < DEG; l++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", g, G + gmul(g, bestS[l]));
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions (unchanged from the parent).
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
# Group sampling and the search driver.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 3, 4, 6, 7, 8, 9, 12, 14, 18, 21, 24, 27, 28])
        m = max(2, -(-target // k2))
        r = 1  # r = 1 is always valid
        if k2 > 1:
            cands = [c for c in range(1, m)
                     if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        return m, k2, r
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.92 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ap = lib.araujo_lopez_graph(d - 2)
                consider(ap[0], ap[1])
            except (ValueError, RuntimeError):
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: tabu search over the connection sets of bi-Cayley graphs.
    # A bi-Cayley graph on group G has 2|G| vertices, so each target group
    # order is chosen just above best/2. Any success is a strict improvement.
    errors = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 20.0)
        base = best[0] // 2
        target = base + 1 + rng.randrange(0, max(3, base // 25))
        grp = _sample_group(target, rng)
        if grp is None:
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                C_SOURCE,
                [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 10.0,
            )
        except RuntimeError:
            errors += 1
            if errors >= 3:
                break
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
