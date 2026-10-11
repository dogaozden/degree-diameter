import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New search: Haar graphs H(G, S) over small groups G = Z_m x|_r Z_k2.
#
# A Haar graph has parts A_x and B_y (x, y in G), and A_x ~ B_{x*s} for s in S,
# |S| = DEG. It is bipartite and DEG-regular with 2|G| vertices. Left
# multiplication is an automorphism, so BFS from A_identity and B_identity
# decides the diameter exactly. WLOG the identity is in S (right-translate),
# so S[0] = identity is fixed.
#
# The search is simulated annealing over the elements of S, with an
# excess-distance cost (zero iff diameter <= DIAM). The engine sweeps group
# orders upward from the current best half-order, trying several groups per
# order, so a success at order n gives a graph with 2n vertices.
#
# Usage: prog DEG DIAM m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXNG 3000
#define BIGCOST (1 << 30)

static int DEG, DIAM, MM, K2, NG, LMAX, UNREACH_W;
static int *MT, *INV, *S, *SI, *BS, *fr, *nx;
static char *inS;
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

/* Excess-distance cost of the Haar graph H(G, S), from A_0 and from B_0. */
static int cost_fn(void) {
    int total = 0;
    int N2 = 2 * NG;
    for (int src_i = 0; src_i < 2; src_i++) {
        int src = (src_i == 0) ? 0 : NG;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N2);
            stamp = 0;
        }
        stamp++;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        vis[src] = stamp;
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                if (u < NG) {
                    const int *row = MT + (size_t)u * NG;
                    for (int t = 0; t < DEG; t++) {
                        int v = NG + row[S[t]];
                        if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                    }
                } else {
                    const int *row = MT + (size_t)(u - NG) * NG;
                    for (int t = 0; t < DEG; t++) {
                        int v = row[SI[t]];
                        if (vis[v] != stamp) { vis[v] = stamp; nxt[nn++] = v; }
                    }
                }
            }
            reached += nn;
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N2 - reached) * UNREACH_W;
    }
    return total;
}

static void random_S(void) {
    memset(inS, 0, (size_t)NG);
    S[0] = 0;
    inS[0] = 1;
    for (int t = 1; t < DEG; t++) {
        int s;
        do { s = rndint(NG); } while (inS[s]);
        S[t] = s;
        inS[s] = 1;
    }
    for (int t = 0; t < DEG; t++) SI[t] = INV[S[t]];
}

static void load_S(const int *src) {
    memset(inS, 0, (size_t)NG);
    for (int t = 0; t < DEG; t++) {
        S[t] = src[t];
        inS[S[t]] = 1;
        SI[t] = INV[S[t]];
    }
}

int main(int argc, char **argv) {
    if (argc < 8) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    MM = atoi(argv[3]);
    K2 = atoi(argv[4]);
    int r = atoi(argv[5]);
    uint64_t seed = strtoull(argv[6], NULL, 10);
    double slice = atof(argv[7]);

    if (DEG < 1 || DIAM < 1 || MM < 1 || K2 < 1) { printf("0 0\n"); return 0; }
    long long ng = (long long)MM * K2;
    if (ng < DEG || ng > MAXNG) { printf("0 0\n"); return 0; }
    NG = (int)ng;
    LMAX = DIAM + 3;
    UNREACH_W = LMAX - DIAM + 2;

    int *POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    MT = malloc(sizeof(int) * (size_t)NG * NG);
    INV = malloc(sizeof(int) * (size_t)NG);
    S = malloc(sizeof(int) * (size_t)DEG);
    SI = malloc(sizeof(int) * (size_t)DEG);
    BS = malloc(sizeof(int) * (size_t)DEG);
    inS = malloc((size_t)NG);
    fr = malloc(sizeof(int) * (size_t)(2 * NG));
    nx = malloc(sizeof(int) * (size_t)(2 * NG));
    vis = calloc((size_t)(2 * NG), sizeof(uint32_t));
    if (!MT || !INV || !S || !SI || !BS || !inS || !fr || !nx || !vis) {
        printf("0 0\n");
        return 0;
    }

    /* Semidirect product: (a,b)*(c,d) = (a + r^b c, b + d), element a*K2 + b. */
    for (int x = 0; x < NG; x++) {
        int a = x / K2, b = x % K2;
        for (int y = 0; y < NG; y++) {
            int c = y / K2, dd = y % K2;
            long long t = ((long long)a + (long long)POWR[b] * c) % MM;
            MT[(size_t)x * NG + y] = (int)(t * K2 + (b + dd) % K2);
        }
    }
    for (int x = 0; x < NG; x++) {
        INV[x] = -1;
        for (int y = 0; y < NG; y++) {
            if (MT[(size_t)x * NG + y] == 0) { INV[x] = y; break; }
        }
        if (INV[x] < 0) { printf("0 0\n"); return 0; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 40000;
    const int STAG = 6000;

    while (!found && elapsed(t0) < slice) {
        if (DEG < 2 || bestCost >= BIGCOST || rnd01() < 0.3) {
            random_S();
        } else {
            load_S(BS);
            if (NG > DEG) {
                for (int k = 0; k < 2; k++) {
                    int t = 1 + rndint(DEG - 1);
                    int s;
                    do { s = rndint(NG); } while (inS[s]);
                    inS[S[t]] = 0;
                    S[t] = s;
                    inS[s] = 1;
                    SI[t] = INV[s];
                }
            }
        }
        double T0 = 1.0;

        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; memcpy(BS, S, sizeof(int) * (size_t)DEG); }
        if (cur == 0) { found = 1; break; }

        int runBest = cur, since = 0;
        for (int it = 0; it < RL && DEG >= 2; it++) {
            if ((it & 127) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.02;
            int t = 1 + rndint(DEG - 1);
            int s = rndint(NG);
            if (inS[s]) continue;
            int old = S[t];
            inS[old] = 0;
            inS[s] = 1;
            S[t] = s;
            SI[t] = INV[s];
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                inS[s] = 0;
                inS[old] = 1;
                S[t] = old;
                SI[t] = INV[old];
            }
            if (cur < bestCost) { bestCost = cur; memcpy(BS, S, sizeof(int) * (size_t)DEG); }
            if (cur == 0) { found = 1; break; }
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
        }
    }

    if (found) {
        printf("%d %d\n", 2 * NG, NG * DEG);
        for (int x = 0; x < NG; x++) {
            for (int t = 0; t < DEG; t++) {
                printf("%d %d\n", x, NG + MT[(size_t)x * NG + S[t]]);
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
# Exact constructions (kept from the parent, used as safe starting points).
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
# Group enumeration for the Haar sweep.
# ----------------------------------------------------------------------------

def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _groups_of_order(n, rng):
    """All semidirect groups Z_m x|_r Z_k2 with m*k2 = n and m >= 2, in random order."""
    out = []
    for k2 in _divisors(n):
        m = n // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    rng.shuffle(out)
    return out


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is larger and valid."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D <= 2:
        return best

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Haar-graph sweep: try group orders n upward from half the current best.
    # Each order gets a time allotment; a success moves on to the next order.
    n_try = max(d, best[0] // 2 + 1)
    while time.monotonic() < deadline - 1.0 and n_try <= 2500:
        now = time.monotonic()
        allot_end = min(deadline, now + max(3.0, 0.2 * (deadline - now)))
        groups = _groups_of_order(n_try, rng)
        gi = 0
        while groups and time.monotonic() < allot_end - 0.3:
            m, k2, r = groups[gi % len(groups)]
            gi += 1
            slice_s = min(3.0, allot_end - time.monotonic())
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    timeout=slice_s + 10.0,
                )
            except RuntimeError:
                return best
            try:
                nn, ee = lib.parse_graph_text(out)
            except ValueError:
                continue
            if nn > 0 and consider(nn, ee):
                break
        n_try = max(n_try + 1, best[0] // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
