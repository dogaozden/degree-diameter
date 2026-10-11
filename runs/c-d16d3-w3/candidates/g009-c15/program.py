"""Diameter-3 search focused on Haar graphs (bold change from the blow-up family).

Starts (validated with lib.is_valid): K_{d,d}, PG(2,q) incidence when d-1 is a prime power,
Araujo-Pardo/Lopez when d-2 is a prime power, and the conic blow-up of PG(2,q) for q = d-3 odd.

Main new engine (D = 3): a Haar graph H(m, S) on Z_m with |S| = d is d-regular and bipartite,
with 2m vertices. Its diameter is at most 3 iff
  (a) S - S covers every residue of Z_m (same-side distance 2), and
  (b) (S - S) + S covers every residue (opposite-side distance 1 or 3).
Since 0 is in S - S, WLOG 0 is in S. The C engine runs simulated annealing over S for
increasing m, starting just above half the best known order, so any success beats the start.
Every returned graph is re-checked with lib.is_valid, and the best valid graph is kept.
For D != 3 the program returns the best valid start, or K_{d,d}.
"""
import time

import lib

C_HAAR = r"""
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64

static int K, M;
static int S[MAXK];
static unsigned char inS[MAXM], Acov[MAXM], Tcov[MAXM];
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

/* Number of residues not in S-S, plus number not in (S-S)+S. Zero means valid. */
static int cost(void) {
    int c = 0;
    memset(Acov, 0, (size_t)M);
    memset(Tcov, 0, (size_t)M);
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) {
            int x = S[i] - S[j];
            if (x < 0) x += M;
            Acov[x] = 1;
        }
    for (int a = 0; a < M; a++) {
        if (!Acov[a]) continue;
        for (int i = 0; i < K; i++) {
            int x = a + S[i];
            if (x >= M) x -= M;
            Tcov[x] = 1;
        }
    }
    for (int x = 0; x < M; x++) {
        c += !Acov[x];
        c += !Tcov[x];
    }
    return c;
}

static void init_S(void) {
    memset(inS, 0, (size_t)M);
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int x;
        do x = rndint(M); while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
}

static int anneal(double until) {
    init_S();
    int cur = cost();
    double T = 1.0;
    long it = 0;
    while (cur > 0) {
        if ((++it & 255) == 0 && now() > until) return 0;
        if (it % 100000 == 0) {
            init_S();
            cur = cost();
            T = 1.0;
            continue;
        }
        int i = 1 + rndint(K - 1);
        int x;
        do x = rndint(M); while (inS[x]);
        int old = S[i];
        inS[old] = 0;
        inS[x] = 1;
        S[i] = x;
        int nc = cost();
        if (nc <= cur || rnd01() < exp((cur - nc) / T)) {
            cur = nc;
        } else {
            inS[x] = 0;
            inS[old] = 1;
            S[i] = old;
        }
        T *= 0.9999;
        if (T < 0.25) T = 0.25;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    K = atoi(argv[1]);
    int mlo = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t_end = now() + budget;
    int mmax = K * (K - 1) + 1;
    if (mmax > MAXM - 1) mmax = MAXM - 1;
    int m = mlo;
    if (m < K + 1) m = K + 1;
    int bestM = 0;
    int bestS[MAXK];
    int fails = 0;

    while (K >= 2 && now() < t_end && m <= mmax) {
        M = m;
        double rem = t_end - now();
        double slice = fmax(2.0, rem * 0.3);
        if (slice > rem) slice = rem;
        if (anneal(now() + slice)) {
            bestM = m;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
            m++;
            fails = 0;
        } else {
            fails++;
            if (fails >= 2) {
                m++;
                fails = 0;
            }
        }
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d", bestM, K);
    for (int i = 0; i < K; i++) printf(" %d", bestS[i]);
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Structured starts.
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Projective plane or Araujo-Pardo/Lopez graph for D = 3, when they apply."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


# ----------------------------------------------------------------------------
# Haar-graph difference search.
# ----------------------------------------------------------------------------

def haar_search(d, D, seed, budget, n_best):
    """Search for H(m, S) with |S| = d, m > n_best/2, via the C annealer. Returns (n, edges) or None."""
    mlo = n_best // 2 + 1
    text = lib.run_c(C_HAAR, [d, mlo, seed, f"{budget:.2f}"], timeout=budget + 10.0)
    t = text.split()
    if len(t) < 2 or int(t[0]) == 0:
        return None
    m, k = int(t[0]), int(t[1])
    S = [int(x) for x in t[2:2 + k]]
    if len(S) != k or len(set(S)) != k:
        return None
    return lib.haar_graph(m, S)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 80% of time_limit."""
    t0 = time.monotonic()
    hard_end = t0 + 0.80 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    def ok(g):
        try:
            return lib.is_valid(g[0], g[1], d, D)
        except Exception:
            return False

    fallback = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2
    cands = []
    for g in (known_start(d, D), conic_blowup(d, D)):
        if g is not None and ok(g):
            cands.append(g)
    if ok(fallback):
        cands.append(fallback)
    if not cands:
        return 1, []
    best = max(cands, key=lambda g: g[0])

    if D == 3 and d >= 3:
        remaining = hard_end - time.monotonic()
        if remaining > 2.0:
            try:
                g = haar_search(d, D, seed * 31 + 7, remaining - 1.0, best[0])
                if g is not None and g[0] > best[0] and ok(g):
                    best = g
            except Exception:
                pass

    if not ok(best):
        best = fallback
    return best
