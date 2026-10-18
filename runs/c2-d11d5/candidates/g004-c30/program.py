"""Bi-Cayley voltage-lift search with a bit-parallel C annealer and order escalation.

New in this version:
  * Search engine in C. Reachability is kept as a bitmask per vertex, one bit per
    block representative (2k bits), so the diameter check for one candidate is a
    few bit-OR sweeps over the lift. This is far faster than the numpy version, so
    many more voltage/layer moves fit in the budget.
  * Order escalation. Each trial targets a group order G just above the best
    found so far, with jitter, so every success raises the bar. Base size k is
    chosen by a success-rate bandit.
  * Semidirect products Z_m x| Z_k2 are multiplied and inverted by closed-form
    formulas, so no multiplication tables are needed.
  * Slack extension was dropped. Lifts are exactly d-regular, so there is no
    spare degree to use.

Calibration cases (d=3, D=3) return the projective-plane incidence graph at once.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define KMAX 5
#define DMAX 64
#define PEN 1000L
#define NCAP 200000

static int dd = 0, DD = 0;
static uint64_t rs = 1;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rng_next(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static uint32_t rnd(uint32_t n) { return (uint32_t)(rng_next() % n); }
static double rndu(void) { return (double)(rng_next() >> 11) * (1.0 / 9007199254740992.0); }

static int pc32(uint32_t x) { int c = 0; while (x) { x &= x - 1; c++; } return c; }
static long gcd_l(long a, long b) { while (b) { long t = a % b; a = b; b = t; } return a; }
static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* ---------------- group Z_m x| Z_k2, element x = a*k2 + b ---------------- */

typedef struct { int G, m, k2; int pw[64]; } Group;

static const int K2OPT[] = {1, 1, 2, 2, 3, 4, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int G, Group *g) {
    int nopt = (int)(sizeof K2OPT / sizeof K2OPT[0]);
    for (int att = 0; att < 300; att++) {
        int k2 = K2OPT[rnd((uint32_t)nopt)];
        if (G % k2) continue;
        int m = G / k2;
        if (m < 2) continue;
        long r = 1;
        if (k2 > 1) {
            int ok = 0;
            if (k2 == 2 && m > 2 && rnd(3) == 0) { r = m - 1; ok = 1; }
            for (int t = 0; t < 400 && !ok; t++) {
                long c = 1 + (long)rnd((uint32_t)(m - 1));
                if (gcd_l(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; ok = 1; }
            }
            if (!ok) continue;
        }
        g->G = G; g->m = m; g->k2 = k2;
        g->pw[0] = 1 % m;
        for (int t = 1; t < k2; t++) g->pw[t] = (int)((long)g->pw[t - 1] * r % m);
        return 1;
    }
    return 0;
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(const Group *g, int x, int y) {
    int k2 = g->k2;
    int a = x / k2, b = x - a * k2;
    int c = y / k2, e = y - c * k2;
    long aa = ((long)a + (long)g->pw[b] * c) % g->m;
    int bb = (b + e) % k2;
    return (int)aa * k2 + bb;
}

/* inverse of s: (c,e)^-1 = (-r^{-e} c, -e), and r^{-e} = r^{k2-e} */
static int ginv(const Group *g, int s) {
    int k2 = g->k2;
    int c = s / k2, e = s - c * k2;
    int e2 = (k2 - e) % k2;
    long c2 = ((long)g->m - (long)g->pw[e2] * c % g->m) % g->m;
    return (int)c2 * k2 + e2;
}

/* ---------------- bi-Cayley lift ----------------
 * A block i (0..k-1) and B block p (k..2k-1), each of size G.
 * Layer l pairs A block i with B block lay[l][i] through voltage S[l][i]:
 * A_{i,x} ~ B_{p, x*s}. Each layer is a permutation, so the lift is d-regular.
 */
typedef struct {
    int k, G, N, d;
    const Group *g;
    int *nbr;               /* N*d neighbour table */
    int lay[DMAX][KMAX];
    int S[DMAX][KMAX];
} Lift;

static void set_dart(Lift *L, int l, int i) {
    const Group *g = L->g;
    int k = L->k, G = L->G, d = L->d, p = L->lay[l][i], s = L->S[l][i];
    int si = ginv(g, s);
    for (int x = 0; x < G; x++) {
        int u = i * G + x;
        L->nbr[(size_t)u * d + l] = (k + p) * G + gmul(g, x, s);
    }
    for (int h = 0; h < G; h++) {
        int w = (k + p) * G + h;
        L->nbr[(size_t)w * d + l] = i * G + gmul(g, h, si);
    }
}

/* Cost = unreached (representative, vertex) pairs + PEN * duplicate darts.
 * Left multiplication is an automorphism, so distance from block representatives
 * to all vertices suffices. reach[v] bit b is set when representative b is within DD of v. */
static long evaluate(const Lift *L, uint32_t *bA, uint32_t *bB, uint32_t **fin) {
    int N = L->N, d = L->d, k = L->k, G = L->G;
    uint32_t full = (1u << (2 * k)) - 1u;
    uint32_t *cur = bA, *nxt = bB;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] |= 1u << b;
    for (int t = 0; t < DD; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            const int *nb = L->nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[nb[l]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        if (!changed) break;
        uint32_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) cost += pc32(full & ~cur[v]);
    long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (L->lay[l1][i] == L->lay[l2][i] && L->S[l1][i] == L->S[l2][i]) dup++;
    *fin = cur;
    return cost + PEN * dup;
}

/* Simulated annealing with stagnation cut-off. Returns 1 when the lift is valid. */
static int anneal(Lift *L, double deadline, long iters, long patience,
                  uint32_t *bA, uint32_t *bB, uint32_t *rc) {
    int k = L->k, d = L->d, G = L->G, N = L->N;
    uint32_t full = (1u << (2 * k)) - 1u;
    for (int l = 0; l < d; l++) {
        int perm[KMAX];
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = (int)rnd((uint32_t)(i + 1));
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            L->lay[l][i] = perm[i];
            L->S[l][i] = (int)rnd((uint32_t)G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(L, l, i);

    uint32_t *fin = NULL;
    long cost = evaluate(L, bA, bB, &fin);
    memcpy(rc, fin, sizeof(uint32_t) * (size_t)N);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best = cost, last = 0;

    for (long t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 127) == 0 && now() > deadline) break;
        double temp = 0.3 + (0.05 * c0 + 1.0) * (1.0 - (double)t / (double)iters);
        long c2;
        int acc;

        if (k >= 2 && rndu() < 0.25) {
            /* layer-swap move: exchange the B-targets of two A blocks in one layer */
            int l = (int)rnd((uint32_t)d);
            int i1 = (int)rnd((uint32_t)k);
            int i2 = (int)rnd((uint32_t)(k - 1));
            if (i2 >= i1) i2++;
            int tmp = L->lay[l][i1]; L->lay[l][i1] = L->lay[l][i2]; L->lay[l][i2] = tmp;
            set_dart(L, l, i1);
            set_dart(L, l, i2);
            c2 = evaluate(L, bA, bB, &fin);
            acc = (c2 <= cost) || (rndu() < exp(-(double)(c2 - cost) / temp));
            if (acc) {
                cost = c2;
                memcpy(rc, fin, sizeof(uint32_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = L->lay[l][i1]; L->lay[l][i1] = L->lay[l][i2]; L->lay[l][i2] = tmp;
                set_dart(L, l, i1);
                set_dart(L, l, i2);
            }
        } else {
            /* voltage move; with prob 0.4 aim at a vertex that is not yet good */
            int l = 0, i = 0;
            int found = -1;
            if (rndu() < 0.4) {
                for (int tries = 0; tries < 40; tries++) {
                    int v = (int)rnd((uint32_t)N);
                    if (rc[v] != full) { found = v; break; }
                }
            }
            if (found >= 0) {
                int block = found / G;
                l = (int)rnd((uint32_t)d);
                if (block < k) i = block;
                else {
                    int p = block - k;
                    for (int q = 0; q < k; q++)
                        if (L->lay[l][q] == p) { i = q; break; }
                }
            } else {
                l = (int)rnd((uint32_t)d);
                i = (int)rnd((uint32_t)k);
            }
            int oldS = L->S[l][i];
            int ns = (int)rnd((uint32_t)G);
            if (ns == oldS) continue;
            L->S[l][i] = ns;
            set_dart(L, l, i);
            c2 = evaluate(L, bA, bB, &fin);
            acc = (c2 <= cost) || (rndu() < exp(-(double)(c2 - cost) / temp));
            if (acc) {
                cost = c2;
                memcpy(rc, fin, sizeof(uint32_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                L->S[l][i] = oldS;
                set_dart(L, l, i);
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    rs = (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    double deadline = now() + budget;

    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    int *se = malloc(sizeof(int) * 2 * (size_t)(sm > 0 ? sm : 1));
    int cnt = 0;
    for (int i = 0; i < sm; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        se[2 * cnt] = u;
        se[2 * cnt + 1] = v;
        cnt++;
    }

    int *E;
    int bestN, bestM;
    if (sn > 0 && sm > 0 && cnt == sm) {
        bestN = sn; bestM = sm; E = se;
    } else {
        free(se);
        if (dd < 1) { printf("0 0\n"); return 0; }
        bestN = 2 * dd;
        bestM = dd * dd;
        E = malloc(sizeof(int) * 2 * (size_t)bestM);
        int c = 0;
        for (int i = 0; i < dd; i++)
            for (int j = 0; j < dd; j++) {
                E[2 * c] = i;
                E[2 * c + 1] = dd + j;
                c++;
            }
    }

    if (dd >= 2 && dd <= DMAX && DD >= 2) {
        double tr[KMAX + 1], wn[KMAX + 1];
        for (int k = 0; k <= KMAX; k++) { tr[k] = 0.0; wn[k] = 0.0; }

        while (now() < deadline) {
            int k;
            if (rndu() < 0.2) {
                k = 1 + (int)rnd(KMAX);
            } else {
                double bs = -1.0;
                k = 1;
                for (int kk = 1; kk <= KMAX; kk++) {
                    double sc = (wn[kk] + 1.0) / (tr[kk] + 2.0) + 0.02 * rndu();
                    if (sc > bs) { bs = sc; k = kk; }
                }
            }
            /* escalation: target a group order whose lift beats the current best */
            long base = bestN / (2 * k);
            long G = base + 1 + (long)rnd((uint32_t)(base / 8 + 2));
            if ((long)2 * k * G > NCAP || (long)k * G < dd) continue;

            Group g;
            if (!sample_group((int)G, &g)) continue;
            tr[k] += 1.0;

            Lift L;
            memset(&L, 0, sizeof L);
            L.k = k; L.G = (int)G; L.N = 2 * k * (int)G; L.d = dd; L.g = &g;
            L.nbr = malloc(sizeof(int) * (size_t)L.N * (size_t)dd);
            uint32_t *bA = malloc(sizeof(uint32_t) * (size_t)L.N);
            uint32_t *bB = malloc(sizeof(uint32_t) * (size_t)L.N);
            uint32_t *rc = malloc(sizeof(uint32_t) * (size_t)L.N);
            if (!L.nbr || !bA || !bB || !rc) {
                free(L.nbr); free(bA); free(bB); free(rc);
                break;
            }

            int ok = anneal(&L, deadline, 80000, 12000, bA, bB, rc);
            if (ok) {
                wn[k] += 1.0;
                if (L.N > bestN) {
                    int newM = k * (int)G * dd;
                    int *ne = malloc(sizeof(int) * 2 * (size_t)newM);
                    int c = 0;
                    int An = k * (int)G;
                    for (int u = 0; u < An; u++)
                        for (int l = 0; l < dd; l++) {
                            ne[2 * c] = u;
                            ne[2 * c + 1] = L.nbr[(size_t)u * dd + l];
                            c++;
                        }
                    free(E);
                    E = ne;
                    bestN = L.N;
                    bestM = newM;
                }
            }
            free(L.nbr); free(bA); free(bB); free(rc);
        }
    }

    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", E[2 * i], E[2 * i + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions (kept from the parent).
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is a valid fallback for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d < 2 or d > 60:
        return best

    # Leave margin for compilation, process startup, and validation.
    budget = max(1.0, min(0.85 * time_limit, time_limit - 7.0))
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                        stdin_graph=best, timeout=max(2.0, time_limit - 2.0))
        n, edges = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
