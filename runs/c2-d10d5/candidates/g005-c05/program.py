"""Bipartite graphs with max degree d and diameter D.

Constructions: projective planes (D = 3), the generalized quadrangle W(q) (D = 4),
and a search over bi-Cayley lifts over semidirect products Z_m x| Z_k2 with K base
pairs per side.

New in this version: the lift search runs in C (bitmask reachability over the 2K
block representatives, exact degree and multi-edge penalty). Each C call searches one
group with iterated local search: after a stagnation the trial restarts from its own
best state with a small random kick, not from a fresh random state. Base sizes K run
from 1 to 6 under a win-rate bandit, and every returned graph passes lib.is_valid.
"""
import itertools
import math
import random
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

#define PEN 1000LL
#define MAXKICK 6

static int dg, Dg, K, Mm, K2, G, N;
static int *pw, *invS, *lay, *sv, *layB, *svB, *nbr, *perm;
static uint64_t *cur, *cand, *tA, *tB;
static uint64_t FULL;
static long long curCost, trialBest;
static double deadline_s;
static int timed_out;
static uint64_t rs = 88172645463325252ULL;

static double now_s(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static uint64_t rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}

static int rndi(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double rndu(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0f0f0f0f0f0f0f0fULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Element x = a*K2 + b is (a,b); (a,b)(c,e) = (a + r^b c, b + e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x - a * K2;
    int c = y / K2, e = y - c * K2;
    long long t = ((long long)pw[b] * c + a) % Mm;
    int bb = b + e;
    if (bb >= K2) bb -= K2;
    return (int)t * K2 + bb;
}

/* Inverse of (a,b) is (-r^(-b) a, -b). */
static int ginv(int x) {
    int a = x / K2, b = x - a * K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)pw[nb] * a) % Mm;
    t = (Mm - t) % Mm;
    return (int)t * K2 + nb;
}

/* Layer l sends A-block i to B-block j with voltage s:
   A_{i,g} ~ B_{j,g*s}, equivalently B_{j,h} ~ A_{i,h*s^-1}. */
static void set_dart(int l, int i, int j, int s) {
    int *nb = nbr + (size_t)l * N;
    int is = invS[s];
    int Ab = i * G, Bb = (K + j) * G;
    for (int g = 0; g < G; g++) {
        nb[Ab + g] = Bb + gmul(g, s);
        nb[Bb + g] = Ab + gmul(g, is);
    }
}

static void build_all(void) {
    for (int l = 0; l < dg; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i, lay[l * K + i], sv[l * K + i]);
}

static void random_state(void) {
    for (int l = 0; l < dg; l++) {
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
    }
    for (int p = 0; p < dg * K; p++) sv[p] = rndi(G);
}

/* Reachability: bit b of out[v] is set when block representative b*G is within Dg of v.
   By left-multiplication symmetry this covers all pairs. Returns unreached pair count. */
static long long reach_eval(uint64_t *out) {
    for (int v = 0; v < N; v++) tA[v] = 0;
    for (int b = 0; b < 2 * K; b++) tA[(size_t)b * G] = 1ULL << b;
    uint64_t *src = tA, *dst = tB;
    for (int t = 0; t < Dg; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t r = src[v];
            for (int l = 0; l < dg; l++) r |= src[nbr[(size_t)l * N + v]];
            dst[v] = r;
            changed |= (r != src[v]);
        }
        uint64_t *tmp = src;
        src = dst;
        dst = tmp;
        if (!changed) break;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) {
        out[v] = src[v];
        unr += 2 * K - popc64(src[v]);
    }
    return unr;
}

/* Number of duplicate (A-block, B-block, voltage) keys; each one is a multi-edge. */
static long long dupcount(void) {
    int L = dg * K;
    long long c = 0;
    for (int p = 0; p < L; p++) {
        int ip = p % K;
        for (int q = 0; q < p; q++)
            if (q % K == ip && lay[q] == lay[p] && sv[q] == sv[p]) c++;
    }
    return c;
}

static long long full_eval(uint64_t *out) {
    long long unr = reach_eval(out);
    return unr + PEN * dupcount();
}

static void save_best(void) {
    memcpy(layB, lay, sizeof(int) * (size_t)(dg * K));
    memcpy(svB, sv, sizeof(int) * (size_t)(dg * K));
    trialBest = curCost;
}

/* Evaluate the current darts into cur. Saves the trial best if it improved. */
static void eval_cur(void) {
    curCost = full_eval(cand);
    uint64_t *t = cur;
    cur = cand;
    cand = t;
    if (curCost < trialBest) save_best();
}

static int accept(long long c2, double temp) {
    if (c2 <= curCost) return 1;
    double pr = exp(-(double)(c2 - curCost) / temp);
    return rndu() < pr;
}

/* Accept a candidate whose reachability is in cand. */
static void commit(long long c2, int t, int *last, long long *bestHere) {
    uint64_t *tmp = cur;
    cur = cand;
    cand = tmp;
    curCost = c2;
    if (curCost < *bestHere) {
        *bestHere = curCost;
        *last = t;
    }
    if (curCost < trialBest) save_best();
}

/* Simulated annealing from the current state. Returns 1 when cost reaches 0. */
static int anneal(int iters, int patience) {
    long long c0 = curCost > 1 ? curCost : 1;
    long long bestHere = curCost;
    int last = 0;
    for (int t = 0; t < iters; t++) {
        if (curCost == 0) return 1;
        if (t - last > patience) break;
        if ((t & 31) == 0 && now_s() > deadline_s) {
            timed_out = 1;
            return 0;
        }
        double temp = 0.01 * (double)c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rndu() < 0.25) {
            /* Layer swap: exchange the B-targets of two A-blocks in one layer. */
            int l = rndi(dg);
            int i1 = rndi(K), i2 = rndi(K - 1);
            if (i2 >= i1) i2++;
            int p1 = l * K + i1, p2 = l * K + i2;
            int t1 = lay[p1];
            lay[p1] = lay[p2];
            lay[p2] = t1;
            set_dart(l, i1, lay[p1], sv[p1]);
            set_dart(l, i2, lay[p2], sv[p2]);
            long long c2 = full_eval(cand);
            if (accept(c2, temp)) {
                commit(c2, t, &last, &bestHere);
            } else {
                t1 = lay[p1];
                lay[p1] = lay[p2];
                lay[p2] = t1;
                set_dart(l, i1, lay[p1], sv[p1]);
                set_dart(l, i2, lay[p2], sv[p2]);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4 (uniform bad vertex). */
        int target = -1;
        if (rndu() < 0.4) {
            int cnt = 0;
            for (int v = 0; v < N; v++)
                if (cur[v] != FULL) {
                    cnt++;
                    if (rndi(cnt) == 0) target = v;
                }
        }
        int l, i;
        if (target >= 0) {
            int block = target / G;
            l = rndi(dg);
            if (block < K) {
                i = block;
            } else {
                int j = block - K;
                i = 0;
                for (int ii = 0; ii < K; ii++)
                    if (lay[l * K + ii] == j) {
                        i = ii;
                        break;
                    }
            }
        } else {
            l = rndi(dg);
            i = rndi(K);
        }
        int p = l * K + i;
        int old = sv[p];
        int nw = rndi(G);
        if (nw == old) continue;
        sv[p] = nw;
        set_dart(l, i, lay[p], nw);
        long long c2 = full_eval(cand);
        if (accept(c2, temp)) {
            commit(c2, t, &last, &bestHere);
        } else {
            sv[p] = old;
            set_dart(l, i, lay[p], old);
        }
    }
    return curCost == 0;
}

int main(int argc, char **argv) {
    char buf[4096];
    while (fread(buf, 1, sizeof buf, stdin) > 0) {
    }
    if (argc < 11) {
        printf("0 0\n");
        return 0;
    }
    dg = atoi(argv[1]);
    Dg = atoi(argv[2]);
    K = atoi(argv[3]);
    Mm = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int Rr = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double budget = atof(argv[8]);
    int iters = atoi(argv[9]);
    int patience = atoi(argv[10]);
    if (dg < 1 || Dg < 1 || K < 1 || K > 32 || Mm < 2 || K2 < 1 || iters < 1) {
        printf("0 0\n");
        return 0;
    }
    Rr = ((Rr % Mm) + Mm) % Mm;
    G = Mm * K2;
    N = 2 * K * G;

    pw = malloc(sizeof(int) * (size_t)(K2 + 1));
    invS = malloc(sizeof(int) * (size_t)G);
    lay = malloc(sizeof(int) * (size_t)(dg * K));
    sv = malloc(sizeof(int) * (size_t)(dg * K));
    layB = malloc(sizeof(int) * (size_t)(dg * K));
    svB = malloc(sizeof(int) * (size_t)(dg * K));
    nbr = malloc(sizeof(int) * (size_t)dg * (size_t)N);
    perm = malloc(sizeof(int) * (size_t)K);
    cur = malloc(sizeof(uint64_t) * (size_t)N);
    cand = malloc(sizeof(uint64_t) * (size_t)N);
    tA = malloc(sizeof(uint64_t) * (size_t)N);
    tB = malloc(sizeof(uint64_t) * (size_t)N);
    if (!pw || !invS || !lay || !sv || !layB || !svB || !nbr || !perm ||
        !cur || !cand || !tA || !tB) {
        printf("0 0\n");
        return 0;
    }

    pw[0] = 1 % Mm;
    for (int b = 1; b <= K2; b++) pw[b] = (int)((long long)pw[b - 1] * Rr % Mm);
    if (pw[K2] != 1 % Mm) {
        printf("0 0\n");
        return 0;
    }
    for (int x = 0; x < G; x++) invS[x] = ginv(x);

    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    FULL = (2 * K >= 64) ? ~0ULL : ((1ULL << (2 * K)) - 1ULL);

    deadline_s = now_s() + budget;
    timed_out = 0;
    int found = 0;
    while (!found && !timed_out && now_s() < deadline_s) {
        random_state();
        build_all();
        trialBest = (1LL << 60);
        eval_cur();
        int fails = 0;
        for (;;) {
            if (anneal(iters, patience)) {
                found = 1;
                break;
            }
            if (timed_out || fails >= MAXKICK) break;
            fails++;
            /* Iterated local search: kick from the trial's best state. */
            memcpy(lay, layB, sizeof(int) * (size_t)(dg * K));
            memcpy(sv, svB, sizeof(int) * (size_t)(dg * K));
            build_all();
            int npert = 2 + rndi(4);
            for (int q = 0; q < npert; q++) {
                int l = rndi(dg), i = rndi(K), p = l * K + i;
                sv[p] = rndi(G);
                set_dart(l, i, lay[p], sv[p]);
            }
            eval_cur();
        }
    }

    if (found && curCost == 0) {
        int A = K * G;
        printf("%d %d\n", N, dg * A);
        for (int l = 0; l < dg; l++)
            for (int u = 0; u < A; u++)
                printf("%d %d\n", u, nbr[(size_t)l * N + u]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""

ITERS = 4000
PATIENCE = 1000
CALL_BUDGET = 3.0


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


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _run_lift(d, D, k, m, k2, r, seed, budget):
    """Search one bi-Cayley lift in C. Returns (n, edges) or None."""
    args = [d, D, k, m, k2, r, seed, f"{budget:.2f}", ITERS, PATIENCE]
    out = lib.run_c(C_SOURCE, args, stdin_graph=None, timeout=budget + 8.0)
    n, edges = lib.parse_graph_text(out)
    if n == 0 or not edges:
        return None
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    search_end = start + max(1.0, min(0.80 * time_limit, time_limit - 12.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < search_end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Lift search: bandit over base sizes K.
    KS = (1, 2, 3, 4, 5, 6)
    trials = {k: 0 for k in KS}
    wins = {k: 0 for k in KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(KS)
        return max(KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    failures = 0
    while failures < 40:
        remaining = search_end - time.monotonic()
        if remaining < 1.5:
            break
        k = pick_k()
        base_min = best_n // (2 * k) + 1
        target = base_min + rng.randrange(0, max(2, base_min // 8 + 1))
        g = _sample_group(target, rng)
        if g is None:
            failures += 1
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best_n:
            failures += 1
            continue
        budget = min(CALL_BUDGET, remaining - 0.5)
        trials[k] += 1
        try:
            res = _run_lift(d, D, k, m, k2, r, rng.randrange(1, 1 << 30), budget)
        except RuntimeError:
            break  # C engine failed: keep the valid fallback
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
