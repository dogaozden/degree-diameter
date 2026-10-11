import time

import lib


# ----------------------------------------------------------------------------
# New family for D >= 3: cyclic Haar graphs.
#
# H(Z_m, S) has parts a_i and b_j, with a_i ~ b_{i+s} for s in S, |S| = d.
# Same-side pairs are at distance 2 exactly when S - S covers Z_m. Opposite-side
# pairs are at distance <= 3 because S - S + S covers Z_m as well. So the graph
# is valid for diameter 3 iff S - S = Z_m. This needs m <= d^2 - d + 1, so the
# order is at most 2(d^2 - d + 1). For d = 16 that is 482, which is the ceiling.
# The C engine searches for difference covers of size d with m as large as it can.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 0x9E3779B97F4A7C15ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int M;        /* modulus m */
static int K;        /* set size d */
static int *cnt;     /* cnt[x] = ordered pairs (s,t) in S with s - t = x, x != 0 */
static int *inS;     /* membership indicator for residues */
static int *S;       /* current set */
static int cost;     /* number of nonzero residues with cnt == 0 */

static int md(int x) {
    x %= M;
    if (x < 0) x += M;
    return x;
}

static void bump(int x, int dlt) {
    if (x == 0) return;
    if (dlt > 0) {
        if (cnt[x] == 0) cost--;
        cnt[x]++;
    } else {
        cnt[x]--;
        if (cnt[x] == 0) cost++;
    }
}

/* Remove element at index idx from S (its differences leave cnt). */
static void remove_at(int idx) {
    int s = S[idx];
    for (int j = 0; j < K; j++) {
        if (j == idx) continue;
        bump(md(s - S[j]), -1);
        bump(md(S[j] - s), -1);
    }
    inS[s] = 0;
}

/* Put value t at index idx (its differences enter cnt). */
static void insert_at(int idx, int t) {
    for (int j = 0; j < K; j++) {
        if (j == idx) continue;
        bump(md(t - S[j]), 1);
        bump(md(S[j] - t), 1);
    }
    S[idx] = t;
    inS[t] = 1;
}

/* Recompute all counts from scratch for the current S (inS already set). */
static void full_init(void) {
    memset(cnt, 0, sizeof(int) * (size_t)M);
    cost = M - 1;
    for (int i = 0; i < K; i++) {
        for (int j = 0; j < K; j++) {
            if (i != j) bump(md(S[i] - S[j]), 1);
        }
    }
}

/* Simulated annealing on the number of uncovered nonzero residues.
   Returns 1 when S - S covers Z_M, 0 when the clock deadline passes first. */
static int anneal(double tlimit) {
    for (long long it = 0;; it++) {
        if (cost == 0) return 1;
        if ((it & 16383) == 0 && (double)clock() > tlimit) return 0;
        double frac = (double)(it % 2000000LL) / 2000000.0;
        double T = 0.03 + 0.5 * (1.0 - frac) * (1.0 - frac);
        int idx = rndi(K);
        int s = S[idx];
        int t = rndi(M);
        if (inS[t]) continue;
        int old = cost;
        remove_at(idx);
        insert_at(idx, t);
        int delta = cost - old;
        if (delta > 0 && rndu() >= exp(-(double)delta / T)) {
            remove_at(idx);
            insert_at(idx, s);
        }
    }
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 3;
    int D = argc > 2 ? atoi(argv[2]) : 3;
    long seed = argc > 3 ? atol(argv[3]) : 1;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    int mstart = argc > 5 ? atoi(argv[5]) : 0;

    rs ^= (uint64_t)seed * 0x2545F4914F6CDD1DULL + 1ULL;
    if (!rs) rs = 1;

    if (d < 1) {
        printf("0 0\n");
        return 0;
    }
    K = d;
    int mmax = K * K - K + 1;

    /* Default: S = {0..K-1} in Z_K, i.e. K_{K,K}. */
    int bestm = K;
    int *bestS = (int *)malloc(sizeof(int) * (size_t)K);
    for (int i = 0; i < K; i++) bestS[i] = i;

    if (D >= 3 && K >= 2) {
        int cap = mmax + 2;
        cnt = (int *)malloc(sizeof(int) * (size_t)cap);
        inS = (int *)malloc(sizeof(int) * (size_t)cap);
        S = (int *)malloc(sizeof(int) * (size_t)K);
        double deadline = (double)clock() + tl * (double)CLOCKS_PER_SEC;
        if (mstart < bestm + 1) mstart = bestm + 1;

        for (int m = mstart; m <= mmax; m++) {
            double now = (double)clock();
            double remain = deadline - now;
            if (remain <= 0) break;
            M = m;
            memset(inS, 0, sizeof(int) * (size_t)m);
            for (int i = 0; i < K; i++) {
                int t;
                do {
                    t = rndi(m);
                } while (inS[t]);
                S[i] = t;
                inS[t] = 1;
            }
            full_init();
            double share = now + 0.5 * remain;
            if (anneal(share)) {
                bestm = m;
                memcpy(bestS, S, sizeof(int) * (size_t)K);
            } else {
                break;
            }
        }
    }

    int m = bestm;
    printf("%d %ld\n", 2 * m, (long)m * K);
    for (int i = 0; i < m; i++) {
        for (int j = 0; j < K; j++) {
            printf("%d %d\n", i, m + (i + bestS[j]) % m);
        }
    }
    return 0;
}
"""


def _conic_graph(d):
    """PG(2,q) incidence plus two new vertices per arc point, q the largest prime power <= d-3."""
    q = next((c for c in range(d - 3, 1, -1) if lib.is_prime_power(c)), None)
    if q is None:
        return None
    F = lib.GF(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    lines_of = [[] for _ in range(m)]
    pts_of = [[] for _ in range(m)]
    for u, v in edges:
        lines_of[u].append(v)        # v is a line vertex id, m..2m-1
        pts_of[v - m].append(u)      # points on line index v - m
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    k = len(S)
    E = list(edges)
    for t, P in enumerate(S):
        E += [(2 * m + t, v) for v in lines_of[P]]
    for t, j in enumerate(S):
        E += [(u, 2 * m + k + t) for u in pts_of[j]]
    return 2 * m + 2 * k, E


def build(d, D, seed, time_limit):
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D < 3 or d < 2:
        return best

    # Arc-extended projective plane baseline (the parent's construction).
    try:
        cand = _conic_graph(d)
    except Exception:
        cand = None
    if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
        best = cand

    # Cyclic Haar difference-cover search, starting just above the baseline order.
    try:
        budget = 0.7 * time_limit
        out = lib.run_c(C_SOURCE, [d, D, seed, budget, best[0] // 2 + 1],
                        timeout=0.9 * time_limit)
        n, e = lib.parse_graph_text(out)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
