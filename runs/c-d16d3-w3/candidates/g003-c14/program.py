import math
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over two multisets on PG(2, q).
#
# Input: the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1) on stdin.
# Let k = q+1 be the common degree and s = d - k the spare degree.
#
# SA side: a multiset of points P, each new A-vertex joined to the k lines through P.
#          Each line may be hit at most s times.
# SB side: a multiset of lines j, each new B-vertex joined to the k points on j.
#          Each point may be hit at most s times.
#
# Any such pair of multisets gives diameter 3 and bipartiteness (argued in the
# design notes and re-checked by lib.is_valid in Python). The C code maximises
# the multiset sizes with annealing, moves that add one unit and eject the units
# that overload its lines, plus removal moves. The cycle restarts from the best
# solution found so far.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

typedef struct {
    int m, s, K;
    int *ncnt, *nb;      /* candidate c -> targets nb[c*K + i], count ncnt[c] */
    int *ocnt, *of;      /* target t -> candidates of[t*K + i], count ocnt[t] */
    int *x, *load, *bestx;
    int total, best;
} side_t;

static void inc_c(side_t *S, int c) {
    S->x[c]++;
    S->total++;
    for (int i = 0; i < S->ncnt[c]; i++) S->load[S->nb[c * S->K + i]]++;
}

static void dec_c(side_t *S, int c) {
    S->x[c]--;
    S->total--;
    for (int i = 0; i < S->ncnt[c]; i++) S->load[S->nb[c * S->K + i]]--;
}

static void rebuild(side_t *S, const int *src) {
    memset(S->load, 0, sizeof(int) * (size_t)S->m);
    S->total = 0;
    for (int c = 0; c < S->m; c++) {
        S->x[c] = src[c];
        S->total += src[c];
        for (int i = 0; i < S->ncnt[c]; i++) S->load[S->nb[c * S->K + i]] += src[c];
    }
}

static void solve_side(side_t *S, double budget, int *tmp, int *logc) {
    const double Tmax = 0.6, Tmin = 0.08;
    const double lr = log(Tmin / Tmax);
    const long CYC = 200000;
    int m = S->m, s = S->s, K = S->K;
    double deadline = now_s() + budget;
    long it = 0, pos = 0;
    for (;;) {
        if ((it & 255) == 0 && now_s() > deadline) break;
        it++;
        pos++;
        if (pos >= CYC) {
            pos = 0;
            if (S->total < S->best) rebuild(S, S->bestx);
        }
        double T = Tmax * exp(lr * (double)pos / (double)CYC);
        if (rnd01() < 0.8) {
            int c = rndint(m);
            if (S->x[c] >= s) continue;
            inc_c(S, c);
            int nrem = 0, bad = 0;
            for (int i = 0; i < S->ncnt[c] && !bad; i++) {
                int t = S->nb[c * K + i];
                while (S->load[t] > s) {
                    int cnt = 0;
                    for (int j = 0; j < S->ocnt[t]; j++) {
                        int c2 = S->of[t * K + j];
                        if (c2 != c && S->x[c2] > 0) tmp[cnt++] = c2;
                    }
                    if (cnt == 0) { bad = 1; break; }
                    int c2 = tmp[rndint(cnt)];
                    dec_c(S, c2);
                    logc[nrem++] = c2;
                }
            }
            int delta = 1 - nrem;
            int ok = !bad && (delta >= 0 || rnd01() < exp((double)delta / T));
            if (!ok) {
                for (int r = nrem - 1; r >= 0; r--) inc_c(S, logc[r]);
                dec_c(S, c);
            }
        } else {
            int c = rndint(m);
            if (S->x[c] == 0) continue;
            dec_c(S, c);
            if (!(rnd01() < exp(-1.0 / T))) inc_c(S, c);
        }
        if (S->total > S->best) {
            S->best = S->total;
            memcpy(S->bestx, S->x, sizeof(int) * (size_t)m);
        }
    }
}

static void print_input(int n, int me, const int *eu, const int *ev) {
    printf("%d %d\n", n, me);
    for (int i = 0; i < me; i++) printf("%d %d\n", eu[i], ev[i]);
}

int main(int argc, char **argv) {
    int d = argc > 1 ? atoi(argv[1]) : 0;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 5.0;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();

    int n = 0, me = 0;
    if (scanf("%d %d", &n, &me) != 2 || n < 0 || me < 0) { printf("0 0\n"); return 0; }
    int *eu = malloc(sizeof(int) * (size_t)(me > 0 ? me : 1));
    int *ev = malloc(sizeof(int) * (size_t)(me > 0 ? me : 1));
    for (int i = 0; i < me; i++) {
        if (scanf("%d %d", &eu[i], &ev[i]) != 2) { printf("0 0\n"); return 0; }
    }
    if (n <= 0) { printf("0 0\n"); return 0; }

    int *deg = calloc((size_t)n, sizeof(int));
    for (int i = 0; i < me; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    int K = 0;
    for (int v = 0; v < n; v++) if (deg[v] > K) K = deg[v];
    int half = n / 2;
    int s = d - K;
    int bip = (n % 2 == 0);
    for (int i = 0; i < me && bip; i++) {
        if ((eu[i] < half) == (ev[i] < half)) bip = 0;
    }
    if (!bip || s <= 0 || K == 0 || half == 0) {
        print_input(n, me, eu, ev);
        return 0;
    }

    int *plc = calloc((size_t)half, sizeof(int));
    int *lpc = calloc((size_t)half, sizeof(int));
    int *pl = malloc(sizeof(int) * (size_t)half * (size_t)K);
    int *lp = malloc(sizeof(int) * (size_t)half * (size_t)K);
    for (int i = 0; i < me; i++) {
        int a = eu[i], b = ev[i];
        int p = a < half ? a : b;
        int l = (a < half ? b : a) - half;
        pl[p * K + plc[p]++] = l;
        lp[l * K + lpc[l]++] = p;
    }

    int *xA = calloc((size_t)half, sizeof(int));
    int *lA = calloc((size_t)half, sizeof(int));
    int *bA = calloc((size_t)half, sizeof(int));
    int *xB = calloc((size_t)half, sizeof(int));
    int *lB = calloc((size_t)half, sizeof(int));
    int *bB = calloc((size_t)half, sizeof(int));

    side_t A, B;
    A.m = half; A.s = s; A.K = K;
    A.ncnt = plc; A.nb = pl; A.ocnt = lpc; A.of = lp;
    A.x = xA; A.load = lA; A.bestx = bA; A.total = 0; A.best = 0;

    B.m = half; B.s = s; B.K = K;
    B.ncnt = lpc; B.nb = lp; B.ocnt = plc; B.of = pl;
    B.x = xB; B.load = lB; B.bestx = bB; B.total = 0; B.best = 0;

    int *tmp = malloc(sizeof(int) * (size_t)(K + 2));
    int *logc = malloc(sizeof(int) * (size_t)(K + 2));

    solve_side(&A, tl * 0.5, tmp, logc);
    solve_side(&B, tl * 0.5, tmp, logc);

    int nA = A.best, nB = B.best;
    int *SA = malloc(sizeof(int) * (size_t)(nA + 1));
    int *SB = malloc(sizeof(int) * (size_t)(nB + 1));
    int k = 0;
    for (int c = 0; c < half; c++)
        for (int r = 0; r < bA[c]; r++) SA[k++] = c;
    k = 0;
    for (int c = 0; c < half; c++)
        for (int r = 0; r < bB[c]; r++) SB[k++] = c;

    long mm = me;
    for (int t = 0; t < nA; t++) mm += plc[SA[t]];
    for (int t = 0; t < nB; t++) mm += lpc[SB[t]];

    printf("%d %ld\n", n + nA + nB, mm);
    for (int i = 0; i < me; i++) printf("%d %d\n", eu[i], ev[i]);
    for (int t = 0; t < nA; t++) {
        int id = n + t, P = SA[t];
        for (int i = 0; i < plc[P]; i++) printf("%d %d\n", id, half + pl[P * K + i]);
    }
    for (int t = 0; t < nB; t++) {
        int id = n + nA + t, j = SB[t];
        for (int i = 0; i < lpc[j]; i++) printf("%d %d\n", lp[j * K + i], id);
    }
    return 0;
}
"""


def _candidates(d):
    """Prime powers q with q+1 <= d, as (estimated order, q), best estimate first.

    The estimate is 2m + 2*floor(s*m/(q+1)) with m = q^2+q+1 and s = d-q-1. It is the
    LP-type bound for the two multisets, so it is an upper-ish guide, not a promise.
    """
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        m = q * q + q + 1
        out.append((2 * m + 2 * ((s * m) // (q + 1)), q))
    out.sort(reverse=True)
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit

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
        cands = _candidates(d)
        for _est, q in cands[:1]:
            H_n, H_e = lib.projective_plane_incidence(q)
            now = time.monotonic()
            remaining = end - now
            if remaining < 1.5:
                break
            budget = max(0.5, remaining - 1.0)
            timeout = max(1.0, time_limit * 0.9 - (now - t0))
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=(H_n, H_e), timeout=timeout)
                n_new, e_new = lib.parse_graph_text(text)
                consider(n_new, e_new)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
