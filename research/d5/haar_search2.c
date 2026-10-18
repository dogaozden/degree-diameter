/* Incremental version of haar_search.c (same model, same cost function).
 *
 * Model and cost: see haar_search.c. Cost = N - |(S^-1 S)^2| + N - |(S S^-1)^2|.
 *
 * Changes:
 *  - group multiplication and inversion are table lookups (MT, IT), built once from the same formulas;
 *  - coverage is kept as counts: cov[side][g] = number of ordered pairs (p, q) of "pair products"
 *    with tp[p] * tp[q] = g, where p = i*d + j and tp[p] = S_i^-1 S_j (side 0) or S_i S_j^-1 (side 1).
 *    Changing S_i only changes tp for the 2d-1 pairs in C_i = {(i,*)} u {(*,i)}, so only the words
 *    with p or q in C_i are removed and re-added (about 4 d^3 words instead of d^4);
 *  - each step samples K random replacements, scores each by apply + revert, then keeps the best one
 *    (Metropolis test on the best candidate, same temperature schedule as haar_search.c).
 *
 * Usage: haar_search2 d m k lam seed seconds [outfile|-] [K]     (K defaults to 20; K = 1 is plain annealing)
 *        haar_search2 check d m k lam seed                       (incremental cost vs full recompute)
 * Prints best cost; on cost 0 writes S (as "a j" lines) to outfile.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXD 16

static int m, k, lam, d, N, nd;
static int *pw, *ipw;           /* lam^j, lam^-j mod m */
static uint16_t *MT;            /* MT[g*N + h] = g*h */
static int *IT;                 /* IT[g] = g^-1 */
static int *stamp, cur = 1;     /* for full_cost */
static int *cov[2];             /* cov[s][g]: ordered pairs (p,q) with tp[s][p]*tp[s][q] = g */
static int covered[2];
static int tp[2][MAXD * MAXD];
static int S[MAXD], best[MAXD];
static int Cset[2 * MAXD], nc;
static char inC[MAXD * MAXD];
static long long evals;

static inline int mul(int g, int h) {
    int a = g / k, j = g % k, b = h / k, l = h % k;
    return ((a + (long)pw[j] * b) % m) * k + (j + l) % k;
}
static inline int inv(int g) {
    int a = g / k, j = g % k;
    int jj = (k - j) % k;
    int aa = (int)((m - ((long)ipw[j] * a) % m) % m);
    return aa * k + jj;
}

static unsigned long long rs;
static inline unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static double now(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec;
}

/* Full recompute, a copy of misses()/cost() in haar_search.c (uses the closed-form mul/inv, not the tables). */
static int misses(const int *X, int side) {
    static int T[MAXD * MAXD];
    int nt = 0;
    cur++;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++) {
            int t = side == 0 ? mul(inv(X[i]), X[j]) : mul(X[i], inv(X[j]));
            if (stamp[t] != cur) { stamp[t] = cur; T[nt++] = t; }
        }
    cur++;
    int cov_ = 0;
    for (int i = 0; i < nt; i++)
        for (int j = 0; j < nt; j++) {
            int t = mul(T[i], T[j]);
            if (stamp[t] != cur) { stamp[t] = cur; cov_++; }
        }
    return N - cov_;
}
static int full_cost(const int *X) { return misses(X, 0) + misses(X, 1); }

static inline int used(int x, int n) {
    for (int j = 0; j < n; j++) if (S[j] == x) return 1;
    return 0;
}

static inline int pairprod(int side, int x, int y) {
    return side == 0 ? MT[IT[x] * N + y] : MT[x * N + IT[y]];
}

static inline void bump(int side, int g, int sign) {
    if (sign > 0) { if (cov[side][g]++ == 0) covered[side]++; }
    else if (--cov[side][g] == 0) covered[side]--;
}

static inline int curcost(void) { return 2 * N - covered[0] - covered[1]; }

/* pairs p = i*d + j whose product involves S_i */
static void set_C(int i) {
    nc = 0;
    memset(inC, 0, nd);
    for (int j = 0; j < d; j++) { int p = i * d + j; inC[p] = 1; Cset[nc++] = p; }
    for (int q = 0; q < d; q++) {
        if (q == i) continue;
        int p = q * d + i; inC[p] = 1; Cset[nc++] = p;
    }
}

/* add (sign +1) or remove (sign -1) every word tp[p]*tp[q] with p in C or q in C */
static void words(int side, int sign) {
    const int *t = tp[side];
    for (int a = 0; a < nc; a++) {
        int p = Cset[a];
        for (int q = 0; q < nd; q++) bump(side, MT[t[p] * N + t[q]], sign);
    }
    for (int a = 0; a < nc; a++) {
        int q = Cset[a];
        for (int p = 0; p < nd; p++)
            if (!inC[p]) bump(side, MT[t[p] * N + t[q]], sign);
    }
}

/* S[i] = x, with incremental update of both coverage tables */
static void setel(int i, int x) {
    set_C(i);
    words(0, -1);
    words(1, -1);
    S[i] = x;
    for (int s = 0; s < 2; s++)
        for (int a = 0; a < nc; a++) {
            int p = Cset[a];
            tp[s][p] = pairprod(s, S[p / d], S[p % d]);
        }
    words(0, +1);
    words(1, +1);
}

static void init_state(void) {
    memset(cov[0], 0, sizeof(int) * N);
    memset(cov[1], 0, sizeof(int) * N);
    covered[0] = covered[1] = 0;
    for (int s = 0; s < 2; s++)
        for (int p = 0; p < nd; p++) tp[s][p] = pairprod(s, S[p / d], S[p % d]);
    for (int s = 0; s < 2; s++)
        for (int p = 0; p < nd; p++)
            for (int q = 0; q < nd; q++) bump(s, MT[tp[s][p] * N + tp[s][q]], +1);
}

static void random_start(void) {
    S[0] = 0;   /* left-translating S leaves the diameter test unchanged, so S[0] = identity WLOG */
    for (int i = 1; i < d; i++) {
        int x;
        do { x = rnd() % N; } while (used(x, i));
        S[i] = x;
    }
}

int main(int argc, char **argv) {
    int check = argc > 1 && strcmp(argv[1], "check") == 0;
    int a = check ? 2 : 1;
    if (argc < a + 5 + (check ? 0 : 1)) {
        fprintf(stderr, "usage: haar_search2 d m k lam seed seconds [outfile|-] [K]\n"
                        "       haar_search2 check d m k lam seed\n");
        return 1;
    }
    d = atoi(argv[a]); m = atoi(argv[a + 1]); k = atoi(argv[a + 2]); lam = atoi(argv[a + 3]);
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[a + 4]) * 2654435761ULL;
    double secs = check ? 0 : atof(argv[a + 5]);
    const char *out = (!check && argc > a + 6 && strcmp(argv[a + 6], "-")) ? argv[a + 6] : NULL;
    int K = (!check && argc > a + 7) ? atoi(argv[a + 7]) : 20;
    if (d > MAXD || K < 1) { fprintf(stderr, "d > %d or K < 1\n", MAXD); return 1; }
    N = m * k; nd = d * d;

    pw = malloc(sizeof(int) * k); ipw = malloc(sizeof(int) * k);
    pw[0] = 1 % m;
    for (int j = 1; j < k; j++) pw[j] = (int)((long)pw[j - 1] * lam % m);
    if ((long)pw[k - 1] * lam % m != 1 % m) { fprintf(stderr, "lam^k != 1\n"); return 1; }
    for (int j = 0; j < k; j++) ipw[j] = pw[(k - j) % k];

    MT = malloc(sizeof(uint16_t) * (size_t)N * N);
    IT = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) {
        IT[g] = inv(g);
        for (int h = 0; h < N; h++) MT[g * N + h] = (uint16_t)mul(g, h);
    }
    stamp = calloc(N, sizeof(int));
    cov[0] = calloc(N, sizeof(int));
    cov[1] = calloc(N, sizeof(int));

    if (check) {
        int ok = 1;
        for (int trial = 0; trial < 20 && ok; trial++) {
            random_start();
            init_state();
            if (curcost() != full_cost(S)) { ok = 0; break; }
            for (int it = 0; it < 500 && ok; it++) {
                int i = 1 + rnd() % (d - 1);
                int x, old = S[i];
                do { x = rnd() % N; } while (used(x, d));
                setel(i, x);
                if (curcost() != full_cost(S)) { ok = 0; printf("mismatch trial %d move %d\n", trial, it); break; }
                if (it % 3 == 0) {          /* revert some moves, check they restore the cost */
                    int before = curcost();
                    setel(i, old);
                    if (curcost() != full_cost(S)) { ok = 0; printf("revert mismatch\n"); break; }
                    setel(i, x);
                    if (curcost() != before) { ok = 0; printf("re-apply mismatch\n"); break; }
                }
            }
        }
        printf("check %s (d=%d m=%d k=%d lam=%d N=%d)\n", ok ? "OK" : "FAILED", d, m, k, lam, N);
        return ok ? 0 : 1;
    }

    int bestc = 1 << 30, restarts = 0;
    long long steps = 0;
    double t0 = now();
    while (now() - t0 < secs && bestc > 0) {
        restarts++;
        random_start();
        init_state();
        int c = curcost();
        double T0 = 2.0, temp = T0;
        long since = 0;
        int runbest = c;
        while (c > 0 && now() - t0 < secs) {
            steps++;
            int bi = -1, bx = 0, bc = 1 << 30;
            for (int t = 0; t < K; t++) {
                int i = 1 + rnd() % (d - 1);
                int nw, old = S[i];
                do { nw = rnd() % N; } while (used(nw, d));
                setel(i, nw);
                int c2 = curcost();
                setel(i, old);
                evals++;
                if (c2 < bc) { bc = c2; bi = i; bx = nw; }
            }
            if (bc <= c || exp((c - bc) / temp) * 4294967296.0 > (double)(rnd() & 0xffffffffULL)) {
                setel(bi, bx);
                c = bc;
                if (c < runbest) { runbest = c; since = 0; } else since++;
            } else {
                since++;
            }
            temp = T0 * exp(-(double)(since % 20000) / 4000.0) + 0.05;
            if (c < bestc) { bestc = c; memcpy(best, S, sizeof(int) * d); }
            if (since > 60000) break;
        }
    }
    double el = now() - t0;
    printf("d=%d m=%d k=%d lam=%d N=%d n=%d K=%d best=%d restarts=%d steps=%lld evals=%lld time=%.1f evals_per_s=%.0f\n",
           d, m, k, lam, N, 2 * N, K, bestc, restarts, steps, evals, el, evals / el);
    if (bestc == 0 && out) {
        if (full_cost(best) != 0) { fprintf(stderr, "internal: full_cost disagrees on best\n"); return 2; }
        FILE *f = fopen(out, "w");
        fprintf(f, "%d %d %d %d\n", d, m, k, lam);
        for (int i = 0; i < d; i++) fprintf(f, "%d %d\n", best[i] / k, best[i] % k);
        fclose(f);
    }
    return 0;
}
