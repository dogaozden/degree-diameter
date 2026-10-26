/* Card v3: maximise |(S-S)+(S-S)| over 6-subsets S of a finite abelian group.
 * Usage: climb <iters_random> <restarts> <climb_iters> <seed> m1 [m2 ...]
 *   group = Z_m1 x Z_m2 x ...  (order N = prod m_i, must be <= 1<<16)
 * Prints: group order, best value found by random sampling, best value by annealing,
 *         and the best set S (as tuples). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define D 6
static int K, mod[8], N;
static int *addt, *negt;
static unsigned long long rs;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs;
}
static int rndint(int n) { return (int)(rnd() % (unsigned long long)n); }

static void decode(int x, int *c) {
    for (int i = K - 1; i >= 0; i--) { c[i] = x % mod[i]; x /= mod[i]; }
}
static int encode(const int *c) {
    int x = 0;
    for (int i = 0; i < K; i++) x = x * mod[i] + ((c[i] % mod[i]) + mod[i]) % mod[i];
    return x;
}

static int *mark1, *mark2, *Dlist;
static int stamp1 = 1, stamp2 = 1;

/* value = |(S-S)+(S-S)| */
static int value(const int *S) {
    int nd = 0;
    stamp1++;
    /* S-S */
    for (int i = 0; i < D; i++)
        for (int j = 0; j < D; j++) {
            int x = addt[S[i] * N + negt[S[j]]];
            if (mark1[x] != stamp1) { mark1[x] = stamp1; Dlist[nd++] = x; }
        }
    stamp2++;
    int cnt = 0;
    for (int i = 0; i < nd; i++)
        for (int j = 0; j < nd; j++) {
            int x = addt[Dlist[i] * N + Dlist[j]];
            if (mark2[x] != stamp2) { mark2[x] = stamp2; cnt++; }
        }
    return cnt;
}

static void randset(int *S) {
    for (int i = 0; i < D; i++) {
        int x, ok;
        do {
            x = rndint(N); ok = 1;
            for (int j = 0; j < i; j++) if (S[j] == x) ok = 0;
        } while (!ok);
        S[i] = x;
    }
}

static void print_set(const char *tag, int val, const int *S) {
    printf("%s value=%d S=", tag, val);
    for (int i = 0; i < D; i++) {
        int c[8]; decode(S[i], c);
        printf("%s(", i ? " " : "");
        for (int k = 0; k < K; k++) printf("%d%s", c[k], k < K - 1 ? "," : "");
        printf(")");
    }
    printf("\n");
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage\n"); return 1; }
    long iters_random = atol(argv[1]);
    int restarts = atoi(argv[2]);
    long climb_iters = atol(argv[3]);
    rs = strtoull(argv[4], NULL, 10) * 2654435761ULL + 88172645463325252ULL;
    K = argc - 5;
    N = 1;
    for (int i = 0; i < K; i++) { mod[i] = atoi(argv[5 + i]); N *= mod[i]; }
    if (N > 65536) { fprintf(stderr, "too big\n"); return 1; }
    addt = malloc(sizeof(int) * N * N);
    negt = malloc(sizeof(int) * N);
    int a[8], b[8], c[8];
    for (int x = 0; x < N; x++) {
        decode(x, a);
        for (int k = 0; k < K; k++) c[k] = (mod[k] - a[k]) % mod[k];
        negt[x] = encode(c);
        for (int y = 0; y < N; y++) {
            int bb[8]; decode(y, bb);
            for (int k = 0; k < K; k++) c[k] = (a[k] + bb[k]) % mod[k];
            addt[x * N + y] = encode(c);
        }
    }
    mark1 = calloc(N, sizeof(int)); mark2 = calloc(N, sizeof(int));
    Dlist = malloc(sizeof(int) * (D * D + 1));

    int S[D], best[D], bestv = -1;
    /* 1. plain random sampling */
    int rmax = -1; int rS[D];
    int hist_top = 0;
    for (long t = 0; t < iters_random; t++) {
        randset(S);
        int v = value(S);
        if (v > rmax) { rmax = v; memcpy(rS, S, sizeof S); }
        if (v == rmax) hist_top++;
    }
    /* 2. simulated annealing hill-climb with restarts */
    for (int r = 0; r < restarts; r++) {
        int cur[D], cv;
        randset(cur); cv = value(cur);
        for (long t = 0; t < climb_iters; t++) {
            double T = 1.5 * (1.0 - (double)t / climb_iters) + 0.05;
            int i = rndint(D);
            int x, ok;
            do {
                x = rndint(N); ok = 1;
                for (int j = 0; j < D; j++) if (cur[j] == x) ok = 0;
            } while (!ok);
            int old = cur[i];
            cur[i] = x;
            int nv = value(cur);
            int diff = nv - cv;
            if (diff >= 0 || (double)(rnd() % 1000000) / 1e6 < __builtin_exp(diff / T)) {
                cv = nv;
                if (cv > bestv) { bestv = cv; memcpy(best, cur, sizeof cur); }
            } else cur[i] = old;
        }
    }
    printf("group order=%d moduli=", N);
    for (int k = 0; k < K; k++) printf("%d%s", mod[k], k < K - 1 ? "x" : "");
    printf("\n");
    print_set("random_best", rmax, rS);
    print_set("anneal_best", bestv, best);
    int mx = rmax > bestv ? rmax : bestv;
    printf("MAX %d\n", mx);
    return 0;
}
