// d14: bi-Cayley graph over a Frobenius group G = AGL(1,p) = {x -> a x + b}, |G| = p(p-1), |S| = 17.
// Bipartite graph: (g,0) ~ (s g,1) for s in S, 2|G| vertices, 17-regular.
// Reduction (proved in NOTES): diameter <= 5  <=>  M*M = G, where M = S^{-1} S (contains 1).
// (Same-side distances from (1,0) are the even words M, M*M; cross distances are S*M*M = G automatically.)
// Cost = |G| - |M*M|  (uncovered elements). Simulated annealing over S with 1 in S (left-translation normal form).
// usage: mm P seconds seed statefile_in_or_- statefile_out
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

#define K 17
static int P, N;
static int INV1[1 << 12];
static double now(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+ts.tv_nsec*1e-9; }
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
/* element encoding: id = (a-1)*P + b, a in 1..P-1, b in 0..P-1 ; identity = 0 */
static inline void dec(int g, int *a, int *b){ *a = g / P + 1; *b = g % P; }
static inline int enc(int a, int b){ return (a - 1) * P + b; }
static int ginv(int g){ int a, b; dec(g, &a, &b); int ai = INV1[a]; return enc(ai, (P - (ai * b) % P) % P); }

static int S[K];
static unsigned char *cov;
static int *Mel; static int *stamp; static int gen = 1;
static int Ma[K * K], Mb[K * K], nM;

static int cost(void) {
    /* M = S^{-1} S distinct */
    gen++; nM = 0;
    for (int i = 0; i < K; i++) {
        int si = ginv(S[i]); int a1, b1; dec(si, &a1, &b1);
        for (int j = 0; j < K; j++) {
            int x = 0; int a2, b2; dec(S[j], &a2, &b2);
            /* product si * S[j] = (a1 a2, a1 b2 + b1) */
            int a = (a1 * a2) % P, b = (a1 * b2 + b1) % P;
            x = enc(a, b);
            if (stamp[x] != gen) { stamp[x] = gen; Ma[nM] = a; Mb[nM] = b; nM++; }
        }
    }
    memset(cov, 0, N);
    int cnt = 0;
    for (int i = 0; i < nM; i++) {
        int a1 = Ma[i], b1 = Mb[i];
        for (int j = 0; j < nM; j++) {
            int a2 = Ma[j], b2 = Mb[j];
            int a = (a1 * a2) % P, b = (a1 * b2 + b1) % P;
            int x = enc(a, b);
            if (!cov[x]) { cov[x] = 1; cnt++; }
        }
    }
    return N - cnt;
}

static int inS(int g, int upto) { for (int i = 0; i < upto; i++) if (S[i] == g) return 1; return 0; }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: mm P seconds seed statein statefile_out\n"); return 1; }
    P = atoi(argv[1]); double secs = atof(argv[2]); rs = strtoull(argv[3], 0, 10) * 2654435761ULL + 88172645463325252ULL;
    const char *fin = argv[4], *fout = argv[5];
    N = P * (P - 1);
    for (int a = 1; a < P; a++) for (int t = 1; t < P; t++) if ((a * t) % P == 1) { INV1[a] = t; break; }
    cov = malloc(N); stamp = calloc(N, sizeof(int));
    int have = 0;
    if (strcmp(fin, "-") != 0) {
        FILE *f = fopen(fin, "r");
        if (f) { for (int i = 0; i < K; i++) if (fscanf(f, "%d", &S[i]) != 1) break; else have++; fclose(f); }
    }
    if (have != K) {
        S[0] = 0; int n = 1;
        while (n < K) { int g = rnd() % N; if (!inS(g, n)) S[n++] = g; }
    }
    int cur = cost(), best = cur; int bestS[K]; memcpy(bestS, S, sizeof S);
    double t0 = now(), T0 = getenv("T0")?atof(getenv("T0")):3.0, T1 = getenv("T1")?atof(getenv("T1")):0.2; long it = 0, acc = 0;
    while (1) {
        double el = now() - t0; if (el > secs) break;
        double frac = el / secs; double T = T0 * pow(T1 / T0, frac);
        int i = 1 + rnd() % (K - 1); int old = S[i];
        int g = rnd() % N; if (inS(g, K)) continue;
        S[i] = g;
        int c = cost(); it++;
        if (c <= cur || exp(-(c - cur) / T) > (rnd() % 1000000) / 1e6) {
            cur = c; acc++;
            if (c < best) { best = c; memcpy(bestS, S, sizeof S); }
            if (c == 0) break;
        } else S[i] = old;
    }
    FILE *f = fopen(fout, "w");
    for (int i = 0; i < K; i++) { int a, b; dec(bestS[i], &a, &b); fprintf(f, "%d\n", bestS[i]); }
    fclose(f);
    printf("P=%d N=%d iters=%ld acc=%ld best_cost=%d final_cur=%d time=%.1f\n", P, N, it, acc, best, cur, now() - t0);
    if (best == 0) printf("FOUND\n");
    return 0;
}
