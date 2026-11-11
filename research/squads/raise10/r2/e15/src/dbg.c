/* e15: exhaustive / sampled search for Haar graphs H(G,S) of G = Z_p x|_r Z_k (r of order k mod p)
 * with S = {e} + t phi-orbits + f alpha-fixed elements, where phi(a,b) = (u a, b) is an automorphism of G of order m.
 * Only S invariant under phi are considered (the orbit-symmetric family).
 * Usage: symhaar d D p k m mode CAP seed
 *   mode 0: exhaustive if the family has <= CAP members, else CAP random samples; mode 1: always CAP random samples.
 * Output line: RES p k m d D cand best_cost  (and S when cost 0, written to stdout as "SOL ...").
 * Cost = number of (vertex, source) pairs at distance > D from (e,A) and (e,B).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned long long u64;
static int P, K, R, M, D, d, N;
static int *rp;            /* r^b mod P */
static int *orbrep; static int nrep;   /* orbit representative elements (a != 0) */
static int *Lm, *Li;       /* left mult tables: Lm[i*N+g] = s_i g, Li[i*N+g] = s_i^{-1} g */
static int *S;             /* chosen element indices, S[0] = 0 (= e) */
static int *dist, *queue;
static int U;              /* automorphism multiplier u of order M in Z_P^* */
static u64 rs = 88172645463325252ULL;
static long long cand = 0, best = 1LL << 60; static int bestS[64];
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int mulg(int g1, int g2) {
    int a1 = g1 / K, b1 = g1 % K, a2 = g2 / K, b2 = g2 % K;
    int a = (int)((a1 + (long long)rp[b1] * a2) % P);
    int b = (b1 + b2) % K;
    return a * K + b;
}
static int invg(int g) {
    int a = g / K, b = g % K;
    int ap = (int)(((long long)(P - a) % P) * rp[(K - b) % K] % P);
    return ap * K + ((K - b) % K);
}
static long long evalS(void) {
    /* build tables for the d elements in S */
    for (int i = 0; i < d; i++) {
        int s = S[i], si = invg(s);
        for (int g = 0; g < N; g++) { Lm[i * N + g] = mulg(s, g); Li[i * N + g] = mulg(si, g); }
    }
    long long cost = 0;
    int srcs[2] = {0, N};
    for (int q = 0; q < 2; q++) {
        for (int v = 0; v < 2 * N; v++) dist[v] = -1;
        int h = 0, tl = 0; queue[tl++] = srcs[q]; dist[srcs[q]] = 0;
        while (h < tl) {
            int v = queue[h++]; int dv = dist[v];
            if (dv >= D) continue;
            if (v < N) {
                for (int i = 0; i < d; i++) { int w = N + Lm[i * N + v]; if (dist[w] < 0) { dist[w] = dv + 1; queue[tl++] = w; } }
            } else {
                int g = v - N;
                for (int i = 0; i < d; i++) { int w = Li[i * N + g]; if (dist[w] < 0) { dist[w] = dv + 1; queue[tl++] = w; } }
            }
        }
        { int rc=0, mx=0; for (int v = 0; v < 2 * N; v++) { if (dist[v] >= 0) rc++; if (dist[v] > mx) mx = dist[v]; if (dist[v] < 0 || dist[v] > D) cost++; } if (getenv("DBG")) fprintf(stderr, "src %d reached %d maxd %d tl %d\n", q, rc, mx, tl); }
    }
    return cost;
}
static void record(long long c) {
    cand++;
    if (c < best) {
        best = c; memcpy(bestS, S, sizeof(int) * d);
    }
    if (c == 0) {
        printf("SOL p=%d k=%d r=%d m=%d d=%d D=%d S=", P, K, R, M, d, D);
        for (int i = 0; i < d; i++) printf("%d,%d%s", S[i] / K, S[i] % K, i + 1 < d ? ";" : "\n");
        fflush(stdout);
    }
}
/* orbit of rep (a,b): elements (u^j a, b), j=0..M-1 */
static int orbit_elem(int rep, int j) {
    int a = rep / K, b = rep % K;
    long long x = a; for (int t = 0; t < j; t++) x = x * U % P;
    return (int)x * K + b;
}
static int nfix;   /* fixed points available: (0,c), c=1..K-1 -> element c */
static int T, F;   /* orbits and fixed points in this family */
static int ids[64];
static int exhaustive_rec(int stage, int start, int *picked, int *nf) {
    /* stage 0..T-1: choose orbit reps, then F fixed points; returns 1 when CAP exhausted */
    return 0;
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: symhaar d D p k m mode CAP seed\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); P = atoi(argv[3]); K = atoi(argv[4]); M = atoi(argv[5]);
    int mode = atoi(argv[6]); long long CAP = atoll(argv[7]); rs ^= (u64)atoll(argv[8]) * 2654435761ULL + 1;
    N = P * K;
    if ((P - 1) % K || (P - 1) % M) { printf("bad p k m\n"); return 1; }
    /* find r of order exactly K mod P */
    R = -1;
    for (int r = 2; r < P && R < 0; r++) {
        long long x = 1; int ord = 0;
        do { x = x * r % P; ord++; } while (x != 1 && ord <= K);
        if (ord == K) R = r;
    }
    if (R < 0) { printf("no r\n"); return 1; }
    rp = malloc(sizeof(int) * K); rp[0] = 1 % P; for (int b = 1; b < K; b++) rp[b] = (int)((long long)rp[b - 1] * R % P);
    /* u of order M */
    U = -1;
    for (int u = 2; u < P && U < 0; u++) {
        long long x = 1; int ord = 0;
        do { x = x * u % P; ord++; } while (x != 1 && ord <= M);
        if (ord == M) U = u;
    }
    if (M == 1) U = 1;
    if (U < 0) { printf("no u\n"); return 1; }
    /* orbit reps: elements (a,b) a != 0 with a minimal in its orbit */
    orbrep = malloc(sizeof(int) * N); nrep = 0;
    for (int a = 1; a < P; a++) for (int b = 0; b < K; b++) {
        int e = a * K + b, ok = 1;
        for (int j = 1; j < M && ok; j++) if (orbit_elem(e, j) < e) ok = 0;
        if (ok) orbrep[nrep++] = e;
    }
    /* families: d-1 = T*M + F, T >= 1, F <= K-1 */
    Lm = malloc(sizeof(int) * (size_t)d * N); Li = malloc(sizeof(int) * (size_t)d * N);
    S = malloc(sizeof(int) * d); dist = malloc(sizeof(int) * 2 * N); queue = malloc(sizeof(int) * 2 * N);
    int fam = 0;
    for (T = 1; T * M <= d - 1; T++) {
        F = d - 1 - T * M; if (F > K - 1) continue;
        fam++;
        /* count of family members (as doubles) */
        double cnt = 1; for (int i = 0; i < T; i++) cnt = cnt * (nrep - i) / (i + 1);
        for (int i = 0; i < F; i++) cnt = cnt * (K - 1 - i) / (i + 1);
        int exhaustive = (mode == 0 && cnt <= (double)CAP);
        if (exhaustive && T == 1 && F == 0) {
            for (int i = 0; i < nrep; i++) {
                S[0] = 0; for (int j = 0; j < M; j++) S[1 + j] = orbit_elem(orbrep[i], j);
                if (1 + M != d) continue;
                record(evalS());
            }
        } else {
            for (long long it = 0; it < CAP; it++) {
                /* random T distinct orbit reps (all as full orbits), F distinct fixed points (0,c) */
                int n = 0; S[n++] = 0; int ok = 1;
                for (int t = 0; t < T && ok; t++) {
                    int e = orbrep[rnd() % nrep];
                    for (int j = 0; j < M; j++) {
                        int x = orbit_elem(e, j);
                        for (int q = 0; q < n; q++) if (S[q] == x) ok = 0;
                        if (n < d) S[n++] = x; else ok = 0;
                    }
                }
                for (int f = 0; f < F && ok; f++) {
                    int c = 1 + (int)(rnd() % (K - 1));
                    int x = c; for (int q = 0; q < n; q++) if (S[q] == x) ok = 0;
                    if (n < d) S[n++] = x; else ok = 0;
                }
                if (!ok || n != d) continue;
                record(evalS());
            }
        }
    }
    printf("RES p=%d k=%d r=%d m=%d u=%d N=%d d=%d D=%d families=%d cand=%lld best=%lld bestS=", P, K, R, M, U, N, d, D, fam, cand, best);
    for (int i = 0; i < d; i++) printf("%d,%d%s", bestS[i] / K, bestS[i] % K, i + 1 < d ? ";" : "\n");
    return 0;
}
