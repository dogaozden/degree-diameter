/* c06 (r3): plain random-S annealing on G = F_512 x| C_73, Haar graph H(G,S), S = {e,s1,s2,s3}, target (4,12) with N = 37,376.
 * Same group, same cost as r2/b01/frobA.c (cost = B-elements not within 11 of (e,A)); changes vs frobA:
 *   - left-multiplication tables F[i][g] = s_i g and B[i][y] = s_i^-1 y are kept up to date (no gmul in the BFS inner loop),
 *   - uncovered B list collected during the cost pass (targeted move needs no rejection sampling),
 *   - restart-from-best option (RESET=1: each cooling cycle restarts from the best state), state in/out files,
 *   - "swap" mode: exhaustive single-generator replacement scan of a saved state (all s_i <- x, i = 1..3, x in [lo,hi)).
 * Usage:
 *   anneal SEED SECS T0 RESET STARTFILE|- OUTFILE     writes OUTFILE (4 group indices of S) for the best state; on cost 0 also OUTFILE.edges
 *   swap STATEFILE LO HI [THR]                          prints every (i,x) with cost <= THR (default 2) and the min
 *   eval STATEFILE                                      prints the cost of a saved state
 * Group element index g = v*73 + j, v in GF(512), j in Z_73. Edge list of H(G,S): 2N vertices, A = g, B = N + g, edges (g, N + s g).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#define NF 512
#define K 73
#define N (NF * K)
static int expt[2 * NF], logt[NF], pw7[K];
static uint8_t dist[2 * N];
static int q[2 * N];
static int qlen;
static int uncov[N];
static int nunc;
static int S[4], Sinv[4];
static int F[4][N], Bt[4][N];   /* F[i][g] = S[i]*g ; Bt[i][y] = Sinv[i]*y */
static uint8_t bdist[2 * N]; static int bq[2 * N], bqlen, bunc[N], bnunc, bF[N], bBt[N]; /* backup for rejected moves */
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double wall(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static int fmul(int a, int b) { if (!a || !b) return 0; return expt[logt[a] + logt[b]]; }
static inline int gmul(int g1, int g2) {
    int v1 = g1 / K, j1 = g1 % K, v2 = g2 / K, j2 = g2 % K;
    int v = v1 ^ fmul(pw7[j1], v2);
    int j = (j1 + j2) % K;
    return v * K + j;
}
static int ginv(int g) {
    int v = g / K, j = g % K;
    int jinv = (K - j) % K;
    int vi = fmul(pw7[jinv], v);
    return vi * K + jinv;
}
static void init_field(void) {
    int poly = (1 << 9) | (1 << 4) | 1, e = 1;
    for (int i = 0; i < 511; i++) { expt[i] = e; expt[i + 511] = e; e <<= 1; if (e & 512) e ^= poly; }
    for (int i = 0; i < 511; i++) logt[expt[i]] = i;
    for (int j = 0; j < K; j++) pw7[j] = expt[(7 * j) % 511];
}
static int distinct(void) { for (int i = 0; i < 4; i++) for (int j = 0; j < i; j++) if (S[i] == S[j]) return 0; return 1; }
/* out[g] = (c, sj) * g for all g: v' = c ^ z^sj v, j' = sj + j (same as gmul, tabulated per v) */
static void leftperm(int c, int sj, int *out) {
    int mul[NF];
    for (int v = 0; v < NF; v++) mul[v] = c ^ fmul(pw7[sj], v);
    for (int v = 0; v < NF; v++) for (int j = 0; j < K; j++) out[v * K + j] = mul[v] * K + (sj + j) % K;
}
static void setgen(int i) {
    Sinv[i] = ginv(S[i]);
    leftperm(S[i] / K, S[i] % K, F[i]);
    leftperm(Sinv[i] / K, Sinv[i] % K, Bt[i]);
}
static void setall(void) { for (int i = 0; i < 4; i++) setgen(i); }
/* BFS from (e,A) to depth 11; returns number of uncovered B-elements; fills uncov[] */
static int holes(void) {
    memset(dist, 255, 2 * N);
    int head = 0, tail = 0;
    q[tail++] = 0; dist[0] = 0;
    while (head < tail) {
        int v = q[head++]; int d = dist[v];
        if (d >= 11) continue;
        if (v < N) {
            for (int i = 0; i < 4; i++) { int w = N + F[i][v]; if (dist[w] == 255) { dist[w] = d + 1; q[tail++] = w; } }
        } else {
            int y = v - N;
            for (int i = 0; i < 4; i++) { int w = Bt[i][y]; if (dist[w] == 255) { dist[w] = d + 1; q[tail++] = w; } }
        }
    }
    qlen = tail;
    nunc = 0;
    for (int v = N; v < 2 * N; v++) if (dist[v] == 255) uncov[nunc++] = v - N;
    return nunc;
}
static void write_state(const char *fn) { FILE *f = fopen(fn, "w"); if (!f) return; fprintf(f, "%d %d %d %d\n", S[0], S[1], S[2], S[3]); fclose(f); }
static int read_state(const char *fn) { FILE *f = fopen(fn, "r"); if (!f) return 0; int ok = fscanf(f, "%d %d %d %d", &S[0], &S[1], &S[2], &S[3]) == 4; fclose(f); return ok; }
static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", 2 * N);
    for (int g = 0; g < N; g++) for (int i = 0; i < 4; i++) fprintf(f, "%d %d\n", g, N + F[i][g]);
    fclose(f);
}
int main(int argc, char **argv) {
    init_field();
    if (argc < 2) return 1;
    if (!strcmp(argv[1], "eval")) {
        if (!read_state(argv[2])) return 1;
        S[0] = 0; if (!distinct()) { printf("not distinct\n"); return 1; }
        setall(); printf("cost %d\n", holes()); return 0;
    }
    if (!strcmp(argv[1], "swap")) {
        if (!read_state(argv[2])) return 1;
        int lo = atoi(argv[3]), hi = atoi(argv[4]), thr = argc > 5 ? atoi(argv[5]) : 2;
        int base[4]; memcpy(base, S, sizeof S);
        setall(); int c0 = holes();
        printf("base cost %d\n", c0);
        int best = 1 << 30, bi = -1, bx = -1; long tested = 0; long hist[8] = {0};
        for (int i = 1; i < 4; i++) {
            for (int x = lo; x < hi && x < N; x++) {
                if (x == 0 || x == base[i]) continue;
                int ok = 1; for (int j = 0; j < 4; j++) if (j != i && base[j] == x) ok = 0;
                if (!ok) continue;
                S[0] = 0; memcpy(S, base, sizeof base); S[i] = x; if (!distinct()) continue;
                setgen(i);
                int c = holes(); tested++;
                if (c < 8) hist[c]++;
                if (c < best) { best = c; bi = i; bx = x; }
                if (c <= thr) { printf("cost %d i %d x %d S %d %d %d %d\n", c, i, x, S[0], S[1], S[2], S[3]); fflush(stdout); }
                if (c == 0) {
                    char fn[256]; sprintf(fn, "%s.edges", argv[2]); write_edges(fn);
                    sprintf(fn, "%s.zero", argv[2]); write_state(fn);
                }
                memcpy(S, base, sizeof base); setgen(i);
            }
        }
        printf("swap [%d,%d) tested=%ld best=%d (i %d x %d) hist(c<8):", lo, hi, tested, best, bi, bx);
        for (int c = 0; c < 8; c++) printf(" %d:%ld", c, hist[c]);
        printf("\n");
        return 0;
    }
    if (!strcmp(argv[1], "anneal")) {
        uint64_t seed = strtoull(argv[2], 0, 10); double secs = atof(argv[3]);
        double T0 = atof(argv[4]); int reset = atoi(argv[5]);
        const char *start = argv[6], *outf = argv[7];
        rs ^= seed * 2654435761ULL; for (int i = 0; i < 10; i++) rnd();
        int bestS[4]; int bestC = 1 << 30;
        double t0 = wall();
        long evals = 0, cycles = 0;
        int have_start = strcmp(start, "-") && read_state(start);
        if (!have_start) { S[0] = 0; do { for (int i = 1; i < 4; i++) S[i] = 1 + rnd() % (N - 1); } while (!distinct()); }
        setall(); int C = holes(); evals++;
        memcpy(bestS, S, sizeof S); bestC = C;
        int curS[4]; memcpy(curS, S, sizeof S);
        const long L = getenv("CYC") ? atol(getenv("CYC")) : 20000; /* cooling cycle length in steps (env CYC) */
        long step = 0; double lastrep = t0;
        while (C > 0) {
            step++;
            if ((step & 15) == 0) {
                double el = wall() - t0;
                if (el > secs) break;
                if (el - (lastrep - t0) > 10.0) { lastrep = wall(); printf("t %.0f evals %ld cur %d best %d cycles %ld\n", el, evals, C, bestC, cycles); fflush(stdout); }
            }
            if (step % L == 0) {
                cycles++;
                if (reset) { memcpy(S, bestS, sizeof S); setall(); C = holes(); evals++; }
            }
            double frac = (double)(step % L) / (double)L;
            double T = T0 * (1.0 - 0.9 * frac);
            int old[4]; memcpy(old, S, sizeof old);
            int i = 1 + rnd() % 3;
            int nw;
            if (rnd() % 10 < 7) {
                int y = uncov[rnd() % nunc];
                int v, tv = 0;
                do { v = q[rnd() % qlen]; tv++; } while ((v >= N || dist[v] > 10) && tv < 100000);
                if (v >= N || dist[v] > 10) continue;
                nw = gmul(y, ginv(v));
            } else nw = 1 + rnd() % (N - 1);
            S[i] = nw;
            if (!distinct()) { memcpy(S, old, sizeof old); continue; }
            /* back up the BFS state of the current S so a rejected candidate costs no recomputation */
            memcpy(bdist, dist, 2 * N); memcpy(bq, q, sizeof(int) * qlen); bqlen = qlen;
            memcpy(bunc, uncov, sizeof(int) * nunc); bnunc = nunc;
            memcpy(bF, F[i], sizeof bF); memcpy(bBt, Bt[i], sizeof bBt);
            setgen(i);
            int Cn = holes(); evals++;
            int dlt = Cn - C;
            if (dlt <= 0 || (double)(rnd() % 1000000) / 1e6 < __builtin_exp(-dlt / T)) {
                C = Cn;
                if (C < bestC) { bestC = C; memcpy(bestS, S, sizeof S); }
            } else {
                memcpy(S, old, sizeof old);
                memcpy(dist, bdist, 2 * N); memcpy(q, bq, sizeof(int) * bqlen); qlen = bqlen;
                memcpy(uncov, bunc, sizeof(int) * bnunc); nunc = bnunc;
                memcpy(F[i], bF, sizeof bF); memcpy(Bt[i], bBt, sizeof bBt); Sinv[i] = ginv(S[i]);
            }
        }
        double el = wall() - t0;
        if (bestC == 0) {
            memcpy(S, bestS, sizeof S); setall(); int c = holes();
            printf("COST 0 seed %llu S %d %d %d %d check %d\n", (unsigned long long)seed, S[0], S[1], S[2], S[3], c);
            write_state(outf);
            char fn[256]; sprintf(fn, "%s.edges", outf); write_edges(fn);
        } else write_state(outf);
        printf("anneal seed %llu secs %.1f evals %ld (%.2f ms/eval) cycles %ld best_cost %d bestS %d %d %d %d\n",
               (unsigned long long)seed, el, evals, 1e3 * el / evals, cycles, bestC, bestS[0], bestS[1], bestS[2], bestS[3]);
        return 0;
    }
    return 1;
}
