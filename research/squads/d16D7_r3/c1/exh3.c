/* exh3.c: exhaustive over independent subsets T of the weight-3 quotient vertices (pts quotient), and for each T a
   simulated-annealing estimate of alpha(R_T), R_T = weight-9 quotient vertices with no neighbour in T.
   Total weight of the quotient set = 9*alpha + 3*|T| + 3 (the weight-1 vertices {0,1,2} are compatible with everything).
   usage: exh3 QUOT OUT ITER T0 T1 SEED
   OUT receives the best quotient set (ids of nines in the best set + threes of T + the caller adds the ones). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: exh3 QUOT OUT ITER T0 T1 SEED [RESTARTS] [ONLYMASK]\n"); return 1; }
    int RESTARTS = argc > 7 ? atoi(argv[7]) : 1; long long ONLY = argc > 8 ? atoll(argv[8]) : -1;
    int DUMP = argc > 9 ? atoi(argv[9]) : -1; const char *DUMPDIR = argc > 10 ? argv[10] : ".";
    long long ITER = atoll(argv[3]); double T0 = atof(argv[4]), T1 = atof(argv[5]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)atoll(argv[6]) * 0xD1B54A32D192ED03ULL); if (!rs) rs = 1;
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    int n; if (fscanf(f, "%d", &n) != 1) return 1;
    int *w = malloc(sizeof(int) * n), *deg = malloc(sizeof(int) * n), **nb = malloc(sizeof(int *) * n);
    for (int i = 0; i < n; i++) {
        if (fscanf(f, "%d %d", &w[i], &deg[i]) != 2) return 1;
        nb[i] = malloc(sizeof(int) * (deg[i] + 1));
        for (int k = 0; k < deg[i]; k++) if (fscanf(f, "%d", &nb[i][k]) != 1) return 1;
    }
    fclose(f);
    int *nid = malloc(sizeof(int) * n), *tid = malloc(sizeof(int) * n);
    int N = 0, M = 0;
    int *N9 = malloc(sizeof(int) * n), *T3 = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) {
        nid[i] = -1; tid[i] = -1;
        if (w[i] == 9) { nid[i] = N; N9[N++] = i; }
        else if (w[i] == 3) { tid[i] = M; T3[M++] = i; }
    }
    if (M > 24) { fprintf(stderr, "too many threes\n"); return 1; }
    /* nine-nine adjacency lists, three-nine masks (as bool arrays), three-three masks */
    int **nn = malloc(sizeof(int *) * N), *nnd = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) {
        int v = N9[a]; nn[a] = malloc(sizeof(int) * (deg[v] + 1)); nnd[a] = 0;
        for (int k = 0; k < deg[v]; k++) if (nid[nb[v][k]] >= 0) nn[a][nnd[a]++] = nid[nb[v][k]];
    }
    char *tn = calloc((size_t)M * N, 1);       /* tn[j*N+a] = 1 if three j adjacent to nine a */
    unsigned int *t33 = calloc(M, sizeof(unsigned int));
    for (int j = 0; j < M; j++) {
        int v = T3[j];
        for (int k = 0; k < deg[v]; k++) {
            int u = nb[v][k];
            if (nid[u] >= 0) tn[(size_t)j * N + nid[u]] = 1;
            if (tid[u] >= 0) t33[j] |= 1u << tid[u];
        }
    }
    fprintf(stderr, "nines %d threes %d\n", N, M);
    char *inS = calloc(N, 1), *bestS = calloc(N, 1), *allow = malloc(N);
    int *conf = malloc(sizeof(int) * N), *Al = malloc(sizeof(int) * N);
    int bestAlpha[25]; for (int t = 0; t <= M; t++) bestAlpha[t] = -1;
    int bestObj = -1; unsigned int bestMask = 0; char *bestNines = calloc(N, 1);
    long long masks = 0;
    for (unsigned int mask = 0; mask < (1u << M); mask++) {
        if (ONLY >= 0 && mask != (unsigned)ONLY) continue;
        int ok = 1, t = 0;
        for (int j = 0; j < M && ok; j++) if (mask >> j & 1) { t++; if (t33[j] & mask) ok = 0; }
        if (!ok) continue;
        masks++;
        int na = 0;
        for (int a = 0; a < N; a++) {
            allow[a] = 1;
            for (int j = 0; j < M; j++) if ((mask >> j & 1) && tn[(size_t)j * N + a]) { allow[a] = 0; break; }
            if (allow[a]) Al[na++] = a;
        }
        /* SA for maximum independent set on the allowed nines */
        int best = 0;
        for (int rr = 0; rr < RESTARTS && na > 0; rr++) {
        memset(inS, 0, N); memset(conf, 0, sizeof(int) * N);
        int cur = 0;
        for (long long it = 0; it < ITER && na > 0; it++) {
            double T = T0 * pow(T1 / T0, (double)it / (double)ITER);
            int v = Al[rnd() % (uint64_t)na];
            if (inS[v]) {
                if (urand() < exp(-1.0 / T)) {
                    inS[v] = 0; cur--;
                    for (int k = 0; k < nnd[v]; k++) conf[nn[v][k]]--;
                }
            } else {
                int c = conf[v], delta = 1 - c;
                if (delta >= 0 || urand() < exp((double)delta / T)) {
                    if (c > 0) {
                        for (int k = 0; k < nnd[v]; k++) {
                            int u = nn[v][k];
                            if (inS[u]) { inS[u] = 0; cur--; for (int q = 0; q < nnd[u]; q++) conf[nn[u][q]]--; }
                        }
                    }
                    inS[v] = 1; cur++;
                    for (int k = 0; k < nnd[v]; k++) conf[nn[v][k]]++;
                    if (cur > best) { best = cur; memcpy(bestS, inS, N); }
                }
            }
        }
        if (ONLY >= 0) fprintf(stderr, "mask %u restart %d alpha_run_best_so_far %d\n", mask, rr, best);
        }
        if (best > bestAlpha[t]) bestAlpha[t] = best;
        int obj = 3 * best + t;
        if (DUMP >= 0 && obj >= DUMP) {
            char fn[256]; snprintf(fn, sizeof fn, "%s/m%u_o%d.sol", DUMPDIR, mask, obj);
            FILE *d = fopen(fn, "w");
            if (d) {
                for (int a = 0; a < N; a++) if (bestS[a]) fprintf(d, "%d\n", N9[a]);
                for (int j = 0; j < M; j++) if (mask >> j & 1) fprintf(d, "%d\n", T3[j]);
                fclose(d);
            }
        }
        if (obj > bestObj) {
            bestObj = obj; bestMask = mask; memcpy(bestNines, bestS, N);
            fprintf(stderr, "new best obj %d (t=%d alpha=%d) mask %u\n", obj, t, best, mask);
        }
    }
    printf("masks %lld best_obj %d (quotient weight %d)\n", masks, bestObj, 3 * (bestObj + 1));
    for (int t = 0; t <= M; t++) if (bestAlpha[t] >= 0) printf("t=%d best_alpha=%d\n", t, bestAlpha[t]);
    FILE *o = fopen(argv[2], "w");
    if (!o) return 2;
    int cnt = 0;
    for (int a = 0; a < N; a++) if (bestNines[a]) { fprintf(o, "%d\n", N9[a]); cnt++; }
    for (int j = 0; j < M; j++) if (bestMask >> j & 1) { fprintf(o, "%d\n", T3[j]); cnt++; }
    fclose(o);
    printf("wrote %d vertices (without the weight-1 vertices)\n", cnt);
    return 0;
}
