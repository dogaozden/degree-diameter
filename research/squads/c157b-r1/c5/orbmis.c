/* orbmis: weighted independent set on the orbit graph of lines of H(11) (c5 card).
 * Orbit o (a set of lines) is usable iff no point lies on two of its lines. Two usable orbits conflict iff some point
 * lies on a line of each. Weight = orbit size. Simulated annealing over insertions (insert v, drop its chosen
 * neighbours), with restarts from the best set.
 * usage: orbmis HEXBIN LABELS SECONDS SEED OUT [TFAC0 TFAC1 ITERS]
 * LABELS: int32 per line (orbit id). OUT: line ids, one per line (union of chosen orbits). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: orbmis HEXBIN LABELS SECONDS SEED OUT [TFAC0 TFAC1 ITERS]\n"); return 1; }
    double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    double tf0 = argc > 6 ? atof(argv[6]) : 0.4, tf1 = argc > 7 ? atof(argv[7]) : 0.03;
    long iters = argc > 8 ? atol(argv[8]) : 2000000;
    /* hex */
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("hex"); return 1; }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1;
    int q = hdr[0], N = hdr[1], L = hdr[2], Q1 = q + 1;
    int32_t *LP = malloc(sizeof(int32_t) * (size_t)L * Q1);
    if (fread(LP, 4, (size_t)L * Q1, f) != (size_t)L * Q1) return 1; fclose(f);
    int32_t *lab = malloc(sizeof(int32_t) * L);
    f = fopen(argv[2], "rb"); if (!f) { perror("labels"); return 1; }
    if (fread(lab, 4, L, f) != (size_t)L) { fprintf(stderr, "bad labels\n"); return 1; } fclose(f);
    int K = 0; for (int l = 0; l < L; l++) if (lab[l] + 1 > K) K = lab[l] + 1;
    int *osz = calloc(K, sizeof(int)); for (int l = 0; l < L; l++) osz[lab[l]]++;
    /* point -> lines through it (each point on Q1 lines) */
    int32_t *PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *pc = calloc(N, sizeof(int));
    for (int l = 0; l < L; l++) for (int j = 0; j < Q1; j++) { int p = LP[(size_t)l * Q1 + j]; if (pc[p] >= Q1) { fprintf(stderr, "point degree\n"); return 1; } PL[(size_t)p * Q1 + pc[p]++] = l; }
    /* validity: orbit invalid iff two of its lines share a point */
    char *invalid = calloc(K, 1);
    for (int p = 0; p < N; p++) for (int j = 0; j < Q1; j++) for (int k = 0; k < j; k++)
        if (lab[PL[(size_t)p * Q1 + j]] == lab[PL[(size_t)p * Q1 + k]]) invalid[lab[PL[(size_t)p * Q1 + j]]] = 1;
    int *vid = malloc(sizeof(int) * K); int V = 0; int *vorb = malloc(sizeof(int) * K);
    for (int o = 0; o < K; o++) { if (!invalid[o] && osz[o] > 0) { vid[o] = V; vorb[V] = o; V++; } else vid[o] = -1; }
    /* members of valid orbits */
    int *mstart = calloc(V + 1, sizeof(int)); for (int v = 0; v < V; v++) mstart[v + 1] = mstart[v] + osz[vorb[v]];
    int *mem = malloc(sizeof(int) * (size_t)L); int *mfill = calloc(V, sizeof(int));
    for (int l = 0; l < L; l++) { int o = lab[l]; if (vid[o] < 0) continue; int v = vid[o]; mem[mstart[v] + mfill[v]++] = l; }
    /* cover lists: valid orbits through each point (distinct, <= Q1) */
    int32_t *cov = malloc(sizeof(int32_t) * (size_t)N * Q1); int *cc = calloc(N, sizeof(int));
    for (int p = 0; p < N; p++) for (int j = 0; j < Q1; j++) { int o = lab[PL[(size_t)p * Q1 + j]]; if (vid[o] >= 0) cov[(size_t)p * Q1 + cc[p]++] = vid[o]; }
    /* adjacency (CSR), two passes */
    int *mark = calloc(V, sizeof(int)); int *deg = calloc(V, sizeof(int));
    for (int v = 0; v < V; v++) {
        int st = v + 1;
        for (int t = mstart[v]; t < mstart[v + 1]; t++) { int l = mem[t];
            for (int j = 0; j < Q1; j++) { int p = LP[(size_t)l * Q1 + j];
                for (int c = 0; c < cc[p]; c++) { int u = cov[(size_t)p * Q1 + c]; if (u != v && mark[u] != st) { mark[u] = st; deg[v]++; } } } }
    }
    long E2 = 0; int *ast = malloc(sizeof(int) * (V + 1)); ast[0] = 0;
    for (int v = 0; v < V; v++) { ast[v + 1] = ast[v] + deg[v]; E2 += deg[v]; }
    int *adj = malloc(sizeof(int) * (size_t)(E2 + 1));
    memset(mark, 0, sizeof(int) * V);
    for (int v = 0; v < V; v++) {
        int st = v + 1, k = ast[v];
        for (int t = mstart[v]; t < mstart[v + 1]; t++) { int l = mem[t];
            for (int j = 0; j < Q1; j++) { int p = LP[(size_t)l * Q1 + j];
                for (int c = 0; c < cc[p]; c++) { int u = cov[(size_t)p * Q1 + c]; if (u != v && mark[u] != st) { mark[u] = st; adj[k++] = u; } } } }
    }
    int *w = malloc(sizeof(int) * V); double wsum = 0; int wmax = 0, wmin = 1 << 30;
    for (int v = 0; v < V; v++) { w[v] = osz[vorb[v]]; wsum += w[v]; if (w[v] > wmax) wmax = w[v]; if (w[v] < wmin) wmin = w[v]; }
    double wbar = wsum / (V ? V : 1);
    fprintf(stderr, "orbits K=%d usable V=%d (lines covered %d) avg deg %.1f  wmin %d wmax %d\n", K, V, mstart[V], V ? (double)E2 / V : 0.0, wmin, wmax);
    /* SA state */
    char *inS = calloc(V, 1); long *sumw = calloc(V, sizeof(long)); long totalW = 0, bestW = -1;
    char *bestS = calloc(V, 1);
    #define REMOVE(u) do { int _u = (u); inS[_u] = 0; totalW -= w[_u]; for (int _k = ast[_u]; _k < ast[_u + 1]; _k++) sumw[adj[_k]] -= w[_u]; } while (0)
    #define INSERT(v) do { int _v = (v); for (int _k = ast[_v]; _k < ast[_v + 1]; _k++) if (inS[adj[_k]]) REMOVE(adj[_k]); \
        inS[_v] = 1; totalW += w[_v]; for (int _k = ast[_v]; _k < ast[_v + 1]; _k++) sumw[adj[_k]] += w[_v]; } while (0)
    double t0 = now(); double T0 = tf0 * wbar, T1 = tf1 * wbar; long cycles = 0; double tbest = 0;
    while (now() - t0 < secs) {
        double lr = log(T1 / T0);
        for (long it = 0; it < iters; it++) {
            double T = T0 * exp(lr * (double)it / (double)iters);
            int v = (int)(xr() % (uint64_t)V);
            if (inS[v]) continue;
            long delta = (long)w[v] - sumw[v];
            if (delta >= 0 || ur() < exp((double)delta / T)) INSERT(v);
            if (totalW > bestW) { bestW = totalW; memcpy(bestS, inS, V); tbest = now() - t0; }
        }
        cycles++;
        /* greedy completion of free vertices */
        for (int v = 0; v < V; v++) if (!inS[v] && sumw[v] == 0) INSERT(v);
        if (totalW > bestW) { bestW = totalW; memcpy(bestS, inS, V); tbest = now() - t0; }
        if (ur() < 0.5) { /* restart from best */
            for (int v = 0; v < V; v++) if (inS[v]) REMOVE(v);
            for (int v = 0; v < V; v++) if (bestS[v] && !inS[v]) { int ok = 1; for (int k = ast[v]; k < ast[v + 1]; k++) if (inS[adj[k]]) { ok = 0; break; } if (ok) INSERT(v); }
        }
        fprintf(stderr, "cycle %ld t=%.1f cur=%ld best=%ld (at %.1fs)\n", cycles, now() - t0, totalW, bestW, tbest);
    }
    /* output best: lines of chosen orbits */
    FILE *o = fopen(argv[5], "w"); long cnt = 0;
    for (int l = 0; l < L; l++) { int v = vid[lab[l]]; if (v >= 0 && bestS[v]) { fprintf(o, "%d\n", l); cnt++; } }
    fclose(o);
    printf("RESULT K=%d V=%d best_lines=%ld cycles=%ld time_best=%.1f\n", K, V, cnt, cycles, tbest);
    return 0;
}
