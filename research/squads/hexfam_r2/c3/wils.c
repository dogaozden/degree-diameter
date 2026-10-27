/* weighted ILS (ARW-style) for maximum-weight independent set on a CONFLICT graph.
   Max-weight clique in the compatibility graph = max-weight independent set in its complement.
   graph file (little endian): int32 n, int32 m, int64 w[n], int32 e[2m] (conflict pairs).
   usage: wils GRAPH OUT SECONDS SEED [SEEDSET]   OUT receives chosen vertex ids (one per line) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, m;
static long long *w;
static int *adjs, *adj;
static uint64_t *bits; static size_t W64;
static int *inS, *tight, *bestS; static long long *gain; static long long solW, bestW;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int isadj(int a, int b) { return (bits[(size_t)a * W64 + (b >> 6)] >> (b & 63)) & 1; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void addv(int v) {
    inS[v] = 1; solW += w[v];
    for (int k = adjs[v]; k < adjs[v + 1]; k++) { int u = adj[k]; gain[u] -= w[v]; tight[u]++; }
}
static void remv(int v) {
    inS[v] = 0; solW -= w[v];
    for (int k = adjs[v]; k < adjs[v + 1]; k++) { int u = adj[k]; gain[u] += w[v]; tight[u]--; }
}
static void force_insert(int v) {
    for (int k = adjs[v]; k < adjs[v + 1]; k++) { int u = adj[k]; if (inS[u]) remv(u); }
    addv(v);
}
static void local_search(void) {
    int improved = 1;
    int *L = malloc(sizeof(int) * (n + 1));
    while (improved) {
        improved = 0;
        /* (1) insertion of vertices with positive gain (weight gain after removing S-neighbours) */
        for (int v = 0; v < n; v++) {
            if (!inS[v] && gain[v] > 0) { force_insert(v); improved = 1; }
        }
        /* (2) (1,2)-type swap: remove s in S, insert two non-adjacent vertices whose only S-neighbour is s */
        for (int s = 0; s < n; s++) {
            if (!inS[s]) continue;
            int nl = 0;
            for (int k = adjs[s]; k < adjs[s + 1]; k++) { int x = adj[k]; if (!inS[x] && tight[x] == 1) L[nl++] = x; }
            if (nl < 2) continue;
            int done = 0;
            for (int i = 0; i < nl && !done; i++) for (int j = i + 1; j < nl && !done; j++) {
                int x = L[i], y = L[j];
                if (isadj(x, y)) continue;
                if (w[x] + w[y] > w[s]) {
                    remv(s); addv(x); addv(y);
                    /* fill any freed vertex */
                    for (int k = adjs[s]; k < adjs[s + 1]; k++) { int z = adj[k]; if (!inS[z] && tight[z] == 0) addv(z); }
                    done = 1; improved = 1;
                }
            }
        }
    }
    free(L);
}
static void set_from(int *src) { /* rebuild state from an indicator array */
    for (int v = 0; v < n; v++) { inS[v] = 0; tight[v] = 0; gain[v] = w[v]; }
    solW = 0;
    for (int v = 0; v < n; v++) if (src[v] && tight[v] == 0 && !inS[v]) addv(v);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: wils GRAPH OUT SECONDS SEED [SEEDSET]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("graph"); return 1; }
    int32_t hdr[2]; if (fread(hdr, 4, 2, f) != 2) return 1; n = hdr[0]; m = hdr[1];
    w = malloc(sizeof(long long) * n); if (fread(w, 8, n, f) != (size_t)n) return 1;
    int32_t *e = malloc(sizeof(int32_t) * 2 * (size_t)m); if (m && fread(e, 4, 2 * (size_t)m, f) != 2 * (size_t)m) return 1;
    fclose(f);
    int *deg = calloc(n + 1, sizeof(int));
    for (long i = 0; i < m; i++) { deg[e[2 * i]]++; deg[e[2 * i + 1]]++; }
    adjs = malloc(sizeof(int) * (n + 1)); adjs[0] = 0;
    for (int v = 0; v < n; v++) adjs[v + 1] = adjs[v] + deg[v];
    adj = malloc(sizeof(int) * (size_t)(2 * (size_t)m + 1));
    int *fill = calloc(n + 1, sizeof(int));
    W64 = (n + 63) / 64;
    bits = calloc((size_t)n * W64 + 1, sizeof(uint64_t));
    for (long i = 0; i < m; i++) {
        int a = e[2 * i], b = e[2 * i + 1];
        adj[adjs[a] + fill[a]++] = b; adj[adjs[b] + fill[b]++] = a;
        bits[(size_t)a * W64 + (b >> 6)] |= 1ULL << (b & 63);
        bits[(size_t)b * W64 + (a >> 6)] |= 1ULL << (a & 63);
    }
    free(e); free(deg); free(fill);
    double seconds = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    inS = calloc(n, sizeof(int)); tight = calloc(n, sizeof(int)); bestS = calloc(n, sizeof(int));
    gain = malloc(sizeof(long long) * n);
    for (int v = 0; v < n; v++) gain[v] = w[v];
    solW = 0;
    if (argc >= 6) {
        FILE *g = fopen(argv[5], "r");
        if (g) { int v; while (fscanf(g, "%d", &v) == 1) if (v >= 0 && v < n && !inS[v] && tight[v] == 0) addv(v); fclose(g); }
    }
    local_search();
    bestW = solW; memcpy(bestS, inS, sizeof(int) * n);
    fprintf(stderr, "n %d m %d init %lld\n", n, m, solW);
    double t0 = now(); long iter = 0, lastimp = 0;
    int *tmp = malloc(sizeof(int) * n);
    while (now() - t0 < seconds) {
        iter++;
        /* perturbation: force a random non-solution vertex in (occasionally 2 of them) */
        int k = 1 + (rnd() % 10 == 0);
        for (int t = 0; t < k; t++) {
            int v; int tries = 0;
            do { v = rnd() % n; tries++; } while (inS[v] && tries < 1000);
            if (!inS[v]) force_insert(v);
        }
        local_search();
        if (solW > bestW) {
            bestW = solW; memcpy(bestS, inS, sizeof(int) * n); lastimp = iter;
            fprintf(stderr, "  best %lld at iter %ld t=%.1f\n", bestW, iter, now() - t0);
        }
        if (iter - lastimp > 400) { /* restart from best */
            memcpy(tmp, bestS, sizeof(int) * n); set_from(tmp); local_search(); lastimp = iter;
        }
    }
    FILE *o = fopen(argv[2], "w");
    for (int v = 0; v < n; v++) if (bestS[v]) fprintf(o, "%d\n", v);
    fclose(o);
    fprintf(stderr, "final best %lld iters %ld\n", bestW, iter);
    printf("%lld\n", bestW);
    return 0;
}
