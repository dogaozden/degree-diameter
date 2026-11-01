// Haar graph H(G,S) on G = Sz(8) (ovoid stabilizer in PGL(4,8), built by sz8.py), |S| = K, annealing on
// uncovered vertices within distance D of both (e,A) and (e,B).  Usage: sz_haar D secs seed K OUT sz8.bin
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
static double wall(void){ struct timespec ts; clock_gettime(CLOCK_MONOTONIC,&ts); return ts.tv_sec+1e-9*ts.tv_nsec; }
static uint8_t MUL[8][8], INV[8];
static int N;
static uint8_t (*E)[16];
static int32_t *INVG;
#define HS (1 << 16)
static uint64_t hk[HS]; static int32_t hv[HS];
static uint64_t key(const uint8_t *m) { uint64_t k = 0; for (int i = 0; i < 16; i++) k = (k << 3) | m[i]; return k; }
static void hput(uint64_t k, int v) { uint64_t h = (k * 0x9E3779B97F4A7C15ULL) >> 48; while (hv[h] >= 0) h = (h + 1) & (HS - 1); hk[h] = k; hv[h] = v; }
static int hget(uint64_t k) { uint64_t h = (k * 0x9E3779B97F4A7C15ULL) >> 48; while (hv[h] >= 0) { if (hk[h] == k) return hv[h]; h = (h + 1) & (HS - 1); } return -1; }
static int prodidx(int a, int b) {
    uint8_t c[16];
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) {
        uint8_t s = 0; for (int k = 0; k < 4; k++) s ^= MUL[E[a][i * 4 + k]][E[b][k * 4 + j]];
        c[i * 4 + j] = s; }
    int t = 0; while (!c[t]) t++;
    uint8_t iv = INV[c[t]];
    for (int i = 0; i < 16; i++) c[i] = MUL[iv][c[i]];
    int r = hget(key(c)); if (r < 0) { fprintf(stderr, "closure fail\n"); exit(2); }
    return r;
}
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int D, K;
static uint16_t *LF[16], *LB[16];   // LF[k][g] = index(s_k g); LB[k][x] = index(s_k^{-1} x)
static int S[16];
static uint8_t *dist; static int32_t *Q;
static int cover_cost(int src) {
    // BFS on 2N vertices: A-vertex g in [0,N), B-vertex x in [N,2N). Edges (g,A)~(s g,B).
    int V = 2 * N;
    for (int i = 0; i < V; i++) dist[i] = 255;
    int h = 0, t = 0; dist[src] = 0; Q[t++] = src;
    while (h < t) {
        int v = Q[h++]; int d = dist[v]; if (d >= D) continue;
        if (v < N) { for (int k = 0; k < K; k++) { int w = N + LF[k][v]; if (dist[w] == 255) { dist[w] = d + 1; Q[t++] = w; } } }
        else { int x = v - N; for (int k = 0; k < K; k++) { int w = LB[k][x]; if (dist[w] == 255) { dist[w] = d + 1; Q[t++] = w; } } }
    }
    return V - t;
}
static int cost(void) { return cover_cost(0) + cover_cost(N); }
static void setslot(int k, int s) {
    S[k] = s;
    for (int g = 0; g < N; g++) { LF[k][g] = prodidx(s, g); LB[k][g] = prodidx(INVG[s], g); }
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: D secs seed K OUT sz8.bin\n"); return 1; }
    D = atoi(argv[1]); double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; K = atoi(argv[4]);
    const char *out = argv[5];
    for (int a = 0; a < 8; a++) for (int b = 0; b < 8; b++) { int r = 0, x = a, y = b; while (y) { if (y & 1) r ^= x; y >>= 1; x <<= 1; if (x & 8) x ^= 0xB; } MUL[a][b] = r; }
    for (int a = 1; a < 8; a++) for (int b = 1; b < 8; b++) if (MUL[a][b] == 1) INV[a] = b;
    FILE *f = fopen(argv[6], "rb"); int32_t n; if (fread(&n, 4, 1, f) != 1) return 1; N = n;
    E = malloc((size_t)N * 16); INVG = malloc(N * sizeof(int32_t));
    if (fread(E, 16, N, f) != (size_t)N || fread(INVG, 4, N, f) != (size_t)N) return 1; fclose(f);
    memset(hv, -1, sizeof hv);
    for (int g = 0; g < N; g++) hput(key(E[g]), g);
    for (int k = 0; k < K; k++) { LF[k] = malloc(N * 2); LB[k] = malloc(N * 2); }
    dist = malloc(2 * N); Q = malloc(2 * N * sizeof(int32_t));
    int cur_S[16], best_S[16]; int cur, best = 1 << 30;
    for (int k = 0; k < K; k++) { int s; int ok; do { s = rnd() % N; ok = 1; for (int j = 0; j < k; j++) if (S[j] == s) ok = 0; } while (!ok); setslot(k, s); }
    cur = cost(); memcpy(cur_S, S, sizeof S); best = cur; memcpy(best_S, S, sizeof S);
    double t0 = wall(); long it = 0; double T = 1.0;
    fprintf(stderr, "N=%d K=%d D=%d init cost %d\n", N, K, D, cur);
    while (cur > 0 && wall() - t0 < secs) {
        it++;
        int k = rnd() % K; int s; int ok;
        do { s = rnd() % N; ok = 1; for (int j = 0; j < K; j++) if (S[j] == s) ok = 0; } while (!ok);
        int old = S[k];
        setslot(k, s);
        int c = cost();
        if (c <= cur || (double)(rnd() % 1000000) / 1e6 < exp(-(c - cur) / T)) {
            cur = c; memcpy(cur_S, S, sizeof S);
            if (cur < best) { best = cur; memcpy(best_S, S, sizeof S); }
        } else { setslot(k, old); }
        if (it % 200 == 0) fprintf(stderr, "it %ld cur %d best %d t=%.0f\n", it, cur, best, wall() - t0);
    }
    printf("N=%d D=%d K=%d best_cost=%d iters=%ld S=", N, D, K, best, it);
    for (int k = 0; k < K; k++) printf("%d ", best_S[k]); printf("\n");
    if (best == 0) { FILE *o = fopen(out, "w"); fprintf(o, "%d %d", N, K); for (int k = 0; k < K; k++) fprintf(o, " %d", best_S[k]); fprintf(o, "\n"); fclose(o); }
    return 0;
}
