/* dcsa.c: SA over 6-regular simple graphs Gamma on N vertices; cost = far pairs (dist > D) of the bipartite
 * double cover B(Gamma) (vertices x0 = x, x1 = x+N; edges x0-y1 and y0-x1 for each edge xy of Gamma).
 * Moves: degree-preserving double edge swaps in Gamma (applied to the cover).
 * usage: dcsa GAMMA_EDGES OUT ITERS T0 T1 SEED [D] ; GAMMA file: "N" then "u v" lines */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define MAXV 1024
#define W ((2*MAXV + 63) / 64)
int N, D = 5, n2, m;
int gu[4000], gv[4000];
int nb[2*MAXV][8], deg[2*MAXV];
static uint64_t R[2][2*MAXV][W];
int words;
uint64_t rng_s;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int adj_g[MAXV][8], dg[MAXV];
int has_g(int a, int b) { for (int j = 0; j < dg[a]; j++) if (adj_g[a][j] == b) return 1; return 0; }
void build_cover(void) {
    for (int v = 0; v < 2*N; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) {
        int x = gu[i], y = gv[i];
        int a = x, b = y + N; nb[a][deg[a]++] = b; nb[b][deg[b]++] = a;
        a = y; b = x + N; nb[a][deg[a]++] = b; nb[b][deg[b]++] = a;
    }
}
long cost(void) {
    int cur = 0;
    for (int v = 0; v < n2; v++) { memset(R[0][v], 0, sizeof(uint64_t) * words); R[0][v][v >> 6] |= 1ULL << (v & 63); }
    for (int k = 1; k <= D; k++) {
        int nxt = 1 - cur;
        for (int v = 0; v < n2; v++) {
            uint64_t *dst = R[nxt][v];
            memcpy(dst, R[cur][v], sizeof(uint64_t) * words);
            for (int j = 0; j < deg[v]; j++) {
                uint64_t *src = R[cur][nb[v][j]];
                for (int w = 0; w < words; w++) dst[w] |= src[w];
            }
        }
        cur = nxt;
    }
    long bad = 0;
    for (int v = 0; v < n2; v++)
        for (int u = v + 1; u < n2; u++)
            if (!((R[cur][v][u >> 6] >> (u & 63)) & 1)) bad++;
    return bad;
}
void save(const char *p) {
    FILE *g = fopen(p, "w"); fprintf(g, "%d\n", N);
    for (int i = 0; i < m; i++) fprintf(g, "%d %d\n", gu[i], gv[i]);
    fclose(g);
}
void rebuild_adj(void) {
    for (int v = 0; v < N; v++) dg[v] = 0;
    for (int i = 0; i < m; i++) { adj_g[gu[i]][dg[gu[i]]++] = gv[i]; adj_g[gv[i]][dg[gv[i]]++] = gu[i]; }
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    if (fscanf(f, "%d", &N) != 1) return 2;
    int a, b; m = 0;
    while (fscanf(f, "%d %d", &a, &b) == 2) { gu[m] = a; gv[m] = b; m++; }
    fclose(f);
    if (argc > 7) D = atoi(argv[7]);
    n2 = 2 * N; words = (n2 + 63) / 64;
    long iters = atol(argv[3]); double T0 = atof(argv[4]), T1 = atof(argv[5]);
    rng_s = 88172645463325252ULL ^ ((uint64_t)atol(argv[6]) * 2654435761ULL + 99991);
    rebuild_adj();
    build_cover();
    long c = cost(), best = c;
    fprintf(stderr, "N=%d m=%d start cost %ld\n", N, m, c);
    save(argv[2]);
    for (long it = 0; it < iters && best > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int i1 = rnd() % m, i2 = rnd() % m;
        if (i1 == i2) continue;
        int x1 = gu[i1], y1 = gv[i1], x2 = gu[i2], y2 = gv[i2];
        if (x1 == x2 || y1 == y2 || x1 == y2 || x2 == y1) continue;
        rebuild_adj();
        if (has_g(x1, y2) || has_g(x2, y1)) continue;
        gv[i1] = y2; gv[i2] = y1;
        rebuild_adj(); build_cover();
        long c2 = cost();
        if (c2 <= c || urand() < exp(-(double)(c2 - c) / T)) {
            c = c2;
            if (c < best) { best = c; save(argv[2]); fprintf(stderr, "it %ld T %.3f best %ld\n", it, T, best); }
        } else {
            gv[i1] = y1; gv[i2] = y2; rebuild_adj(); build_cover();
        }
        if (it % 20000 == 0) fprintf(stderr, "it %ld T %.3f cur %ld best %ld\n", it, T, c, best);
    }
    printf("final best %ld\n", best);
    return 0;
}
