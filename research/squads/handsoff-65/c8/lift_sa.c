/* lift_sa.c: SA over cyclic Z_m voltages of a bipartite base graph (edges u<v in file, first number = base n).
 * lift vertices v*m+i; base edge (u,w) with voltage g lifts to (u,i)-(w,i+g). cost = unordered pairs at distance > D.
 * usage: lift_sa BASE M OUT ITERS T0 T1 SEED [D] */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define MAXN 2048
#define W ((MAXN + 63) / 64)
int bn, M, D = 5, n, E;
int eu[4000], ev[4000], vol[4000];
int nb[MAXN][8], deg[MAXN];
static uint64_t R[2][MAXN][W];
int words;
uint64_t rng_s;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
void build(void) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int e = 0; e < E; e++) {
        for (int i = 0; i < M; i++) {
            int a = eu[e] * M + i, b = ev[e] * M + (i + vol[e]) % M;
            nb[a][deg[a]++] = b; nb[b][deg[b]++] = a;
        }
    }
}
long cost(void) {
    int cur = 0;
    for (int v = 0; v < n; v++) { memset(R[0][v], 0, sizeof(uint64_t) * words); R[0][v][v >> 6] |= 1ULL << (v & 63); }
    for (int k = 1; k <= D; k++) {
        int nxt = 1 - cur;
        for (int v = 0; v < n; v++) {
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
    for (int v = 0; v < n; v++)
        for (int u = v + 1; u < n; u++)
            if (!((R[cur][v][u >> 6] >> (u & 63)) & 1)) bad++;
    return bad;
}
void save(const char *path) {
    FILE *g = fopen(path, "w"); fprintf(g, "%d\n", n);
    for (int e = 0; e < E; e++) for (int i = 0; i < M; i++)
        fprintf(g, "%d %d\n", eu[e] * M + i, ev[e] * M + (i + vol[e]) % M);
    fclose(g);
}
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: lift_sa BASE M OUT ITERS T0 T1 SEED [D]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    if (fscanf(f, "%d", &bn) != 1) return 2;
    int a, b; E = 0;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (a > b) { int t = a; a = b; b = t; }
        eu[E] = a; ev[E] = b; E++;
    }
    fclose(f);
    M = atoi(argv[2]);
    if (argc > 8) D = atoi(argv[8]);
    n = bn * M; words = (n + 63) / 64;
    if (n > MAXN) { fprintf(stderr, "too big\n"); return 2; }
    long iters = atol(argv[4]);
    double T0 = atof(argv[5]), T1 = atof(argv[6]);
    rng_s = 88172645463325252ULL ^ ((uint64_t)atol(argv[7]) * 2654435761ULL + 12345);
    for (int e = 0; e < E; e++) vol[e] = rnd() % M;
    build();
    long c = cost(), best = c;
    fprintf(stderr, "base n=%d E=%d lift n=%d cost=%ld\n", bn, E, n, c);
    if (c < best) best = c;
    save(argv[3]);
    for (long it = 0; it < iters && best > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int e = rnd() % E; int old = vol[e];
        int nv = (old + 1 + rnd() % (M - 1)) % M;
        vol[e] = nv; build();
        long c2 = cost();
        if (c2 <= c || urand() < exp(-(double)(c2 - c) / T)) {
            c = c2;
            if (c < best) { best = c; save(argv[3]); fprintf(stderr, "it %ld T %.3f best %ld\n", it, T, best); }
        } else {
            vol[e] = old; build();
        }
        if (it % 20000 == 0) fprintf(stderr, "it %ld T %.3f cur %ld best %ld\n", it, T, c, best);
    }
    printf("final best %ld\n", best);
    return 0;
}
