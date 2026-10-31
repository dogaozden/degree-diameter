/* c1 common graph utilities: cubic-ish graphs up to MAXN vertices, far cost by radius-7 reach sets. */
#ifndef G37_H
#define G37_H
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAXN 256
#define WMAX 4
typedef uint64_t u64;

typedef struct { int n; int deg[MAXN]; int nb[MAXN][3]; } G;

static void g_init(G *g, int n) { g->n = n; memset(g->deg, 0, sizeof(g->deg)); }

static int g_has(const G *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) if (g->nb[a][i] == b) return 1;
    return 0;
}
static void g_add(G *g, int a, int b) {
    g->nb[a][g->deg[a]++] = b; g->nb[b][g->deg[b]++] = a;
}
static void g_del(G *g, int a, int b) {
    for (int i = 0; i < g->deg[a]; i++) if (g->nb[a][i] == b) { g->nb[a][i] = g->nb[a][--g->deg[a]]; break; }
    for (int i = 0; i < g->deg[b]; i++) if (g->nb[b][i] == a) { g->nb[b][i] = g->nb[b][--g->deg[b]]; break; }
}

/* read "n" then edge pairs; returns number of edges, -1 on error */
static int g_load(G *g, const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); return -1; }
    int n; if (fscanf(f, "%d", &n) != 1) { fclose(f); return -1; }
    g_init(g, n);
    int a, b, m = 0;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (a < 0 || b < 0 || a >= n || b >= n || a == b || g->deg[a] >= 3 || g->deg[b] >= 3) { fclose(f); return -1; }
        g_add(g, a, b); m++;
    }
    fclose(f); return m;
}

static void g_write(const G *g, const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", g->n);
    for (int a = 0; a < g->n; a++) for (int i = 0; i < g->deg[a]; i++) if (g->nb[a][i] > a) fprintf(f, "%d %d\n", a, g->nb[a][i]);
    fclose(f);
}

/* Number of unordered pairs at distance > 7 (far). Radius-7 reach sets via R_{k} = R_{k-1} OR neighbours. */
static long far_cost(const G *g) {
    int n = g->n; int Wn = (n + 63) / 64;
    static u64 R[2][MAXN][WMAX];
    int cur = 0;
    for (int x = 0; x < n; x++) { for (int w = 0; w < Wn; w++) R[0][x][w] = 0; R[0][x][x >> 6] |= 1ULL << (x & 63); }
    for (int step = 0; step < 7; step++) {
        int nx = cur ^ 1;
        for (int x = 0; x < n; x++) {
            for (int w = 0; w < Wn; w++) {
                u64 acc = R[cur][x][w];
                for (int i = 0; i < g->deg[x]; i++) acc |= R[cur][g->nb[x][i]][w];
                R[nx][x][w] = acc;
            }
        }
        cur = nx;
    }
    long tot = 0;
    for (int x = 0; x < n; x++) {
        int pc = 0;
        for (int w = 0; w < Wn; w++) pc += __builtin_popcountll(R[cur][x][w]);
        tot += n - pc;
    }
    return tot / 2;
}

/* For each vertex, the number of vertices NOT within distance 7 of it (excess per vertex). Returns far, fills ex[]. */
static long far_detail(const G *g, int *ex) {
    int n = g->n; int Wn = (n + 63) / 64;
    static u64 R[2][MAXN][WMAX];
    int cur = 0;
    for (int x = 0; x < n; x++) { for (int w = 0; w < Wn; w++) R[0][x][w] = 0; R[0][x][x >> 6] |= 1ULL << (x & 63); }
    for (int step = 0; step < 7; step++) {
        int nx = cur ^ 1;
        for (int x = 0; x < n; x++) for (int w = 0; w < Wn; w++) {
            u64 acc = R[cur][x][w];
            for (int i = 0; i < g->deg[x]; i++) acc |= R[cur][g->nb[x][i]][w];
            R[nx][x][w] = acc;
        }
        cur = nx;
    }
    long tot = 0;
    for (int x = 0; x < n; x++) {
        int pc = 0;
        for (int w = 0; w < Wn; w++) pc += __builtin_popcountll(R[cur][x][w]);
        ex[x] = n - pc; tot += n - pc;
    }
    return tot / 2;
}

static uint64_t rng_s[2];
static inline uint64_t rng_next(void) {
    uint64_t s1 = rng_s[0]; const uint64_t s0 = rng_s[1];
    rng_s[0] = s0; s1 ^= s1 << 23; rng_s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26);
    return rng_s[1] + s0;
}
static void rng_seed(uint64_t s) { rng_s[0] = s * 0x9E3779B97F4A7C15ULL + 1; rng_s[1] = (s + 7) * 0xBF58476D1CE4E5B9ULL + 3; for (int i = 0; i < 20; i++) rng_next(); }
static inline int rng_int(int k) { return (int)(rng_next() % (uint64_t)k); }
static inline double rng_unif(void) { return (rng_next() >> 11) * (1.0 / 9007199254740992.0); }

#endif
