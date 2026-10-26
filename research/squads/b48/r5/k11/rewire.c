/* k11: repair a near-miss cubic bipartite lift by bipartite-preserving 2-switches (simulated annealing).
   Move: edges (a,b),(c,d) with a,c on side 0 and b,d on side 1 become (a,d),(c,b).
   a is random, c is reached from a by a walk of length 2 (or 4), so moves are mostly local.
   Objective F = sum over ordered pairs of pen(dist), pen(d) = max(0, d-D), unreachable = D+10.
   usage: rewire IN.edges D SECONDS SEED T0 T1 OUT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

static int n, D;
static int adj[2048][3];
static int col[2048];
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rint_(int m) { return (int)(rnd() % (uint64_t)m); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static long evalF(long *far_out) {
    static int dist[2048], q[2048];
    long F = 0, far = 0;
    for (int s = 0; s < n; s++) {
        for (int i = 0; i < n; i++) dist[i] = -1;
        int h = 0, t = 0; q[t++] = s; dist[s] = 0;
        while (h < t) {
            int u = q[h++];
            for (int k = 0; k < 3; k++) { int v = adj[u][k]; if (dist[v] < 0) { dist[v] = dist[u] + 1; q[t++] = v; } }
        }
        for (int i = 0; i < n; i++) {
            if (i == s) continue;
            int d = dist[i] < 0 ? D + 10 : dist[i];
            if (d > D) { F += d - D; if (dist[i] < 0 || dist[i] > D) far++; }
        }
    }
    *far_out = far / 2;
    return F;
}

static int has(int u, int v) { for (int k = 0; k < 3; k++) if (adj[u][k] == v) return 1; return 0; }
static int slot(int u, int v) { for (int k = 0; k < 3; k++) if (adj[u][k] == v) return k; return -1; }

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", n);
    for (int u = 0; u < n; u++) for (int k = 0; k < 3; k++) if (adj[u][k] > u) fprintf(f, "%d %d\n", u, adj[u][k]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: rewire IN.edges D SECONDS SEED T0 T1 OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d", &n) != 1) return 1;
    int deg[2048] = {0};
    int m = 0; int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) { if (deg[u] >= 3 || deg[v] >= 3) { fprintf(stderr, "degree >3\n"); return 1; } adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; m++; }
    fclose(f);
    for (int i = 0; i < n; i++) if (deg[i] != 3) { fprintf(stderr, "not cubic at %d\n", i); return 1; }
    D = atoi(argv[2]); double secs = atof(argv[3]); rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL); if (!rs) rs = 1;
    double T0 = atof(argv[5]), T1 = atof(argv[6]); const char *out = argv[7];
    /* 2-colour */
    for (int i = 0; i < n; i++) col[i] = -1;
    col[0] = 0; int q[2048], h = 0, t = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int k = 0; k < 3; k++) { int y = adj[x][k]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); return 1; } } }
    long far; long F = evalF(&far); long F0 = F, far0 = far;
    fprintf(stderr, "start n=%d F=%ld far=%ld\n", n, F, far);
    long bestF = F, bestFar = far; long acc = 0, tried = 0;
    double t0 = now(), tend = t0 + secs;
    while (1) {
        double tn = now(); if (tn > tend) break;
        double frac = (tn - t0) / secs;
        double T = T0 * pow(T1 / T0, frac);
        /* propose */
        int a = rint_(n); if (col[a] != 0) continue;
        int b = adj[a][rint_(3)];
        int L = (rnd() % 10 < 7) ? 2 : 4;
        int c = a, prev = -1;
        for (int s = 0; s < L; s++) { int nx; do { nx = adj[c][rint_(3)]; } while (nx == prev && 0); prev = c; c = nx; }
        if (c == a || col[c] != 0) continue;
        int d = adj[c][rint_(3)];
        if (d == b) continue;
        if (has(a, d) || has(c, b)) continue;
        /* apply: adj[a]: b->d ; adj[d]: c->a ; adj[c]: d->b ; adj[b]: a->c */
        int sa = slot(a, b), sd = slot(d, c), sc = slot(c, d), sb = slot(b, a);
        adj[a][sa] = d; adj[d][sd] = a; adj[c][sc] = b; adj[b][sb] = c;
        long far2; long F2 = evalF(&far2);
        tried++;
        double dF = (double)(F2 - F);
        if (dF <= 0 || exp(-dF / T) > (rnd() % 1000000) / 1e6) {
            F = F2; far = far2; acc++;
            if (F < bestF || (F == bestF && far < bestFar)) {
                bestF = F; bestFar = far;
                if (far == 0) { write_edges(out); fprintf(stderr, "FOUND valid after %ld tries\n", tried); break; }
            }
        } else {
            adj[a][sa] = b; adj[d][sd] = c; adj[c][sc] = d; adj[b][sb] = a;
        }
        if (tried % 500 == 0) fprintf(stderr, "t=%.1f tried=%ld acc=%ld F=%ld far=%ld best=%ld bestfar=%ld T=%.3f\n", now() - t0, tried, acc, F, far, bestF, bestFar, T);
    }
    printf("RESULT n=%d start_far=%ld best_far=%ld best_F=%ld tried=%ld acc=%ld\n", n, far0, bestFar, bestF, tried, acc);
    (void)F0; (void)m;
    return 0;
}
