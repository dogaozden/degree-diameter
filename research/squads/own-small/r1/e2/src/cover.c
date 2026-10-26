/* cover: simulated annealing over voltage covers of a bipartite cubic base with up to 256 vertices and any group table.
   Convention as flift: edge (u,v) with voltage a gives lift edges (u,x)-(v,a*x); G acts by right multiplication,
   transitive on fibres, so cost = sum over base u of #{lift vertices farther than D from (u,e)}.
   Usage: cover BASE.txt GROUP.bin D seconds seed OUT.prefix [T0=3] [T1=0.05]
   BASE.txt: "b m" then m lines "u v". GROUP.bin: int32 N then N*N uint16 (identity 0). Spanning tree gets voltage 0.
   Writes OUT.prefix.edges (n = b*N, vertex u*N+x) and OUT.prefix.sol (voltages) at the end. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#define MAXB 256
#define MAXE 1024
static int b, m, N, D;
static int eu[MAXE], ev[MAXE], volt[MAXE], best[MAXE], cot[MAXE], ncot, istree[MAXE];
static uint16_t *MT; static int *INV;
static int nd[MAXB], dto[MAXB][8], dg[MAXB][8];   /* darts: (u,x)~(dto,dg*x) */
static int *queue; static unsigned char *dist;
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static void build(void) {
    for (int u = 0; u < b; u++) nd[u] = 0;
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e], a = volt[e];
        dto[u][nd[u]] = v; dg[u][nd[u]++] = a;
        dto[v][nd[v]] = u; dg[v][nd[v]++] = INV[a];
    }
}
static long cost(void) {
    build();
    long tot = 0; int n = b * N;
    for (int r = 0; r < b; r++) {
        memset(dist, 255, n);
        int h = 0, t = 0, src = r * N + 0;
        dist[src] = 0; queue[t++] = src;
        while (h < t) {
            int c = queue[h++]; int u = c / N, x = c - u * N; int dc = dist[c];
            for (int k = 0; k < 3; k++) {
                int v = dto[u][k], y = MT[(size_t)dg[u][k] * N + x];
                int w = v * N + y;
                if (dist[w] == 255) { dist[w] = dc + 1; queue[t++] = w; }
            }
        }
        for (int c = 0; c < n; c++) if (dist[c] == 255 || dist[c] > D) tot++;
    }
    return tot;
}
static void write_out(const char *pre) {
    char p[1024]; int n = b * N;
    for (int e = 0; e < m; e++) volt[e] = best[e];
    snprintf(p, sizeof p, "%s.edges", pre); FILE *f = fopen(p, "w");
    fprintf(f, "%d\n", n);
    for (int e = 0; e < m; e++) for (int x = 0; x < N; x++)
        fprintf(f, "%d %d\n", eu[e] * N + x, ev[e] * N + MT[(size_t)best[e] * N + x]);
    fclose(f);
    snprintf(p, sizeof p, "%s.sol", pre); f = fopen(p, "w");
    fprintf(f, "base %d %d group N=%d\n", b, m, N);
    for (int e = 0; e < m; e++) fprintf(f, "e %d %d %d\n", eu[e], ev[e], best[e]);
    fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: cover BASE GROUP.bin D seconds seed OUT [T0] [T1]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &b, &m) != 2) return 2;
    for (int e = 0; e < m; e++) if (fscanf(f, "%d %d", &eu[e], &ev[e]) != 2) return 2;
    fclose(f);
    f = fopen(argv[2], "rb"); int32_t n32; if (!f || fread(&n32, 4, 1, f) != 1) return 2;
    N = n32; MT = malloc((size_t)N * N * 2); if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) return 2; fclose(f);
    INV = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { INV[g] = -1; for (int h = 0; h < N; h++) if (MT[(size_t)g * N + h] == 0) { INV[g] = h; break; } }
    D = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    const char *pre = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 3.0, T1 = argc > 8 ? atof(argv[8]) : 0.05;
    /* spanning tree (BFS on base) -> voltage 0 */
    int seen[MAXB] = {0}, q[MAXB], qh = 0, qt = 0; seen[0] = 1; q[qt++] = 0;
    for (int e = 0; e < m; e++) istree[e] = 0;
    while (qh < qt) { int u = q[qh++];
        for (int e = 0; e < m; e++) { int v = -1;
            if (eu[e] == u) v = ev[e]; else if (ev[e] == u) v = eu[e];
            if (v >= 0 && !seen[v]) { seen[v] = 1; q[qt++] = v; istree[e] = 1; } } }
    if (qt != b) { fprintf(stderr, "base not connected\n"); return 2; }
    ncot = 0; for (int e = 0; e < m; e++) if (!istree[e]) cot[ncot++] = e;
    queue = malloc(sizeof(int) * b * N); dist = malloc(b * N);
    for (int e = 0; e < m; e++) volt[e] = istree[e] ? 0 : (int)(rnd() % N);
    long cur = cost(), bestc = cur; memcpy(best, volt, sizeof volt);
    double t0 = now(), T = T0, lastp = t0; long it = 0;
    fprintf(stderr, "start cost=%ld n=%d N=%d ncot=%d\n", cur, b * N, N, ncot);
    while (1) {
        if ((it & 63) == 0) { double tn = now(); if (tn - t0 > secs) break;
            double fr = (tn - t0) / secs; T = T0 * pow(T1 / T0, fr); }
        it++;
        int e = cot[rnd() % ncot]; int old = volt[e]; int nv = (int)(rnd() % (N - 1)); if (nv >= old) nv++;
        volt[e] = nv; long c = cost();
        long dlt = c - cur;
        if (dlt <= 0 || rnd01() < exp(-dlt / T)) { cur = c;
            if (cur < bestc) { bestc = cur; memcpy(best, volt, sizeof volt); if (bestc == 0) break; } }
        else volt[e] = old;
        if (now() - lastp > 15) { lastp = now(); fprintf(stderr, "t=%.0f it=%ld T=%.3f cur=%ld best=%ld\n", now() - t0, it, T, cur, bestc); }
    }
    memcpy(volt, best, sizeof volt); long fin = cost();
    printf("RESULT cover base=%s group=%s D=%d n=%d best=%ld evals=%ld time=%.1f\n", argv[1], argv[2], D, b * N, fin, it, now() - t0);
    write_out(pre);
    return 0;
}
