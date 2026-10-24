/* Edge-switch annealing for k-regular bipartite graphs (m + m vertices) with
   cost = #(ordered same-side pairs at distance > 4) + W4 * #(vertices on no 4-cycle).
   Cost 0 <=> diameter <= 5 and every vertex on a 4-cycle: exactly the controllers needed for a universal,
   pencil-complete chart (CHART_LIFTS.md).  usage: graph_anneal k m seconds seed [W4] [out]
   out: "2m" then edges "a b" with A = 0..m-1, B = m..2m-1 (k-regular).  Colour it with controller.py. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int k, m, n, adj[512][8], E[4096][2], ne; double W4 = 4;
static int has(int a, int b) { for (int i = 0; i < k; i++) if (adj[a][i] == b) return 1; return 0; }
static void rebuild(void) { int d[512] = {0}; for (int e = 0; e < ne; e++) { int a = E[e][0], b = E[e][1]; adj[a][d[a]++] = b; adj[b][d[b]++] = a; } }
static long cost(long *far, long *no4) {
    *far = 0; *no4 = 0; int dist[512], qu[512];
    for (int s = 0; s < n; s++) {
        for (int i = 0; i < n; i++) dist[i] = -1; dist[s] = 0; int h = 0, t = 0; qu[t++] = s;
        while (h < t) { int x = qu[h++]; if (dist[x] >= 4) continue; for (int i = 0; i < k; i++) { int y = adj[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
        int lo = s < m ? 0 : m; for (int i = lo; i < lo + m; i++) if (dist[i] < 0) (*far)++;
        /* 4-cycle through s: two neighbours sharing another common neighbour */
        int ok = 0; for (int i = 0; i < k && !ok; i++) for (int j = i + 1; j < k && !ok; j++) { int a = adj[s][i], b = adj[s][j];
            for (int x = 0; x < k && !ok; x++) { int w = adj[a][x]; if (w != s && has(b, w)) ok = 1; } }
        if (!ok) (*no4)++; }
    return *far + (long)(W4 * *no4); }
int main(int argc, char **argv) {
    k = atoi(argv[1]); m = atoi(argv[2]); n = 2 * m; double secs = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr();
    if (argc > 5) W4 = atof(argv[5]); const char *out = argc > 6 ? argv[6] : NULL;
    ne = k * m; long best = -1; int bE[4096][2]; clock_t t0 = clock(); long it = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && best != 0) {
        /* random simple k-regular bipartite graph: union of k random perfect matchings, retry on collisions */
        for (;;) { int perm[256]; ne = 0; int okk = 1;
            for (int c = 0; c < k && okk; c++) { for (int i = 0; i < m; i++) perm[i] = i;
                for (int i = m - 1; i > 0; i--) { int j = xr() % (i + 1); int x = perm[i]; perm[i] = perm[j]; perm[j] = x; }
                for (int i = 0; i < m; i++) { for (int e = 0; e < ne; e++) if (E[e][0] == i && E[e][1] == m + perm[i]) okk = 0; E[ne][0] = i; E[ne][1] = m + perm[i]; ne++; } }
            if (okk) break; }
        rebuild(); long f, z; long c = cost(&f, &z); if (best < 0 || c < best) { best = c; memcpy(bE, E, sizeof(int) * 2 * ne); }
        long stall = 0;
        while (stall < 300000 && best != 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
            it++; int e1 = xr() % ne, e2 = xr() % ne; if (e1 == e2) continue;
            int a1 = E[e1][0], b1 = E[e1][1], a2 = E[e2][0], b2 = E[e2][1];
            if (a1 == a2 || b1 == b2 || has(a1, b2) || has(a2, b1)) continue;
            E[e1][1] = b2; E[e2][1] = b1; rebuild();
            long c2 = cost(&f, &z); double TT = 0.6 * exp(-(double)stall / 50000.0) + 0.15;
            if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) { if (c2 < c) stall = 0; else stall++; c = c2;
                if (c < best) { best = c; memcpy(bE, E, sizeof(int) * 2 * ne); } }
            else { E[e1][1] = b1; E[e2][1] = b2; rebuild(); stall++; } } }
    memcpy(E, bE, sizeof(int) * 2 * ne); rebuild(); long f, z; cost(&f, &z);
    printf("k=%d m=%d best=%ld far=%ld no4=%ld iters=%ld\n", k, m, best, f, z, it);
    if (out && best == 0) { FILE *o = fopen(out, "w"); fprintf(o, "%d\n", n); for (int e = 0; e < ne; e++) fprintf(o, "%d %d\n", E[e][0], E[e][1]); fclose(o); }
    return 0; }
