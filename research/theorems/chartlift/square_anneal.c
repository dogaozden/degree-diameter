/* Cubic bipartite graphs made of s disjoint 4-cycles ("squares") plus a perfect matching of external edges.
   Square i: A-vertices 2i, 2i+1; B-vertices m+2i, m+2i+1 (m = 2s), all four square edges.  External edges:
   A-vertex p ~ B-vertex m + sigma(p), sigma a bijection with sigma(p) outside p's square.  Every vertex is on a
   4-cycle by construction.  Cost = ordered same-side pairs at distance > 4 (cost 0 <=> diameter <= 5).
   usage: square_anneal s seconds seed [out.edges] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int s, m, n, sig[256], adj[512][3];
static void build(void) {
    for (int p = 0; p < m; p++) { int sq = p / 2; adj[p][0] = m + 2 * sq; adj[p][1] = m + 2 * sq + 1; adj[p][2] = m + sig[p]; }
    for (int p = 0; p < m; p++) { int sq = p / 2; adj[m + p][0] = 2 * sq; adj[m + p][1] = 2 * sq + 1; }
    for (int p = 0; p < m; p++) adj[m + sig[p]][2] = p; }
static long cost(void) {
    long far = 0; int dist[512], qu[512];
    for (int st = 0; st < n; st++) {
        for (int i = 0; i < n; i++) dist[i] = -1; dist[st] = 0; int h = 0, t = 0; qu[t++] = st;
        while (h < t) { int x = qu[h++]; if (dist[x] >= 4) continue; for (int i = 0; i < 3; i++) { int y = adj[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
        int lo = st < m ? 0 : m; for (int i = lo; i < lo + m; i++) if (dist[i] < 0) far++; }
    return far; }
int main(int argc, char **argv) {
    s = atoi(argv[1]); m = 2 * s; n = 2 * m; double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; xr();
    const char *out = argc > 4 ? argv[4] : NULL;
    long best = -1; int bs[256]; clock_t t0 = clock(); long it = 0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && best != 0) {
        for (;;) { for (int i = 0; i < m; i++) sig[i] = i;
            for (int i = m - 1; i > 0; i--) { int j = xr() % (i + 1); int x = sig[i]; sig[i] = sig[j]; sig[j] = x; }
            int ok = 1; for (int i = 0; i < m; i++) if (sig[i] / 2 == i / 2) ok = 0; if (ok) break; }
        build(); long c = cost(); if (best < 0 || c < best) { best = c; memcpy(bs, sig, sizeof sig); }
        long stall = 0;
        while (stall < 200000 && best != 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
            it++; int p1 = xr() % m, p2 = xr() % m; if (p1 == p2) continue;
            if (sig[p2] / 2 == p1 / 2 || sig[p1] / 2 == p2 / 2) continue;
            int x = sig[p1]; sig[p1] = sig[p2]; sig[p2] = x; build();
            long c2 = cost(); double TT = 0.8 * exp(-(double)stall / 40000.0) + 0.2;
            if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) { if (c2 < c) stall = 0; else stall++; c = c2;
                if (c < best) { best = c; memcpy(bs, sig, sizeof sig); } }
            else { x = sig[p1]; sig[p1] = sig[p2]; sig[p2] = x; build(); stall++; } } }
    memcpy(sig, bs, sizeof sig); build();
    printf("s=%d m=%d best=%ld iters=%ld sigma=", s, m, cost(), it); for (int i = 0; i < m; i++) printf("%d%c", bs[i], i + 1 < m ? ',' : '\n');
    if (out && best == 0) { FILE *o = fopen(out, "w"); fprintf(o, "%d\n", n);
        for (int x = 0; x < m; x++) for (int i = 0; i < 3; i++) fprintf(o, "%d %d\n", x, adj[x][i]); fclose(o); }
    return 0; }
