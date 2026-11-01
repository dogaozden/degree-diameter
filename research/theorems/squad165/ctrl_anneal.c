/* Anneal general 4-regular bipartite controllers (m + m vertices, simple) for exact-NB-4 coverage:
   every ordered same-side pair (u,v), u = v included, joined by a nonbacktracking walk of length exactly 4.
   Moves: edge switches (a1b1, a2b2) -> (a1b2, a2b1).  Cost = number of uncovered ordered pairs.
   usage: ctrl_anneal m seconds seed [T0] [out] [start]   (writes the edge list "a b" of the best graph found to out;
   start: optional edge list "a b" (a, b in 0..m-1, 4m lines) to start from instead of a random graph) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int m, n;            /* n = 2m vertices: A = 0..m-1, B = m..2m-1 */
int adj[512][4];
int cost_all(void) {
    static unsigned char hit[512];
    int c = 0;
    for (int u = 0; u < n; u++) {
        memset(hit, 0, n);
        for (int i = 0; i < 4; i++) { int a = adj[u][i];
            for (int j = 0; j < 4; j++) { int w = adj[a][j]; if (w == u) continue;
                for (int k = 0; k < 4; k++) { int b = adj[w][k]; if (b == a) continue;
                    for (int l = 0; l < 4; l++) { int v = adj[b][l]; if (v == w) continue; hit[v] = 1; } } } }
        int lo = u < m ? 0 : m, hi = lo + m;
        for (int v = lo; v < hi; v++) c += !hit[v];
    }
    return c;
}
int has(int a, int b) { for (int i = 0; i < 4; i++) if (adj[a][i] == b) return 1; return 0; }
void repl(int a, int old, int nw) { for (int i = 0; i < 4; i++) if (adj[a][i] == old) { adj[a][i] = nw; return; } }
int main(int argc, char **argv) {
    m = atoi(argv[1]); n = 2 * m; double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    double T0 = argc > 4 ? atof(argv[4]) : 2.0; const char *out = argc > 5 ? argv[5] : NULL;
    const char *start = argc > 6 ? argv[6] : NULL;
    if (start) {
        FILE *f = fopen(start, "r"); int deg[512] = {0}, x, y;
        while (fscanf(f, "%d %d", &x, &y) == 2) { adj[x][deg[x]++] = m + y; adj[m + y][deg[m + y]++] = x; }
        fclose(f);
        for (int v = 0; v < n; v++) if (deg[v] != 4) { printf("start graph not 4-regular at %d\n", v); return 1; }
    }
    /* random 4-regular bipartite simple graph: union of 4 random perfect matchings, retry on collisions */
    for (; !start;) {
        int ok = 1; int deg[512] = {0};
        for (int k = 0; k < 4 && ok; k++) {
            int p[256]; for (int i = 0; i < m; i++) p[i] = i;
            for (int i = m - 1; i > 0; i--) { int j = xr() % (i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
            for (int a = 0; a < m; a++) { int b = m + p[a]; for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) ok = 0;
                adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
        }
        if (ok) break;
    }
    int c = cost_all(), best = c; int bestadj[512][4]; memcpy(bestadj, adj, sizeof adj);
    clock_t t0 = clock(); long it = 0; double T = T0;
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && best > 0) {
        it++;
        double frac = (double)(clock() - t0) / CLOCKS_PER_SEC / secs; T = T0 * (1 - frac) + 0.05;
        int a1 = xr() % m, a2 = xr() % m; if (a1 == a2) continue;
        int i1 = xr() % 4, i2 = xr() % 4; int b1 = adj[a1][i1], b2 = adj[a2][i2];
        if (b1 == b2 || has(a1, b2) || has(a2, b1)) continue;
        repl(a1, b1, b2); repl(b2, a2, a1); repl(a2, b2, b1); repl(b1, a1, a2);
        int c2 = cost_all();
        if (c2 <= c || exp((c - c2) / T) > (double)(xr() % 1000000) / 1e6) {
            c = c2; if (c < best) { best = c; memcpy(bestadj, adj, sizeof adj); }
        } else { repl(a1, b2, b1); repl(b1, a2, a1); repl(a2, b1, b2); repl(b2, a1, a2); }
    }
    printf("m=%d best_cost=%d iters=%ld\n", m, best, it);
    if (out) { FILE *f = fopen(out, "w"); for (int a = 0; a < m; a++) for (int i = 0; i < 4; i++) fprintf(f, "%d %d\n", a, bestadj[a][i] - m); fclose(f); }
    return 0;
}
