/* Bit-parallel diameter check for a graph given as text: first line "n m", then m lines "u v".
   Usage: diam FILE D  -> prints max degree, whether every pair is within distance D, and the number
   of ordered pairs farther than D. 64 BFS sources at a time. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: diam FILE D\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]);
    long n, m; if (fscanf(f, "%ld %ld", &n, &m) != 2) return 2;
    long *eu = malloc(m * sizeof(long)), *ev = malloc(m * sizeof(long));
    long *deg = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { if (fscanf(f, "%ld %ld", &eu[i], &ev[i]) != 2) return 2; deg[eu[i]]++; deg[ev[i]]++; }
    long *off = malloc((n + 1) * sizeof(long)); off[0] = 0; long maxd = 0;
    for (long v = 0; v < n; v++) { off[v + 1] = off[v] + deg[v]; if (deg[v] > maxd) maxd = deg[v]; }
    long *adj = malloc(2 * m * sizeof(long)); long *pos = malloc(n * sizeof(long));
    memcpy(pos, off, n * sizeof(long));
    for (long i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    uint64_t *vis = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    long bad = 0;
    for (long b = 0; b < n; b += 64) {
        int k = (n - b < 64) ? (int)(n - b) : 64; uint64_t full = (k == 64) ? ~0ULL : ((1ULL << k) - 1);
        memset(vis, 0, n * 8); memset(fr, 0, n * 8);
        for (int j = 0; j < k; j++) { vis[b + j] = fr[b + j] = 1ULL << j; }
        for (int r = 0; r < D; r++) {
            for (long v = 0; v < n; v++) {
                uint64_t x = 0; for (long t = off[v]; t < off[v + 1]; t++) x |= fr[adj[t]];
                nx[v] = x & ~vis[v];
            }
            for (long v = 0; v < n; v++) vis[v] |= nx[v];
            uint64_t *t = fr; fr = nx; nx = t;
        }
        for (long v = 0; v < n; v++) bad += __builtin_popcountll(full & ~vis[v]);
    }
    printf("n=%ld m=%ld maxdeg=%ld D=%d far_ordered_pairs=%ld %s\n", n, m, maxd, D, bad, bad ? "FAIL" : "OK");
    return bad ? 1 : 0;
}
