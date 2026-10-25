/* hexcheck: read hex/hex_q{q}.bin, BFS from several points and lines, print sphere sizes.
   For a generalized hexagon of order (q,q): spheres 1, q+1, (q+1)q, ..., (q+1)q^4, q^5 (Moore: girth 12, diameter 6). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    char fn[64]; sprintf(fn, "hex/hex_q%s.bin", argv[1]);
    FILE *f = fopen(fn, "rb"); int32_t h[3]; fread(h, 4, 3, f);
    int q = h[0], N = h[1], L = h[2], Q1 = q + 1, V = N + L;
    int32_t *ln = malloc(4L * L * Q1); fread(ln, 4, (size_t)L * Q1, f); fclose(f);
    int *adj = malloc(sizeof(int) * V * Q1), *deg = calloc(V, sizeof(int));
    for (int l = 0; l < L; l++) for (int k = 0; k < Q1; k++) { int p = ln[l * Q1 + k]; adj[p * Q1 + deg[p]++] = N + l; adj[(N + l) * Q1 + deg[N + l]++] = p; }
    for (int v = 0; v < V; v++) if (deg[v] != Q1) { printf("bad degree\n"); return 1; }
    int *dist = malloc(sizeof(int) * V), *qu = malloc(sizeof(int) * V);
    int ok = 1;
    int srcs[8] = {0, N / 3, N - 1, 7 % N, N, N + L / 2, V - 1, N + 5 % L};
    for (int si = 0; si < 8; si++) {
        int s = srcs[si];
        for (int v = 0; v < V; v++) dist[v] = -1;
        int hd = 0, tl = 0; dist[s] = 0; qu[tl++] = s; long sph[16] = {0};
        while (hd < tl) { int u = qu[hd++]; sph[dist[u]]++; for (int k = 0; k < Q1; k++) { int w = adj[u * Q1 + k]; if (dist[w] < 0) { dist[w] = dist[u] + 1; qu[tl++] = w; } } }
        long want[7] = {1, Q1, (long)Q1 * q, (long)Q1 * q * q, (long)Q1 * q * q * q, (long)Q1 * q * q * q * q, (long)q * q * q * q * q};
        for (int d = 0; d < 7; d++) if (sph[d] != want[d]) ok = 0;
        if (tl != V || sph[7]) ok = 0;
        if (si == 0) { printf("q=%d V=%d spheres:", q, V); for (int d = 0; d < 8; d++) printf(" %ld", sph[d]); printf("\n"); }
    }
    printf("q=%d generalized hexagon (Moore spheres from 8 sources): %s\n", q, ok ? "yes" : "NO");
    return !ok;
}
