/* hubcheck.c: same-side distances in the lifted hub graph of a typed5s .sol (hub graph alone, no main-graph routes).
   BFS from hub (k,0) of every orbit k on both sides (enough by the Z_m symmetry); counts same-side hubs farther than 6.
   Usage: hubcheck SOL */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    char line[1 << 16]; int m = 0, KB = -1, KA = -1, ne = -1, q, N, L; long n; char ty[64];
    if (!fgets(line, sizeof line, f) || sscanf(line, "typed5s %d %d %d %63s %d %ld", &q, &N, &L, ty, &m, &n) != 6) return 1;
    int *eB = NULL, *eA = NULL, *eC = NULL;
    while (fgets(line, sizeof line, f)) {
        if (!strncmp(line, "hubB ", 5)) KB = atoi(line + 5);
        else if (!strncmp(line, "hubA ", 5)) KA = atoi(line + 5);
        else if (!strncmp(line, "hg ", 3)) { ne = atoi(line + 3); eB = malloc(4 * ne); eA = malloc(4 * ne); eC = malloc(4 * ne);
            for (int e = 0; e < ne; e++) if (fscanf(f, "%d %d %d", &eB[e], &eA[e], &eC[e]) != 3) return 1; }
    }
    long H = (long)m * (KB + KA);
    int *deg = calloc(H, sizeof(int)); int **adj = malloc(sizeof(int *) * H);
    for (long h = 0; h < H; h++) adj[h] = malloc(sizeof(int) * 32);
    for (int e = 0; e < ne; e++) for (int t = 0; t < m; t++) { long u = (long)m * eB[e] + t, v = (long)m * (KB + eA[e]) + (t + eC[e]) % m; adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
    int *dist = malloc(sizeof(int) * H), *qq = malloc(sizeof(int) * H); long far = 0, worst = 0; int maxd = 0;
    for (int side = 0; side < 2; side++) for (int k = 0; k < (side ? KA : KB); k++) {
        long s = side ? (long)m * (KB + k) : (long)m * k; for (long h = 0; h < H; h++) dist[h] = -1;
        int hd = 0, tl = 0; dist[s] = 0; qq[tl++] = s;
        while (hd < tl) { int x = qq[hd++]; for (int i = 0; i < deg[x]; i++) { int y = adj[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qq[tl++] = y; } } }
        long lo = side ? (long)m * KB : 0, hi = side ? H : (long)m * KB, cnt = 0;
        for (long h = lo; h < hi; h++) { if (dist[h] < 0 || dist[h] > 6) cnt++; if (dist[h] > maxd) maxd = dist[h]; }
        far += cnt; if (cnt > worst) worst = cnt;
    }
    printf("hub orbits %d + %d (|G| = %d), hubs %ld; same-side pairs (from orbit reps) farther than 6 in the hub graph alone: %ld (worst source %ld), max same-side distance %d\n", KB, KA, m, H, far, worst, maxd);
    return 0;
}
