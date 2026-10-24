/* For an edge list (apsp format) of a lift with 256-point fibers (vertex = c*256 + x), BFS from every vertex of the
   fibers of controller vertices given on the command line; report, per controller target, how many (source, target)
   pairs have distance > 5, and the total. usage: liftmiss EDGES c1 [c2 ...] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); long n, m = 0, cap = 1 << 22; if (fscanf(f, "%ld", &n) != 1) return 1;
    long *U = malloc(cap * 8), *W = malloc(cap * 8), a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) { U[m] = a; W[m] = b; m++; }
    int *deg = calloc(n, 4); for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, 8); for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    int *adj = malloc(2 * m * 4), *pos = calloc(n, 4);
    for (long i = 0; i < m; i++) { adj[st[U[i]] + pos[U[i]]++] = W[i]; adj[st[W[i]] + pos[W[i]]++] = U[i]; }
    int nc = n / 256; long *missc = calloc(nc, 8); int *dist = malloc(n * 4), *q = malloc(n * 4);
    long total = 0;
    for (int k = 2; k < argc; k++) { int c = atoi(argv[k]);
        memset(missc, 0, nc * 8);
        for (int x = 0; x < 256; x++) { int s = c * 256 + x;
            for (long i = 0; i < n; i++) dist[i] = -1; int h = 0, t = 0; dist[s] = 0; q[t++] = s;
            while (h < t) { int v = q[h++]; if (dist[v] >= 5) continue; for (long i = st[v]; i < st[v + 1]; i++) if (dist[adj[i]] < 0) { dist[adj[i]] = dist[v] + 1; q[t++] = adj[i]; } }
            for (long i = 0; i < n; i++) if (dist[i] < 0) { missc[i / 256]++; total++; } }
        int nbad = 0; for (int i = 0; i < nc; i++) if (missc[i]) nbad++;
        printf("source controller vertex %d: %d controller targets with misses;", c, nbad);
        int shown = 0; for (int i = 0; i < nc && shown < 12; i++) if (missc[i]) { printf(" %d:%ld", i, missc[i]); shown++; } printf("\n");
    }
    printf("total missed (source,target) pairs %ld\n", total);
    return 0; }
