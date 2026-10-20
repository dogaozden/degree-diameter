/* Independent check of a large graph given as text ("n m" then m lines "u v"):
   simple (no loops, no repeated edges), bipartite (BFS 2-colouring), maximum degree, and diameter <= D
   (bit-parallel BFS, 64 sources per pass, written separately from research/p4/d6/diam.c).
   Usage: check_big FILE D */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int cmp64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b;
    return x < y ? -1 : x > y;
}

int main(int argc, char **argv) {
    if (argc < 3) return 2;
    FILE *f = fopen(argv[1], "r");
    int D = atoi(argv[2]);
    long n, m;
    if (fscanf(f, "%ld %ld", &n, &m) != 2) return 2;
    long *u = malloc(m * sizeof(long)), *w = malloc(m * sizeof(long));
    uint64_t *key = malloc(m * sizeof(uint64_t));
    long *deg = calloc(n, sizeof(long));
    for (long i = 0; i < m; i++) {
        if (fscanf(f, "%ld %ld", &u[i], &w[i]) != 2) { printf("read error\n"); return 2; }
        if (u[i] == w[i] || u[i] < 0 || w[i] < 0 || u[i] >= n || w[i] >= n) { printf("bad edge\n"); return 1; }
        long a = u[i] < w[i] ? u[i] : w[i], b = u[i] < w[i] ? w[i] : u[i];
        key[i] = (uint64_t)a * (uint64_t)n + (uint64_t)b;
        deg[u[i]]++; deg[w[i]]++;
    }
    qsort(key, m, sizeof(uint64_t), cmp64);
    for (long i = 1; i < m; i++) if (key[i] == key[i - 1]) { printf("repeated edge\n"); return 1; }
    long *off = malloc((n + 1) * sizeof(long)), maxd = 0;
    off[0] = 0;
    for (long x = 0; x < n; x++) { off[x + 1] = off[x] + deg[x]; if (deg[x] > maxd) maxd = deg[x]; }
    long *adj = malloc(2 * m * sizeof(long)), *pos = malloc(n * sizeof(long));
    memcpy(pos, off, n * sizeof(long));
    for (long i = 0; i < m; i++) { adj[pos[u[i]]++] = w[i]; adj[pos[w[i]]++] = u[i]; }
    /* 2-colouring by BFS from every uncoloured vertex */
    int *col = malloc(n * sizeof(int));
    long *queue = malloc(n * sizeof(long));
    for (long x = 0; x < n; x++) col[x] = -1;
    long comps = 0;
    for (long s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        comps++;
        long h = 0, t = 0;
        col[s] = 0; queue[t++] = s;
        while (h < t) {
            long x = queue[h++];
            for (long k = off[x]; k < off[x + 1]; k++) {
                long y = adj[k];
                if (col[y] < 0) { col[y] = 1 - col[x]; queue[t++] = y; }
                else if (col[y] == col[x]) { printf("not bipartite\n"); return 1; }
            }
        }
    }
    long side0 = 0;
    for (long x = 0; x < n; x++) side0 += col[x] == 0;
    /* diameter <= D */
    uint64_t *seen = malloc(n * 8), *fr = malloc(n * 8), *nx = malloc(n * 8);
    long bad = 0;
    for (long base = 0; base < n; base += 64) {
        int k = (n - base) < 64 ? (int)(n - base) : 64;
        uint64_t full = k == 64 ? ~0ULL : ((1ULL << k) - 1);
        memset(seen, 0, n * 8); memset(fr, 0, n * 8);
        for (int j = 0; j < k; j++) { seen[base + j] = 1ULL << j; fr[base + j] = 1ULL << j; }
        for (int step = 0; step < D; step++) {
            for (long x = 0; x < n; x++) {
                uint64_t acc = 0;
                for (long e = off[x]; e < off[x + 1]; e++) acc |= fr[adj[e]];
                nx[x] = acc & ~seen[x];
            }
            for (long x = 0; x < n; x++) { seen[x] |= nx[x]; fr[x] = nx[x]; }
        }
        for (long x = 0; x < n; x++) if (seen[x] != full) bad += __builtin_popcountll(full & ~seen[x]);
    }
    printf("n=%ld m=%ld components=%ld bipartite=yes sides=%ld+%ld maxdeg=%ld pairs_beyond_D=%ld -> %s\n", n, m, comps,
           side0, n - side0, maxd, bad, (bad == 0 && comps == 1) ? "DIAMETER<=D OK" : "FAIL");
    return bad != 0;
}
