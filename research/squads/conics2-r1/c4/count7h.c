/* count7.c: number of ordered pairs (s,v) with dist(s,v) > D (default 7) in a graph given as "n" then "u v" edges.
   Bitset BFS, 64 sources per batch, exact. Build: cc -O3 -march=native -o count7 count7.c
   Usage: count7 EDGES [D] [MAXPRINT]  -> prints bad ordered pairs, and the number of sources with a bad pair. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    int D = argc > 2 ? atoi(argv[2]) : 7;
    int n; if (fscanf(f, "%d", &n) != 1) return 1;
    int cap = 1 << 20, m = 0; int *eu = malloc(sizeof(int) * cap), *ev = malloc(sizeof(int) * cap);
    int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) {
        if (m == cap) { cap *= 2; eu = realloc(eu, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        eu[m] = u; ev[m] = v; m++;
    }
    fclose(f);
    int *deg = calloc(n + 1, sizeof(int));
    for (int i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    int *off = malloc(sizeof(int) * (n + 1)); off[0] = 0;
    for (int i = 0; i < n; i++) off[i + 1] = off[i] + deg[i];
    int *adj = malloc(sizeof(int) * 2 * m + 4); int *fill = calloc(n, sizeof(int));
    for (int i = 0; i < m; i++) {
        adj[off[eu[i]] + fill[eu[i]]++] = ev[i];
        adj[off[ev[i]] + fill[ev[i]]++] = eu[i];
    }
    uint64_t *cur = malloc(sizeof(uint64_t) * n), *nxt = malloc(sizeof(uint64_t) * n);
    long long bad = 0; int badsrc = 0; int maxd = 0;
    int NN = argc > 3 ? atoi(argv[3]) : 0; long long hist[4][4][4][4]; memset(hist, 0, sizeof hist);
    for (int b0 = 0; b0 < n; b0 += 64) {
        int k = n - b0 < 64 ? n - b0 : 64;
        uint64_t valid = k == 64 ? ~0ULL : ((1ULL << k) - 1);
        for (int i = 0; i < n; i++) cur[i] = 0;
        for (int j = 0; j < k; j++) cur[b0 + j] |= 1ULL << j;
        for (int d = 0; d < D; d++) {
            for (int x = 0; x < n; x++) {
                uint64_t acc = cur[x];
                for (int e = off[x]; e < off[x + 1]; e++) acc |= cur[adj[e]];
                nxt[x] = acc;
            }
            uint64_t *t = cur; cur = nxt; nxt = t;
        }
        long long cnt = 0;
        for (int x = 0; x < n; x++) {
            uint64_t miss = ~cur[x] & valid;
            cnt += __builtin_popcountll(miss);
            if (NN && miss) for (int j = 0; j < k; j++) if (miss >> j & 1) {
                int s = b0 + j;
                int ls = s < 6 * NN ? s / (2 * NN) : 3, ks = s < 6 * NN ? ((s % (2 * NN)) < NN ? 0 : 1) : 2;
                int lv = x < 6 * NN ? x / (2 * NN) : 3, kv = x < 6 * NN ? ((x % (2 * NN)) < NN ? 0 : 1) : 2;
                hist[ls][ks][lv][kv]++;
            }
        }
        if (cnt) { badsrc++; }
        bad += cnt;
    }
    printf("n=%d edges=%d D=%d bad_ordered_pairs=%lld unordered=%lld sources_with_bad=%d\n", n, m, D, bad, bad / 2, badsrc);
    (void)maxd;
    if (NN) { const char *K[3] = {"pt","ln","hub"}; for (int a=0;a<4;a++) for(int b=0;b<3;b++) for(int c=0;c<4;c++) for(int d=0;d<3;d++) if (hist[a][b][c][d]) printf("src L%d %s -> tgt L%d %s : %lld\n", a,K[b],c,K[d],hist[a][b][c][d]); }
    return 0;
}
