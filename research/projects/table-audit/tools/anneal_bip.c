/* anneal_bip.c (table-audit): simulated annealing for a d-regular bipartite graph with sides a, b (a*d = b*d needs
   a = b) of diameter <= D.  State: d-regular simple bipartite graph; move: 2-switch (a1-b1, a2-b2) -> (a1-b2, a2-b1);
   cost = number of unordered pairs at distance > D (bitset BFS from every vertex).  Writes the first cost-0 graph
   as an edge list ("n" then "u v") for apsp.c.  Small cells only (n <= 4096).
   Usage: anneal_bip n d D seconds seed OUT */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int n, h, d, D;
static int *adj;            /* adj[v*d + i] */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int W;               /* words per bitset */
static uint64_t *R, *F, *NF;
static int has(int u, int v) { for (int i = 0; i < d; i++) if (adj[u * d + i] == v) return 1; return 0; }
static void rep(int u, int old, int nw) { for (int i = 0; i < d; i++) if (adj[u * d + i] == old) { adj[u * d + i] = nw; return; } }
static long cost(void) {
    /* bitset BFS from each source: R = reached; distances <= D */
    long bad = 0;
    for (int s = 0; s < n; s++) {
        memset(R, 0, 8L * W); R[s >> 6] |= 1ULL << (s & 63);
        int fr[4096], nf = 1; fr[0] = s;
        static int nx[4096];
        for (int lev = 0; lev < D && nf; lev++) {
            int nn = 0;
            for (int t = 0; t < nf; t++) { int u = fr[t]; for (int i = 0; i < d; i++) { int v = adj[u * d + i]; if (!(R[v >> 6] >> (v & 63) & 1)) { R[v >> 6] |= 1ULL << (v & 63); nx[nn++] = v; } } }
            memcpy(fr, nx, sizeof(int) * nn); nf = nn;
        }
        int c = 0; for (int w = 0; w < W; w++) c += __builtin_popcountll(R[w]);
        bad += n - c;
    }
    return bad / 2;
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); d = atoi(argv[2]); D = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (uint64_t)atoi(argv[5]) * 0x9E3779B97F4A7C15ULL;
    const char *out = argv[6]; h = n / 2; W = (n + 63) / 64;
    R = malloc(8L * W); F = malloc(8L * W); NF = malloc(8L * W);
    adj = malloc(sizeof(int) * n * d);
    /* initial: circulant-style d-regular bipartite: a_i ~ b_{(i + j*step) mod h} */
    for (;;) {
        int ok = 1; int *deg = calloc(n, sizeof(int));
        for (int i = 0; i < h && ok; i++) for (int j = 0; j < d; j++) {
            int tries = 0, v;
            do { v = h + rnd() % h; tries++; } while ((deg[v] >= d || has(i, v)) && tries < 1000);
            if (tries >= 1000) { ok = 0; break; }
            adj[i * d + deg[i]++] = v; adj[v * d + deg[v]++] = i;
        }
        free(deg); if (ok) break;
    }
    long c = cost(), best = c; double T = 2.0; clock_t t0 = clock(); long it = 0;
    while (c > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        int a1 = rnd() % h, a2 = rnd() % h; if (a1 == a2) continue;
        int b1 = adj[a1 * d + rnd() % d], b2 = adj[a2 * d + rnd() % d];
        if (b1 == b2 || has(a1, b2) || has(a2, b1)) continue;
        rep(a1, b1, b2); rep(b2, a2, a1); rep(a2, b2, b1); rep(b1, a1, a2);
        long c2 = cost();
        if (c2 <= c || exp((c - c2) / T) > (rnd() >> 11) * (1.0 / 9007199254740992.0)) { c = c2; if (c < best) { best = c; } }
        else { rep(a1, b2, b1); rep(b1, a2, a1); rep(a2, b1, b2); rep(b2, a1, a2); }
        T *= 0.9995; if (T < 0.05) T = 1.0;
    }
    printf("RESULT n=%d d=%d D=%d cost=%ld best=%ld iters=%ld\n", n, d, D, c, best, it);
    if (c == 0) {
        FILE *f = fopen(out, "w"); fprintf(f, "%d\n", n);
        for (int u = 0; u < h; u++) for (int i = 0; i < d; i++) fprintf(f, "%d %d\n", u, adj[u * d + i]);
        fclose(f); printf("wrote %s\n", out);
    }
    return c != 0;
}
