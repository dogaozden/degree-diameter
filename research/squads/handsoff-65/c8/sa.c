/* sa.c: simulated annealing on a bipartite graph (max degree 6) by degree-preserving double edge swaps.
 * cost = number of unordered vertex pairs at distance > D (default 5) (bitset BFS to depth D).
 * usage: sa EDGES OUT ITERS T0 T1 SEED   (EDGES: "n" then "u v" lines, 0-based; sides from 2-colouring)
 * prints progress; writes best graph to OUT. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#define MAXN 1600
#define W ((MAXN + 63) / 64)
int n, m, D = 5;
int eu[4000], ev[4000];           /* edges: eu in side 0, ev in side 1 */
int side[MAXN];
int nb[MAXN][8], deg[MAXN];
static uint64_t R[2][MAXN][W];
int words;
static uint64_t rng_s;
static inline uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
long cost(void) {
    /* R_k[v] = ball of radius k around v */
    int cur = 0;
    for (int v = 0; v < n; v++) { memset(R[0][v], 0, sizeof(uint64_t) * words); R[0][v][v >> 6] |= 1ULL << (v & 63); }
    for (int k = 1; k <= D; k++) {
        int nxt = 1 - cur;
        for (int v = 0; v < n; v++) {
            uint64_t *dst = R[nxt][v];
            memcpy(dst, R[cur][v], sizeof(uint64_t) * words);
            for (int j = 0; j < deg[v]; j++) {
                uint64_t *src = R[cur][nb[v][j]];
                for (int w = 0; w < words; w++) dst[w] |= src[w];
            }
        }
        cur = nxt;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        for (int u = v + 1; u < n; u++) {
            if (!((R[cur][v][u >> 6] >> (u & 63)) & 1)) bad++;
        }
    }
    return bad;
}
int edge_exists(int a, int b) { for (int j = 0; j < deg[a]; j++) if (nb[a][j] == b) return 1; return 0; }
void rebuild(int m_) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m_; i++) {
        int a = eu[i], b = ev[i];
        nb[a][deg[a]++] = b; nb[b][deg[b]++] = a;
    }
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: sa EDGES OUT ITERS T0 T1 SEED [D]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    if (fscanf(f, "%d", &n) != 1) return 2;
    int a, b; m = 0;
    static int U[4000], V[4000];
    while (fscanf(f, "%d %d", &a, &b) == 2) { U[m] = a; V[m] = b; m++; }
    fclose(f);
    if (argc > 7) D = atoi(argv[7]);
    words = (n + 63) / 64;
    /* 2-colour */
    for (int v = 0; v < n; v++) side[v] = -1;
    int adjc[MAXN][8], dc[MAXN]; memset(dc, 0, sizeof dc);
    for (int i = 0; i < m; i++) { adjc[U[i]][dc[U[i]]++] = V[i]; adjc[V[i]][dc[V[i]]++] = U[i]; }
    int qu[MAXN], qh = 0, qt = 0;
    for (int s = 0; s < n; s++) if (side[s] < 0) {
        side[s] = 0; qu[qt++] = s;
        while (qh < qt) { int x = qu[qh++]; for (int j = 0; j < dc[x]; j++) { int y = adjc[x][j]; if (side[y] < 0) { side[y] = 1 - side[x]; qu[qt++] = y; } else if (side[y] == side[x]) { fprintf(stderr, "not bipartite\n"); return 1; } } }
    }
    int ne = 0;
    for (int i = 0; i < m; i++) {
        int x = U[i], y = V[i];
        if (side[x] == 1) { int t = x; x = y; y = t; }
        eu[ne] = x; ev[ne] = y; ne++;
    }
    m = ne;
    rebuild(m);
    long iters = atol(argv[3]);
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    rng_s = 88172645463325252ULL ^ (uint64_t)atol(argv[6]) * 2654435761ULL;
    long c = cost(), best = c;
    fprintf(stderr, "start n=%d m=%d cost=%ld\n", n, m, c);
    for (long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int i1 = rnd() % m, i2 = rnd() % m;
        if (i1 == i2) continue;
        int a1 = eu[i1], b1 = ev[i1], a2 = eu[i2], b2 = ev[i2];
        if (a1 == a2 || b1 == b2) continue;
        if (edge_exists(a1, b2) || edge_exists(a2, b1)) continue;
        /* apply */
        ev[i1] = b2; eu[i2] = a2; ev[i2] = b1; eu[i2] = a2;
        eu[i1] = a1; eu[i2] = a2;
        rebuild(m);
        long c2 = cost();
        if (c2 <= c || urand() < exp(-(double)(c2 - c) / T)) {
            c = c2;
            if (c < best) {
                best = c;
                FILE *g = fopen(argv[2], "w"); fprintf(g, "%d\n", n);
                for (int e = 0; e < m; e++) fprintf(g, "%d %d\n", eu[e], ev[e]);
                fclose(g);
                fprintf(stderr, "it %ld T %.3f best %ld\n", it, T, best);
                if (best == 0) break;
            }
        } else {
            /* revert */
            ev[i1] = b1; ev[i2] = b2; eu[i1] = a1; eu[i2] = a2;
            rebuild(m);
        }
        if (it % 20000 == 0) fprintf(stderr, "it %ld T %.3f cur %ld best %ld\n", it, T, c, best);
    }
    printf("final best %ld\n", best);
    return 0;
}
