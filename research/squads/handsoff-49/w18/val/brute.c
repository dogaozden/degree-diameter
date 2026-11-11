/* brute.c (auditor w18): brute force over ALL S = {e,x,y,z} of a metacyclic group Z_m x|_r Z_k, no symmetry reduction.
 * Haar graph: vertices A-g = g, B-g = N+g, edges (g,A) ~ (s g,B), s in S (same convention as w11 exh3).
 * Cost (w11 convention, D = 9): for each root (e,A) and (e,B), number of same-side vertices at distance > 8 (or unreached).
 * Prints min cost, number of S attaining it, and one minimiser. Usage: brute M K R */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int m, k, r, N, D = 9;
int *T, *INV;
#define MUL(x, y) T[(x) * N + (y)]
int main(int argc, char **argv) {
    m = atoi(argv[1]); k = atoi(argv[2]); r = atoi(argv[3]); N = m * k; if (argc > 4) D = atoi(argv[4]);
    int *pw = malloc(sizeof(int) * (k + 1)); pw[0] = 1 % m;
    for (int j = 1; j <= k; j++) pw[j] = (pw[j - 1] * r) % m;
    if (pw[k] != 1 % m) { printf("bad group: r^k != 1 mod m\n"); return 1; }
    T = malloc(sizeof(int) * N * N); INV = malloc(sizeof(int) * N);
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) {
        int a1 = x % m, j1 = x / m, a2 = y % m, j2 = y / m;
        int a = (a1 + (int)((long)pw[j1] * a2 % m)) % m, j = (j1 + j2) % k;
        T[x * N + y] = a + m * j;
    }
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (MUL(x, y) == 0) INV[x] = y;
    /* sanity: associativity on a sample */
    for (int t = 0; t < 2000; t++) { int x = rand() % N, y = rand() % N, z = rand() % N;
        if (MUL(MUL(x, y), z) != MUL(x, MUL(y, z))) { printf("not associative\n"); return 1; } }
    int best = 1 << 30, nbest = 0, bs[4] = {0, 0, 0, 0};
    int nv = 2 * N, *adj = malloc(sizeof(int) * nv * 4), *deg = malloc(sizeof(int) * nv);
    int *dist = malloc(sizeof(int) * nv), *q = malloc(sizeof(int) * nv);
    long sets = 0;
    for (int x = 1; x < N; x++) for (int y = x + 1; y < N; y++) for (int z = y + 1; z < N; z++) {
        int S[4] = {0, x, y, z}; sets++;
        for (int v = 0; v < nv; v++) deg[v] = 0;
        for (int g = 0; g < N; g++) for (int i = 0; i < 4; i++) {
            int b = MUL(S[i], g);            /* A-g ~ B-(s g) */
            adj[g * 4 + deg[g]++] = N + b;
            adj[(N + b) * 4 + deg[N + b]++] = g;
        }
        int cost = 0;
        int roots[2] = {0, N};
        for (int ri = 0; ri < 2; ri++) {
            int s = roots[ri];
            for (int v = 0; v < nv; v++) dist[v] = -1;
            int h = 0, t = 0; dist[s] = 0; q[t++] = s;
            while (h < t) { int u = q[h++]; for (int i = 0; i < deg[u]; i++) { int w = adj[u * 4 + i];
                if (dist[w] < 0) { dist[w] = dist[u] + 1; q[t++] = w; } } }
            int side0 = (s < N) ? 0 : N;
            for (int v = side0; v < side0 + N; v++) if (dist[v] < 0 || dist[v] > D - 1) cost++;
        }
        if (cost < best) { best = cost; nbest = 0; }
        if (cost == best) { if (nbest == 0) { bs[0] = S[0]; bs[1] = S[1]; bs[2] = S[2]; bs[3] = S[3]; } nbest++; }
    }
    printf("BRUTE m=%d k=%d r=%d N=%d sets=%ld min=%d count_at_min=%d example_S={%d,%d,%d,%d}\n",
           m, k, r, N, sets, best, nbest, bs[0], bs[1], bs[2], bs[3]);
    return 0;
}
