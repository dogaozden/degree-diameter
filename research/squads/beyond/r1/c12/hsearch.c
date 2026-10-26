/* c12: Haar graphs H(G,S) of a finite group G (table from research/squads/b48/tools/groups.py), S = {e,a,b}.
   Vertices (g,0),(g,1), g in G. Edges (g,0)~(s g,1) for s in S.  G acts on the right transitively on each part,
   so diameter = max(ecc((e,0)), ecc((e,1))): two BFS per graph.
   Cost = number of vertices not within distance D of (e,0) plus same for (e,1). Local search over a,b.
   Usage: hsearch TABLE.bin D seconds seed OUT_EDGES
   If cost 0 is reached, writes OUT_EDGES (apsp format) and prints "FOUND a b". */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
static int N, D; static uint16_t *T; static int *inv;
static uint64_t rs;
static uint64_t rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static double now(void){ struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t); return t.tv_sec+1e-9*t.tv_nsec; }
static int *dist, *q;
/* unreached count from source (src part) within D */
static long unreached(int S0, int S1, int S2, int src) {
    int nn = 2*N; for (int i = 0; i < nn; i++) dist[i] = -1;
    int h = 0, t = 0; dist[src] = 0; q[t++] = src; long reached = 1;
    int Ss[3] = {S0, S1, S2}, Si[3] = {inv[S0], inv[S1], inv[S2]};
    while (h < t) {
        int x = q[h++]; int dx = dist[x]; if (dx >= D) continue;
        if (x < N) { /* (g,0) -> (s g,1) */
            for (int k = 0; k < 3; k++) { int y = N + T[(size_t)Ss[k]*N + x]; if (dist[y] < 0) { dist[y] = dx+1; q[t++] = y; reached++; } }
        } else { int g = x - N; /* (y,1) -> (s^-1 y, 0) */
            for (int k = 0; k < 3; k++) { int y = T[(size_t)Si[k]*N + g]; if (dist[y] < 0) { dist[y] = dx+1; q[t++] = y; reached++; } }
        }
    }
    return nn - reached;
}
static long cost(int a, int b) { return unreached(0, a, b, 0) + unreached(0, a, b, N); }
static int *best_dummy;
static void write_edges(const char *fn, int a, int b) {
    FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", 2*N);
    int S[3] = {0, a, b};
    for (int g = 0; g < N; g++) for (int k = 0; k < 3; k++) fprintf(f, "%d %d\n", g, N + T[(size_t)S[k]*N + g]);
    fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: hsearch TABLE.bin D seconds seed OUT_EDGES\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 2; N = n32;
    T = malloc((size_t)N*N*2); if (fread(T, 2, (size_t)N*N, f) != (size_t)N*N) return 2; fclose(f);
    D = atoi(argv[2]); double secs = atof(argv[3]); rs = 88172645463325252ULL ^ (uint64_t)atoll(argv[4])*2654435761ULL; if (!rs) rs = 1;
    inv = malloc(N*sizeof(int));
    for (int s = 0; s < N; s++) { inv[s] = -1; for (int h = 0; h < N; h++) if (T[(size_t)s*N+h] == 0) { inv[s] = h; break; } }
    dist = malloc(2*N*sizeof(int)); q = malloc(2*N*sizeof(int));
    double t0 = now(); long evals = 0; long bestc = -1; int ba = 0, bb = 0;
    while (now() - t0 < secs) {
        /* random restart */
        int a = 1 + rnd() % (N-1), b = 1 + rnd() % (N-1);
        if (a == b) continue;
        long c = cost(a, b); evals++;
        double T0 = 0.5 * (1 + (double)(rnd() % 1000) / 1000.0);
        for (int it = 0; it < 4000 && c > 0; it++) {
            int na = a, nb = b;
            if (rnd() & 1) na = 1 + rnd() % (N-1); else nb = 1 + rnd() % (N-1);
            if (na == nb || na == 0 || nb == 0) continue;
            long nc = cost(na, nb); evals++;
            if (nc <= c || (double)(rnd() % 1000000) / 1e6 < 0.02 * T0) { a = na; b = nb; c = nc; }
            if (bestc < 0 || c < bestc) { bestc = c; ba = a; bb = b; }
            if (c == 0) break;
        }
        if (bestc < 0 || c < bestc) { bestc = c; ba = a; bb = b; }
        if (bestc == 0) break;
    }
    printf("RESULT N=%d (graph %d vertices) D=%d evals=%ld best_cost=%ld S={0,%d,%d}\n", N, 2*N, D, evals, bestc, ba, bb);
    if (bestc == 0) { printf("FOUND %d %d\n", ba, bb); write_edges(argv[5], ba, bb); }
    return bestc == 0 ? 0 : 3;
}
