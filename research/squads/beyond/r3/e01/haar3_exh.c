/* e01: exhaustive search over cubic Haar graphs H(G,{e,x,y}) for one group table.
 * Vertices: A-side g -> g, B-side h -> N+h.  Edges (g,A)~(s g,B) for s in S={e,x,y}.
 * Right multiplication is an automorphism, so diam = max(ecc(A0), ecc(B0)).
 * cost = #vertices not within D of A0 + #not within D of B0 (0 iff diameter <= D).
 * Usage: haar3_exh TABLE.bin D [EDGES_OUT]   (table format of research/squads/b48/tools/groups.py)
 * Exact minimum cost over all pairs x<y (pruned: a pair is abandoned once its cost reaches the best so far).
 * Stops at the first cost-0 pair and writes its edge list (first line 2N) if EDGES_OUT is given. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>

static int N, D;
static uint16_t *T;
static int *inv;
static uint32_t *stamp, cur;
static int *dist, *q;

/* BFS from src over the Haar graph with S = {0,x,y}, Si = {0,inv x,inv y}; returns #visited within D. */
static int bfs(int src, const int *S, const int *Si) {
    cur++;
    int h = 0, t = 0, cnt = 0;
    stamp[src] = cur; dist[src] = 0; q[t++] = src; cnt = 1;
    while (h < t) {
        int v = q[h++];
        int dv = dist[v];
        if (dv == D) continue;
        if (v < N) {               /* A-vertex g: B-neighbours s*g */
            for (int k = 0; k < 3; k++) {
                int w = N + T[(size_t)S[k] * N + v];
                if (stamp[w] != cur) { stamp[w] = cur; dist[w] = dv + 1; q[t++] = w; cnt++; }
            }
        } else {                   /* B-vertex h: A-neighbours s^-1 * h */
            int hh = v - N;
            for (int k = 0; k < 3; k++) {
                int w = T[(size_t)Si[k] * N + hh];
                if (stamp[w] != cur) { stamp[w] = cur; dist[w] = dv + 1; q[t++] = w; cnt++; }
            }
        }
    }
    return cnt;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: haar3_exh TABLE.bin D [EDGES_OUT]\n"); return 2; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror("table"); return 2; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 2; N = n32;
    T = malloc((size_t)N * N * 2);
    if (fread(T, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short table\n"); return 2; }
    fclose(f);
    D = atoi(argv[2]);
    inv = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) for (int h = 0; h < N; h++) if (T[(size_t)g * N + h] == 0) { inv[g] = h; break; }
    stamp = calloc((size_t)2 * N, sizeof(uint32_t)); dist = malloc((size_t)2 * N * sizeof(int)); q = malloc((size_t)2 * N * sizeof(int));
    cur = 0;
    int V = 2 * N;
    int best = INT_MAX, bx = -1, by = -1, bestA = 0, bestB = 0;
    long long pairs = 0, zero = 0;
    int S[3], Si[3];
    S[0] = 0; Si[0] = 0;
    for (int x = 1; x < N && best > 0; x++) for (int y = x + 1; y < N && best > 0; y++) {
        S[1] = x; S[2] = y; Si[1] = inv[x]; Si[2] = inv[y];
        pairs++;
        int vA = bfs(0, S, Si);           /* from A0 */
        int costA = V - vA;
        if (costA >= best) continue;
        int vB = bfs(N + 0, S, Si);       /* from B0 */
        int cost = costA + (V - vB);
        if (cost < best) { best = cost; bx = x; by = y; bestA = costA; bestB = V - vB; }
        if (cost == 0) zero++;
    }
    printf("N=%d order=%d D=%d pairs=%lld min_cost=%d (A0 part %d, B0 part %d) x=%d y=%d zero_found=%lld\n",
           N, N, D, pairs, best, bestA, bestB, bx, by, zero);
    if (argc > 3 && best == 0) {
        FILE *o = fopen(argv[3], "w");
        fprintf(o, "%d\n", V);
        for (int g = 0; g < N; g++) {
            int s3[3] = {0, bx, by};
            for (int k = 0; k < 3; k++) fprintf(o, "%d %d\n", g, N + T[(size_t)s3[k] * N + g]);
        }
        fclose(o);
        printf("EDGES_WRITTEN %s\n", argv[3]);
    }
    return 0;
}
