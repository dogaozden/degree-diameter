/* Exhaustive search over Haar graphs H(G,S), S = {e, a, b}, cubic bipartite on 2N vertices.
 * Vertex g (A side) = g, vertex N+g (B side). (g,A) ~ (s g, B) for s in S.
 * cost = (2N - #within 10 of (e,A)) + (2N - #within 10 of (e,B)); cost 0 <=> diameter <= 10.
 * Usage: haar_c4 TABLE [EDGEOUT]   (TABLE: N then N rows of N ints, identity = 0) */
#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#define DIAM 10

static int N;
static int *T, *INV, *stamp, *dist, *q;
static int cur = 0;
static int S[3], SI[3];

static int bfs(int start) {
    int head = 0, tail = 0, cnt = 0;
    cur++;
    stamp[start] = cur; dist[start] = 0; q[tail++] = start;
    while (head < tail) {
        int v = q[head++];
        int dv = dist[v];
        cnt++;
        if (dv == DIAM) continue;
        if (v < N) {
            for (int i = 0; i < 3; i++) {
                int u = N + T[S[i] * N + v];
                if (stamp[u] != cur) { stamp[u] = cur; dist[u] = dv + 1; q[tail++] = u; }
            }
        } else {
            int h = v - N;
            for (int i = 0; i < 3; i++) {
                int u = T[SI[i] * N + h];
                if (stamp[u] != cur) { stamp[u] = cur; dist[u] = dv + 1; q[tail++] = u; }
            }
        }
    }
    return cnt;
}

static int cost_of(int a, int b) {
    S[0] = 0; S[1] = a; S[2] = b;
    SI[0] = 0; SI[1] = INV[a]; SI[2] = INV[b];
    int c1 = bfs(0), c2 = bfs(N);
    return (2 * N - c1) + (2 * N - c2);
}

static void write_edges(const char *path, int a, int b) {
    S[0] = 0; S[1] = a; S[2] = b;
    FILE *o = fopen(path, "w");
    if (!o) return;
    fprintf(o, "%d\n", 2 * N);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < 3; i++)
            fprintf(o, "%d %d\n", g, N + T[S[i] * N + g]);
    fclose(o);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haar_c4 TABLE [EDGEOUT]\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("table"); return 1; }
    if (fscanf(f, "%d", &N) != 1) return 1;
    T = malloc(sizeof(int) * N * N);
    for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &T[i]) != 1) return 1;
    fclose(f);
    INV = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++)
        for (int h = 0; h < N; h++)
            if (T[g * N + h] == 0) INV[g] = h;
    stamp = calloc(2 * N, sizeof(int));
    dist = malloc(sizeof(int) * 2 * N);
    q = malloc(sizeof(int) * 2 * N);

    int best = INT_MAX, bA = -1, bB = -1, nbest = 0, nzero = 0, wrote = 0;
    for (int a = 1; a < N; a++)
        for (int b = a + 1; b < N; b++) {
            int c = cost_of(a, b);
            if (c < best) { best = c; bA = a; bB = b; nbest = 1; }
            else if (c == best) nbest++;
            if (c == 0) {
                nzero++;
                if (!wrote && argc > 2) { write_edges(argv[2], a, b); wrote = 1; }
            }
        }
    printf("RESULT N=%d best=%d a=%d b=%d nbest=%d nzero=%d\n", N, best, bA, bB, nbest, nzero);
    return 0;
}
