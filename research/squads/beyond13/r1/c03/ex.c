/* Exhaustive search over Haar graphs H(G,S), S = {e,x,y} (WLOG e in S), on a group given by a multiplication table
 * (identity = index 0).  Exact diameter test: G acts transitively on each side, so diam = max(ecc(A0), ecc(B0)); the
 * cost is the number of vertices not within D of A0 plus those not within D of B0 (cost 0 <=> diameter <= D).
 *   ex TABLE.bin D maxsol [x y]      search (stop after maxsol valid pairs); with x y: report that pair's cost
 *   ex TABLE.bin D verify x y        independent check: explicit 2N-vertex graph, BFS from every vertex
 * Output lines: "VALID x y" for each valid pair; a summary "SUMMARY pairs=.. valid=.. bestcost=.. bestpair=.. secs=..".
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int N;
static uint16_t *T;
static int *inv;

static int mul(int a, int b) { return T[(size_t)a * N + b]; }

/* cost of pair (x,y) at depth limit D: unreached-within-D count from A0 and B0 */
static int *dist; static int *queue;
static int cost_from(int src, int S[3], int D) {
    int V = 2 * N;
    for (int i = 0; i < V; i++) dist[i] = -1;
    int qh = 0, qt = 0;
    dist[src] = 0; queue[qt++] = src;
    while (qh < qt) {
        int v = queue[qh++];
        int dv = dist[v];
        if (dv >= D) continue;
        if (v < N) {               /* A vertex g: neighbours B (s g) */
            for (int k = 0; k < 3; k++) {
                int w = N + mul(S[k], v);
                if (dist[w] < 0) { dist[w] = dv + 1; queue[qt++] = w; }
            }
        } else {                   /* B vertex h: neighbours A (s^-1 h) */
            int h = v - N;
            for (int k = 0; k < 3; k++) {
                int w = mul(inv[S[k]], h);
                if (dist[w] < 0) { dist[w] = dv + 1; queue[qt++] = w; }
            }
        }
    }
    return V - qt;   /* vertices not reached within D */
}

static int cost_pair(int x, int y, int D) {
    int S[3] = {0, x, y};
    int c = cost_from(0, S, D);          /* A0 */
    c += cost_from(N + 0, S, D);         /* B0 */
    return c;
}

static int verify(int x, int y) {
    int S[3] = {0, x, y};
    int V = 2 * N;
    int *adj = malloc(sizeof(int) * V * 3);
    for (int g = 0; g < N; g++)
        for (int k = 0; k < 3; k++) adj[g * 3 + k] = N + mul(S[k], g);
    for (int h = 0; h < N; h++)
        for (int k = 0; k < 3; k++) adj[(N + h) * 3 + k] = mul(inv[S[k]], h);
    /* symmetry check: every edge must be listed from both ends */
    int bad = 0;
    for (int v = 0; v < V; v++)
        for (int k = 0; k < 3; k++) {
            int w = adj[v * 3 + k], found = 0;
            for (int j = 0; j < 3; j++) if (adj[w * 3 + j] == v) found = 1;
            if (!found) bad++;
        }
    int diam = 0, reached_all = 1;
    for (int src = 0; src < V; src++) {
        for (int i = 0; i < V; i++) dist[i] = -1;
        int qh = 0, qt = 0; dist[src] = 0; queue[qt++] = src;
        while (qh < qt) {
            int v = queue[qh++];
            for (int k = 0; k < 3; k++) {
                int w = adj[v * 3 + k];
                if (dist[w] < 0) { dist[w] = dist[v] + 1; queue[qt++] = w; }
            }
        }
        if (qt != V) reached_all = 0;
        for (int i = 0; i < V; i++) if (dist[i] > diam) diam = dist[i];
    }
    printf("VERIFY x=%d y=%d N=%d vertices=%d edges_asym=%d connected=%d diameter=%d\n", x, y, N, V, bad, reached_all, diam);
    free(adj);
    return diam;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: ex TABLE D maxsol|verify [x y]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("table"); return 1; }
    int32_t n32; if (fread(&n32, 4, 1, f) != 1) return 1;
    N = n32;
    T = malloc(sizeof(uint16_t) * (size_t)N * N);
    if (fread(T, sizeof(uint16_t), (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short read\n"); return 1; }
    fclose(f);
    inv = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) {
        int found = -1;
        for (int b = 0; b < N; b++) if (mul(a, b) == 0) { found = b; break; }
        inv[a] = found;
    }
    dist = malloc(sizeof(int) * 2 * N); queue = malloc(sizeof(int) * 2 * N);
    int D = atoi(argv[2]);
    if (strcmp(argv[3], "verify") == 0) {
        int x = atoi(argv[4]), y = atoi(argv[5]);
        verify(x, y);
        return 0;
    }
    int maxsol = atoi(argv[3]);
    if (argc >= 6) {
        int x = atoi(argv[4]), y = atoi(argv[5]);
        printf("PAIR x=%d y=%d cost=%d\n", x, y, cost_pair(x, y, D));
        return 0;
    }
    clock_t t0 = clock();
    long pairs = 0, valid = 0; int bestc = 1 << 30, bx = -1, by = -1;
    for (int x = 1; x < N && valid < maxsol; x++)
        for (int y = x + 1; y < N && valid < maxsol; y++) {
            pairs++;
            int c = cost_pair(x, y, D);
            if (c < bestc) { bestc = c; bx = x; by = y; }
            if (c == 0) { valid++; printf("VALID %d %d\n", x, y); fflush(stdout); }
        }
    printf("SUMMARY N=%d D=%d pairs=%ld valid=%ld bestcost=%d bestpair=%d,%d secs=%.1f\n", N, D, pairs, valid, bestc, bx, by,
           (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
