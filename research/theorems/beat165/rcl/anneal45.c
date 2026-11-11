/* Anneal a 4-regular bipartite graph on N + N vertices (4 perfect matchings A->B) toward:
   every same-side pair at distance <= 4, and every vertex on a 4-cycle.
   cost = #ordered same-side pairs at distance > 4 + W * #vertices on no 4-cycle.
   Move: in matching i, swap the B-partners of two A-vertices (rejected if it creates a parallel edge).
   Output on success: controller in pv format with k = N, m = 1 (pa, pb from M1/M2 and M3/M4).
   usage: anneal45 N seed iters W */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int N, M[4][512], Minv[4][512];   /* M[i][a] = b (0..N-1), Minv[i][b] = a */
static int adj[1024][4];
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void build(void) { for (int a = 0; a < N; a++) for (int i = 0; i < 4; i++) { adj[a][i] = N + M[i][a]; adj[N + M[i][a]][i] = a; } }
static int simple(void) { for (int a = 0; a < N; a++) for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++) if (M[i][a] == M[j][a]) return 0; return 1; }
static int cost(int W) {
    static int dist[1024], q[1024]; int bad = 0, no4 = 0, n2 = 2 * N;
    for (int s = 0; s < n2; s++) {
        for (int i = 0; i < n2; i++) dist[i] = -1; int h = 0, t = 0; dist[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; if (dist[x] >= 4) continue; for (int i = 0; i < 4; i++) { int y = adj[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
        int lo = s < N ? 0 : N; for (int i = lo; i < lo + N; i++) if (dist[i] < 0) bad++;
        /* 4-cycle through s: two neighbours of s with a common neighbour other than s */
        int f = 0; for (int i = 0; i < 4 && !f; i++) for (int j = i + 1; j < 4 && !f; j++) { int u = adj[s][i], v = adj[s][j];
            for (int k = 0; k < 4 && !f; k++) { int w = adj[u][k]; if (w == s) continue; for (int l = 0; l < 4; l++) if (adj[v][l] == w) { f = 1; break; } } }
        if (!f) no4++;
    }
    return bad + W * no4; }
int main(int argc, char **argv) {
    N = atoi(argv[1]); rs ^= (unsigned long long)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; long iters = atol(argv[3]); int W = atoi(argv[4]);
    do { for (int i = 0; i < 4; i++) { for (int a = 0; a < N; a++) M[i][a] = a; for (int a = N - 1; a > 0; a--) { int j = rnd() % (a + 1); int t = M[i][a]; M[i][a] = M[i][j]; M[i][j] = t; } } } while (!simple());
    build(); int c = cost(W), best = c; double T = 5.0;
    for (long it = 0; it < iters && c > 0; it++) {
        int i = rnd() % 4, x = rnd() % N, y = rnd() % N; if (x == y) continue;
        int bx = M[i][x], by = M[i][y]; int ok = 1;
        for (int j = 0; j < 4; j++) if (j != i && (M[j][x] == by || M[j][y] == bx)) ok = 0;
        if (!ok) continue;
        M[i][x] = by; M[i][y] = bx; build();
        int c2 = cost(W);
        if (c2 <= c || (double)(rnd() % 1000000) / 1e6 < exp((c - c2) / T)) { c = c2; if (c < best) { best = c; fprintf(stderr, "N=%d it %ld cost %d\n", N, it, c); } }
        else { M[i][x] = bx; M[i][y] = by; build(); }
        T *= 0.999997; if (T < 0.3) T = 0.3;
    }
    printf("N=%d final cost %d\n", N, c);
    if (c == 0) { /* pv format: k = N, m = 1: pa: A-vertex a -> B via M0, B-vertex b -> A via inverse of M1 (sigma_a^-1 = M1 on A) */
        int inv1[512], inv3[512]; for (int a = 0; a < N; a++) { inv1[M[1][a]] = a; inv3[M[3][a]] = a; }
        printf("CTRL %d 1", N);
        for (int a = 0; a < N; a++) printf(" %d", N + M[0][a]); for (int b = 0; b < N; b++) printf(" %d", inv1[b]);
        for (int a = 0; a < N; a++) printf(" %d", N + M[2][a]); for (int b = 0; b < N; b++) printf(" %d", inv3[b]);
        for (int v = 0; v < 4 * N; v++) printf(" 0"); printf("\n"); }
    return 0; }
