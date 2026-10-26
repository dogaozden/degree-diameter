/* k11: repair a near-miss cubic bipartite lift by bipartite-preserving 2-switches (annealing, targeted).
   Move: edges (a,b),(c,d), a,c on side 0 and b,d on side 1, become (a,d),(c,b).
   Targeted move: x random on side 0 with a far partner y (side 1, dist > D found by BFS from x);
   a = end of an even random walk from x, d = end of an odd walk from y, c, b random neighbours.
   Objective F = sum over unordered pairs of min(dist - D, 4) for dist > D (exact up to K = D + 4), via bitset balls.
   usage: rewire2 IN.edges D SECONDS SEED T0 T1 OUT */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>

#define MAXN 1024
#define W 16
static int n, D, K, nw;
static int adj[MAXN][3];
static int col[MAXN];
static uint64_t rs;
static uint64_t B[2][MAXN][W];
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rint_(int m) { return (int)(rnd() % (uint64_t)m); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* F = sum over unordered pairs of sum_{k=D}^{K-1} [dist > k]; far = unordered pairs with dist > D */
static long evalF(long *far) {
    int cur = 0;
    memset(B[0], 0, sizeof(B[0]));
    for (int v = 0; v < n; v++) B[0][v][v >> 6] |= 1ULL << (v & 63);
    long F = 0;
    for (int k = 0; k <= K; k++) {
        long c = 0;
        for (int v = 0; v < n; v++) for (int w = 0; w < nw; w++) c += __builtin_popcountll(B[cur][v][w]);
        long cntk = (long)n * n - c;
        if (k == D) *far = cntk / 2;
        if (k >= D && k < K) F += cntk;
        if (k == K) break;
        int nx = 1 - cur;
        for (int v = 0; v < n; v++)
            for (int w = 0; w < nw; w++) {
                uint64_t x = B[cur][v][w];
                for (int j = 0; j < 3; j++) x |= B[cur][adj[v][j]][w];
                B[nx][v][w] = x;
            }
        cur = nx;
    }
    return F / 2;
}

static int has(int u, int v) { for (int k = 0; k < 3; k++) if (adj[u][k] == v) return 1; return 0; }
static int slot(int u, int v) { for (int k = 0; k < 3; k++) if (adj[u][k] == v) return k; return -1; }

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", n);
    for (int u = 0; u < n; u++) for (int k = 0; k < 3; k++) if (adj[u][k] > u) fprintf(f, "%d %d\n", u, adj[u][k]);
    fclose(f);
}

static int walk(int x, int L) { int c = x; for (int s = 0; s < L; s++) c = adj[c][rint_(3)]; return c; }

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: rewire2 IN.edges D SECONDS SEED T0 T1 OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d", &n) != 1) return 1;
    static int deg[MAXN];
    int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) { if (deg[u] >= 3 || deg[v] >= 3) return 1; adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
    fclose(f);
    for (int i = 0; i < n; i++) if (deg[i] != 3) { fprintf(stderr, "not cubic at %d\n", i); return 1; }
    nw = (n + 63) / 64; if (nw > W) { fprintf(stderr, "n too big\n"); return 1; }
    D = atoi(argv[2]); K = D + 4; double secs = atof(argv[3]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)atoll(argv[4]) * 0xD1B54A32D192ED03ULL); if (!rs) rs = 1;
    double T0 = atof(argv[5]), T1 = atof(argv[6]); const char *out = argv[7];
    for (int i = 0; i < n; i++) col[i] = -1;
    col[0] = 0; static int q[MAXN]; int h = 0, t = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int k = 0; k < 3; k++) { int y = adj[x][k]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); return 1; } } }
    long far; long F = evalF(&far);
    long far0 = far, bestFar = far, bestF = F, acc = 0, tried = 0;
    fprintf(stderr, "start n=%d F=%ld far=%ld\n", n, F, far);
    double t0 = now(), tend = t0 + secs;
    static int dist[MAXN], qq[MAXN], cand[MAXN];
    while (now() < tend && far > 0) {
        double T = T0 * pow(T1 / T0, (now() - t0) / secs);
        /* random side-0 vertex x with a far side-1 partner */
        int x = rint_(n); if (col[x] != 0) continue;
        int hh = 0, tt = 0;
        for (int i = 0; i < n; i++) dist[i] = -1;
        qq[tt++] = x; dist[x] = 0;
        while (hh < tt) { int a0 = qq[hh++]; for (int j = 0; j < 3; j++) { int b0 = adj[a0][j]; if (dist[b0] < 0) { dist[b0] = dist[a0] + 1; qq[tt++] = b0; } } }
        int nc = 0;
        for (int i = 0; i < n; i++) if (col[i] == 1 && (dist[i] < 0 || dist[i] > D)) cand[nc++] = i;
        if (nc == 0) continue;
        int y = cand[rint_(nc)];
        int a = walk(x, 2 * rint_(3));          /* side 0, dist <= 4 */
        int d = walk(y, 2 * rint_(3));      /* side 1, dist <= 4 */
        if (col[a] != 0 || col[d] != 1) continue;
        int b = adj[a][rint_(3)];
        int c = adj[d][rint_(3)];
        if (c == a || b == d) continue;
        if (has(a, d) || has(c, b)) continue;
        int sa = slot(a, b), sd = slot(d, c), sc = slot(c, d), sb = slot(b, a);
        adj[a][sa] = d; adj[d][sd] = a; adj[c][sc] = b; adj[b][sb] = c;
        long far2; long F2 = evalF(&far2);
        tried++;
        double dF = (double)(F2 - F);
        if (dF <= 0 || exp(-dF / T) > (rnd() % 1000000) / 1e6) {
            F = F2; far = far2; acc++;
            if (F < bestF || (F == bestF && far < bestFar)) { bestF = F; bestFar = far; }
            if (far == 0) { write_edges(out); fprintf(stderr, "FOUND valid after %ld tries\n", tried); break; }
        } else {
            adj[a][sa] = b; adj[d][sd] = c; adj[c][sc] = d; adj[b][sb] = a;
        }
        if (tried % 500 == 0) fprintf(stderr, "t=%.1f tried=%ld acc=%ld F=%ld far=%ld best=%ld bestfar=%ld T=%.3f\n", now() - t0, tried, acc, F, far, bestF, bestFar, T);
    }
    printf("RESULT n=%d start_far=%ld best_far=%ld best_F=%ld tried=%ld acc=%ld cur_far=%ld\n", n, far0, bestFar, bestF, tried, acc, far);
    return 0;
}
