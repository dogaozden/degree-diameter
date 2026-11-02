/* lns: exact large-neighbourhood search for bipartite (3,7) candidates (deep-37 round 1, card c3).
 * Repeatedly: pick a far pair (u,v) (distance > 7), take K edges with an endpoint within distance 2 of u (or v),
 * delete them, and enumerate ALL re-pairings of the freed side-0 half-edges with the freed side-1 half-edges
 * (K! permutations, skipping multi-edges). Keep a best re-pairing (ties broken at random, the identity re-pairing is
 * always among them, so far never increases). Score = far = pairs at distance > 7 (bit-parallel BFS).
 * usage: lns IN OUTPREFIX SECONDS K SEED
 * Writes OUTPREFIX_best.edges on every improvement. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
typedef uint64_t u64;
#define MAXN 192
int n, adj[MAXN][3], deg[MAXN], side[MAXN];
static u64 farm[MAXN][3];
static u64 rs = 88172645463325252ULL;
static u64 rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int m) { return (int)(rnd64() % (u64)m); }
static int far_eval(void) {
    static u64 M1[MAXN][3], M2[MAXN][3];
    u64 (*M)[3] = M1, (*NM)[3] = M2;
    for (int v = 0; v < n; v++) { M[v][0] = M[v][1] = M[v][2] = 0; M[v][v >> 6] |= 1ULL << (v & 63); }
    for (int k = 0; k < 7; k++) {
        for (int v = 0; v < n; v++) {
            u64 x0 = M[v][0], x1 = M[v][1], x2 = M[v][2];
            for (int i = 0; i < deg[v]; i++) { int u = adj[v][i]; x0 |= M[u][0]; x1 |= M[u][1]; x2 |= M[u][2]; }
            NM[v][0] = x0; NM[v][1] = x1; NM[v][2] = x2;
        }
        u64 (*t)[3] = M; M = NM; NM = t;
    }
    long far2 = 0;
    for (int v = 0; v < n; v++) {
        far2 += n - (__builtin_popcountll(M[v][0]) + __builtin_popcountll(M[v][1]) + __builtin_popcountll(M[v][2]));
        farm[v][0] = ~M[v][0]; farm[v][1] = ~M[v][1]; farm[v][2] = ~M[v][2];
    }
    return (int)(far2 / 2);
}
static void add_edge(int a, int b) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
static void rem_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) { adj[a][i] = adj[a][--deg[a]]; break; }
    for (int i = 0; i < deg[b]; i++) if (adj[b][i] == a) { adj[b][i] = adj[b][--deg[b]]; break; }
}
static int has_edge(int a, int b) { for (int i = 0; i < deg[a]; i++) if (adj[a][i] == b) return 1; return 0; }
static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", n);
    for (int v = 0; v < n; v++) for (int i = 0; i < deg[v]; i++) if (adj[v][i] > v) fprintf(f, "%d %d\n", v, adj[v][i]);
    fclose(f);
}
#define K_MAX 9
static int K;
static int A_[K_MAX], B_[K_MAX], perm[K_MAX], bestperm[K_MAX];
static int bestf, nties;
/* enumerate permutations by recursion over positions; adds edges (A_[i], B_[perm[i]]) */
static void rec(int i, int used) {
    if (i == K) {
        int f = far_eval();
        if (f < bestf) { bestf = f; nties = 1; memcpy(bestperm, perm, sizeof perm); }
        else if (f == bestf) { nties++; if (rndint(nties) == 0) memcpy(bestperm, perm, sizeof perm); }
        return;
    }
    for (int j = 0; j < K; j++) {
        if (used & (1 << j)) continue;
        int a = A_[i], b = B_[j];
        if (has_edge(a, b)) continue;
        add_edge(a, b);
        perm[i] = j;
        rec(i + 1, used | (1 << j));
        rem_edge(a, b);
    }
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: lns IN OUTPREFIX SECONDS K SEED\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    if (fscanf(f, "%d", &n) != 1) return 2;
    int a, b, E[400][2], m = 0;
    while (fscanf(f, "%d %d", &a, &b) == 2) { E[m][0] = a; E[m][1] = b; m++; }
    fclose(f);
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < m; i++) add_edge(E[i][0], E[i][1]);
    for (int v = 0; v < n; v++) side[v] = -1;
    { int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
      while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = adj[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } } }
    K = atoi(argv[4]); if (K > K_MAX) K = K_MAX;
    double secs = atof(argv[3]);
    rs ^= (u64)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    char fn[512]; snprintf(fn, sizeof fn, "%s_best.edges", argv[2]);
    int cur = far_eval(), best = cur;
    write_graph(fn);
    fprintf(stderr, "init far=%d\n", cur);
    struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
    long nb = 0;
    while (1) {
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
        if (el >= secs || best == 0) break;
        /* seed: random vertex with far partners */
        int u = -1;
        for (int tries = 0; tries < 1000; tries++) {
            int x = rndint(n);
            if (farm[x][0] | farm[x][1] | farm[x][2]) { u = x; break; }
        }
        if (u < 0) break;
        /* ball of radius 2 around u */
        int ball[MAXN], nball = 0; int inb[MAXN]; memset(inb, 0, sizeof inb);
        ball[nball++] = u; inb[u] = 1;
        for (int i = 0; i < deg[u]; i++) { int y = adj[u][i]; if (!inb[y]) { inb[y] = 1; ball[nball++] = y; } }
        for (int i = 0; i < nball; i++) { int y = ball[i]; for (int j = 0; j < deg[y]; j++) { int x = adj[y][j]; if (!inb[x]) { inb[x] = 1; ball[nball++] = x; } } }
        /* candidate edges: incident to ball, listed once */
        int ce[400][2], nc = 0;
        for (int i = 0; i < nball; i++) { int x = ball[i]; for (int j = 0; j < deg[x]; j++) { int y = adj[x][j]; if (x < y || !inb[y]) { if (x < y) { ce[nc][0] = x; ce[nc][1] = y; nc++; } else { ce[nc][0] = y; ce[nc][1] = x; nc++; } } } }
        /* dedupe */
        int nd = 0;
        for (int i = 0; i < nc; i++) { int dup = 0; for (int j = 0; j < nd; j++) if (ce[j][0] == ce[i][0] && ce[j][1] == ce[i][1]) { dup = 1; break; } if (!dup) { ce[nd][0] = ce[i][0]; ce[nd][1] = ce[i][1]; nd++; } }
        if (nd < K) continue;
        /* choose K distinct random candidate edges */
        int chosen[K_MAX], nch = 0;
        while (nch < K) { int r = rndint(nd); int dup = 0; for (int j = 0; j < nch; j++) if (chosen[j] == r) dup = 1; if (!dup) chosen[nch++] = r; }
        int ra[K_MAX], rb[K_MAX];
        for (int i = 0; i < K; i++) {
            int x = ce[chosen[i]][0], y = ce[chosen[i]][1];
            if (side[x] == 0) { ra[i] = x; rb[i] = y; } else { ra[i] = y; rb[i] = x; }
            rem_edge(x, y);
        }
        for (int i = 0; i < K; i++) { A_[i] = ra[i]; B_[i] = rb[i]; }
        bestf = 1 << 30; nties = 0;
        rec(0, 0);
        /* apply best re-pairing */
        for (int i = 0; i < K; i++) add_edge(A_[i], B_[bestperm[i]]);
        nb++;
        cur = far_eval();   /* refreshes farm too */
        if (cur != bestf) fprintf(stderr, "warning: eval mismatch %d vs %d\n", cur, bestf);
        if (cur < best) { best = cur; write_graph(fn); fprintf(stderr, "nb=%ld t=%.1f best=%d\n", nb, el, best); }
    }
    printf("LNS DONE best=%d cur=%d neighbourhoods=%ld file=%s\n", best, cur, nb, fn);
    return 0;
}
