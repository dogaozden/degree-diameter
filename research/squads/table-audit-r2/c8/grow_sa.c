/* grow_sa: grow a bipartite cubic graph to N vertices by bipartite gadget insertions,
   then repair the diameter (<= DIAM) by 2-switch annealing near unreached pairs.
   Gadget: pick edges a-b (a side0, b side1) and c-d (c side0, d side1); replace them with
   a-Y, c-Y, and add X adjacent to b, d, Y (X side0, Y side1). Stays cubic and bipartite.
   2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1); bipartition preserved.
   Usage: grow_sa IN OUT N seed seconds T0 Tend Rmax Dmin  (IN: "n" then "u v" lines, 0-based) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 1000
#define MAXM 1700
#define DIAM 10

static int n, M, N;
static int eu[MAXM], ev[MAXM];
static int adj[MAXN][3], deg[MAXN], col[MAXN];
static uint64_t visA[MAXN], frA[MAXN], nxA[MAXN];
static long unr[MAXN], unr_cur[MAXN];
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int k) { return (int)(rnd() % (unsigned long long)k); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void rebuild(void) {
    for (int v = 0; v < n; v++) deg[v] = 0;
    for (int i = 0; i < M; i++) { int a = eu[i], b = ev[i]; adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
}

static int isadj(int a, int b) { for (int k = 0; k < 3; k++) if (adj[a][k] == b) return 1; return 0; }

static long cost(void) {
    long total = 0;
    for (int v = 0; v < n; v++) unr[v] = 0;
    for (int s0 = 0; s0 < n; s0 += 64) {
        int ns = (n - s0 < 64) ? n - s0 : 64;
        uint64_t *F = frA, *G = nxA;
        for (int x = 0; x < n; x++) { visA[x] = 0; F[x] = 0; }
        for (int k = 0; k < ns; k++) { visA[s0 + k] |= 1ULL << k; F[s0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < DIAM; lev++) {
            int any = 0;
            for (int x = 0; x < n; x++) {
                uint64_t acc = F[adj[x][0]] | F[adj[x][1]] | F[adj[x][2]];
                acc &= ~visA[x];
                G[x] = acc; any |= (acc != 0);
            }
            if (!any) break;
            for (int x = 0; x < n; x++) visA[x] |= G[x];
            uint64_t *t = F; F = G; G = t;
        }
        for (int x = 0; x < n; x++) {
            int miss = ns - __builtin_popcountll(visA[x]);
            unr[x] += miss; total += miss;
        }
    }
    return total;
}

static void bfs(int s, int *dist) {
    static int q[MAXN];
    for (int v = 0; v < n; v++) dist[v] = -1;
    int h = 0, t = 0; q[t++] = s; dist[s] = 0;
    while (h < t) { int x = q[h++]; for (int k = 0; k < 3; k++) { int y = adj[x][k]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
}

static int inball[MAXN];
static void ball(int c, int R) {
    static int q[MAXN], d[MAXN];
    for (int v = 0; v < n; v++) inball[v] = 0;
    int h = 0, t = 0; q[t++] = c; inball[c] = 1; d[c] = 0;
    while (h < t) { int x = q[h++]; if (d[x] == R) continue;
        for (int k = 0; k < 3; k++) { int y = adj[x][k]; if (!inball[y]) { inball[y] = 1; d[y] = d[x] + 1; q[t++] = y; } } }
}

static void save(const char *path, int *U, int *V, int m, int nn) {
    FILE *f = fopen(path, "w");
    fprintf(f, "%d\n", nn);
    for (int i = 0; i < m; i++) fprintf(f, "%d %d\n", U[i], V[i]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage\n"); return 2; }
    const char *inp = argv[1], *outp = argv[2];
    N = atoi(argv[3]); rs ^= (unsigned long long)atoll(argv[4]) * 2654435761ULL + 1;
    double secs = atof(argv[5]), T0 = atof(argv[6]), Tend = atof(argv[7]);
    int Rmax = atoi(argv[8]), Dmin = atoi(argv[9]);

    FILE *f = fopen(inp, "r");
    if (!f || fscanf(f, "%d", &n) != 1) { fprintf(stderr, "bad input\n"); return 2; }
    static int RU[MAXM], RV[MAXM];
    M = 0; int u, v;
    while (fscanf(f, "%d %d", &u, &v) == 2) { RU[M] = u; RV[M] = v; M++; }
    fclose(f);
    int n0 = n;
    for (int i = 0; i < M; i++) { eu[i] = RU[i]; ev[i] = RV[i]; }
    rebuild();
    for (int v2 = 0; v2 < n; v2++) if (deg[v2] != 3) { fprintf(stderr, "not cubic at %d\n", v2); return 2; }
    /* bipartition */
    for (int v2 = 0; v2 < n; v2++) col[v2] = -1;
    { static int q[MAXN]; int h = 0, t = 0; col[0] = 0; q[t++] = 0;
      while (h < t) { int x = q[h++]; for (int k = 0; k < 3; k++) { int y = adj[x][k];
          if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); return 2; } } }
    }
    for (int i = 0; i < M; i++) { if (col[eu[i]] == 0) { /* keep */ } else { int t2 = eu[i]; eu[i] = ev[i]; ev[i] = t2; } }
    rebuild();

    /* insert gadgets */
    if (N < n0 || ((N - n0) & 1)) { fprintf(stderr, "bad N\n"); return 2; }
    int K = (N - n0) / 2;
    static int d1[MAXN], d2[MAXN];
    for (int g = 0; g < K; g++) {
        int ok = 0, i = 0, j = 0, a = 0, b = 0, c = 0, d = 0;
        for (int tries = 0; tries < 200000 && !ok; tries++) {
            i = rndi(M); j = rndi(M); if (i == j) continue;
            a = eu[i]; b = ev[i]; c = eu[j]; d = ev[j];
            if (a == c || b == d) continue;
            bfs(a, d1); if (d1[c] < Dmin) continue;
            bfs(b, d2); if (d2[d] < Dmin) continue;
            ok = 1;
        }
        if (!ok) { fprintf(stderr, "no gadget found\n"); return 2; }
        int Y = n, X = n + 1;
        col[Y] = 1; col[X] = 0;
        eu[i] = a; ev[i] = Y;
        eu[j] = c; ev[j] = Y;
        eu[M] = X; ev[M] = b; M++;
        eu[M] = X; ev[M] = d; M++;
        eu[M] = X; ev[M] = Y; M++;
        n += 2;
        rebuild();
    }
    for (int v2 = 0; v2 < n; v2++) if (deg[v2] != 3) { fprintf(stderr, "deg broke\n"); return 2; }

    long cur = cost();
    memcpy(unr_cur, unr, sizeof(long) * n);
    long best = cur;
    static int BU[MAXM], BV[MAXM];
    memcpy(BU, eu, sizeof(int) * M); memcpy(BV, ev, sizeof(int) * M);
    int bestM = M;
    printf("grown n=%d M=%d initial unreached(ordered)=%ld (pairs %ld)\n", n, M, cur, cur / 2);
    fflush(stdout);
    if (cur == 0) { save(outp, eu, ev, M, n); printf("already valid\n"); return 0; }

    clock_t t0 = clock();
    long it = 0, acc = 0;
    static int cand[MAXN], ce[MAXM];
    while (1) {
        it++;
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el > secs) break;
        if ((it % 5000) == 0) { printf("it=%ld t=%.0f cur=%ld best=%ld T=%.3f acc=%ld\n", it, el, cur, best, 0.0, acc); fflush(stdout); }
        double T = T0 * pow(Tend / T0, el / secs);
        int nc = 0;
        for (int x = 0; x < n; x++) if (unr_cur[x] > 0) cand[nc++] = x;
        if (nc == 0) break;
        int c = cand[rndi(nc)];
        int R = 1 + rndi(Rmax);
        ball(c, R);
        int nce = 0;
        for (int e = 0; e < M; e++) if (inball[eu[e]] || inball[ev[e]]) ce[nce++] = e;
        if (nce < 2) continue;
        int i = ce[rndi(nce)];
        int j = (rnd() % 10 == 0) ? rndi(M) : ce[rndi(nce)];
        if (i == j) continue;
        int a1 = eu[i], b1 = ev[i], a2 = eu[j], b2 = ev[j];
        if (a1 == a2 || b1 == b2) continue;
        if (isadj(a1, b2) || isadj(a2, b1)) continue;
        eu[i] = a1; ev[i] = b2; eu[j] = a2; ev[j] = b1;
        rebuild();
        long nw = cost();
        long delta = nw - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = nw; memcpy(unr_cur, unr, sizeof(long) * n); acc++;
            if (cur < best) { best = cur; bestM = M; memcpy(BU, eu, sizeof(int) * M); memcpy(BV, ev, sizeof(int) * M);
                printf("  new best %ld at it=%ld t=%.0f\n", best, it, el); fflush(stdout);
                if (best == 0) break; }
        } else {
            eu[i] = a1; ev[i] = b1; eu[j] = a2; ev[j] = b2;
            rebuild();
        }
    }
    save(outp, BU, BV, bestM, n);
    printf("done n=%d best_ordered=%ld best_pairs=%ld iters=%ld acc=%ld -> %s\n", n, best, best / 2, it, acc, outp);
    return 0;
}
