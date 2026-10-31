/* r2d/inv.c: search for cubic bipartite graphs (n = 2m, A = 0..m-1, B = m..2m-1) with diameter <= 7 that are
   invariant under an involution sigma which fixes f EDGES pointwise (i, m+i for i < f) and swaps the other vertices
   in pairs within each side. Moves: equivariant 4-edge 2-switches (e, f, sigma e, sigma f -> a-d, c-b, and sigma images).
   Cost = far = number of unordered pairs at distance > 7 (same definition as shared/score37).
   usage: inv n f seed seconds mode(sa|tabu) outprefix [T0 T1 | tenure K]
   writes outprefix_best.edges whenever a new best is found and outprefix_zero.edges if far = 0.
   build: gcc -O3 -march=native -o inv inv.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 256
#define WORDS 4
static int n, m, f;
static int sg[MAXN];
static int adj[MAXN][3];
static int deg[MAXN];
static unsigned char has[MAXN][MAXN];
static uint64_t rng_s[2];

static inline uint64_t rnd64(void) { uint64_t s1 = rng_s[0]; const uint64_t s0 = rng_s[1];
    rng_s[0] = s0; s1 ^= s1 << 23; rng_s[1] = s1 ^ s0 ^ (s1 >> 17) ^ (s0 >> 26); return rng_s[1] + s0; }
static inline int rndint(int k) { return (int)(rnd64() % (uint64_t)k); }
static inline double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static void add_edge(int x, int y) {
    int j; for (j = 0; j < 3 && adj[x][j] >= 0; j++) ; int k; for (k = 0; k < 3 && adj[y][k] >= 0; k++) ;
    if (j >= 3 || k >= 3) { fprintf(stderr, "add_edge overflow %d %d\n", x, y); exit(1); }
    adj[x][j] = y; adj[y][k] = x; deg[x]++; deg[y]++; has[x][y] = has[y][x] = 1;
}
static void del_edge(int x, int y) {
    int j, k; for (j = 0; j < 3; j++) if (adj[x][j] == y) break;
    for (k = 0; k < 3; k++) if (adj[y][k] == x) break;
    if (j >= 3 || k >= 3) { fprintf(stderr, "del_edge missing %d %d\n", x, y); exit(1); }
    adj[x][j] = -1; adj[y][k] = -1; deg[x]--; deg[y]--; has[x][y] = has[y][x] = 0;
}
static void init_sigma(void) {
    for (int i = 0; i < f; i++) { sg[i] = i; sg[m + i] = m + i; }
    for (int i = f; i < m; i += 2) { sg[i] = i + 1; sg[i + 1] = i; sg[m + i] = m + i + 1; sg[m + i + 1] = m + i; }
}

/* far: unordered pairs at distance > 7, bit-parallel BFS, 64 sources per batch */
static long long far_cost(void) {
    static uint64_t vis[MAXN], fr[MAXN], nx[MAXN];
    long long farord = 0;
    for (int s0 = 0; s0 < n; s0 += 64) {
        memset(vis, 0, sizeof(uint64_t) * n); memset(fr, 0, sizeof(uint64_t) * n);
        int ns = (n - s0 < 64) ? (n - s0) : 64; uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 1; lev <= 7; lev++) {
            int any = 0;
            for (int x = 0; x < n; x++) { uint64_t acc = 0;
                for (int j = 0; j < 3; j++) { int y = adj[x][j]; if (y >= 0) acc |= fr[y]; }
                acc &= ~vis[x]; nx[x] = acc; if (acc) any = 1; }
            for (int x = 0; x < n; x++) vis[x] |= nx[x];
            memcpy(fr, nx, sizeof(uint64_t) * n);
            if (!any) break;
        }
        for (int x = 0; x < n; x++) farord += __builtin_popcountll(full & ~vis[x]);
    }
    return farord / 2;
}

/* random greedy equivariant construction; returns 1 on success */
static int gen_init(void) {
    memset(has, 0, sizeof has); for (int v = 0; v < n; v++) { deg[v] = 0; adj[v][0] = adj[v][1] = adj[v][2] = -1; }
    for (int i = 0; i < f; i++) add_edge(i, m + i);
    static int ca[MAXN * MAXN], cb[MAXN * MAXN];
    for (;;) {
        int nc = 0;
        for (int x = 0; x < m; x++) { if (deg[x] >= 3) continue;
            for (int q = m; q < n; q++) { if (deg[q] >= 3 || has[x][q]) continue;
                int xf = sg[x] == x, qf = sg[q] == q;
                if (xf && qf) continue;
                if (!xf && !qf) { int sx = sg[x], sq = sg[q];
                    if (deg[sx] > 2 || deg[sq] > 2 || has[sx][sq] || sx == q) continue;
                    if (deg[x] > 2 || deg[q] > 2) continue;
                } else if (xf) { int sq = sg[q]; if (deg[x] > 1 || deg[sq] > 2 || has[x][sq] || deg[q] > 2) continue; }
                else { int sx = sg[x]; if (deg[q] > 1 || deg[sx] > 2 || has[sx][q] || deg[x] > 2) continue; }
                ca[nc] = x; cb[nc] = q; nc++; } }
        if (nc == 0) break;
        int t = rndint(nc); int x = ca[t], q = cb[t];
        if (sg[x] == x) { add_edge(x, q); add_edge(x, sg[q]); }
        else if (sg[q] == q) { add_edge(x, q); add_edge(sg[x], q); }
        else { add_edge(x, q); add_edge(sg[x], sg[q]); }
    }
    for (int v = 0; v < n; v++) if (deg[v] != 3) return 0;
    return 1;
}

/* a move: remove e=(a,b), f=(c,d), sg e, sg f; add (a,d),(c,b),(sg a, sg d),(sg c, sg b) */
typedef struct { int a, b, c, d; } Move;
static int is_fixed_edge(int a, int b) { return sg[a] == a && sg[b] == b; }
static int valid_move(const Move *M) {
    int a = M->a, b = M->b, c = M->c, d = M->d;
    int sa = sg[a], sb = sg[b], sc = sg[c], sd = sg[d];
    /* R = {ab, cd, sa sb, sc sd} must be 4 distinct edges: f not fixed, f != e, f != sigma e */
    if (is_fixed_edge(c, d)) return 0;
    if ((c == a && d == b) || (c == sa && d == sb)) return 0;
    if (is_fixed_edge(a, b)) return 0;
    /* added edges */
    int X[4][2] = {{a, d}, {c, b}, {sa, sd}, {sc, sb}};
    for (int i = 0; i < 4; i++) for (int j = i + 1; j < 4; j++)
        if ((X[i][0] == X[j][0] && X[i][1] == X[j][1])) return 0;
    for (int i = 0; i < 4; i++) {
        int x = X[i][0], y = X[i][1];
        /* present after removal? present unless it is one of R */
        int inR = 0;
        int R[4][2] = {{a, b}, {c, d}, {sa, sb}, {sc, sd}};
        for (int r = 0; r < 4; r++) if ((R[r][0] == x && R[r][1] == y) || (R[r][0] == y && R[r][1] == x)) inR = 1;
        if (!inR && has[x][y]) return 0;
    }
    return 1;
}
static void apply_move(const Move *M, int dir) { /* dir=+1 apply, -1 undo */
    int a = M->a, b = M->b, c = M->c, d = M->d;
    int sa = sg[a], sb = sg[b], sc = sg[c], sd = sg[d];
    int R[4][2] = {{a, b}, {c, d}, {sa, sb}, {sc, sd}};
    int X[4][2] = {{a, d}, {c, b}, {sa, sd}, {sc, sb}};
    if (dir > 0) { for (int i = 0; i < 4; i++) del_edge(R[i][0], R[i][1]); for (int i = 0; i < 4; i++) add_edge(X[i][0], X[i][1]); }
    else { for (int i = 0; i < 4; i++) del_edge(X[i][0], X[i][1]); for (int i = 0; i < 4; i++) add_edge(R[i][0], R[i][1]); }
}
static int rand_move(Move *M) {
    for (int tries = 0; tries < 50; tries++) {
        int a = rndint(m); int b = adj[a][rndint(3)]; if (b < 0) continue;
        int c = rndint(m); int d = adj[c][rndint(3)]; if (d < 0) continue;
        M->a = a; M->b = b; M->c = c; M->d = d;
        if (valid_move(M)) return 1;
    }
    return 0;
}
static void write_graph(const char *fn) {
    FILE *o = fopen(fn, "w"); if (!o) return; fprintf(o, "%d\n", n);
    for (int x = 0; x < n; x++) for (int j = 0; j < 3; j++) { int y = adj[x][j]; if (y > x) fprintf(o, "%d %d\n", x, y); }
    fclose(o);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: inv n f seed seconds sa|tabu outprefix [T0 T1 | tenure K]\n"); return 2; }
    n = atoi(argv[1]); m = n / 2; f = atoi(argv[2]); uint64_t seed = strtoull(argv[3], 0, 10);
    double secs = atof(argv[4]); const char *mode = argv[5]; const char *pre = argv[6];
    double T0 = argc > 7 ? atof(argv[7]) : 2.0, T1 = argc > 8 ? atof(argv[8]) : 0.2;
    int tenure = argc > 7 ? atoi(argv[7]) : 20; int K = argc > 8 ? atoi(argv[8]) : 40;
    if (n > MAXN || (!getenv("INIT_EDGES") && (m - f) % 2 != 0)) { fprintf(stderr, "bad n/f (need m-f even)\n"); return 2; }
    rng_s[0] = seed * 0x9E3779B97F4A7C15ULL + 12345; rng_s[1] = seed ^ 0xD1B54A32D192ED03ULL; for (int i = 0; i < 10; i++) rnd64();
    const char *ie = getenv("INIT_EDGES"), *is = getenv("INIT_SIGMA");
    if (ie && is) { /* start from a given graph and sigma (file of n integers) */
        FILE *fs = fopen(is, "r"); for (int v = 0; v < n; v++) if (fscanf(fs, "%d", &sg[v]) != 1) { fprintf(stderr, "bad sigma\n"); return 1; }
        fclose(fs); f = 0; for (int v = 0; v < m; v++) if (sg[v] == v) f++;
        FILE *fe = fopen(ie, "r"); int nn; if (fscanf(fe, "%d", &nn) != 1 || nn != n) { fprintf(stderr, "n mismatch\n"); return 1; }
        memset(has, 0, sizeof has); for (int v = 0; v < n; v++) { deg[v] = 0; adj[v][0] = adj[v][1] = adj[v][2] = -1; }
        int a, b; while (fscanf(fe, "%d %d", &a, &b) == 2) add_edge(a, b);
        fclose(fe);
        for (int v = 0; v < n; v++) if (deg[v] != 3) { fprintf(stderr, "init graph not cubic at %d\n", v); return 1; }
        for (int x = 0; x < n; x++) for (int j = 0; j < 3; j++) { int y = adj[x][j]; if (!has[sg[x]][sg[y]]) { fprintf(stderr, "init graph not sigma-invariant\n"); return 1; } }
        fprintf(stderr, "init from file: f=%d\n", f);
    } else {
        init_sigma();
        int tries = 0; while (!gen_init()) { tries++; if (tries > 200000) { fprintf(stderr, "init failed\n"); return 1; } }
        fprintf(stderr, "init ok after %d restarts\n", tries);
    }
    long long cur = far_cost(), best = cur; long long bestever = cur;
    static long tabu_until[MAXN][MAXN]; memset(tabu_until, 0, sizeof tabu_until);
    time_t t0 = time(NULL); long long it = 0; char fn[512];
    Move M, bestM; int ok;
    fprintf(stderr, "start far=%lld mode=%s\n", cur, mode);
    int strict = 0;
    while (1) {
        if ((it & 255) == 0 && difftime(time(NULL), t0) >= secs) break;
        it++;
        if (strcmp(mode, "sa") == 0) {
            double frac = difftime(time(NULL), t0) / secs; if (frac > 1) frac = 1;
            double T = T0 * pow(T1 / T0, frac);
            if (!rand_move(&M)) continue;
            apply_move(&M, +1); long long nw = far_cost();
            long long dlt = nw - cur;
            if (dlt <= 0 || rnd01() < exp(-dlt / T)) { cur = nw; }
            else apply_move(&M, -1);
        } else { /* tabu: best of K sampled moves */
            long long bestv = 1LL << 60; ok = 0;
            for (int k = 0; k < K; k++) {
                if (!rand_move(&M)) continue;
                int a = M.a, b = M.b, c = M.c, d = M.d, sa = sg[a], sb = sg[b], sc = sg[c], sd = sg[d];
                /* tabu: adding an edge that was removed recently */
                int X[4][2] = {{a, d}, {c, b}, {sa, sd}, {sc, sb}}; int istabu = 0;
                for (int i = 0; i < 4; i++) if (tabu_until[X[i][0]][X[i][1]] > it) istabu = 1;
                apply_move(&M, +1); long long nw = far_cost(); apply_move(&M, -1);
                if (istabu && nw >= bestever) continue;
                if (nw < bestv) { bestv = nw; bestM = M; ok = 1; }
            }
            if (!ok) continue;
            int a = bestM.a, b = bestM.b, c = bestM.c, d = bestM.d, sa = sg[a], sb = sg[b], sc = sg[c], sd = sg[d];
            int R[4][2] = {{a, b}, {c, d}, {sa, sb}, {sc, sd}};
            apply_move(&bestM, +1); cur = bestv;
            for (int i = 0; i < 4; i++) tabu_until[R[i][0]][R[i][1]] = tabu_until[R[i][1]][R[i][0]] = it + tenure + rndint(tenure + 1);
        }
        if (cur < bestever) {
            bestever = cur; snprintf(fn, sizeof fn, "%s_best.edges", pre); write_graph(fn);
            fprintf(stderr, "it=%lld t=%.0fs new best far=%lld\n", it, difftime(time(NULL), t0), bestever);
            if (bestever == 0) { snprintf(fn, sizeof fn, "%s_zero.edges", pre); write_graph(fn); break; }
        }
        if (it % 20000 == 0) fprintf(stderr, "it=%lld t=%.0fs cur=%lld best=%lld\n", it, difftime(time(NULL), t0), cur, bestever);
    }
    printf("n=%d f=%d seed=%llu mode=%s iters=%lld best_far=%lld\n", n, f, (unsigned long long)seed, mode, it, bestever);
    (void)best; (void)strict;
    return 0;
}
