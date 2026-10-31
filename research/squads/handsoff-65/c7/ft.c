/* c7 sa.c: simulated annealing over 2-switches of a bipartite 6-regular graph (edge swaps keep degrees and bipartiteness).
 * Cost = number of unordered vertex pairs at distance > 5 (bit-parallel BFS, full recomputation per move).
 * env: INFILE (edge list: n then "u v" lines, 0-based; sides found by BFS), RANDN (random 6-regular bipartite on RANDN
 *      vertices instead), GROW (number of vertex pairs added to INFILE by 5-edge insertion, see below), SEED (1),
 *      ITERS (moves per round, 200000), T0 (2.0), T1 (0.05), ROUNDS (1), SECS (600), OUT (edge list output file).
 * GROW: a new pair (u in A, v in B) is inserted by deleting 5 edges (a_i b_i) with distinct a_i, b_i and adding
 *       u b_i (i=1..5), v a_i (i=1..5), and uv. Degrees stay 6.
 * Prints "SA round r best b cur c iters i secs s" lines; writes OUT when best improves and at the end. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1024
#define W 16
#define MAXE (3 * MAXN)
typedef uint64_t u64;

static int n, nw, ne;
static int side[MAXN];
static int adj[MAXN][6], deg[MAXN];
static int EA[MAXE], EB[MAXE];
static u64 LA[MAXN][W], LB[MAXN][W], L4[MAXN][W];
static u64 (*cur)[W] = LA, (*nxt)[W] = LB;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int has_edge(int a, int b) {
    for (int k = 0; k < deg[a]; k++) if (adj[a][k] == b) return 1;
    return 0;
}
static void rep(int v, int old, int nw_) {
    for (int k = 0; k < deg[v]; k++) if (adj[v][k] == old) { adj[v][k] = nw_; return; }
    fprintf(stderr, "rep failed\n"); exit(1);
}
/* swap B-endpoints of edges i and j (2-switch); self-inverse */
static int swap_edges(int i, int j) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
    rep(a1, b1, b2); rep(b1, a1, a2); rep(a2, b2, b1); rep(b2, a2, a1);
    EB[i] = b2; EB[j] = b1;
    return 0;
}
static int valid_switch(int i, int j) {
    int a1 = EA[i], b1 = EB[i], a2 = EA[j], b2 = EB[j];
    if (a1 == a2 || b1 == b2) return 0;
    if (has_edge(a1, b2) || has_edge(a2, b1)) return 0;
    return 1;
}
static long cost_full(void) {
    for (int v = 0; v < n; v++) {
        memset(cur[v], 0, nw * 8);
        cur[v][v >> 6] |= 1ULL << (v & 63);
    }
    for (int k = 0; k < 5; k++) {
        for (int v = 0; v < n; v++) {
            u64 *d = nxt[v];
            memcpy(d, cur[v], nw * 8);
            for (int t = 0; t < deg[v]; t++) {
                u64 *s = cur[adj[v][t]];
                for (int w = 0; w < nw; w++) d[w] |= s[w];
            }
        }
        if (k == 3) memcpy(L4, nxt, sizeof(L4[0][0]) * W * n);
        u64 (*tmp)[W] = cur; cur = nxt; nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        for (int w = 0; w < nw; w++) c += __builtin_popcountll(cur[v][w]);
        bad += n - c;
    }
    return bad / 2;
}
static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", n);
    for (int i = 0; i < ne; i++) fprintf(f, "%d %d\n", EA[i], EB[i]);
    fclose(f);
}
static void build_from_edges(int m, int *U, int *V) {
    /* sides by BFS */
    static int col[MAXN]; for (int v = 0; v < n; v++) col[v] = -1;
    static int q[MAXN];
    static int g[MAXN][6]; /* unused */
    (void)g;
    int *dg = calloc(n, sizeof(int));
    for (int i = 0; i < m; i++) { dg[U[i]]++; dg[V[i]]++; }
    /* adjacency for BFS */
    int *st = calloc(n + 1, sizeof(int));
    for (int v = 0; v < n; v++) st[v + 1] = st[v] + dg[v];
    int *fill = calloc(n, sizeof(int)); int *al = malloc(sizeof(int) * 2 * m + 4);
    for (int i = 0; i < m; i++) {
        al[st[U[i]] + fill[U[i]]++] = V[i];
        al[st[V[i]] + fill[V[i]]++] = U[i];
    }
    int h = 0, t = 0;
    for (int s = 0; s < n; s++) if (col[s] < 0) {
        col[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int k = st[x]; k < st[x + 1]; k++) { int y = al[k]; if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) { fprintf(stderr, "not bipartite\n"); exit(1); } } }
    }
    for (int v = 0; v < n; v++) side[v] = col[v];
    ne = 0;
    for (int i = 0; i < m; i++) {
        int a = U[i], b = V[i];
        if (side[a] == 1) { int tmp = a; a = b; b = tmp; }
        EA[ne] = a; EB[ne] = b; ne++;
    }
    memset(deg, 0, sizeof deg);
    for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
    free(dg); free(st); free(fill); free(al);
}
static void simplify_random(void) {
    /* random graph with multi-edges: repair by random valid switches (not used when simple) */
    (void)0;
}

static int tabu[MAXN][MAXN];
static int find_edge(int a, int b) { for (int i = 0; i < ne; i++) if ((EA[i] == a && EB[i] == b) || (EA[i] == b && EB[i] == a)) return i; return -1; }
static inline int in_ball4(int z, int y) { return (L4[y][z >> 6] >> (z & 63)) & 1ULL; }
static inline int in_ball5(int z, int y) { return (cur[y][z >> 6] >> (z & 63)) & 1ULL; }
static inline int is_adj(int a, int b) { return has_edge(a, b); }

int main(void) {
    const char *in = getenv("INFILE"), *out = getenv("OUT") ? getenv("OUT") : "c7_ft_best.edges";
    int randn = getenv("RANDN") ? atoi(getenv("RANDN")) : 0;
    int grow = getenv("GROW") ? atoi(getenv("GROW")) : 0;
    int K = getenv("K") ? atoi(getenv("K")) : 100;
    int TT = getenv("TT") ? atoi(getenv("TT")) : 15;
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 300;
    long maxsteps = getenv("STEPS") ? atol(getenv("STEPS")) : 1L << 40;
    int SEEDV = getenv("SEED") ? atoi(getenv("SEED")) : 1;
    rs ^= (uint64_t)SEEDV * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    if (in) {
        FILE *f = fopen(in, "r"); if (!f) { fprintf(stderr, "no input\n"); return 2; }
        int m0; if (fscanf(f, "%d", &n) != 1) return 2;
        static int U[MAXE], V[MAXE]; m0 = 0;
        int a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { U[m0] = a; V[m0] = b; m0++; }
        fclose(f);
        build_from_edges(m0, U, V);
        for (int g = 0; g < grow; g++) {
            int u = n, v = n + 1; n += 2;
            int chosen[5], cnt = 0, tries = 0, ea[5], eb[5];
            while (cnt < 5 && tries < 1000000) {
                tries++;
                int i = rnd() % ne, ok = 1;
                for (int k = 0; k < cnt; k++) if (chosen[k] == i || ea[k] == EA[i] || eb[k] == EB[i]) ok = 0;
                if (ok) { chosen[cnt] = i; ea[cnt] = EA[i]; eb[cnt] = EB[i]; cnt++; }
            }
            for (int k = 0; k < 5; k++) for (int l = k + 1; l < 5; l++) if (chosen[l] > chosen[k]) { int t = chosen[k]; chosen[k] = chosen[l]; chosen[l] = t; }
            for (int k = 0; k < 5; k++) { int i = chosen[k]; EA[i] = EA[ne - 1]; EB[i] = EB[ne - 1]; ne--; }
            side[u] = 0; side[v] = 1;
            for (int k = 0; k < 5; k++) { EA[ne] = u; EB[ne] = eb[k]; ne++; }
            for (int k = 0; k < 5; k++) { EA[ne] = ea[k]; EB[ne] = v; ne++; }
            EA[ne] = u; EB[ne] = v; ne++;
            memset(deg, 0, sizeof deg);
            for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
        }
    } else if (randn) {
        n = randn; int h = n / 2; ne = 0;
        for (int r = 0; r < 6; r++) {
            int *p = malloc(sizeof(int) * h); for (int i = 0; i < h; i++) p[i] = i;
            for (int i = h - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = p[i]; p[i] = p[j]; p[j] = t; }
            for (int i = 0; i < h; i++) { EA[ne] = i; EB[ne] = h + p[i]; ne++; }
            free(p);
        }
        for (int v = 0; v < n; v++) side[v] = v >= h;
        memset(deg, 0, sizeof deg);
        for (int i = 0; i < ne; i++) { adj[EA[i]][deg[EA[i]]++] = EB[i]; adj[EB[i]][deg[EB[i]]++] = EA[i]; }
        for (long it = 0; it < 10000000; it++) {
            int bad = 0;
            for (int i = 0; i < ne && !bad; i++) { int c = 0; for (int k = 0; k < deg[EA[i]]; k++) if (adj[EA[i]][k] == EB[i]) c++; if (c > 1) bad = 1; }
            if (!bad) break;
            int i = rnd() % ne, j = rnd() % ne;
            if (valid_switch(i, j)) swap_edges(i, j);
        }
    } else { fprintf(stderr, "need INFILE or RANDN\n"); return 2; }
    for (int v = 0; v < n; v++) if (deg[v] != 6) { fprintf(stderr, "degree %d\n", v); return 2; }
    nw = (n + 63) >> 6;
    long curc = cost_full(), best = curc;
    fprintf(stderr, "start n=%d cost=%ld\n", n, curc);
    static int bestEA[MAXE], bestEB[MAXE];
    memcpy(bestEA, EA, sizeof(int) * ne); memcpy(bestEB, EB, sizeof(int) * ne);
    double t0 = now();
    long step;
    static int cand[4][MAXE];
    for (step = 1; step <= maxsteps && best > 0; step++) {
        /* levels of current state: cur = level 5, L4 = level 4 (recompute if last eval was a candidate) */
        curc = cost_full();
        /* pick a far pair (x,y) */
        int x = -1, y = -1;
        for (int tries = 0; tries < 100000; tries++) {
            int xx = rnd() % n;
            int far = 0; for (int w = 0; w < nw; w++) far += __builtin_popcountll(~cur[xx][w] & (w == nw - 1 && (n & 63) ? ((1ULL << (n & 63)) - 1) : ~0ULL));
            if (far > 1 || (far == 1 && !in_ball5(xx, xx))) { /* far>=1 counts xx itself? xx is in its own ball so far excludes it */ }
            if (far > 0) {
                int cnt = 0;
                for (int yy = 0; yy < n; yy++) if (!in_ball5(yy, xx)) { cnt++; if (rnd() % cnt == 0) y = yy; }
                x = xx; break;
            }
        }
        if (x < 0) break;
        if (rnd() & 1) { int t = x; x = y; y = t; }   /* move the endpoint x: add an edge from x into the ball of y */
        /* generate K candidates: (x,w) and (p,z) -> (x,z),(p,w) with z in ball4(y), opposite side of x */
        long bestc = -1; int bi = -1, bestAllowed = 0;
        int bw[1], bp[1];
        static int CX[MAXE], CW[MAXE], CP[MAXE], CZ[MAXE];
        int nc = 0;
        int ntry = 0;
        while (nc < K && ntry < 20 * K) {
            ntry++;
            int w = adj[x][rnd() % 6];
            int z = rnd() % n;
            if (side[z] == side[x] || z == w || !in_ball4(z, y) || is_adj(x, z)) continue;
            int p = adj[z][rnd() % 6];
            if (p == x || is_adj(p, w)) continue;
            CX[nc] = x; CW[nc] = w; CP[nc] = p; CZ[nc] = z; nc++;
        }
        long bestv = 1L << 60; int chosen = -1; int nties = 0;
        for (int c = 0; c < nc; c++) {
            int xx = CX[c], ww = CW[c], pp = CP[c], zz = CZ[c];
            int admiss = !(tabu[xx][zz] > step) && !(tabu[pp][ww] > step);
            int i = find_edge(xx, ww), j = find_edge(pp, zz);
            if (i < 0 || j < 0) continue;
            if (!valid_switch(i, j)) continue;
            swap_edges(i, j);
            long cc = cost_full();
            swap_edges(i, j);
            if (!admiss && cc >= best) continue;
            if (cc < bestv) { bestv = cc; chosen = c; nties = 1; }
            else if (cc == bestv) { nties++; if (rnd() % nties == 0) chosen = c; }
        }
        if (chosen < 0) { if (step % 100 == 0) fprintf(stderr, "nochoice step %ld nc %d\n", step, nc); if (now() - t0 > secs) break; continue; }
        {
            int xx = CX[chosen], ww = CW[chosen], pp = CP[chosen], zz = CZ[chosen];
            int i = find_edge(xx, ww), j = find_edge(pp, zz);
            swap_edges(i, j);
            int tt = TT + (int)(rnd() % (TT + 1));
            tabu[xx][ww] = tabu[ww][xx] = step + tt;
            tabu[pp][zz] = tabu[zz][pp] = step + tt;
            curc = bestv;
            if (curc < best) {
                best = curc;
                memcpy(bestEA, EA, sizeof(int) * ne); memcpy(bestEB, EB, sizeof(int) * ne);
                printf("BEST %ld step %ld secs %.1f\n", best, step, now() - t0); fflush(stdout);
                write_edges(out);
            }
        }
        if (step % 2000 == 0) { printf("STEP %ld cur %ld best %ld secs %.1f\n", step, curc, best, now() - t0); fflush(stdout); }
        if (now() - t0 > secs) break;
    }
    memcpy(EA, bestEA, sizeof(int) * ne); memcpy(EB, bestEB, sizeof(int) * ne);
    write_edges(out);
    printf("RESULT best %ld n %d steps %ld out %s\n", best, n, step, out);
    return 0;
}
