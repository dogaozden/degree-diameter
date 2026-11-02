/* lns.c (deep-37 squad r1, card c6): large-neighbourhood search with EXACT completion for cubic bipartite graphs.
   Each step: pick a random far pair (u,v) (distance > 7); candidate edges = edges with an endpoint within distance
   RADIUS of u or v; remove a random set S of edges (size KMIN..KMAX, or unions of G-orbits of edges when the group
   G is nontrivial, so S and the completion stay G-invariant); then enumerate ALL completions T (edge sets on the
   deficient vertices making the graph cubic, bipartite, simple, and G-invariant) by a DFS with canonical branching
   (first deficient vertex v, partner w = min remaining partner; orbit of (v,w) added at once). Score every completion
   with the bit-parallel far count; move to a uniformly random completion of minimum far if that is <= current far
   (plateau walk; the identity completion T=S is always among them). MAXLEAF caps one region (capped = not exhausted).
   usage: lns IN.edges GROUP.txt OUTPREFIX SEED SECONDS KMIN KMAX RADIUS MAXLEAF
   GROUP.txt: "n order" then order lines of permutations (identity included). Writes OUTPREFIX_best.edges and
   OUTPREFIX_cur.edges. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 256
#define MAXE 1024
#define MAXG 64
#define MAXK 64

static int n, ng;
static int G[MAXG][MAXN];
static int col[MAXN];
static int ne, CA[MAXE], CB[MAXE];
static int BESTN, BESTA[MAXE], BESTB[MAXE];
static unsigned char adjm[MAXN][MAXN];
static int need[MAXN], lo[MAXN];
static unsigned char dist[MAXN][MAXN];
static int eidx[MAXN][MAXN];

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int m) { return (int)(rnd() % (uint64_t)m); }

static int fcount(const int *ea, const int *eb, int m) {
    static int adj[MAXN][MAXN]; static int deg[MAXN];
    static uint64_t R[MAXN], F[MAXN], NF[MAXN];
    memset(deg, 0, sizeof(int) * n);
    for (int i = 0; i < m; i++) { adj[ea[i]][deg[ea[i]]++] = eb[i]; adj[eb[i]][deg[eb[i]]++] = ea[i]; }
    long far = 0; int W = (n + 63) / 64;
    for (int blk = 0; blk < W; blk++) {
        for (int v = 0; v < n; v++) { R[v] = (v / 64 == blk) ? (1ULL << (v % 64)) : 0; F[v] = R[v]; }
        for (int step = 0; step < 7; step++) {
            for (int v = 0; v < n; v++) { uint64_t x = 0; for (int j = 0; j < deg[v]; j++) x |= F[adj[v][j]]; NF[v] = x & ~R[v]; }
            for (int v = 0; v < n; v++) { F[v] = NF[v]; R[v] |= NF[v]; }
        }
        int nsrc = (blk == W - 1 && n % 64) ? n % 64 : 64;
        for (int v = 0; v < n; v++) far += nsrc - __builtin_popcountll(R[v]);
    }
    return (int)(far / 2);
}

static void alldist(void) {
    static int adj[MAXN][4]; static int deg[MAXN]; static int q[MAXN];
    memset(deg, 0, sizeof(int) * n);
    for (int i = 0; i < ne; i++) { adj[CA[i]][deg[CA[i]]++] = CB[i]; adj[CB[i]][deg[CB[i]]++] = CA[i]; }
    for (int s = 0; s < n; s++) {
        for (int v = 0; v < n; v++) dist[s][v] = 99;
        int h = 0, t = 0; q[t++] = s; dist[s][s] = 0;
        while (h < t) { int u = q[h++]; for (int j = 0; j < deg[u]; j++) { int w = adj[u][j]; if (dist[s][w] == 99) { dist[s][w] = dist[s][u] + 1; q[t++] = w; } } }
    }
}

static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static int nr, RA[MAXE], RB[MAXE];
static int nt, TA[MAXE], TB[MAXE];
static int LA[MAXE], LB[MAXE];
static long leaves, nodes_, maxleaf;
static int capped, minfar, cntmin;
static int vcur, wcur;
static double regsecs = 5.0;
static int prunelvl = 2, bound_thr = 0, delta = 0; static long pruned_nodes = 0;

static void leaf(void) {
    leaves++;
    int m = 0;
    for (int i = 0; i < nr; i++) { LA[m] = RA[i]; LB[m] = RB[i]; m++; }
    for (int i = 0; i < nt; i++) { LA[m] = TA[i]; LB[m] = TB[i]; m++; }
    int f = fcount(LA, LB, m);
    if (f < minfar) minfar = f;
    if (f <= bound_thr) {
        cntmin++;
        if (rndint(cntmin) == 0) { BESTN = nt; for (int i = 0; i < nt; i++) { BESTA[i] = TA[i]; BESTB[i] = TB[i]; } }
    }
    if (leaves >= maxleaf) capped = 1;
}

static inline int partner_ok(int e, int p) {
    if (e == vcur) return p >= wcur;
    return p > lo[e];
}

/* lower bound for every completion below this node: the graph R + T + ALL admissible pairs among deficient
   vertices is a supergraph of every completion, so its far count is <= far of every completion. */
static int bound_far(void) {
    static int BA2[MAXE], BB2[MAXE];
    int m = 0;
    for (int i = 0; i < nr; i++) { BA2[m] = RA[i]; BB2[m] = RB[i]; m++; }
    for (int i = 0; i < nt; i++) { BA2[m] = TA[i]; BB2[m] = TB[i]; m++; }
    for (int x = 0; x < n; x++) if (need[x] > 0)
        for (int y = x + 1; y < n; y++) if (need[y] > 0 && col[x] != col[y] && !adjm[x][y]) {
            if (m >= MAXE) return 0;
            BA2[m] = x; BB2[m] = y; m++;
        }
    return fcount(BA2, BB2, m);
}

static double region_deadline = 1e18; static double now(void);
static void dfs(void) {
    if (capped) return;
    nodes_++;
    if ((nodes_ & 4095) == 0 && now() > region_deadline) { capped = 1; return; }
    int v = -1;
    for (int x = 0; x < n; x++) if (need[x] > 0) { v = x; break; }
    if (v < 0) { leaf(); return; }
    if (prunelvl >= 2 && bound_far() > bound_thr) { pruned_nodes++; return; }
    int cand[MAXN], nc = 0;
    for (int w = 0; w < n; w++)
        if (col[w] != col[v] && need[w] > 0 && !adjm[v][w] && w > lo[v]) cand[nc++] = w;
    if (nc < need[v]) return;
    for (int ci = 0; ci < nc && !capped; ci++) {
        int w = cand[ci];
        vcur = v; wcur = w;
        int px[MAXG], py[MAXG], np = 0;
        for (int g = 0; g < ng; g++) {
            int a = G[g][v], b = G[g][w];
            int x = a < b ? a : b, y = a < b ? b : a;
            int dup = 0;
            for (int j = 0; j < np; j++) if (px[j] == x && py[j] == y) { dup = 1; break; }
            if (!dup) { px[np] = x; py[np] = y; np++; }
        }
        int ok = 1;
        for (int j = 0; j < np && ok; j++) {
            int x = px[j], y = py[j];
            if (x == y || adjm[x][y] || !partner_ok(x, y) || !partner_ok(y, x)) ok = 0;
        }
        for (int j = 0; j < np && ok; j++) {
            for (int side = 0; side < 2 && ok; side++) {
                int z = side ? py[j] : px[j], c = 0;
                for (int i = 0; i < np; i++) if (px[i] == z || py[i] == z) c++;
                if (c > need[z]) ok = 0;
            }
        }
        if (!ok) continue;
        int oldlo = lo[v];
        lo[v] = w;
        for (int j = 0; j < np; j++) {
            int x = px[j], y = py[j];
            adjm[x][y] = adjm[y][x] = 1; need[x]--; need[y]--;
            TA[nt] = x; TB[nt] = y; nt++;
        }
        dfs();
        for (int j = 0; j < np; j++) {
            int x = px[j], y = py[j];
            adjm[x][y] = adjm[y][x] = 0; need[x]++; need[y]++; nt--;
        }
        lo[v] = oldlo;
    }
}


static void savegraph(const char *path, const int *A, const int *B, int m) {
    FILE *o = fopen(path, "w"); if (!o) { perror(path); exit(1); }
    fprintf(o, "%d\n", n);
    for (int i = 0; i < m; i++) fprintf(o, "%d %d\n", A[i] < B[i] ? A[i] : B[i], A[i] < B[i] ? B[i] : A[i]);
    fclose(o);
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: lns IN GROUP OUTPREFIX SEED SECONDS KMIN KMAX RADIUS MAXLEAF\n"); return 1; }
    const char *inf = argv[1], *gf = argv[2], *outp = argv[3];
    rs ^= strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[5]); int kmin = atoi(argv[6]), kmax = atoi(argv[7]), rad = atoi(argv[8]);
    maxleaf = atol(argv[9]);
    if (kmax > MAXK) kmax = MAXK;
    FILE *f = fopen(inf, "r"); if (!f) { perror(inf); return 1; }
    if (fscanf(f, "%d", &n) != 1) return 1;
    int a, b; ne = 0;
    while (fscanf(f, "%d %d", &a, &b) == 2) { CA[ne] = a; CB[ne] = b; ne++; }
    fclose(f);
    static int adjl[MAXN][4], degl[MAXN];
    for (int i = 0; i < ne; i++) { adjl[CA[i]][degl[CA[i]]++] = CB[i]; adjl[CB[i]][degl[CB[i]]++] = CA[i]; }
    for (int i = 0; i < n; i++) col[i] = -1;
    col[0] = 0; { int q[MAXN], h = 0, t = 0; q[t++] = 0;
      while (h < t) { int u = q[h++]; for (int j = 0; j < degl[u]; j++) { int w = adjl[u][j]; if (col[w] < 0) { col[w] = 1 - col[u]; q[t++] = w; } } } }
    f = fopen(gf, "r"); if (!f) { perror(gf); return 1; }
    if (fscanf(f, "%*d %d", &ng) != 1 || ng < 1 || ng > MAXG) { fprintf(stderr, "bad group\n"); return 1; }
    /* re-read n from group header for safety */
    rewind(f); { int nn; fscanf(f, "%d", &nn); if (nn != n) { fprintf(stderr, "group n mismatch\n"); return 1; } }
    fscanf(f, "%*d");
    for (int g = 0; g < ng; g++) for (int i = 0; i < n; i++) if (fscanf(f, "%d", &G[g][i]) != 1) { fprintf(stderr, "bad group line\n"); return 1; }
    fclose(f);
    /* check invariance of the start graph under G */
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) adjm[i][j] = 0;
    for (int i = 0; i < ne; i++) adjm[CA[i]][CB[i]] = adjm[CB[i]][CA[i]] = 1;
    for (int g = 0; g < ng; g++) for (int i = 0; i < ne; i++) if (!adjm[G[g][CA[i]]][G[g][CB[i]]]) { fprintf(stderr, "start graph not G-invariant\n"); return 1; }
    /* edge index map */
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) eidx[i][j] = -1;
    for (int i = 0; i < ne; i++) eidx[CA[i]][CB[i]] = eidx[CB[i]][CA[i]] = i;

    if (getenv("LNS_PRUNE")) prunelvl = atoi(getenv("LNS_PRUNE"));
    if (getenv("LNS_DELTA")) delta = atoi(getenv("LNS_DELTA"));
    if (getenv("LNS_REGSECS")) regsecs = atof(getenv("LNS_REGSECS"));
    int curfar = fcount(CA, CB, ne), bestfar = curfar;
    savegraph("/dev/null", CA, CB, 0);
    { char p[1024]; sprintf(p, "%s_best.edges", outp); savegraph(p, CA, CB, ne); }
    printf("start n=%d edges=%d group=%d far=%d seed=%s k=%d..%d radius=%d maxleaf=%ld\n", n, ne, ng, curfar, argv[4], kmin, kmax, rad, maxleaf);
    static long regs[MAXK + 1], exh[MAXK + 1], lsum[MAXK + 1], impr[MAXK + 1], eqm[MAXK + 1];
    static int bestk[MAXK + 1];
    for (int i = 0; i <= MAXK; i++) bestk[i] = 1 << 30;
    double t0 = now(); long iters = 0, totleaves = 0; int candidates_done = 0;
    static int cand[MAXE], inS[MAXE], S[MAXE], sh[MAXE];
    static int NCA[MAXE], NCB[MAXE];
    while (now() - t0 < secs && curfar > 0) {
        iters++;
        alldist();
        int u, v;
        long tries = 0;
        do { u = rndint(n); v = rndint(n); tries++; } while ((u == v || dist[u][v] <= 7) && tries < 2000000);
        if (u == v || dist[u][v] <= 7) break;
        int target = kmin + rndint(kmax - kmin + 1);
        int r = rad, nc = 0;
        for (;;) {
            nc = 0;
            for (int e = 0; e < ne; e++) {
                int x = CA[e], y = CB[e];
                int dx = dist[u][x] < dist[v][x] ? dist[u][x] : dist[v][x];
                int dy = dist[u][y] < dist[v][y] ? dist[u][y] : dist[v][y];
                if ((dx <= r || dy <= r)) cand[nc++] = e;
            }
            if (nc >= target || r >= 4) break;
            r++;
        }
        /* shuffle candidates */
        for (int i = 0; i < nc; i++) sh[i] = cand[i];
        for (int i = nc - 1; i > 0; i--) { int j = rndint(i + 1), t = sh[i]; sh[i] = sh[j]; sh[j] = t; }
        for (int e = 0; e < ne; e++) inS[e] = 0;
        int sz = 0;
        for (int i = 0; i < nc && sz < target; i++) {
            int e = sh[i];
            if (inS[e]) continue;
            int oe[MAXG], no = 0;
            for (int g = 0; g < ng; g++) {
                int x = G[g][CA[e]], y = G[g][CB[e]];
                int id = eidx[x][y], dup = 0;
                for (int j = 0; j < no; j++) if (oe[j] == id) dup = 1;
                if (!dup) oe[no++] = id;
            }
            int add = 0;
            for (int j = 0; j < no; j++) if (!inS[oe[j]]) add++;
            if (sz + add > kmax) continue;
            for (int j = 0; j < no; j++) if (!inS[oe[j]]) { inS[oe[j]] = 1; S[sz++] = oe[j]; }
        }
        if (sz == 0) continue;
        if (getenv("LNS_TEST")) { printf("REG k=%d", sz); for (int i = 0; i < sz; i++) printf(" %d-%d", CA[S[i]], CB[S[i]]); printf("\n"); }
        /* remaining graph */
        nr = 0;
        for (int x = 0; x < n; x++) need[x] = 3;
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) adjm[i][j] = 0;
        for (int e = 0; e < ne; e++) if (!inS[e]) {
            RA[nr] = CA[e]; RB[nr] = CB[e]; nr++;
            need[CA[e]]--; need[CB[e]]--; adjm[CA[e]][CB[e]] = adjm[CB[e]][CA[e]] = 1;
        }
        for (int x = 0; x < n; x++) lo[x] = -1;
        nt = 0; leaves = 0; nodes_ = 0; capped = 0; minfar = 1 << 30; cntmin = 0;
        bound_thr = curfar > bestfar + delta ? curfar : bestfar + delta;
        region_deadline = now() + regsecs;
        if (prunelvl >= 1 && bound_far() > bound_thr) { pruned_nodes++; leaves = 0; }
        else dfs();
        if (getenv("LNS_TEST")) { printf("LEAVES %ld MINFAR %d CAPPED %d BAND %ld\n", leaves, minfar, capped, cntmin); continue; }
        totleaves += leaves;
        regs[sz]++; if (!capped) exh[sz]++; lsum[sz] += leaves;
        if (minfar < curfar) impr[sz]++;
        if (minfar == curfar) eqm[sz]++;
        if (minfar < bestk[sz]) bestk[sz] = minfar;
        if (cntmin > 0) {
            /* accept: new graph = R + best completion */
            int m = 0;
            for (int i = 0; i < nr; i++) { NCA[m] = RA[i]; NCB[m] = RB[i]; m++; }
            for (int i = 0; i < BESTN; i++) { NCA[m] = BESTA[i]; NCB[m] = BESTB[i]; m++; }
            for (int i = 0; i < m; i++) { CA[i] = NCA[i]; CB[i] = NCB[i]; }
            ne = m;
            {
                int nf = fcount(CA, CB, ne);
                if (nf != bound_thr && 0) curfar = nf;
                curfar = nf;
            }
            for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) eidx[i][j] = -1;
            for (int i = 0; i < ne; i++) eidx[CA[i]][CB[i]] = eidx[CB[i]][CA[i]] = i;
            if (curfar < bestfar) {
                bestfar = curfar;
                char p[1024]; sprintf(p, "%s_best.edges", outp); savegraph(p, CA, CB, ne);
                printf("iter %ld t=%.0f NEW BEST far=%d (k=%d leaves=%ld)\n", iters, now() - t0, bestfar, sz, leaves); fflush(stdout);
            }
        }
    }
    {
        char p[1024]; sprintf(p, "%s_cur.edges", outp); savegraph(p, CA, CB, ne);
    }
    printf("END iters=%ld leaves=%ld pruned_nodes=%ld time=%.1f cur_far=%d best_far=%d\n", iters, totleaves, pruned_nodes, now() - t0, curfar, bestfar);
    for (int s = 0; s <= MAXK; s++) if (regs[s])
        printf("  k=%d regions=%ld exhausted=%ld avg_leaves=%.0f improved=%ld equal_moves=%ld best_far_region=%d\n",
               s, regs[s], exh[s], (double)lsum[s] / regs[s], impr[s], eqm[s], bestk[s]);
    return 0;
}
