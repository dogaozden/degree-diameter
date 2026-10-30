/* cycgen.c: cyclic (Z_n) voltage lifts of any small bipartite base multigraph, D = 5 (or env D):
 * random sampling of all free voltages but two, and exact enumeration of the last two (n^2 candidates per sample)
 * with 128-bit rotations of partial-sum bitsets.
 *
 * Abelian lift: a walk's product is c . v (c = signed edge-use counts). For each condition (source s, target t;
 * s on side 0 with every t, s on side 1 with t on side 1, and only s <= t for same-side pairs, since the reach of
 * t from s is minus the reach of s from t) the distinct coefficient vectors of non-backtracking walks of the right
 * parity and length (<= D from side 0, <= D-1 within side 1) are precomputed. Diameter <= D iff every condition's
 * sums cover Z_n. A BFS spanning tree has voltage 0; the first free edge is fixed to 1 (unit normalisation; with n
 * composite this loses solutions whose first free voltage is a non-unit). Parallel edges must get distinct voltages.
 *
 * usage: cycgen BASE n SAMPLES SEED   (SAMPLES = 0: run until killed; prints SOL lines, a vl solution each)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <math.h>

typedef unsigned __int128 u128;
#define MAXB 32
#define MAXE 96
#define MAXC 600
#define MAXV 4096
static int b, E, n, D = 5;
static int side[MAXB], eu[MAXE], ew[MAXE], volt[MAXE], isfree[MAXE];
static int deg[MAXB], adjv[MAXB][MAXE], adje[MAXB][MAXE], adjs[MAXB][MAXE];
static int ncond, cs[MAXC], ct[MAXC], nvec[MAXC];
static signed char *vec[MAXC];
static u128 MASK;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline u128 rot(u128 x, long k) { k %= n; if (k < 0) k += n; if (!k) return x; return ((x << k) | (x >> (n - k))) & MASK; }

static int cur_s, cur_t, cur_L, ntmp; static signed char cvec[MAXE]; static signed char (*tmpv)[MAXE];
static void dfs(int v, int laste, int len) {
    if (v == cur_t && ((len & 1) == (side[cur_s] != side[cur_t]))) {
        int k; for (k = 0; k < ntmp; k++) if (!memcmp(tmpv[k], cvec, E)) break;
        if (k == ntmp) { if (ntmp >= MAXV) { fprintf(stderr, "MAXV\n"); exit(1); } memcpy(tmpv[ntmp++], cvec, E); }
    }
    if (len == cur_L) return;
    for (int i = 0; i < deg[v]; i++) { int e = adje[v][i]; if (e == laste) continue;
        cvec[e] += adjs[v][i]; dfs(adjv[v][i], e, len + 1); cvec[e] -= adjs[v][i]; }
}

static int eA, eB;
static u128 PL[MAXC][64]; static int LA[MAXC][64], LB[MAXC][64], nl[MAXC], built[MAXC], qx[MAXC];
static u128 Q[MAXC][9];
static void build(int c) {
    u128 P[9][9]; memset(P, 0, sizeof P);
    signed char *V = vec[c];
    for (int k = 0; k < nvec[c]; k++, V += E) { long s = 0;
        for (int e = 0; e < E; e++) if (V[e] && e != eA && e != eB) s += V[e] * volt[e];
        s %= n; if (s < 0) s += n;
        P[V[eA] + 4][V[eB] + 4] |= ((u128)1) << s; }
    nl[c] = 0;
    for (int i = 0; i < 9; i++) for (int j = 0; j < 9; j++) if (P[i][j]) {
        PL[c][nl[c]] = P[i][j]; LA[c][nl[c]] = i - 4; LB[c][nl[c]] = j - 4; nl[c]++; }
    built[c] = 1; qx[c] = -1;
}
static int par_ok(int e) {   /* parallel edges distinct */
    for (int f = 0; f < E; f++) if (f != e && eu[f] == eu[e] && ew[f] == ew[e] && volt[f] == volt[e]) return 0;
    return 1;
}


/* hybrid: cost of the current outer assignment = min over inner (x, y) of the total number of uncovered sheets */
static long inner_min(int *bx, int *by, long limit) {
    long best = 1L << 60;
    for (int c = 0; c < ncond; c++) built[c] = 0;
    for (int c = 0; c < ncond; c++) build(c);
    for (int x = 0; x < n; x++) {
        volt[eA] = x; volt[eB] = -1; if (!par_ok(eA)) continue;
        for (int c = 0; c < ncond; c++) { memset(Q[c], 0, sizeof Q[c]);
            for (int k = 0; k < nl[c]; k++) Q[c][LB[c][k] + 4] |= rot(PL[c][k], (long)LA[c][k] * x); }
        for (int y = 0; y < n; y++) {
            volt[eB] = y; if (!par_ok(eB)) continue;
            long cost = 0;
            for (int c = 0; c < ncond && cost < best; c++) {
                u128 U = Q[c][4];
                for (int j = 0; j < 9; j++) if (j != 4 && Q[c][j]) U |= rot(Q[c][j], (long)(j - 4) * y);
                cost += n - (__builtin_popcountll((uint64_t)U) + __builtin_popcountll((uint64_t)(U >> 64)));
            }
            if (cost < best) { best = cost; *bx = x; *by = y; }
        }
    }
    (void)limit;
    return best;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: cycgen BASE n SAMPLES SEED\n"); return 2; }
    if (getenv("D")) D = atoi(getenv("D"));
    n = atoi(argv[2]); long SAMPLES = atol(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 10; i++) rnd();
    if (n > 127 || n < 2) return 2;
    MASK = (((u128)1) << n) - 1;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &b, &E) != 2 || b > MAXB || E > MAXE) return 2;
    for (int v = 0; v < b; v++) if (fscanf(f, "%d", &side[v]) != 1) return 2;
    for (int e = 0; e < E; e++) { int x, y; if (fscanf(f, "%d %d", &x, &y) != 2) return 2;
        int c; while ((c = fgetc(f)) != '\n' && c != EOF) {}
        if (side[x] == 1) { int t = x; x = y; y = t; } eu[e] = x; ew[e] = y; }
    fclose(f);
    for (int e = 0; e < E; e++) { int u = eu[e], w = ew[e];
        adjv[u][deg[u]] = w; adje[u][deg[u]] = e; adjs[u][deg[u]] = 1; deg[u]++;
        adjv[w][deg[w]] = u; adje[w][deg[w]] = e; adjs[w][deg[w]] = -1; deg[w]++; }
    /* BFS tree */
    for (int e = 0; e < E; e++) isfree[e] = 1;
    { int seen[MAXB] = {0}, q[MAXB], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
      while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) if (!seen[adjv[x][i]]) {
          seen[adjv[x][i]] = 1; q[t++] = adjv[x][i]; isfree[adje[x][i]] = 0; volt[adje[x][i]] = 0; } }
      if (t != b) { fprintf(stderr, "disconnected\n"); return 2; } }
    int fr[MAXE], nf = 0; for (int e = 0; e < E; e++) if (isfree[e]) fr[nf++] = e;
    /* fix the first free edge parallel to a tree edge?  just the first free edge */
    int e1 = fr[0]; volt[e1] = 1; isfree[e1] = 0;
    nf = 0; for (int e = 0; e < E; e++) if (isfree[e]) fr[nf++] = e;
    /* conditions */
    tmpv = malloc(sizeof(signed char[MAXE]) * MAXV);
    ncond = 0;
    for (int s = 0; s < b; s++) for (int t = 0; t < b; t++) {
        if (side[s] == 1 && side[t] == 0) continue;
        if (side[s] == side[t] && t < s) continue;
        cur_s = s; cur_t = t; cur_L = side[s] == 0 ? D : D - 1; ntmp = 0; memset(cvec, 0, sizeof cvec);
        dfs(s, -1, 0);
        cs[ncond] = s; ct[ncond] = t; nvec[ncond] = ntmp;
        vec[ncond] = malloc((size_t)ntmp * E); for (int k = 0; k < ntmp; k++) memcpy(vec[ncond] + (size_t)k * E, tmpv[k], E);
        ncond++;
    }
    /* order: fewest vectors first */
    for (int i = 0; i < ncond; i++) for (int j = i + 1; j < ncond; j++) if (nvec[j] < nvec[i]) {
        int t; signed char *p;
        t = nvec[i]; nvec[i] = nvec[j]; nvec[j] = t; t = cs[i]; cs[i] = cs[j]; cs[j] = t; t = ct[i]; ct[i] = ct[j]; ct[j] = t;
        p = vec[i]; vec[i] = vec[j]; vec[j] = p; }
    /* inner edges: the two free edges used most in the tightest condition */
    int use[MAXE] = {0};
    for (int k = 0; k < nvec[0]; k++) for (int e = 0; e < E; e++) if (vec[0][(size_t)k * E + e]) use[e]++;
    eA = -1; eB = -1;
    for (int i = 0; i < nf; i++) { int e = fr[i]; if (eA < 0 || use[e] > use[eA]) eA = e; }
    for (int i = 0; i < nf; i++) { int e = fr[i]; if (e != eA && (eB < 0 || use[e] > use[eB])) eB = e; }
    fprintf(stderr, "b %d E %d n %d free %d conditions %d (min vectors %d, max %d); inner edges %d %d\n",
            b, E, n, nf, ncond, nvec[0], nvec[ncond - 1], eA, eB);
    for (int c = 0; c < ncond; c++) for (int k = 0; k < nvec[c]; k++) for (int e = 0; e < E; e++) {
        int x = vec[c][(size_t)k * E + e]; if ((e == eA || e == eB) && (x > 4 || x < -4)) { fprintf(stderr, "coef\n"); return 2; } }
    if (getenv("SA")) {
        double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60, T0 = getenv("T0") ? atof(getenv("T0")) : 2,
               T1 = getenv("T1") ? atof(getenv("T1")) : 0.2; long ITERS = getenv("ITERS") ? atol(getenv("ITERS")) : 20000;
        int outer[MAXE], no = 0; for (int i = 0; i < nf; i++) if (fr[i] != eA && fr[i] != eB) outer[no++] = fr[i];
        clock_t ts = clock(); long gbest = 1L << 60; int run = 0;
        while ((double)(clock() - ts) / CLOCKS_PER_SEC < SECS && gbest > 0) {
            run++;
            for (int i = 0; i < no; i++) { do volt[outer[i]] = rnd() % n; while (!par_ok(outer[i])); }
            int bx, by; long cur = inner_min(&bx, &by, 0);
            for (long it = 0; it < ITERS && gbest > 0; it++) {
                if ((it & 15) == 0 && (double)(clock() - ts) / CLOCKS_PER_SEC > SECS) break;
                double T = T0 * pow(T1 / T0, (double)it / ITERS);
                int e = outer[rnd() % no], old = volt[e];
                volt[e] = rnd() % n; if (volt[e] == old || !par_ok(e)) { volt[e] = old; continue; }
                int x2, y2; long c = inner_min(&x2, &y2, 0);
                if (c <= cur || ((double)(rnd() >> 11) * (1.0 / 9007199254740992.0)) < exp(-(c - cur) / T)) { cur = c; bx = x2; by = y2; }
                else volt[e] = old;
                if (cur < gbest) { gbest = cur; fprintf(stderr, "  run %d it %ld best %ld t %.1f\n", run, it, gbest, (double)(clock() - ts) / CLOCKS_PER_SEC); }
                if (cur == 0) { volt[eA] = bx; volt[eB] = by; printf("SOL n %d :", n);
                    for (int f = 0; f < E; f++) printf(" %d-%d:%d", eu[f], ew[f], volt[f]); printf("\n"); fflush(stdout); }
            }
        }
        fprintf(stderr, "RESULT best %ld runs %d n %d vertices %d secs %.1f\n", gbest, run, n, b * n, (double)(clock() - ts) / CLOCKS_PER_SEC);
        return 0;
    }
    long long samples = 0, cand = 0, nsol = 0; clock_t t0 = clock();
    while (SAMPLES == 0 || samples < SAMPLES) {
        samples++;
        int ok = 1;
        for (int i = 0; i < nf; i++) if (fr[i] != eA && fr[i] != eB) volt[fr[i]] = rnd() % n;
        volt[eA] = volt[eB] = -1;
        for (int i = 0; i < nf && ok; i++) if (fr[i] != eA && fr[i] != eB && !par_ok(fr[i])) ok = 0;
        if (!ok) continue;
        for (int c = 0; c < ncond; c++) built[c] = 0;
        for (int x = 0; x < n; x++) {
            volt[eA] = x; volt[eB] = -1; if (!par_ok(eA)) continue;
            for (int y = 0; y < n; y++) {
                volt[eB] = y; if (!par_ok(eB)) continue;
                cand++;
                int good = 1;
                for (int c = 0; c < ncond && good; c++) {
                    if (!built[c]) build(c);
                    if (qx[c] != x) { memset(Q[c], 0, sizeof Q[c]);
                        for (int k = 0; k < nl[c]; k++) Q[c][LB[c][k] + 4] |= rot(PL[c][k], (long)LA[c][k] * x);
                        qx[c] = x; }
                    u128 U = Q[c][4];
                    for (int j = 0; j < 9; j++) if (j != 4 && Q[c][j]) U |= rot(Q[c][j], (long)(j - 4) * y);
                    if (U != MASK) good = 0;
                }
                if (good) {
                    nsol++;
                    printf("SOL n %d :", n);
                    for (int e = 0; e < E; e++) printf(" %d-%d:%d", eu[e], ew[e], volt[e]);
                    printf("\n"); fflush(stdout);
                }
            }
        }
        if ((samples & 0xFFFF) == 0) { fprintf(stderr, "samples %lld cand %lld sol %lld secs %.0f\n", samples, cand, nsol,
            (double)(clock() - t0) / CLOCKS_PER_SEC); }
    }
    fprintf(stderr, "done samples %lld cand %lld sol %lld secs %.1f\n", samples, cand, nsol, (double)(clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
