/* cyc22.c: exhaustive search over cyclic (Z_n) voltage lifts of a 2+2 base multigraph, for D = 5.
 *
 * Base: A0, A1 | B0, B1 with multiplicity matrix [[a, d-a], [d-a, a]] (d = degree). Edges are listed class by class;
 * a spanning tree (first edge of classes A0B0, A0B1, A1B0) has voltage 0; the first non-tree edge of class A0B0 has
 * voltage 1 when its class has one (unit normalisation, n prime), else it is free. Parallel edges have distinct
 * voltages and are sorted (symmetry breaking).
 * Lift of an abelian base: a walk's product is the integer combination c . v of edge voltages. For each condition
 * (source s, target t) the distinct coefficient vectors of the non-backtracking walks of the right parity and length
 * (<= 5 from A sources, <= 4 between B vertices) are precomputed. The lift has diameter <= 5 iff, for every condition,
 * the sums c . v cover Z_n. The last two free voltages are handled with 128-bit rotations of partial-sum bitsets.
 * usage: cyc22 n a [d] [SLICE NSLICES]   prints every solution as a vl solution line set.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef unsigned __int128 u128;
static int n, a, d = 5, E;
static int eu[32], ew[32], cls[32];
static int side[4] = {0, 0, 1, 1};
static int adjv[4][32], adje[4][32], adjs[4][32], deg[4];
#define MAXV 4096
#define NC 10
static int ncond, cs[NC], ct[NC];
static int nvec[NC];
static signed char vec[NC][MAXV][32];
static int volt[32], isfree[32], nfree, freeidx[32];
static u128 MASK;

static inline u128 rot(u128 x, int k) { k %= n; if (k < 0) k += n; if (!k) return x; return ((x << k) | (x >> (n - k))) & MASK; }

static int cur_s, cur_L; static signed char cvec[32];
static signed char (*tmpv)[32]; static int ntmp;
static void dfs(int v, int laste, int len, int target) {
    if (v == target && ((len & 1) == (side[cur_s] != side[target]))) {
        int k; for (k = 0; k < ntmp; k++) if (!memcmp(tmpv[k], cvec, 32)) break;
        if (k == ntmp) { if (ntmp >= MAXV) { fprintf(stderr, "MAXV\n"); exit(1); } memcpy(tmpv[ntmp++], cvec, 32); }
    }
    if (len == cur_L) return;
    for (int i = 0; i < deg[v]; i++) { int e = adje[v][i]; if (e == laste) continue;
        cvec[e] += adjs[v][i]; dfs(adjv[v][i], e, len + 1, target); cvec[e] -= adjs[v][i]; }
}

static u128 Q[NC][7]; static int qx[NC];
static u128 PL[NC][49]; static int LA[NC][49], LB[NC][49], nl[NC], built[NC];
static void build(int c, int eA, int eB) {
    u128 P[7][7]; memset(P, 0, sizeof P);
    for (int k = 0; k < nvec[c]; k++) { int s = 0;
        for (int e = 0; e < E; e++) if (e != eA && e != eB && vec[c][k][e]) s += vec[c][k][e] * volt[e];
        s %= n; if (s < 0) s += n;
        P[vec[c][k][eA] + 3][vec[c][k][eB] + 3] |= ((u128)1) << s; }
    nl[c] = 0;
    for (int ca = 0; ca < 7; ca++) for (int cb = 0; cb < 7; cb++) if (P[ca][cb]) {
        PL[c][nl[c]] = P[ca][cb]; LA[c][nl[c]] = ca - 3 + 3 * n; LB[c][nl[c]] = cb - 3 + 3 * n; nl[c]++; }
    built[c] = 1;
}
static int asg[32];
/* 1 if edge e conflicts with an assigned edge of its class (equal voltage, or free edges out of order) */
static int clash(int e) {
    for (int f = 0; f < E; f++) if (f != e && asg[f] && cls[f] == cls[e]) {
        if (volt[f] == volt[e]) return 1;
        if (isfree[f] && isfree[e] && ((f < e) != (volt[f] < volt[e]))) return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); a = atoi(argv[2]); if (argc > 3) d = atoi(argv[3]);
    int slice = argc > 5 ? atoi(argv[4]) : 0, nsl = argc > 5 ? atoi(argv[5]) : 1;
    if (n > 127) { fprintf(stderr, "n <= 127\n"); return 2; }
    MASK = (((u128)1) << n) - 1;
    int mult[4] = {a, d - a, d - a, a};   /* A0B0, A0B1, A1B0, A1B1 */
    int cu[4] = {0, 0, 1, 1}, cw[4] = {2, 3, 2, 3};
    E = 0;
    for (int c = 0; c < 4; c++) for (int k = 0; k < mult[c]; k++) { eu[E] = cu[c]; ew[E] = cw[c]; cls[E] = c; E++; }
    for (int e = 0; e < E; e++) {
        int u = eu[e], w = ew[e];
        adjv[u][deg[u]] = w; adje[u][deg[u]] = e; adjs[u][deg[u]] = 1; deg[u]++;
        adjv[w][deg[w]] = u; adje[w][deg[w]] = e; adjs[w][deg[w]] = -1; deg[w]++;
    }
    /* tree: first edge of classes 0, 1, 2 */
    int seen[4] = {0};
    for (int e = 0; e < E; e++) { isfree[e] = 1; if (cls[e] < 3 && !seen[cls[e]]) { seen[cls[e]] = 1; isfree[e] = 0; volt[e] = 0; } }
    /* unit normalisation: first free edge of class 0 = 1 (if any) */
    int fixed1 = -1;
    for (int e = 0; e < E; e++) if (isfree[e] && cls[e] == 0) { fixed1 = e; isfree[e] = 0; volt[e] = 1; break; }
    nfree = 0; for (int e = 0; e < E; e++) if (isfree[e]) freeidx[nfree++] = e;
    /* conditions */
    int S[NC][2] = {{0,0},{0,1},{1,1},{0,2},{0,3},{1,2},{1,3},{2,2},{2,3},{3,3}};
    tmpv = malloc(sizeof(signed char[32]) * MAXV);
    ncond = NC;
    for (int c = 0; c < NC; c++) {
        cs[c] = S[c][0]; ct[c] = S[c][1]; cur_s = cs[c]; cur_L = side[cur_s] == 0 ? 5 : 4; ntmp = 0;
        memset(cvec, 0, 32); dfs(cur_s, -1, 0, ct[c]);
        nvec[c] = ntmp; memcpy(vec[c], tmpv, sizeof(signed char[32]) * ntmp);
    }
    /* order conditions by vector count (fewest first) */
    for (int i = 0; i < NC; i++) for (int j = i + 1; j < NC; j++) if (nvec[j] < nvec[i]) {
        int t; t = nvec[i]; nvec[i] = nvec[j]; nvec[j] = t; t = cs[i]; cs[i] = cs[j]; cs[j] = t; t = ct[i]; ct[i] = ct[j]; ct[j] = t;
        signed char tv[MAXV][32]; memcpy(tv, vec[i], sizeof tv); memcpy(vec[i], vec[j], sizeof tv); memcpy(vec[j], tv, sizeof tv); }
    fprintf(stderr, "n %d a %d d %d E %d free %d (fixed1 %d); vectors:", n, a, d, E, nfree, fixed1);
    for (int c = 0; c < NC; c++) fprintf(stderr, " %d%d:%d", cs[c], ct[c], nvec[c]); fprintf(stderr, "\n");
    if (nfree < 2) return 2;
    int eA = freeidx[nfree - 2], eB = freeidx[nfree - 1];   /* the last two free edges: inner 2D loop */
    /* constraint helpers: parallel edges sorted & distinct, nonzero if parallel to a tree edge (class 0..2) */
    long long outer = 0, nsol = 0; double t0 = clock();
    int idx[32];
    int no = nfree - 2;
    for (int i = 0; i < no; i++) idx[i] = 0;
    /* iterate the outer free voltages as an odometer */
    long long counter = 0;
    while (1) {
        /* set outer voltages */
        for (int i = 0; i < no; i++) volt[freeidx[i]] = idx[i];
        for (int e = 0; e < E; e++) asg[e] = (e != eA && e != eB);
        int ok = 1;
        for (int i = 0; i < no && ok; i++) if (clash(freeidx[i])) ok = 0;
        if (ok && (counter++ % nsl) == slice) {
            outer++;
            /* partial sums per condition, classed by the coefficients of eA, eB */
            int alive_any = 1;
            for (int c = 0; c < NC; c++) built[c] = 0;
            (void)alive_any;
            for (int x = 0; x < n; x++) {
                volt[eA] = x;
                asg[eA] = 1; asg[eB] = 0; int bad = clash(eA);
                if (bad) continue;
                for (int y = 0; y < n; y++) {
                    if (cls[eB] == cls[eA] && y <= x) continue;
                    volt[eB] = y; asg[eB] = 1; bad = clash(eB);
                    if (bad) continue;
                    int good = 1;
                    for (int c = 0; c < NC && good; c++) {
                        if (!built[c]) { build(c, eA, eB); qx[c] = -1; }
                        if (qx[c] != x) { memset(Q[c], 0, sizeof Q[c]);
                            for (int k = 0; k < nl[c]; k++) Q[c][LB[c][k] - 3 * n + 3] |= rot(PL[c][k], LA[c][k] * x);
                            qx[c] = x; }
                        u128 U = Q[c][3];
                        for (int cb = 0; cb < 7; cb++) if (cb != 3 && Q[c][cb]) U |= rot(Q[c][cb], (cb - 3 + 3 * n) * y);
                        if (U != MASK) good = 0;
                    }
                    if (good) {
                        nsol++;
                        printf("SOL n %d a %d :", n, a);
                        for (int e = 0; e < E; e++) printf(" %d-%d:%d", eu[e], ew[e], volt[e]);
                        printf("\n"); fflush(stdout);
                    }
                }
            }
        }
        int i = 0;
        while (i < no) { idx[i]++; if (idx[i] < n) break; idx[i] = 0; i++; }
        if (i == no) break;
    }
    fprintf(stderr, "done n %d a %d outer %lld solutions %lld secs %.1f\n", n, a, outer, nsol, (clock() - t0) / CLOCKS_PER_SEC);
    return 0;
}
