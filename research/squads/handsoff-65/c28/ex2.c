/* t18.c: tabu search for bipartite graphs of type "1,k|1,k" (c18, card in cards.md).
 * Orbits: A0 = G (regular), A1 = G/H (|H| = k), B0 = G (regular), B1 = G/K (|K| = k); H, K cyclic of order k.
 * Blocks (double cosets, full size): A0-B0: n00 single elements s (x ~ xs); A0-B1: n01 left cosets gK (x ~ coset of xg);
 * A1-B0: n10 right cosets Hg (coset xH ~ x h g); A1-B1: n11 double cosets H g K (coset xH ~ coset of x h g, h in H).
 * Degrees: n00 + n01 = 6, k (n10 + n11) = 6, n00 + n10 = 6, k (n01 + n11) = 6 (only n11 = 0 or 1 with k=6 types).
 * Vertices: A0 x -> x; A1 coset c -> m + c; B0 y -> m + q + y; B1 coset c -> 2m + q + c; q = m / k.
 * G acts on the graph, so diameter <= 5 iff the four representatives (vertex 0 of each orbit) reach everything in <= 5.
 * cost = number of (representative, vertex) pairs at distance > 5 (same scale as mcos).
 * usage: t18 TABLE K N00,N01,N10,N11 SEED ITERS TENURE OUT [HGEN KGEN]
 *   TABLE: group table as for mcos. HGEN / KGEN: optional fixed generators of the hub subgroups (else random).
 *   Moves: change one element of S, G01, G10 or G11 to another element; change H or K to another cyclic subgroup of order k.
 *   Prints "best C step S" lines; writes OUT (edge list) when cost 0 (and at the end, the best found).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define MAXV 2600
#define MAXSUB 256
static int m, *T, inv_[MAXM], ord_[MAXM];
#define MUL(x, y) T[(x) * m + (y)]
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int k, q, nsub;
static int subel[MAXSUB][8];                 /* elements of subgroup s (k of them) */
static int *cosl[MAXSUB];                    /* left coset index of z for subgroup s: cosl[s][z] */
static int *cosr_rep[MAXSUB];                /* representative element of each left coset */
static int nS[4] = {0, 0, 0, 0};            /* n00 n01 n10 n11 */
static int par[4][8];                        /* parameter slots: [block][i] */
static int hs = 0, ks = 0;                   /* current subgroups for H (A1) and K (B1) */

/* inverse of a subgroup's cosets: cosets of left multiplication: zH = {z h} */
static void build_subgroup_cosets(int s) {
    int *c = malloc(sizeof(int) * m), nxt = 0;
    for (int z = 0; z < m; z++) c[z] = -1;
    cosr_rep[s] = malloc(sizeof(int) * (m / k));
    for (int z = 0; z < m; z++) if (c[z] < 0) {
        int id = nxt++; cosr_rep[s][id] = z;
        for (int i = 0; i < k; i++) c[MUL(z, subel[s][i])] = id;
    }
    cosl[s] = c;
}
static int enum_subgroups(void) {
    /* all cyclic subgroups of order k, identified by their element sets */
    int n = 0;
    for (int g = 0; g < m; g++) {
        if (ord_[g] != k) continue;
        int e[8], x = 0;
        for (int i = 0; i < k; i++) { e[i] = x; x = MUL(x, g); }
        int dup = 0;
        for (int s = 0; s < n && !dup; s++) for (int i = 0; i < k; i++) if (subel[s][i] == g) dup = 1;
        if (dup) continue;
        if (n >= MAXSUB) break;
        memcpy(subel[n], e, sizeof(int) * k);
        n++;
    }
    return n;
}
/* graph arrays */
static int adj[MAXV][6], deg[MAXV];
static int nv;
static int overflow;
static void add_edge(int u, int v) { if (deg[u] >= 6 || deg[v] >= 6) { overflow = 1; return; } adj[u][deg[u]++] = v; adj[v][deg[v]++] = u; }
static void build(const int *P, int ps, int ks_) {
    /* P: the parameter sets for the current subgroups */
    (void)P; (void)ps; (void)ks_;
}
static int cost_now(void) {
    /* build adjacency from par[][] and cosets of hs (H) and ks (K) */
    int *cH = cosl[hs], *cK = cosl[ks];
    int base_A1 = m, base_B0 = m + q, base_B1 = 2 * m + q;
    nv = 2 * m + 2 * q;
    for (int v = 0; v < nv; v++) deg[v] = 0;
    overflow = 0;
    /* A0 side: S (A0-B0) and G01 (A0-B1) */
    for (int i = 0; i < nS[0]; i++) { int s = par[0][i]; for (int x = 0; x < m; x++) add_edge(x, base_B0 + MUL(x, s)); }
    for (int i = 0; i < nS[1]; i++) { int g = par[1][i]; for (int x = 0; x < m; x++) add_edge(x, base_B1 + cK[MUL(x, g)]); }
    /* A1 side: for each A1 coset c with representative x_c: G10 (B0) and G11 (B1), all h in H */
    for (int c = 0; c < q; c++) {
        int xc = cosr_rep[hs][c];
        for (int i = 0; i < nS[2]; i++) { int g = par[2][i]; for (int j = 0; j < k; j++) add_edge(base_A1 + c, base_B0 + MUL(MUL(xc, subel[hs][j]), g)); }
        for (int i = 0; i < nS[3]; i++) { int g = par[3][i]; for (int j = 0; j < k; j++) add_edge(base_A1 + c, base_B1 + cK[MUL(MUL(xc, subel[hs][j]), g)]); }
    }
    (void)cH;
    /* degree sanity */
    if (overflow) return 1 << 28;
    for (int v = 0; v < nv; v++) if (deg[v] != 6) return 1 << 28;
    { static int mark[MAXV]; static int stampc = 0;
      for (int v = 0; v < nv; v++) { stampc++; for (int a = 0; a < 6; a++) { int w = adj[v][a]; if (mark[w] == stampc) return 1 << 27; mark[w] = stampc; } } }
    /* BFS from the four representatives: 0, A1 coset of identity (0), B0 identity, B1 coset of identity */
    static int dist[MAXV], queue[MAXV];
    int srcs[4] = {0, base_A1 + 0, base_B0 + 0, base_B1 + 0};
    int total = 0;
    for (int r = 0; r < 4; r++) {
        for (int v = 0; v < nv; v++) dist[v] = -1;
        int h = 0, t = 0; queue[t++] = srcs[r]; dist[srcs[r]] = 0;
        while (h < t) {
            int x = queue[h++];
            if (dist[x] >= 5) continue;
            for (int j = 0; j < 6; j++) { int y = adj[x][j]; if (dist[y] < 0) { dist[y] = dist[x] + 1; queue[t++] = y; } }
        }
        total += nv - t;
    }
    return total;
}
static int dist_ok_side = 0;
static int cost_with(int blk, int i, int val) {
    int old = par[blk][i];
    par[blk][i] = val;
    int c = cost_now();
    par[blk][i] = old;
    return c;
}
static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    /* rebuild the current graph and write it */
    cost_now();
    fprintf(f, "%d\n", nv);
    for (int v = 0; v < nv; v++) for (int j = 0; j < 6; j++) if (adj[v][j] > v) fprintf(f, "%d %d\n", v, adj[v][j]);
    fclose(f);
}
/* ex2.c (c28): exhaustive k-change neighbourhoods of a 1,6|1,6 state (N = 5,1,1,0), H and K as given.
 * usage: ex2 TABLE 6 5,1,1,0 INIT STAGE OUT
 *   INIT: as t18 (4 lines of block values, then "H g K h"); STAGE: "pairs" = all changes of two of the 7 slots
 *   (5 S, G01, G10) to any element; "hub" = all (H,K) pairs with the same slots, then all single-slot changes
 *   under every (H,K) pair (TLIM seconds). Prints the minimum cost found and any cost-0 state (written to OUT).
 */
static int nslot_b[3] = {5, 1, 1}; /* slots per block: S (block 0), G01 (1), G10 (1) */
static int nslots = 7;
static int slot_blk(int s) { return s < 5 ? 0 : (s == 5 ? 1 : 2); }
static int slot_idx(int s) { return s < 5 ? s : 0; }
static double tlim_s;
static double t_start;
static int found0 = 0;
static long evals = 0;
static void dump(const char *tag, int c) {
    printf("ZERO_FOUND %s cost %d S %d %d %d %d %d G01 %d G10 %d H %d K %d\n", tag, c,
           par[0][0], par[0][1], par[0][2], par[0][3], par[0][4], par[1][0], par[2][0], hs, ks);
    fflush(stdout);
}
static void write_init(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    for (int i = 0; i < 5; i++) fprintf(f, "%d ", par[0][i]); fprintf(f, "\n%d \n%d \n\n", par[1][0], par[2][0]);
    fprintf(f, "H %d K %d cost\n", subel[hs][1], subel[ks][1]); fclose(f);
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: ex2 TABLE 6 5,1,1,0 INIT STAGE OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d", &m) != 1) return 1;
    T = malloc(sizeof(int) * m * m);
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &T[i]) != 1) return 1;
    fclose(f);
    k = atoi(argv[2]);
    if (sscanf(argv[3], "%d,%d,%d,%d", &nS[0], &nS[1], &nS[2], &nS[3]) != 4) return 1;
    q = m / k;
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) if (MUL(x, y) == 0) inv_[x] = y;
    for (int x = 0; x < m; x++) { int y = x, o = 1; while (y != 0) { y = MUL(y, x); o++; } ord_[x] = o; }
    nsub = enum_subgroups();
    for (int s = 0; s < nsub; s++) build_subgroup_cosets(s);
    FILE *fi = fopen(argv[4], "r"); if (!fi) return 2;
    for (int b = 0; b < 4; b++) for (int i = 0; i < nS[b]; i++) if (fscanf(fi, "%d", &par[b][i]) != 1) return 2;
    int hg, kg; if (fscanf(fi, "%*s %d %*s %d", &hg, &kg) != 2) return 2;
    fclose(fi);
    for (int s2 = 0; s2 < nsub; s2++) for (int i = 0; i < k; i++) { if (subel[s2][i] == hg) hs = s2; if (subel[s2][i] == kg) ks = s2; }
    const char *stage = argv[5];
    tlim_s = getenv("TLIM") ? atof(getenv("TLIM")) : 1e9;
    t_start = now();
    int base = cost_now();
    printf("m %d nsub %d base cost %d (H %d K %d)\n", m, nsub, base, hg, kg); fflush(stdout);
    int bestc = 1 << 30;
    long hist[8] = {0};
    if (!strcmp(stage, "pairs")) {
        /* all pairs of slots (i<j), all values: exact 2-change neighbourhood with H, K fixed */
        for (int i = 0; i < nslots; i++) for (int j = i + 1; j < nslots; j++) {
            int bi = slot_blk(i), ii = slot_idx(i), bj = slot_blk(j), jj = slot_idx(j);
            if (i >= 5 && j >= 5) {} /* G01/G10 pairs included */
            int oi = par[bi][ii], oj = par[bj][jj];
            for (int vi = 0; vi < m; vi++) for (int vj = 0; vj < m; vj++) {
                par[bi][ii] = vi; par[bj][jj] = vj;
                int c = cost_now(); evals++;
                if (c < 8) hist[c]++;
                if (c < bestc) bestc = c;
                if (c == 0) { dump("pairs", c); found0 = 1; char fn[256]; snprintf(fn, sizeof fn, "%s_z%ld.edges", argv[6], evals); write_edges(fn); }
            }
            par[bi][ii] = oi; par[bj][jj] = oj;
            if (now() - t_start > tlim_s) break;
        }
        printf("pairs done: evals %ld best %d hist(0..7) %ld %ld %ld %ld %ld %ld %ld %ld time %.1f\n", evals, bestc,
               hist[0], hist[1], hist[2], hist[3], hist[4], hist[5], hist[6], hist[7], now() - t_start);
    } else if (!strcmp(stage, "hub")) {
        /* every (H,K) pair; with the current slots, then every single-slot change */
        int h0 = hs, k0 = ks;
        for (int hh = getenv("HSTART") ? atoi(getenv("HSTART")) : 0; hh < nsub && now() - t_start < tlim_s; hh++) for (int kk = 0; kk < nsub && now() - t_start < tlim_s; kk++) {
            hs = hh; ks = kk;
            for (int i = 0; i < nslots; i++) {
                int bi = slot_blk(i), ii = slot_idx(i), oi = par[bi][ii];
                for (int vi = 0; vi < m; vi++) {
                    par[bi][ii] = vi;
                    int c = cost_now(); evals++;
                    if (c < 8) hist[c]++;
                    if (c < bestc) { bestc = c; printf("new best %d at H %d K %d slot %d val %d (evals %ld, %.1f s)\n", c, hh, kk, i, vi, evals, now() - t_start); fflush(stdout); if (c == 2 && getenv("DUMP")) write_init(getenv("DUMP")); }
                    if (c == 0) { dump("hub", c); found0 = 1; char fn[256]; snprintf(fn, sizeof fn, "%s_z%ld.edges", argv[6], evals); write_edges(fn); }
                }
                par[bi][ii] = oi;
            }
        }
        printf("hub done: evals %ld best %d hist %ld %ld %ld %ld time %.1f (last H %d K %d)\n", evals, bestc,
               hist[0], hist[1], hist[2], hist[3], now() - t_start, hs, ks);
        (void)h0; (void)k0;
    }
    return found0 ? 0 : 0;
}
