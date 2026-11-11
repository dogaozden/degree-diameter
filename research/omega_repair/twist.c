/* twist.c: Gomez's Omega H_q (thesis UPC 1986, sec. 2.9.3, Fig. 2.21a/b) with TWISTED copies (job thm-omega-repair).

   Reading 2 of the figures (unbarred hubs (t,k) on points, barred hubs (m,kbar) on lines, in every copy), A blocks of 5
   copies, block types a/b (the figure's two structures):
     type a: (t,k) ~ copies k-1, k+1;  (m,kbar) ~ copies k+2, k+3
     type b: (t,k) ~ copies k+3, k+4;  (m,kbar) ~ copies k-1, k+1
   Copy c is H(q) (points 0..n-1, lines 0..n-1); P-hub (t,k) is joined to point t of every copy it meets and L-hub
   (m,kbar) to line lam_c(m), where lam_c is a collineation of H(q) (the twist of copy c).  Every relabelling of a copy by
   one collineation on points and another on lines gives such a graph (relabel the copy by the point collineation).
   lam_c = id for all c is the thesis graph (diameter 9).

   modes:
     twist hex.txt twists.bin TYPES formula      far (hub, copy vertex) pairs from the route formulas (fast)
     twist hex.txt twists.bin TYPES bfs [all]     the same count by bit-parallel BFS on the explicit graph, from every hub
                                                  (with 'all': from every vertex; prints the diameter)
     twist hex.txt twists.bin TYPES edges out.txt write the graph as an edge list ("NV" then "u v" lines)
   twists.bin: int32 C, n, then for each copy n point images and n line images of lam_c.  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static int q, n, A, C, Q1, tstep = 1;                 /* Q1 = q+1 */
static int *Lpts;                          /* line l: points Lpts[l*Q1 + j] */
static int *Plin;                          /* point p: lines Plin[p*Q1 + j] */
static int *lamP, *lamL;                   /* lam_c on points / lines: [c*n + x] */
static int *ilamP, *ilamL;
static char types[64];
static int att[64][10];                    /* att[c][cls]: class cls (0..4 unbarred k, 5..9 barred k) meets copy c */

static void wiring(void) {
    memset(att, 0, sizeof att);
    for (int B = 0; B < A; B++) for (int k = 0; k < 5; k++) {
        int a = types[B] == 'a';
        int u1 = a ? k + 4 : k + 3, u2 = a ? k + 1 : k + 4;          /* unbarred */
        int b1 = a ? k + 2 : k + 4, b2 = a ? k + 3 : k + 1;          /* barred */
        att[5 * B + u1 % 5][k] = att[5 * B + u2 % 5][k] = 1;
        att[5 * B + b1 % 5][5 + k] = att[5 * B + b2 % 5][5 + k] = 1;
    }
    for (int c = 0; c < C; c++) { int s = 0; for (int x = 0; x < 10; x++) s += att[c][x];
        if (s != 4) { fprintf(stderr, "wiring: copy %d meets %d classes\n", c, s); exit(1); } }
}

static void load_hex(const char *path) {
    FILE *f = fopen(path, "r"); int nl; if (fscanf(f, "%d %d %d", &q, &n, &nl) != 3) exit(1); Q1 = q + 1;
    Lpts = malloc(sizeof(int) * n * Q1); Plin = malloc(sizeof(int) * n * Q1); int *cnt = calloc(n, sizeof(int));
    for (int l = 0; l < n; l++) for (int j = 0; j < Q1; j++) { int p; if (fscanf(f, "%d", &p) != 1) exit(1);
        Lpts[l * Q1 + j] = p; Plin[p * Q1 + cnt[p]++] = l; }
    fclose(f); free(cnt);
}
static void load_twists(const char *path) {
    FILE *f = fopen(path, "rb"); int hdr[2]; if (fread(hdr, 4, 2, f) != 2) exit(1);
    if (hdr[1] != n || hdr[0] != C) { fprintf(stderr, "twist file: C=%d n=%d, expected C=%d n=%d\n", hdr[0], hdr[1], C, n); exit(1); }
    lamP = malloc(sizeof(int) * C * n); lamL = malloc(sizeof(int) * C * n);
    ilamP = malloc(sizeof(int) * C * n); ilamL = malloc(sizeof(int) * C * n);
    for (int c = 0; c < C; c++) { if (fread(lamP + c * n, 4, n, f) != (size_t)n || fread(lamL + c * n, 4, n, f) != (size_t)n) exit(1); }
    fclose(f);
    /* check: bijections, and lam_c maps incidence to incidence */
    for (int c = 0; c < C; c++) {
        for (int x = 0; x < n; x++) { ilamP[c * n + lamP[c * n + x]] = x; ilamL[c * n + lamL[c * n + x]] = x; }
        char *s = calloc((size_t)n, 1), *s2 = calloc((size_t)n, 1);
        for (int x = 0; x < n; x++) { s[lamP[c * n + x]] = 1; s2[lamL[c * n + x]] = 1; }
        for (int x = 0; x < n; x++) if (!s[x] || !s2[x]) { fprintf(stderr, "copy %d: twist not a bijection\n", c); exit(1); }
        free(s); free(s2);
        for (int l = 0; l < n; l++) { int L2 = lamL[c * n + l];
            for (int j = 0; j < Q1; j++) { int p2 = lamP[c * n + Lpts[l * Q1 + j]], ok = 0;
                for (int i = 0; i < Q1; i++) ok |= Lpts[L2 * Q1 + i] == p2;
                if (!ok) { fprintf(stderr, "copy %d: twist is not a collineation\n", c); exit(1); } } }
    }
}

/* ---------- balls in H(q): point balls (points within distance 2, 4) and line balls (lines within 2, 4) ---------- */
static int W;                       /* 64-bit words per bitset */
static uint64_t *PB2, *PB4, *LB2, *LB4;
static void balls(void) {
    W = (n + 63) / 64;
    PB2 = calloc((size_t)n * W, 8); PB4 = calloc((size_t)n * W, 8); LB2 = calloc((size_t)n * W, 8); LB4 = calloc((size_t)n * W, 8);
    for (int side = 0; side < 2; side++) {
        /* side 0: points (neighbours through lines); side 1: lines (neighbours through points) */
        int *X = side ? Lpts : Plin, *Y = side ? Plin : Lpts;   /* X[x] = the q+1 opposite-type neighbours of x */
        uint64_t *B2 = side ? LB2 : PB2, *B4 = side ? LB4 : PB4;
        for (int z = 0; z < n; z++) {
            uint64_t *b2 = B2 + (size_t)z * W, *b4 = B4 + (size_t)z * W;
            b2[z >> 6] |= 1ULL << (z & 63);
            for (int i = 0; i < Q1; i++) { int y = X[z * Q1 + i];
                for (int j = 0; j < Q1; j++) { int x = Y[y * Q1 + j]; b2[x >> 6] |= 1ULL << (x & 63); } }
            for (int w = 0; w < W; w++) b4[w] = b2[w];
            for (int x = 0; x < n; x++) if (b2[x >> 6] >> (x & 63) & 1)
                for (int i = 0; i < Q1; i++) { int y = X[x * Q1 + i];
                    for (int j = 0; j < Q1; j++) { int x2 = Y[y * Q1 + j]; b4[x2 >> 6] |= 1ULL << (x2 & 63); } }
        }
    }
}

/* ---------- routes ---------- */
/* A route from a hub of class X to a target copy cp: copies c1..cr = cp, exit classes Y1..Y_{r-1}.  In coordinates in
   which the source side is untwisted (P-sources: points untwisted; L-sources: lines untwisted, i.e. apply lam_c^-1 to
   copy c), a transfer through a class of the source's own type is the identity and one through the other type from copy
   c to copy d is w_d w_c^-1, with w = lam on points (P-sources) or w = lam^-1 on lines (L-sources).  All transfers are
   collineations, so the route reaches exactly the ball B(g(t), R) (vertices of the source's neighbour type) where g is the
   composite and R the largest admissible total segment length (see OMEGA_REPAIR.md, Lemma 2.2).  For r <= 3 the composite
   always reduces to w_a w_b^-1; routes with r = 4 have all segments empty and stay at t (composite id). */
typedef struct { int a, b, R; } Cen;     /* centre w_a w_b^-1 (a = b = -1: identity), radius R */
#define MAXCEN 4096
static Cen cen[10][64][MAXCEN]; static int ncen[10][64];
static void addcen(int X, int cp, int a, int b, int R) {
    if (a == b) a = b = -1;
    for (int i = 0; i < ncen[X][cp]; i++) if (cen[X][cp][i].a == a && cen[X][cp][i].b == b) { if (R > cen[X][cp][i].R) cen[X][cp][i].R = R; return; }
    if (ncen[X][cp] >= MAXCEN) { fprintf(stderr, "MAXCEN\n"); exit(1); }
    cen[X][cp][ncen[X][cp]++] = (Cen){a, b, R};
}
/* word as a list of (copy, sign) applied right to left: we keep it as a stack of copies with alternating signs:
   the composite of transfers T_r ... T_1 where each nontrivial T is w_d w_c^-1.  Reduce adjacent w_c^-1 w_c. */
static int wd[16], wsgn[16], wlen;
static void dfs(int X, int c, int tin, int Yin, int used, int minseg, int r) {
    /* currently in copy c, entered at a vertex of type tin (0 = source type, 1 = other), through class Yin;
       used = edges so far (1 + 2(r-1)); minseg = sum of minimal segment lengths so far (excluding current copy) */
    int srcT = X < 5 ? 0 : 1;
    /* (i) end in this copy at a vertex of the source's neighbour type (= source type, 0) */
    if (!att[c][X]) {
        int budget = 7 - used;            /* total segment length allowed */
        int par = (minseg + tin) & 1;     /* total parity: sum of parities so far + this segment's parity (tin != 0) */
        int R = budget; if ((R & 1) != par) R--;
        int need = minseg + tin;
        if (R >= need && R >= 0) {
            /* reduce the word to w_a w_b^-1 */
            int a = -1, b = -1, ok = 1;
            /* stack holds pairs (d, c) meaning w_d w_c^-1, in application order */
            int m = wlen / 2;
            if (m == 0) { a = b = -1; }
            else {
                /* compose: g = P_m ... P_1, P_i = w_{d_i} w_{c_i}^-1; telescopes iff c_{i+1} = d_i */
                a = wd[2 * (m - 1)]; b = wd[1];
                for (int i = 0; i + 1 < m; i++) if (wd[2 * (i + 1) + 1] != wd[2 * i]) ok = 0;
            }
            if (!ok) { fprintf(stderr, "non-telescoping word (r=%d)\n", r); exit(1); }
            addcen(X, c, a, b, R);
        }
    }
    if (r == 4) return;
    /* (ii) leave through a class Y at c */
    for (int Y = 0; Y < 10; Y++) if (att[c][Y]) {
        int tY = (Y < 5 ? 0 : 1) != srcT;        /* 0 if Y has the source type */
        int seg = tin != tY;                     /* minimal segment parity */
        if (seg == 0 && Y == Yin) seg = 2;       /* same hub otherwise */
        int nused = used + 2;
        if (nused + minseg + seg > 7) continue;
        for (int d = 0; d < C; d++) if (d != c && att[d][Y]) {
            if (tY) { wd[wlen] = d; wd[wlen + 1] = c; wlen += 2; }
            dfs(X, d, tY, Y, nused, minseg + seg, r + 1);
            if (tY) wlen -= 2;
        }
    }
}
static void routes(void) {
    memset(ncen, 0, sizeof ncen);
    for (int X = 0; X < 10; X++) for (int c1 = 0; c1 < C; c1++) if (att[c1][X]) { wlen = 0; dfs(X, c1, 0, X, 1, 0, 1); }
}

/* composite permutations w_a w_b^-1 on points (P side) and lam_a^-1 lam_b on lines (L side) */
static int *compP, *compL;
static int *cache[2][64][64];
static void invalidate(int c) { for (int s = 0; s < 2; s++) for (int x = 0; x < 64; x++) { free(cache[s][c][x]); cache[s][c][x] = NULL; if (x != c) { free(cache[s][x][c]); cache[s][x][c] = NULL; } } }
static int *comp(int side, int a, int b) {
    if (a < 0) return NULL;
    if (!cache[side][a][b]) { int *p = malloc(sizeof(int) * n);
        for (int x = 0; x < n; x++) p[x] = side == 0 ? lamP[a * n + ilamP[b * n + x]] : ilamL[a * n + lamL[b * n + x]];
        cache[side][a][b] = p; }
    return cache[side][a][b];
}

static long formula(int verbose) {
    long far = 0, farX[10] = {0};
    for (int X = 0; X < 10; X++) for (int cp = 0; cp < C; cp++) if (!att[cp][X])          /* fill the cache serially */
        for (int i = 0; i < ncen[X][cp]; i++) if (cen[X][cp][i].a >= 0) comp(X < 5 ? 0 : 1, cen[X][cp][i].a, cen[X][cp][i].b);
    int pairs[640][2], np_ = 0;
    for (int X = 0; X < 10; X++) for (int cp = 0; cp < C; cp++) if (!att[cp][X]) { pairs[np_][0] = X; pairs[np_][1] = cp; np_++; }
    #pragma omp parallel for schedule(dynamic) reduction(+:far)
    for (int pi = 0; pi < np_; pi++) {
        int X = pairs[pi][0], cp = pairs[pi][1];
        int side = X < 5 ? 0 : 1; uint64_t *B2 = side ? LB2 : PB2, *B4 = side ? LB4 : PB4;
        uint64_t *acc = malloc(8 * W); long f = 0;
        int **cp_ = malloc(sizeof(int *) * (ncen[X][cp] + 1));
        for (int i = 0; i < ncen[X][cp]; i++) cp_[i] = cen[X][cp][i].a < 0 ? NULL : comp(side, cen[X][cp][i].a, cen[X][cp][i].b);
        for (int t = 0; t < n; t += tstep) {
            memset(acc, 0, 8 * W);
            for (int i = 0; i < ncen[X][cp]; i++) { Cen e = cen[X][cp][i]; int z = cp_[i] ? cp_[i][t] : t;
                if (e.R >= 4) { uint64_t *b = B4 + (size_t)z * W; for (int w = 0; w < W; w++) acc[w] |= b[w]; }
                else if (e.R >= 2) { uint64_t *b = B2 + (size_t)z * W; for (int w = 0; w < W; w++) acc[w] |= b[w]; }
                else acc[z >> 6] |= 1ULL << (z & 63); }
            long cov = 0; for (int w = 0; w < W; w++) cov += __builtin_popcountll(acc[w]);
            f += n - cov;
        }
        free(acc); free(cp_);
        #pragma omp atomic
        farX[X] += f;
        far += f;
    }
    if (verbose) { printf("far by source class:"); for (int X = 0; X < 10; X++) printf(" %ld", farX[X]); printf("\n"); }
    return far;
}

/* ---------- explicit graph ---------- */
static long NV, hubbase; static int maxd, *adj, *deg;
static long vP(int c, int p) { return (long)c * 2 * n + p; }
static long vL(int c, int l) { return (long)c * 2 * n + n + l; }
static void build(void) {
    hubbase = (long)C * 2 * n; NV = hubbase + 10L * n; maxd = Q1 + 2 > 2 * A ? Q1 + 2 : 2 * A;
    adj = malloc(sizeof(int) * NV * maxd); deg = calloc(NV, sizeof(int));
#define ADDE(u, v) do { adj[(u) * maxd + deg[u]++] = (v); adj[(v) * maxd + deg[v]++] = (u); } while (0)
    for (int c = 0; c < C; c++) for (int l = 0; l < n; l++) for (int j = 0; j < Q1; j++) { long u = vL(c, l), v = vP(c, Lpts[l * Q1 + j]); ADDE(u, v); }
    for (int t = 0; t < n; t++) for (int X = 0; X < 10; X++) { long h = hubbase + 10L * t + X;
        for (int c = 0; c < C; c++) if (att[c][X]) { long v = X < 5 ? vP(c, t) : vL(c, lamL[c * n + t]); ADDE(h, v); } }
    for (long v = 0; v < NV; v++) if (deg[v] != (v < hubbase ? Q1 + 2 : 2 * A)) { fprintf(stderr, "degree error at %ld\n", v); exit(1); }
}
static long bfs(long *src, long ns, int *diam) {
    uint64_t *vis = malloc(8 * NV), *fr = malloc(8 * NV), *nx = malloc(8 * NV); long far = 0; *diam = 0;
    for (long s0 = 0; s0 < ns; s0 += 64) {
        int k = ns - s0 < 64 ? ns - s0 : 64; uint64_t full = k == 64 ? ~0ULL : ((1ULL << k) - 1);
        memset(vis, 0, 8 * NV); memset(fr, 0, 8 * NV);
        for (int i = 0; i < k; i++) { vis[src[s0 + i]] |= 1ULL << i; fr[src[s0 + i]] |= 1ULL << i; }
        int lev = 0;
        for (;;) {
            int any = 0;
            for (long x = 0; x < NV; x++) { uint64_t a = 0; int *p = adj + x * maxd; for (int j = 0; j < deg[x]; j++) a |= fr[p[j]];
                nx[x] = a & ~vis[x]; if (nx[x]) any = 1; }
            if (!any) break;
            lev++; for (long x = 0; x < NV; x++) vis[x] |= nx[x];
            uint64_t *tt = fr; fr = nx; nx = tt;
            if (lev == 8) for (long x = 0; x < NV; x++) far += __builtin_popcountll(~vis[x] & full);
        }
        for (long x = 0; x < NV; x++) if ((vis[x] & full) != full) { fprintf(stderr, "disconnected\n"); exit(1); }
        if (lev > *diam) *diam = lev;
    }
    free(vis); free(fr); free(nx); return far;
}

#ifndef TWIST_NO_MAIN
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: twist hex.txt twists.bin TYPES formula|bfs [all]|edges out\n"); return 1; }
    load_hex(argv[1]); strcpy(types, argv[3]); A = strlen(types); C = 5 * A; wiring(); load_twists(argv[2]);
    if (getenv("TSTEP")) tstep = atoi(getenv("TSTEP"));
    if (!strcmp(argv[4], "formula")) {
        balls(); routes();
        int tot = 0, mx = 0; for (int X = 0; X < 10; X++) for (int c = 0; c < C; c++) { tot += ncen[X][c]; if (ncen[X][c] > mx) mx = ncen[X][c]; }
        long far = formula(1);
        printf("q=%d types=%s n=%d copies=%d centres/target max %d avg %.1f FAR_PAIRS %ld%s\n", q, types, n, C, mx, tot / (5.0 * C), far, tstep > 1 ? " (sampled: every TSTEP-th row t)" : "");
    } else if (!strcmp(argv[4], "bfs")) {
        build(); int all = argc > 5 && !strcmp(argv[5], "all");
        long ns = all ? NV : 10L * n; long *src = malloc(sizeof(long) * ns);
        for (long i = 0; i < ns; i++) src[i] = all ? i : hubbase + i;
        int diam; long far = bfs(src, ns, &diam);
        printf("q=%d types=%s NV=%ld sources=%s FAR_PAIRS(dist>8, ordered from sources) %ld max_ecc %d\n", q, types, NV, all ? "all" : "hubs", far, diam);
    } else if (!strcmp(argv[4], "edges")) {
        build(); FILE *f = fopen(argv[5], "w"); fprintf(f, "%ld\n", NV);
        for (long v = 0; v < NV; v++) for (int j = 0; j < deg[v]; j++) if (adj[v * maxd + j] > v) fprintf(f, "%ld %d\n", v, adj[v * maxd + j]);
        fclose(f); printf("wrote %s NV=%ld\n", argv[5], NV);
    }
    return 0;
}
#endif
