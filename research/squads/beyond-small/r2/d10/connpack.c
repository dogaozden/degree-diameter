/* hubpack: add "hubs" to the (16,5) route-chart graph G (33,792 vertices, 16-regular, bipartite, diameter 5).
 *
 * A hub on side S is a new vertex joined to a set N of old vertices of the other side T (|N| <= 17, each old vertex
 * used by at most one hub, so degrees stay <= 17). Diameter stays <= 5 if
 *   (1) every S-vertex is within distance 3 of N (the hub then reaches S in <= 4 and T in <= 5, as T-T distances in
 *       G are <= 4),
 *   (2) any two hubs on side S have some x in N(h), x' in N(h') with d(x,x') <= 2,
 *   (3) hubs on opposite sides are within 5 (checked at the end by apsp; it holds with room to spare).
 * Hubs are built from affine fibre lines {(v, y + lam c) : lam in F4} of side T (card c03's observation: 4 lines,
 * 16 vertices, can cover S). Candidates: randomized greedy covers. Packing: a large set of candidates that are
 * pairwise vertex-disjoint and satisfy (2) = a clique in a compatibility graph (randomized greedy + swap search).
 *
 * usage: hubpack EDGES SIDE NCAND SECS SEED OUT      SIDE = 0: hubs on side A (neighbours in B), 1: hubs on side B.
 * OUT gets one hub per line: the old neighbour ids (global vertex ids). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define H 16896
#define W 264            /* 16896 / 64 */
static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];          /* local ids: A 0..H-1, B 0..H-1 */
static uint64_t *ball, *d2;                    /* per T-vertex: ball over S (radius 3), d2 over T (radius 2) */
static int (*adjT)[16], (*adjS)[16];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* fibre arithmetic: local id = ctrl * 256 + fid, fid = x0 + 4x1 + 16x2 + 64x3 */
static int addv(int a, int b) { return a ^ b; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: hubpack EDGES SIDE NCAND SECS SEED OUT\n"); return 2; }
    int side = atoi(argv[2]), NC = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    adjT = side == 0 ? adjB : adjA; adjS = side == 0 ? adjA : adjB;   /* T-vertex -> S-neighbours; S-vertex -> T-neighbours */
    ball = calloc((size_t)H * W, 8); d2 = calloc((size_t)H * W, 8);
    double t0 = now();
    for (int t = 0; t < H; t++) {
        uint64_t *bl = ball + (size_t)t * W, *dd = d2 + (size_t)t * W;
        dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjT[t][i]; bl[s >> 6] |= 1ULL << (s & 63);
            for (int j = 0; j < 16; j++) { int t2 = adjS[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) { int s = adjT[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } }
    }
    fprintf(stderr, "balls done %.1fs, |ball(0)| = %d, |d2(0)| = %d\n", now() - t0, popw(ball), popw(d2));
    /* lines: for every T controller vertex (66) and direction (85) the 64 parallel lines; score each direction by the
       mean popcount of its line balls, keep the best K directions per controller vertex */
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    int K = 6; int nl = 0; int (*lines)[4] = malloc(sizeof(int[4]) * 66 * K * 64); uint64_t tmp[W];
    for (int cv = 0; cv < 66; cv++) {
        double sc[85];
        for (int di = 0; di < nd; di++) { long tot = 0;
            for (int s = 0; s < 8; s++) { int y = rnd() & 255; memset(tmp, 0, sizeof tmp);
                for (int l = 0; l < 4; l++) { int t = cv * 256 + (y ^ scal(l, dirs[di])); uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) tmp[w] |= bl[w]; }
                tot += popw(tmp); }
            sc[di] = tot / 8.0; }
        for (int k = 0; k < K; k++) { int bi = 0; for (int di = 1; di < nd; di++) if (sc[di] > sc[bi]) bi = di; double best = sc[bi]; sc[bi] = -1;
            int c = dirs[bi], seen[256] = {0};
            for (int y = 0; y < 256; y++) if (!seen[y]) { for (int l = 0; l < 4; l++) { int z = y ^ scal(l, c); seen[z] = 1; lines[nl][l] = cv * 256 + z; } nl++; }
            if (cv == 0) fprintf(stderr, "ctrl 0 dir %d mean line ball %.0f\n", c, best); }
    }
    fprintf(stderr, "%d lines (%d directions per controller vertex) %.1fs\n", nl, K, now() - t0);
    uint64_t *lball = malloc((size_t)nl * W * 8);
    for (int i = 0; i < nl; i++) { uint64_t *o = lball + (size_t)i * W; memset(o, 0, W * 8);
        for (int l = 0; l < 4; l++) { uint64_t *bl = ball + (size_t)lines[i][l] * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; } }
    /* candidates */
    int (*cand)[17] = malloc(sizeof(int[17]) * NC), *csz = malloc(4 * NC); int nc = 0; long tries = 0;
    uint64_t full[W]; for (int w = 0; w < W; w++) full[w] = ~0ULL;
    while (nc < NC && now() - t0 < secs * 0.5) {
        tries++;
        uint64_t unc[W]; memcpy(unc, full, sizeof unc); int ch[5], nch = 0; int ok = 0;
        int first = rnd() % nl; ch[nch++] = first; { uint64_t *o = lball + (size_t)first * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w]; }
        for (int step = 1; step < 4; step++) {
            int best = -1, bg = -1;
            for (int s = 0; s < 3000; s++) { int i = rnd() % nl; int clash = 0;
                for (int a = 0; a < nch && !clash; a++) for (int x = 0; x < 4 && !clash; x++) for (int y = 0; y < 4; y++) if (lines[i][x] == lines[ch[a]][y]) { clash = 1; break; }
                if (clash) continue;
                uint64_t *o = lball + (size_t)i * W; int g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & o[w]);
                if (g > bg) { bg = g; best = i; } }
            if (best < 0) break; ch[nch++] = best; uint64_t *o = lball + (size_t)best * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w];
            int left = popw(unc); if (left == 0) { ok = 1; break; }
        }
        int extra = -1;
        if (!ok && nch == 4) {   /* try one extra old vertex for the residue */
            for (int s = 0; s < 4000 && extra < 0; s++) { int t = rnd() % H; uint64_t *bl = ball + (size_t)t * W; int cov = 1;
                for (int w = 0; w < W; w++) if (unc[w] & ~bl[w]) { cov = 0; break; }
                if (cov) { int clash = 0; for (int a = 0; a < 4; a++) for (int y = 0; y < 4; y++) if (lines[ch[a]][y] == t) clash = 1; if (!clash) extra = t; } }
            if (extra >= 0) ok = 1;
        }
        if (!ok) continue;
        int k = 0; for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) cand[nc][k++] = lines[ch[a]][y];
        if (extra >= 0) cand[nc][k++] = extra; csz[nc] = k; nc++;
    }
    fprintf(stderr, "%d candidate hubs from %ld tries (%.1fs)\n", nc, tries, now() - t0);
    /* keep only 16-neighbour candidates: a hub with 16 old neighbours has one spare slot for a connector */
    { int m = 0; for (int i = 0; i < nc; i++) if (csz[i] == 16) { if (m != i) { memcpy(cand[m], cand[i], sizeof cand[i]); csz[m] = 16; } m++; }
      fprintf(stderr, "%d of %d candidates have 16 old neighbours\n", m, nc); nc = m; }
    /* M(i,j) = R(i) meets N(j), R(i) = radius-2 reach of N(i) (hubpack's test, stored for i<j and mirrored) */
    uint64_t *R = malloc((size_t)nc * W * 8);
    for (int i = 0; i < nc; i++) { uint64_t *o = R + (size_t)i * W; memset(o, 0, W * 8);
        for (int k = 0; k < csz[i]; k++) { uint64_t *dd = d2 + (size_t)cand[i][k] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
    int CW = (nc + 63) / 64; uint64_t *Mt = calloc((size_t)nc * CW, 8);
    long nmeet = 0;
    for (int i = 0; i < nc; i++) { uint64_t *o = R + (size_t)i * W;
        for (int j = i + 1; j < nc; j++) { int meet = 0;
            for (int k = 0; k < csz[j] && !meet; k++) { int t = cand[j][k]; if ((o[t >> 6] >> (t & 63)) & 1) meet = 1; }
            if (meet) { Mt[(size_t)i * CW + (j >> 6)] |= 1ULL << (j & 63); Mt[(size_t)j * CW + (i >> 6)] |= 1ULL << (i & 63); nmeet++; } } }
    fprintf(stderr, "meet density %.4f (%.1fs)\n", 2.0 * nmeet / ((double)nc * (nc - 1)), now() - t0);
    #define MEET(u, v) ((int)((Mt[(size_t)(u) * CW + ((v) >> 6)] >> ((v) & 63)) & 1))
    #define MAXGRP 17
    #define MAXC 20000
    static int inS[MAXC], grp[MAXC], used[H], gsz[MAXC], chosen[MAXC], ns, ng;
    static int bestS[MAXC], bestG[MAXC], bestn;
    static int sv_inS[MAXC], sv_grp[MAXC], sv_used[H], sv_gsz[MAXC], sv_chosen[MAXC];
    int bestF = -1, sv_ns = 0, sv_ng = 0;
    static int copt[MAXC], optg[MAXC];
    /* option for v: -1 infeasible, -2 no constraint (any non-full group or a new one), else the group it must join */
    int option(int v) {
        for (int k = 0; k < csz[v]; k++) if (used[cand[v][k]]) return -1;
        int nmiss = 0, mg = -1;
        for (int a = 0; a < ns; a++) { int u = chosen[a]; if (!MEET(u, v)) { nmiss++; if (mg < 0) mg = grp[u]; else if (grp[u] != mg) return -1; } }
        if (nmiss == 0) return -2;
        return gsz[mg] < MAXGRP ? mg : -1;
    }
    void add(int v, int g) {
        if (g < 0) { g = -1; for (int q = 0; q < ng; q++) if (gsz[q] == 0) { g = q; break; } if (g < 0) g = ng++; }
        inS[v] = 1; grp[v] = g; gsz[g]++; chosen[ns++] = v; for (int k = 0; k < csz[v]; k++) used[cand[v][k]] = 1;
    }
    void remove_at(int a) {
        int v = chosen[a]; inS[v] = 0; gsz[grp[v]]--; for (int k = 0; k < csz[v]; k++) used[cand[v][k]] = 0;
        chosen[a] = chosen[--ns];
    }
    int fval(void) { int f = ns; for (int q = 0; q < ng; q++) if (gsz[q] >= 2) f++; return f; }
    /* randomized greedy: repeatedly add a uniformly random feasible candidate. Forced group if it misses a hub;
       otherwise prefer a standalone hub's group (creates a connector), else a random non-full group, else a new group */
    void fill(void) {
        for (;;) {
            int nopt = 0;
            for (int v = 0; v < nc; v++) if (!inS[v]) { int r = option(v); if (r != -1) { copt[nopt] = v; optg[nopt] = r; nopt++; } }
            if (nopt == 0) return;
            int pick = rnd() % nopt, v = copt[pick], r = optg[pick];
            if (r == -2) {
                int singles[MAXC], n1 = 0, nonfull[MAXC], nf = 0;
                for (int q = 0; q < ng; q++) { if (gsz[q] == 1) singles[n1++] = q; else if (gsz[q] >= 2 && gsz[q] < MAXGRP) nonfull[nf++] = q; }
                int choice = -1;
                if (n1 > 0 && (rnd() & 3)) choice = singles[rnd() % n1];
                else if (nf > 0 && (rnd() & 1)) choice = nonfull[rnd() % nf];
                add(v, choice);
            } else add(v, r);
        }
    }
    memset(inS, 0, sizeof inS); memset(used, 0, sizeof used); memset(gsz, 0, sizeof gsz); ns = 0; ng = 0;
    fill();
    int cur = fval();
    bestF = cur; bestn = ns; for (int a = 0; a < ns; a++) { bestS[a] = chosen[a]; bestG[a] = grp[chosen[a]]; }
    fprintf(stderr, "greedy: hubs %d, F=%d (%.1fs)\n", ns, cur, now() - t0);
    /* iterated local search: remove 1-4 random hubs, refill, keep the result if not worse */
    long iters = 0;
    while (now() - t0 < secs) {
        iters++;
        memcpy(sv_inS, inS, sizeof inS); memcpy(sv_grp, grp, sizeof grp); memcpy(sv_used, used, sizeof used);
        memcpy(sv_gsz, gsz, sizeof gsz); memcpy(sv_chosen, chosen, sizeof chosen); sv_ns = ns; sv_ng = ng;
        int rem = 1 + rnd() % 4;
        for (int r = 0; r < rem && ns > 0; r++) remove_at(rnd() % ns);
        fill();
        int F = fval();
        if (F >= cur) { cur = F;
            if (F > bestF) { bestF = F; bestn = ns; for (int a = 0; a < ns; a++) { bestS[a] = chosen[a]; bestG[a] = grp[chosen[a]]; }
                fprintf(stderr, "ils %ld: F=%d hubs=%d (%.1fs)\n", iters, F, ns, now() - t0); }
        } else {
            memcpy(inS, sv_inS, sizeof inS); memcpy(grp, sv_grp, sizeof grp); memcpy(used, sv_used, sizeof used);
            memcpy(gsz, sv_gsz, sizeof gsz); memcpy(chosen, sv_chosen, sizeof chosen); ns = sv_ns; ng = sv_ng;
        }
    }
    /* output: one hub per line (old neighbour global ids); connector groups (size >= 2) as hub line indices */
    FILE *g = fopen(argv[6], "w");
    for (int a = 0; a < bestn; a++) { int v = bestS[a]; for (int k = 0; k < csz[v]; k++) fprintf(g, "%d ", cand[v][k] + (side == 0 ? H : 0)); fprintf(g, "\n"); }
    fclose(g);
    char gname[1024]; snprintf(gname, sizeof gname, "%s.groups", argv[6]); FILE *gf = fopen(gname, "w");
    int nconn = 0;
    for (int q = 0; q < MAXC; q++) { int cnt = 0; for (int a = 0; a < bestn; a++) if (bestG[a] == q) cnt++;
        if (cnt < 2) continue; nconn++;
        for (int a = 0; a < bestn; a++) if (bestG[a] == q) fprintf(gf, "%d ", a);
        fprintf(gf, "\n"); }
    fclose(gf);
    printf("side %d candidates %d hubs %d connectors %d F %d iters %ld\n", side, nc, bestn, nconn, bestF, iters);
    return 0;
}
