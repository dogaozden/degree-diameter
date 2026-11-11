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
    int inU[66]; for (int i = 0; i < 66; i++) inU[i] = 1;
    if (argc > 7 && strcmp(argv[7], "all")) { memset(inU, 0, sizeof inU); FILE *uf = fopen(argv[7], "r"); int c; while (fscanf(uf, "%d", &c) == 1) inU[c] = 1; fclose(uf); }
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    int K = 6; int nl = 0; int (*lines)[4] = malloc(sizeof(int[4]) * 66 * K * 64); uint64_t tmp[W];
    for (int cv = 0; cv < 66; cv++) { if (!inU[cv]) continue;
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
    { char fn[600]; sprintf(fn, "%s.cands", argv[6]); FILE *cf = fopen(fn, "w");
      for (int i = 0; i < nc; i++) { for (int k = 0; k < csz[i]; k++) fprintf(cf, "%d ", cand[i][k]); fprintf(cf, "\n"); }
      fclose(cf); }
    /* compatibility: R(h) = OR of d2 over N(h); compat iff disjoint and R(h) meets N(h') */
    uint64_t *R = malloc((size_t)nc * W * 8);
    for (int i = 0; i < nc; i++) { uint64_t *o = R + (size_t)i * W; memset(o, 0, W * 8);
        for (int k = 0; k < csz[i]; k++) { uint64_t *dd = d2 + (size_t)cand[i][k] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
    int CW = (nc + 63) / 64; uint64_t *C = calloc((size_t)nc * CW, 8);
    long ncomp = 0; int *stamp = calloc(H, 4);
    for (int i = 0; i < nc; i++) {
        for (int l = 0; l < csz[i]; l++) stamp[cand[i][l]] = i + 1;
        uint64_t *o = R + (size_t)i * W;
        for (int j = i + 1; j < nc; j++) {
            int meet = 0, dis = 1;
            for (int k = 0; k < csz[j]; k++) { int t = cand[j][k]; if (stamp[t] == i + 1) { dis = 0; break; } if ((o[t >> 6] >> (t & 63)) & 1) meet = 1; }
            if (meet && dis) { C[(size_t)i * CW + (j >> 6)] |= 1ULL << (j & 63); C[(size_t)j * CW + (i >> 6)] |= 1ULL << (i & 63); ncomp++; }
        }
    }
    fprintf(stderr, "compatibility density %.4f (%.1fs)\n", 2.0 * ncomp / ((double)nc * (nc - 1)), now() - t0);
    /* max clique: randomized greedy restarts + (1,2)-swaps (remove one, add two) */
    int *best = malloc(4 * nc), nbest = 0, *cur = malloc(4 * nc), ncur; uint64_t *P = malloc(CW * 8); int *inc = calloc(nc, 4);
    int *cnt = calloc(nc, 4);   /* cnt[v] = number of current members v is NOT adjacent to */
    while (now() - t0 < secs) {
        ncur = 0; memset(inc, 0, 4 * nc);
        for (int i = 0; i < nc; i++) cnt[i] = 0;
        /* greedy from a random order */
        for (int it = 0; it < nc; it++) {
            int v = rnd() % nc; if (inc[v] || cnt[v]) continue;
            inc[v] = 1; cur[ncur++] = v;
            for (int x = 0; x < nc; x++) if (x != v && !((C[(size_t)v * CW + (x >> 6)] >> (x & 63)) & 1)) cnt[x]++;
        }
        /* plateau search: swap in a vertex with cnt == 1 (drop its single non-neighbour), add free vertices */
        for (int rounds = 0; rounds < 20000 && now() - t0 < secs; rounds++) {
            int added = 0;
            for (int x = 0; x < nc; x++) if (!inc[x] && cnt[x] == 0) { inc[x] = 1; cur[ncur++] = x;
                for (int y = 0; y < nc; y++) if (y != x && !((C[(size_t)x * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]++; added = 1; }
            if (ncur > nbest) { nbest = ncur; memcpy(best, cur, 4 * ncur); if (nbest % 10 == 0) fprintf(stderr, "clique %d (%.1fs)\n", nbest, now() - t0); }
            if (added) continue;
            int x = -1; for (int s = 0; s < 200; s++) { int y = rnd() % nc; if (!inc[y] && cnt[y] == 1) { x = y; break; } }
            if (x < 0) break;
            int drop = -1; for (int a = 0; a < ncur; a++) { int m = cur[a]; if (!((C[(size_t)x * CW + (m >> 6)] >> (m & 63)) & 1)) { drop = a; break; } }
            int m = cur[drop]; inc[m] = 0; cur[drop] = cur[--ncur];
            for (int y = 0; y < nc; y++) if (y != m && !((C[(size_t)m * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]--;
            inc[x] = 1; cur[ncur++] = x;
            for (int y = 0; y < nc; y++) if (y != x && !((C[(size_t)x * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]++;
        }
    }
    FILE *g = fopen(argv[6], "w");
    for (int a = 0; a < nbest; a++) { int i = best[a]; for (int k = 0; k < csz[i]; k++) fprintf(g, "%d ", cand[i][k] + (side == 0 ? H : 0)); fprintf(g, "\n"); }
    fclose(g);
    printf("side %d candidates %d best packing %d hubs\n", side, nc, nbest);
    return 0;
}
