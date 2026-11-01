/* e12 feas: feasibility study for Z22-orbit hub packing on one side.
 * usage: feas EDGES SIDE POOL SECS SEED OUTPACK
 *   SIDE 0: hubs on A (N subset of B); SIDE 1: hubs on B. POOL: 16-vertex key-distinct covers (global ids).
 * Steps: self-compat (as d06/orb), compat graph among self-compat covers (key-disjoint + 22-shift cover),
 * greedy-colouring upper bound on the clique number of that graph (chi >= omega), max-clique local search,
 * and clique size vs. sub-sample size (trend used for the estimate). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define H 16896
#define W 264
static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static uint64_t *ball, *d2;
static int (*adjT)[16], (*adjS)[16];
static int shT[22][H];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int keyof(int t) { return ((t >> 8) / 22) * 256 + (t & 255); }
static inline int shl(int t, int u) { int blk = t >> 8; int j = blk / 22, h = blk % 22; return ((j * 22 + (h + u) % 22) << 8) | (t & 255); }
static inline int bit(const uint64_t *a, int t) { return (a[t >> 6] >> (t & 63)) & 1; }
#define MAXN 20000
static int (*cand)[16];
static uint64_t (*KS)[12];
static uint64_t *Sb;
static double T0; static double secs;

/* compat test between self-compat covers i,j (indices into pool); shifted vertex = jb + hoff[u][h] + y */
static int *JB, *HH, *YY;   /* per pool cover, per vertex k: block-group base j*22*256, h, y (flattened [i*16+k]) */
static int hoff[22][22];   /* hoff[u][h] = ((h+u)%22)*256 */
static int compat(int i, int j) {
    for (int w = 0; w < 12; w++) if (KS[i][w] & KS[j][w]) return 0;
    const uint64_t *S = Sb + (size_t)i * W; uint32_t covm = 0; const uint32_t full22 = (1u << 22) - 1;
    const int *jb = JB + (size_t)j * 16, *hh = HH + (size_t)j * 16, *yy = YY + (size_t)j * 16;
    for (int uu = 0; uu < 22; uu++) {
        const int *ho = hoff[uu]; int hit = 0;
        for (int k = 0; k < 16 && !hit; k++) { int t = jb[k] + ho[hh[k]] + yy[k]; if ((S[t >> 6] >> (t & 63)) & 1) hit = 1; }
        if (!hit) return 0;
    }
    (void)covm; (void)full22;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: feas EDGES SIDE POOL SECS SEED OUTPACK\n"); return 2; }
    int side = atoi(argv[2]); secs = atof(argv[4]); T0 = now();
    rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    adjT = side == 0 ? adjB : adjA; adjS = side == 0 ? adjA : adjB;
    for (int u2 = 0; u2 < 22; u2++) for (int t = 0; t < H; t++) shT[u2][t] = shl(t, u2);
    ball = calloc((size_t)H * W, 8); d2 = calloc((size_t)H * W, 8);
    for (int t = 0; t < H; t++) {
        uint64_t *bl = ball + (size_t)t * W, *dd = d2 + (size_t)t * W;
        dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjT[t][i]; bl[s >> 6] |= 1ULL << (s & 63);
            for (int j = 0; j < 16; j++) { int t2 = adjS[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) { int s = adjT[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } }
    }
    /* load pool, key-distinct 16-sets only */
    cand = malloc(sizeof(int[16]) * MAXN); KS = calloc(MAXN, sizeof(*KS));
    FILE *pf = fopen(argv[3], "r"); char buf[512]; int np = 0, nbad = 0;
    while (np < MAXN && pf && fgets(buf, sizeof buf, pf)) {
        int m = 0, x, off; char *q = buf; uint64_t KU[12]; memset(KU, 0, sizeof KU); int okp = 1;
        while (sscanf(q, "%d%n", &x, &off) == 1 && m < 16) { q += off; int t = x - (side == 0 ? H : 0);
            int k = keyof(t); if ((KU[k >> 6] >> (k & 63)) & 1) okp = 0; KU[k >> 6] |= 1ULL << (k & 63); cand[np][m++] = t; }
        if (okp && m == 16) { memcpy(KS[np], KU, sizeof KU); np++; } else nbad++;
    }
    if (pf) fclose(pf);
    JB = malloc(sizeof(int) * 16 * (size_t)(np + 1)); HH = malloc(sizeof(int) * 16 * (size_t)(np + 1)); YY = malloc(sizeof(int) * 16 * (size_t)(np + 1));
    for (int u2 = 0; u2 < 22; u2++) for (int h = 0; h < 22; h++) hoff[u2][h] = ((h + u2) % 22) * 256;
    for (int i = 0; i < np; i++) for (int k = 0; k < 16; k++) { int t = cand[i][k], blk = t >> 8, j = blk / 22, h = blk % 22;
        JB[i * 16 + k] = j * 22 * 256; HH[i * 16 + k] = h; YY[i * 16 + k] = t & 255; }
    /* self-compat (stage 2 of orb) */
    Sb = calloc((size_t)np * W, 8);
    for (int i = 0; i < np; i++) { uint64_t *o = Sb + (size_t)i * W;
        for (int k = 0; k < 16; k++) { uint64_t *dd = d2 + (size_t)cand[i][k] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
    int *sc = malloc(4 * np), ns = 0;
    for (int i = 0; i < np; i++) { uint64_t *S = Sb + (size_t)i * W; int good = 1;
        for (int uu = 1; uu < 22 && good; uu++) { int hit = 0;
            for (int k = 0; k < 16 && !hit; k++) if (bit(S, shT[uu][cand[i][k]])) hit = 1;
            if (!hit) good = 0; }
        if (good) sc[ns++] = i; }
    printf("pool 16-key covers %d (dropped %d); self-compatible %d (%.4f)\n", np, nbad, ns, np ? (double)ns / np : 0.0);
    /* compat graph among self-compat covers */
    int CW = (ns + 63) / 64; uint64_t *C = calloc((size_t)ns * CW, 8); long ne = 0; int timeout = 0;
    for (int a = 0; a < ns && !timeout; a++) for (int b = a + 1; b < ns; b++) {
        if (compat(sc[a], sc[b])) { C[(size_t)a * CW + (b >> 6)] |= 1ULL << (b & 63); C[(size_t)b * CW + (a >> 6)] |= 1ULL << (a & 63); ne++; }
        if (now() - T0 > secs * 0.35) { timeout = 1; break; } }
    double dens = ns > 1 ? 2.0 * ne / ((double)ns * (ns - 1)) : 0;
    printf("compat pairs %ld of %ld: density %.4f%s (%.1fs)\n", ne, (long)ns * (ns - 1) / 2, dens, timeout ? " [TIMEOUT, partial]" : "", now() - T0);
    if (timeout) { printf("RESULT incomplete\n"); return 0; }
    /* clique upper bound: greedy colouring of C (chi >= omega); best of several orders, degree-descending */
    int *deg = malloc(4 * ns), *ord = malloc(4 * ns), *col = malloc(4 * ns); int bestUB = ns;
    for (int a = 0; a < ns; a++) { int d = 0; for (int w = 0; w < CW; w++) d += __builtin_popcountll(C[(size_t)a * CW + w]); deg[a] = d; ord[a] = a; }
    for (int trial = 0; trial < 5; trial++) {
        if (trial > 0) for (int a = ns - 1; a > 0; a--) { int b = rnd() % (a + 1); int t = ord[a]; ord[a] = ord[b]; ord[b] = t; }
        /* sort by degree descending on trial 0 */
        if (trial == 0) for (int a = 1; a < ns; a++) { int x = ord[a], b = a - 1; while (b >= 0 && deg[ord[b]] < deg[x]) { ord[b + 1] = ord[b]; b--; } ord[b + 1] = x; }
        int nc = 0; for (int a = 0; a < ns; a++) col[a] = -1;
        for (int oi = 0; oi < ns; oi++) { int v = ord[oi]; int used[ns + 1]; memset(used, 0, sizeof(int) * (nc + 1));
            /* colour c is forbidden if a neighbour in C has colour c (independent-set classes) */
            for (int x = 0; x < ns; x++) if (col[x] >= 0 && ((C[(size_t)v * CW + (x >> 6)] >> (x & 63)) & 1)) used[col[x]] = 1;
            int c = 0; while (c < nc && used[c]) c++; col[v] = c; if (c == nc) nc++; }
        if (nc < bestUB) bestUB = nc;
    }
    printf("greedy colouring upper bound on clique number (this pool): %d\n", bestUB);
    /* max clique: randomized greedy + plateau swaps, on sub-samples of size frac*ns */
    int *best = malloc(4 * (ns + 1)), nbest = 0, *cur = malloc(4 * (ns + 1)), ncur; int *inc = calloc(ns + 1, 4), *cnt = calloc(ns + 1, 4);
    int *bestsub = NULL; int nbestsub = 0;
    double fracs[4] = {0.25, 0.5, 0.75, 1.0};
    for (int fi = 0; fi < 4; fi++) {
        int m = (int)(fracs[fi] * ns); int *S = malloc(4 * (ns + 1)); /* random permutation of 0..ns-1; first m used */
        for (int a = 0; a < ns; a++) S[a] = a; for (int a = ns - 1; a > 0; a--) { int b = rnd() % (a + 1); int t = S[a]; S[a] = S[b]; S[b] = t; }
        int bsz = 0; int *bset = malloc(4 * (m + 1)); int nb_here = 0;
        double tl = T0 + secs * (0.45 + 0.13 * fi);
        while (now() < tl && m > 0) {
            ncur = 0; memset(inc, 0, 4 * (ns + 1)); memset(cnt, 0, 4 * (ns + 1));
            /* work on vertices S[0..m) only: cnt for non-S vertices is ignored */
            for (int it = 0; it < m; it++) { int v = S[rnd() % m]; if (inc[v] || cnt[v]) continue;
                inc[v] = 1; cur[ncur++] = v; for (int x = 0; x < ns; x++) if (x != v && !((C[(size_t)v * CW + (x >> 6)] >> (x & 63)) & 1)) cnt[x]++; }
            for (int rounds = 0; rounds < 20000 && now() < tl; rounds++) {
                int added = 0;
                for (int q = 0; q < m; q++) { int x = S[q]; if (!inc[x] && cnt[x] == 0) { inc[x] = 1; cur[ncur++] = x;
                    for (int y = 0; y < ns; y++) if (y != x && !((C[(size_t)x * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]++; added = 1; } }
                if (ncur > nb_here) { nb_here = ncur; memcpy(bset, cur, 4 * ncur); bsz = ncur; }
                if (added) continue;
                int x = -1; for (int s = 0; s < 400; s++) { int y = S[rnd() % m]; if (!inc[y] && cnt[y] == 1) { x = y; break; } }
                if (x < 0) break;
                int drop = -1; for (int a = 0; a < ncur; a++) { int mm = cur[a]; if (!((C[(size_t)x * CW + (mm >> 6)] >> (mm & 63)) & 1)) { drop = a; break; } }
                int mm = cur[drop]; inc[mm] = 0; cur[drop] = cur[--ncur];
                for (int y = 0; y < ns; y++) if (y != mm && !((C[(size_t)mm * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]--;
                inc[x] = 1; cur[ncur++] = x;
                for (int y = 0; y < ns; y++) if (y != x && !((C[(size_t)x * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]++;
            }
        }
        printf("sub-sample %.0f%% (%d covers): best clique %d (%.1fs)\n", fracs[fi] * 100, m, bsz, now() - T0);
        if (fracs[fi] == 1.0) { nbest = bsz; memcpy(best, bset, 4 * bsz); }
        free(S); free(bset);
    }
    /* output best packing: sorted pool-indices -> covers (global ids) */
    FILE *g = fopen(argv[6], "w");
    for (int a = 0; a < nbest; a++) { int i = sc[best[a]]; for (int k = 0; k < 16; k++) fprintf(g, "%d ", cand[i][k] + (side == 0 ? H : 0)); fprintf(g, "\n"); }
    fclose(g);
    printf("RESULT side %d best packing %d orbits = %d hubs; colouring UB %d orbits (pool-relative)\n", side, nbest, 22 * nbest, bestUB);
    return 0;
}
