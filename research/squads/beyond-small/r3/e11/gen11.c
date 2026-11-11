/* gen11: enlarged candidate space for Z22-orbit bases (card e11).
 * Compared with r2/d06/orb.c (4 lines drawn from the 6 best directions per controller block), lines here are drawn
 * from ALL 85 directions of PG(3,4) on the fly (no 758 MB table), in three generation modes that are pooled together:
 *   mode 0 (free)     : 4 lines, each drawn from any block and any direction (gain-greedy over random samples);
 *   mode 1 (sameblk)  : first two lines share one controller block with different directions (keys stay distinct);
 *   mode 2 (fibre)    : all lines of the cover lie in one fibre (blocks cv with cv/22 = j fixed, the 22 h-blocks),
 *                       with pairwise different directions where possible, i.e. directions mixed inside one fibre.
 * Each cover: key-distinct 4 lines (+1 extra vertex if needed to cover the whole side), as in orb.c stage 1.
 * Stage 2/3: self-compatibility (N vs N+u) and pair compatibility (N vs M+u for all u), then clique search.
 * usage: gen11 EDGES SIDE NPER SECS SEED OUTCAND OUTORB
 *   NPER: candidate covers per mode; SIDE 0 = hubs on side A (N subset of B), SIDE 1 = hubs on side B.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define H 16896
#define W 264
#define NM 3
static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static uint64_t *ball, *d2;
static int (*adjT)[16], (*adjS)[16];
static int shT[22][H];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static inline int keyof(int t) { return ((t >> 8) / 22) * 256 + (t & 255); }
static inline int shl(int t, int u) { int blk = t >> 8; int j = blk / 22, h = blk % 22; return ((j * 22 + (h + u) % 22) << 8) | (t & 255); }
static inline int bit(const uint64_t *a, int t) { return (a[t >> 6] >> (t & 63)) & 1; }

static int dirs[85], nd = 0;
static int MAXC;
static int (*cand)[17];
static int *csz, *cmode;
static uint64_t (*KS)[12];
static uint64_t *Sb;

/* line = (cv, di, y): 4 vertices cv*256 + (y ^ scal(l, dirs[di])) */
static inline void lineverts(int cv, int di, int y, int *out) { for (int l = 0; l < 4; l++) out[l] = cv * 256 + (y ^ scal(l, dirs[di])); }
static inline void lineball(const int *vs, uint64_t *tmp) { memset(tmp, 0, W * 8);
    for (int l = 0; l < 4; l++) { const uint64_t *bl = ball + (size_t)vs[l] * W; for (int w = 0; w < W; w++) tmp[w] |= bl[w]; } }
static inline int lfree(const int *vs, const uint64_t *KU) { for (int l = 0; l < 4; l++) { int k = keyof(vs[l]); if ((KU[k >> 6] >> (k & 63)) & 1) return 0; } return 1; }
static inline void ladd(const int *vs, uint64_t *KU) { for (int l = 0; l < 4; l++) { int k = keyof(vs[l]); KU[k >> 6] |= 1ULL << (k & 63); } }

/* draw a random line according to pool type: 0 any block, 1 block cv0 (dir != di0), 2 fibre j0 (dir != di0 preferred) */
static void drawline(int type, int cv0, int di0, int j0, int *cv, int *di, int *y) {
    if (type == 0) { *cv = rnd() % 66; *di = rnd() % nd; }
    else if (type == 1) { *cv = cv0; do { *di = rnd() % nd; } while (*di == di0); }
    else { *cv = 22 * j0 + rnd() % 22; do { *di = rnd() % nd; } while (*di == di0 && (rnd() & 3)); }
    *y = rnd() & 255;
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: gen11 EDGES SIDE NPER SECS SEED OUTCAND OUTORB\n"); return 2; }
    int side = atoi(argv[2]), NPER = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    MAXC = NPER * NM + 10;
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    adjT = side == 0 ? adjB : adjA; adjS = side == 0 ? adjA : adjB;
    for (int u2 = 0; u2 < 22; u2++) for (int t = 0; t < H; t++) shT[u2][t] = shl(t, u2);
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
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    fprintf(stderr, "setup %.2fs, %d directions\n", now() - t0, nd);

    /* stage 1: candidate covers in three modes */
    cand = malloc(sizeof(int[17]) * MAXC); csz = malloc(4 * MAXC); cmode = malloc(4 * MAXC); KS = calloc(MAXC, sizeof(*KS));
    int nc = 0; long tries[NM] = {0}, fails[NM] = {0}, made[NM] = {0};
    uint64_t full[W]; for (int w = 0; w < W; w++) full[w] = ~0ULL;
    uint64_t lb[W], unc[W];
    const int SAMP = 1500;
    int mask = argc > 8 ? atoi(argv[8]) : 7;
    for (int mode = 0; mode < NM; mode++) {
        int target = (mask >> mode) & 1 ? NPER : 0;
        while (made[mode] < target && now() - t0 < secs * 0.5) {
            tries[mode]++;
            memcpy(unc, full, sizeof unc);
            uint64_t KU[12]; memset(KU, 0, sizeof KU);
            int lv[5][4], lcv[5], ldi[5], nl = 0, ok = 0;
            int cv0 = 0, di0 = 0, j0 = 0, y0 = 0;
            /* first line: any */
            { int tmp4[4]; do { drawline(0, 0, 0, 0, &cv0, &di0, &y0); lineverts(cv0, di0, y0, tmp4); } while (!lfree(tmp4, KU));
              memcpy(lv[0], tmp4, sizeof tmp4); lcv[0] = cv0; ldi[0] = di0; ladd(lv[0], KU); nl = 1;
              lineball(lv[0], lb); for (int w = 0; w < W; w++) unc[w] &= ~lb[w]; j0 = cv0 / 22; }
            for (int step = 1; step < 4; step++) {
                int ptype = mode == 0 ? 0 : mode == 1 ? (step == 1 ? 1 : 0) : 2;
                int bg = -1, bcv = 0, bdi = 0, by = 0, bvs[4];
                for (int s = 0; s < SAMP; s++) {
                    int cv, di, y, vs[4]; drawline(ptype, cv0, di0, j0, &cv, &di, &y);
                    lineverts(cv, di, y, vs); if (!lfree(vs, KU)) continue;
                    lineball(vs, lb); int g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & lb[w]);
                    if (g > bg) { bg = g; bcv = cv; bdi = di; by = y; memcpy(bvs, vs, sizeof vs); }
                }
                if (bg < 0) break;
                if (step == 1 && mode == 1) { cv0 = cv0; }
                memcpy(lv[nl], bvs, sizeof bvs); lcv[nl] = bcv; ldi[nl] = bdi; ladd(lv[nl], KU); nl++;
                lineball(bvs, lb); for (int w = 0; w < W; w++) unc[w] &= ~lb[w];
                if (step == 1 && mode == 1) { /* keep second line in block cv0 but nothing else changes */ }
                (void)by;
                int any = 0; for (int w = 0; w < W; w++) if (unc[w]) { any = 1; break; }
                if (!any) { ok = 1; break; }
            }
            int m = 0;
            if (!ok) {
                /* extra single vertex covering the rest (orb.c style): 4 lines + 1 vertex */
                int any = 0; for (int w = 0; w < W; w++) if (unc[w]) { any = 1; break; }
                if (any && nl == 4) {
                    int extra = -1;
                    for (int s = 0; s < 6000 && extra < 0; s++) { int t = rnd() % H; int k = keyof(t);
                        if ((KU[k >> 6] >> (k & 63)) & 1) continue;
                        uint64_t *bl = ball + (size_t)t * W; int cov = 1;
                        for (int w = 0; w < W; w++) if (unc[w] & ~bl[w]) { cov = 0; break; }
                        if (cov) extra = t; }
                    if (extra >= 0) { ok = 1; int k = keyof(extra); KU[k >> 6] |= 1ULL << (k & 63); cand[nc][16] = extra; m = 17; }
                }
                if (!ok) { fails[mode]++; continue; }
            } else m = 0;
            int base = 0;
            for (int a = 0; a < nl; a++) for (int y = 0; y < 4; y++) cand[nc][base++] = lv[a][y];
            if (m == 17) { cand[nc][16] = cand[nc][16]; csz[nc] = 17; }
            else csz[nc] = base;
            /* ensure key-distinctness and the d2-union covers, then store */
            memcpy(KS[nc], KU, sizeof KU); cmode[nc] = mode; made[mode]++; nc++;
            if (nc >= MAXC) break;
        }
    }
    fprintf(stderr, "stage1: %d covers (", nc); for (int mo = 0; mo < NM; mo++) fprintf(stderr, " mode%d %ld/%ld", mo, made[mo], tries[mo]); fprintf(stderr, " ) %.1fs\n", now() - t0);
    FILE *oc = fopen(argv[6], "w");
    for (int i = 0; i < nc; i++) { for (int k = 0; k < csz[i]; k++) fprintf(oc, "%d ", cand[i][k] + (side == 0 ? H : 0)); fprintf(oc, "%d\n", cmode[i]); }
    fclose(oc);

    /* stage 2: self-compatibility */
    Sb = calloc((size_t)nc * W, 8);
    for (int i = 0; i < nc; i++) { uint64_t *o = Sb + (size_t)i * W;
        for (int k = 0; k < csz[i]; k++) { uint64_t *dd = d2 + (size_t)cand[i][k] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
    int *map = malloc(4 * nc), n2 = 0; long selfm[NM] = {0}, totm[NM] = {0};
    for (int i = 0; i < nc; i++) {
        uint64_t *S = Sb + (size_t)i * W; int good = 1;
        for (int uu = 1; uu < 22 && good; uu++) { int hit = 0;
            for (int k = 0; k < csz[i] && !hit; k++) if (bit(S, shT[uu][cand[i][k]])) hit = 1;
            if (!hit) good = 0; }
        totm[cmode[i]]++;
        if (good) { map[n2++] = i; selfm[cmode[i]]++; }
    }
    fprintf(stderr, "stage2: self-compatible per mode:"); for (int mo = 0; mo < NM; mo++) fprintf(stderr, " m%d %ld/%ld (%.3f)", mo, selfm[mo], totm[mo], totm[mo] ? (double)selfm[mo] / totm[mo] : 0.0); fprintf(stderr, " total %d (%.1fs)\n", n2, now() - t0);

    /* stage 3: pair compatibility among self-compatible covers (keys disjoint, N vs M+u for all 22 u) */
    int CW = (n2 + 63) / 64; uint64_t *C = calloc((size_t)n2 * CW, 8); long ne = 0; long dsum[NM] = {0}, dpairs[NM] = {0};
    const uint32_t full22 = (1u << 22) - 1;
    for (int a = 0; a < n2; a++) { int i = map[a]; uint64_t *S = Sb + (size_t)i * W;
        for (int b = a + 1; b < n2; b++) { int j = map[b];
            int dis = 1; for (int w = 0; w < 12; w++) if (KS[i][w] & KS[j][w]) { dis = 0; break; }
            if (!dis) continue;
            uint32_t covm = 0;
            for (int k = 0; k < csz[j] && covm != full22; k++) for (int uu = 0; uu < 22; uu++)
                if (!((covm >> uu) & 1) && bit(S, shT[uu][cand[j][k]])) covm |= 1u << uu;
            if (covm == full22) { C[(size_t)a * CW + (b >> 6)] |= 1ULL << (b & 63); C[(size_t)b * CW + (a >> 6)] |= 1ULL << (a & 63); ne++;
                int mi = cmode[i], mj = cmode[j]; (void)mi; (void)mj; }
            dpairs[0]++;
            if (now() - t0 > secs * 0.8) goto stage4;
        }
    }
stage4:
    fprintf(stderr, "compat edges %ld density %.4f (%.1fs)\n", ne, n2 > 1 ? 2.0 * ne / ((double)n2 * (n2 - 1)) : 0.0, now() - t0);
    /* stage 4: randomized greedy clique with plateau swaps */
    int *best = malloc(4 * (n2 + 1)), nbest = 0, *cur = malloc(4 * (n2 + 1)), ncur; int *inc = calloc(n2 + 1, 4), *cnt = calloc(n2 + 1, 4);
    while (now() - t0 < secs && n2 > 0) {
        ncur = 0; memset(inc, 0, 4 * n2); for (int i = 0; i < n2; i++) cnt[i] = 0;
        for (int it = 0; it < n2; it++) { int v = rnd() % n2; if (inc[v] || cnt[v]) continue;
            inc[v] = 1; cur[ncur++] = v; for (int x = 0; x < n2; x++) if (x != v && !((C[(size_t)v * CW + (x >> 6)] >> (x & 63)) & 1)) cnt[x]++; }
        for (int rounds = 0; rounds < 20000 && now() - t0 < secs; rounds++) {
            int added = 0;
            for (int x = 0; x < n2; x++) if (!inc[x] && cnt[x] == 0) { inc[x] = 1; cur[ncur++] = x;
                for (int y = 0; y < n2; y++) if (y != x && !((C[(size_t)x * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]++; added = 1; }
            if (ncur > nbest) { nbest = ncur; memcpy(best, cur, 4 * ncur); fprintf(stderr, "clique %d (%.1fs)\n", nbest, now() - t0); }
            if (added) continue;
            int x = -1; for (int s = 0; s < 200; s++) { int y = rnd() % n2; if (!inc[y] && cnt[y] == 1) { x = y; break; } }
            if (x < 0) break;
            int drop = -1; for (int a = 0; a < ncur; a++) { int m = cur[a]; if (!((C[(size_t)x * CW + (m >> 6)] >> (m & 63)) & 1)) { drop = a; break; } }
            int m = cur[drop]; inc[m] = 0; cur[drop] = cur[--ncur];
            for (int y = 0; y < n2; y++) if (y != m && !((C[(size_t)m * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]--;
            inc[x] = 1; cur[ncur++] = x;
            for (int y = 0; y < n2; y++) if (y != x && !((C[(size_t)x * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]++;
        }
    }
    FILE *g = fopen(argv[7], "w"); int mc[NM] = {0};
    for (int a = 0; a < nbest; a++) { int i = map[best[a]]; mc[cmode[i]]++; for (int k = 0; k < csz[i]; k++) fprintf(g, "%d ", cand[i][k] + (side == 0 ? H : 0)); fprintf(g, "\n"); }
    fclose(g);
    printf("side %d covers %d selfcompat %d best orbit packing %d orbits = %d hubs (by mode %d/%d/%d)\n", side, nc, n2, nbest, 22 * nbest, mc[0], mc[1], mc[2]);
    return 0;
}
