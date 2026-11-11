/* orb: Z22-orbit hub packer (card d06). Adapted from director/hubpack.c.
 * A hub orbit on side S is a set N (<= 17 vertices of the other side T) with
 *   (1) ball3(N) = S (every S-vertex within distance 3 of N; holds for every translate since the shift is an automorphism),
 *   (2) the 22 translates N+t are pairwise disjoint: the keys (j,y) of N are distinct (key = j*256 + y, controller block 22j+h),
 *   (3) compat of orbits: for every u in Z22 some x' in M has sh_u(x') within distance 2 of N
 *       (covers N vs N+u, and N vs M+u for orbit pairs; orbits are key-disjoint: no key shared by two orbits).
 * usage: orb EDGES SIDE NCAND SECS SEED OUTCAND OUTORB [K]
 *   SIDE 0 = hubs on side A (N subset of B), SIDE 1 = hubs on side B.
 *   OUTCAND: all key-distinct candidate covers (global ids, one per line).
 *   OUTORB : chosen orbit base sets N (global ids, one per line); the 22 hubs are N+t, t = 0..21.
 */
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
static inline int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static inline int keyof(int t) { return ((t >> 8) / 22) * 256 + (t & 255); }
static inline int shl(int t, int u) { int blk = t >> 8; int j = blk / 22, h = blk % 22; return ((j * 22 + (h + u) % 22) << 8) | (t & 255); }
static inline int bit(const uint64_t *a, int t) { return (a[t >> 6] >> (t & 63)) & 1; }

#define MAXC 40000
static int (*cand)[17];
static int *csz;
static uint64_t (*KS)[12];      /* key set of candidate, 768 bits */
static uint64_t *Sb;            /* S_N bitsets over T, W words each */

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: orb EDGES SIDE NCAND SECS SEED OUTCAND OUTORB [K]\n"); return 2; }
    int side = atoi(argv[2]), NC = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int KD = argc > 8 ? atoi(argv[8]) : 6;
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
    /* lines (as hubpack): K best directions per controller vertex */
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    int nl = 0; int (*lines)[4] = malloc(sizeof(int[4]) * 66 * KD * 64); uint64_t tmp[W];
    for (int cv = 0; cv < 66; cv++) {
        double sc[85];
        for (int di = 0; di < nd; di++) { long tot = 0;
            for (int s = 0; s < 8; s++) { int y = rnd() & 255; memset(tmp, 0, sizeof tmp);
                for (int l = 0; l < 4; l++) { int t = cv * 256 + (y ^ scal(l, dirs[di])); uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) tmp[w] |= bl[w]; }
                tot += popw(tmp); }
            sc[di] = tot / 8.0; }
        for (int k = 0; k < KD; k++) { int bi = 0; for (int di = 1; di < nd; di++) if (sc[di] > sc[bi]) bi = di; sc[bi] = -1;
            int c = dirs[bi], seen[256] = {0};
            for (int y = 0; y < 256; y++) if (!seen[y]) { for (int l = 0; l < 4; l++) { int z = y ^ scal(l, c); seen[z] = 1; lines[nl][l] = cv * 256 + z; } nl++; } }
    }
    uint64_t *lball = malloc((size_t)nl * W * 8);
    for (int i = 0; i < nl; i++) { uint64_t *o = lball + (size_t)i * W; memset(o, 0, W * 8);
        for (int l = 0; l < 4; l++) { uint64_t *bl = ball + (size_t)lines[i][l] * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; } }
    fprintf(stderr, "setup %.2fs, %d lines\n", now() - t0, nl);
    /* stage 1: key-distinct covers */
    cand = malloc(sizeof(int[17]) * MAXC); csz = malloc(4 * MAXC); KS = calloc(MAXC, sizeof(*KS));
    int nc = 0; long tries = 0, fails = 0;
    uint64_t full[W]; for (int w = 0; w < W; w++) full[w] = ~0ULL; full[W - 1] = (H % 64 == 0) ? ~0ULL : ((1ULL << (H % 64)) - 1) ;
    /* W*64 = 16896 exactly, so all words full */
    for (int w = 0; w < W; w++) full[w] = ~0ULL;
    if (argc > 9) { /* preload covers (global ids, one per line) from an earlier run; keys re-checked */
        FILE *pf = fopen(argv[9], "r"); char buf[512];
        while (pf && nc < MAXC && fgets(buf, sizeof buf, pf)) { int m = 0; char *q = buf; int x, off;
            uint64_t KU2[12]; memset(KU2, 0, sizeof KU2); int okp = 1;
            while (sscanf(q, "%d%n", &x, &off) == 1 && m < 17) { q += off; int t = x - (side == 0 ? H : 0);
                int k = keyof(t); if ((KU2[k >> 6] >> (k & 63)) & 1) okp = 0; KU2[k >> 6] |= 1ULL << (k & 63); cand[nc][m++] = t; }
            if (okp && m > 0) { csz[nc] = m; memcpy(KS[nc], KU2, sizeof KU2); nc++; } }
        if (pf) fclose(pf);
        fprintf(stderr, "preloaded %d covers\n", nc);
    }
    int npre = nc;
    while (nc - npre < NC && nc < MAXC && now() - t0 < secs * 0.45) {
        tries++;
        uint64_t unc[W]; memcpy(unc, full, sizeof unc);
        int ch[5], nch = 0; uint64_t KU[12]; memset(KU, 0, sizeof KU); int ok = 0;
        #define LFREE(i) ({ int _f = 1; for (int _l = 0; _l < 4 && _f; _l++) { int _k = keyof(lines[i][_l]); if ((KU[_k >> 6] >> (_k & 63)) & 1) _f = 0; } _f; })
        #define LADD(i) do { for (int _l = 0; _l < 4; _l++) { int _k = keyof(lines[i][_l]); KU[_k >> 6] |= 1ULL << (_k & 63); } ch[nch++] = (i); } while (0)
        int first; do { first = rnd() % nl; } while (!LFREE(first));
        LADD(first); { uint64_t *o = lball + (size_t)first * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w]; }
        for (int step = 1; step < 4; step++) {
            int best = -1, bg = -1;
            for (int s = 0; s < 3000; s++) { int i = rnd() % nl; if (!LFREE(i)) continue;
                uint64_t *o = lball + (size_t)i * W; int g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & o[w]);
                if (g > bg) { bg = g; best = i; } }
            if (best < 0) break;
            LADD(best); uint64_t *o = lball + (size_t)best * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w];
            if (popw(unc) == 0) { ok = 1; break; }
        }
        if (!ok && nch == 4) {
            int extra = -1;
            for (int s = 0; s < 6000 && extra < 0; s++) { int t = rnd() % H; int k = keyof(t);
                if ((KU[k >> 6] >> (k & 63)) & 1) continue;
                uint64_t *bl = ball + (size_t)t * W; int cov = 1;
                for (int w = 0; w < W; w++) if (unc[w] & ~bl[w]) { cov = 0; break; }
                if (cov) extra = t; }
            if (extra >= 0) { ok = 1; int k = keyof(extra); KU[k >> 6] |= 1ULL << (k & 63); }
            if (ok) { /* store with extra */
                int m = 0; for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) cand[nc][m++] = lines[ch[a]][y];
                cand[nc][m++] = extra; csz[nc] = m; memcpy(KS[nc], KU, sizeof KU); nc++; continue; }
        }
        if (!ok) { fails++; continue; }
        int m = 0; for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) cand[nc][m++] = lines[ch[a]][y];
        csz[nc] = m; memcpy(KS[nc], KU, sizeof KU); nc++;
    }
    fprintf(stderr, "stage1: %d key-distinct covers from %ld tries (%.1fs)\n", nc, tries, now() - t0);
    /* outputs candidates */
    FILE *oc = fopen(argv[6], "w");
    for (int i = 0; i < nc; i++) { for (int k = 0; k < csz[i]; k++) fprintf(oc, "%d ", cand[i][k] + (side == 0 ? H : 0)); fprintf(oc, "\n"); }
    fclose(oc);
    /* stage 2: S_N and self-compatibility (N vs N+u, u = 1..21) */
    Sb = calloc((size_t)nc * W, 8);
    for (int i = 0; i < nc; i++) { uint64_t *o = Sb + (size_t)i * W;
        for (int k = 0; k < csz[i]; k++) { uint64_t *dd = d2 + (size_t)cand[i][k] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
    int *ok2 = malloc(4 * nc), n2 = 0, *map = malloc(4 * nc);
    for (int i = 0; i < nc; i++) {
        uint64_t *S = Sb + (size_t)i * W; int good = 1;
        for (int uu = 1; uu < 22 && good; uu++) { int hit = 0;
            for (int k = 0; k < csz[i] && !hit; k++) if (bit(S, shT[uu][cand[i][k]])) hit = 1;
            if (!hit) good = 0; }
        ok2[i] = good; if (good) map[n2++] = i;
    }
    fprintf(stderr, "stage2: %d / %d self-compatible orbits (%.1fs)\n", n2, nc, now() - t0);
    /* compatibility graph among self-compatible orbits: all 22 shifts, key-disjoint */
    int CW = (n2 + 63) / 64; uint64_t *C = calloc((size_t)n2 * CW, 8); long ne = 0;
    for (int a = 0; a < n2; a++) { int i = map[a]; uint64_t *S = Sb + (size_t)i * W;
        for (int b = a + 1; b < n2; b++) { int j = map[b];
            int dis = 1; for (int w = 0; w < 12; w++) if (KS[i][w] & KS[j][w]) { dis = 0; break; }
            if (!dis) continue;
            int cov = 0; /* bitmask of shifts covered */
            uint32_t covm = 0; const uint32_t full22 = (1u << 22) - 1;
            for (int k = 0; k < csz[j] && covm != full22; k++) for (int uu = 0; uu < 22; uu++)
                if (!((covm >> uu) & 1) && bit(S, shT[uu][cand[j][k]])) covm |= 1u << uu;
            cov = covm == full22;
            if (cov) { C[(size_t)a * CW + (b >> 6)] |= 1ULL << (b & 63); C[(size_t)b * CW + (a >> 6)] |= 1ULL << (a & 63); ne++; }
            if (now() - t0 > secs) goto stage3_end_early;
        }
    }
stage3_end_early:
    fprintf(stderr, "compat edges %ld density %.4f (%.1fs)\n", ne, n2 > 1 ? 2.0 * ne / ((double)n2 * (n2 - 1)) : 0.0, now() - t0);
    /* max clique: randomized greedy + plateau swaps */
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
    FILE *g = fopen(argv[7], "w");
    for (int a = 0; a < nbest; a++) { int i = map[best[a]]; for (int k = 0; k < csz[i]; k++) fprintf(g, "%d ", cand[i][k] + (side == 0 ? H : 0)); fprintf(g, "\n"); }
    fclose(g);
    printf("side %d covers %d selfcompat %d best orbit packing %d orbits = %d hubs\n", side, nc, n2, nbest, 22 * nbest);
    return 0;
}
