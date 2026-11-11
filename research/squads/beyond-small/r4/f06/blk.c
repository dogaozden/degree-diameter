/* growb (card e02, round 3): adaptive Z22-orbit growth on side B.
 * B-hub orbit base N is a set of <= 17 A-vertices (global id < H) with
 *   (1) ball3(N) = B, (2) keys (j,y) of N distinct, (3) N vs N+u self-compatible (u != 0),
 *   (4) N vs M+s compatible for every fixed/accepted B-orbit M and every shift s (d2(N) hits M+s for all s),
 *   (5) key-disjoint from every accepted B-orbit.
 * A-side orbits (N in B) never interact with these (disjoint vertex sets), so they are left untouched.
 * Rounds: sample R random key-free 4-line covers (+1 vertex if needed), keep those compatible with the current
 * packing, find a max clique (randomized greedy + plateau) among them, add it, repeat with the new packing.
 * usage: growb EDGES FIXED_B OUT_B SECS SEED [KD=6] [R=4000]
 *   FIXED_B: one B-orbit base per line (global A ids). OUT_B: all B-orbit bases (fixed + added), one per line.
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
static int shT[22][H];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static inline int keyof(int t) { return ((t >> 8) / 22) * 256 + (t & 255); }
static inline int shl(int t, int u) { int blk = t >> 8; int j = blk / 22, h = blk % 22; return ((j * 22 + (h + u) % 22) << 8) | (t & 255); }
static int (*lines)[4];
static inline void lor(int i, uint64_t *o) { memset(o, 0, W * 8);
    for (int l = 0; l < 4; l++) { uint64_t *bl = ball + (size_t)lines[i][l] * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; } }
static inline int bit(const uint64_t *a, int t) { return (a[t >> 6] >> (t & 63)) & 1; }

#define MAXC 30000
static int cand[MAXC][17], csz[MAXC];
static uint64_t KS[MAXC][12];   /* key bitset of each pool entry (768 bits) */
static uint64_t *Sb;           /* union of d2 over N, W words per entry */
static int isCur[MAXC];        /* 1 = member of the current packing */
static uint64_t KG[12];        /* keys used by the current packing */
static int npool = 0;

/* M compat with N (both pool entries): key-disjoint and d2(N) hits M+s for all 22 shifts s */
static int compat(int i, int j) {
    for (int w = 0; w < 12; w++) if (KS[i][w] & KS[j][w]) return 0;
    const uint64_t *S = Sb + (size_t)i * W;
    uint32_t covm = 0; const uint32_t full22 = (1u << 22) - 1;
    for (int k = 0; k < csz[j] && covm != full22; k++)
        for (int uu = 0; uu < 22; uu++)
            if (!((covm >> uu) & 1) && bit(S, shT[uu][cand[j][k]])) covm |= 1u << uu;
    return covm == full22;
}
/* self compatibility: N vs N+u for u = 1..21 */
static int selfcompat(int i) {
    const uint64_t *S = Sb + (size_t)i * W;
    for (int uu = 1; uu < 22; uu++) { int hit = 0;
        for (int k = 0; k < csz[i] && !hit; k++) if (bit(S, shT[uu][cand[i][k]])) hit = 1;
        if (!hit) return 0; }
    return 1;
}
static void addkeys(uint64_t *K, int i) { for (int k = 0; k < csz[i]; k++) { int kk = keyof(cand[i][k]); K[kk >> 6] |= 1ULL << (kk & 63); } }

static inline int lfree(int i, const uint64_t *KU) { for (int l = 0; l < 4; l++) if (bit(KU, keyof(lines[i][l]))) return 0; return 1; }
static inline void ladd(int i, uint64_t *KU) { for (int l = 0; l < 4; l++) { int k = keyof(lines[i][l]); KU[k >> 6] |= 1ULL << (k & 63); } }
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: growb EDGES FIXED_B OUT_B SECS SEED [KD] [R]\n"); return 2; }
    double secs = atof(argv[4]);
    rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int KD = argc > 6 ? atoi(argv[6]) : 6;
    long R = argc > 7 ? atol(argv[7]) : 4000;
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (!f || fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    /* side B hubs: T = A (N subset of A), S = B. */
    int (*adjT)[16] = adjA, (*adjS)[16] = adjB;
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
    /* lines: 4 vertices of one controller block, affine fibre lines in direction dirs[] (as orb.c) */
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    int nl = 0; lines = malloc(sizeof(int[4]) * 66 * KD * 64); uint64_t tmp[W];
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
    fprintf(stderr, "setup %.2fs, %d lines\n", now() - t0, nl);
    uint64_t full[W]; for (int w = 0; w < W; w++) full[w] = ~0ULL;

    Sb = calloc((size_t)MAXC * W, 8);
    /* load fixed B-orbits */
    FILE *ff = fopen(argv[2], "r"); char buf[1024];
    int nfix = 0;
    while (ff && fgets(buf, sizeof buf, ff)) {
        int m = 0; char *q = buf; int x, off; int ok = 1; uint64_t K[12]; memset(K, 0, sizeof K);
        while (sscanf(q, "%d%n", &x, &off) == 1) { q += off; if (x < 0 || x >= H) { ok = 0; break; }
            if (m >= 17) { ok = 0; break; }
            int k = keyof(x); if (bit(K, k)) ok = 0; K[k >> 6] |= 1ULL << (k & 63); cand[npool][m++] = x; }
        if (!ok || m == 0) continue;
        csz[npool] = m; memcpy(KS[npool], K, sizeof K);
        for (int k = 0; k < m; k++) { uint64_t *dd = d2 + (size_t)cand[npool][k] * W; uint64_t *o = Sb + (size_t)npool * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; }
        isCur[npool] = 1; npool++; nfix++;
    }
    if (ff) fclose(ff);
    for (int i = 0; i < npool; i++) { if (!selfcompat(i)) fprintf(stderr, "fixed %d not self-compatible\n", i); addkeys(KG, i); }
    int bad = 0; for (int i = 0; i < npool; i++) for (int j = i + 1; j < npool; j++) if (!compat(i, j) || !compat(j, i)) bad++;
    fprintf(stderr, "loaded %d fixed B-orbits, pairwise incompatible pairs: %d\n", nfix, bad);
    /* ---- conflict scoring (f06): for each kept orbit k, sample covers key-free w.r.t. packing minus k and compatible
       with the rest. sc1[k] = covers blocked by k alone (dropping k would admit them); sc0[k] = covers compatible with all. */
    int np0 = npool;
    int *sc1 = calloc(np0 + 1, sizeof(int)), *sc0 = calloc(np0 + 1, sizeof(int));
    double tb = now();
    for (int k = 0; k < np0; k++) {
        uint64_t KO[12]; memset(KO, 0, sizeof KO);
        for (int q = 0; q < np0; q++) if (q != k) for (int w = 0; w < 12; w++) KO[w] |= KS[q][w];
        for (long tr = 0; tr < R; tr++) {
            uint64_t KU[12]; memcpy(KU, KO, sizeof KU);
            int chosen[5], nch = 0, okc = 0, guard = 0, first;
            uint64_t om[W], unc[W]; memcpy(unc, full, sizeof unc);
            do { first = rnd() % nl; } while (!lfree(first, KU) && ++guard < 100000);
            if (guard >= 100000) continue;
            ladd(first, KU); chosen[nch++] = first; lor(first, om); for (int w = 0; w < W; w++) unc[w] &= ~om[w];
            okc = (popw(unc) == 0);
            for (int step = 1; step < 4 && !okc; step++) {
                int best = -1; long bg = -1;
                for (int s = 0; s < 3000; s++) { int i = rnd() % nl; if (!lfree(i, KU)) continue;
                    lor(i, om); long g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & om[w]);
                    if (g > bg) { bg = g; best = i; } }
                if (best < 0) break;
                ladd(best, KU); chosen[nch++] = best; lor(best, om); for (int w = 0; w < W; w++) unc[w] &= ~om[w];
                if (popw(unc) == 0) okc = 1;
            }
            int extra = -1;
            if (!okc && nch == 4) {
                for (int s = 0; s < 6000 && extra < 0; s++) { int t = rnd() % H; int kk = keyof(t);
                    if (bit(KU, kk)) continue;
                    uint64_t *bl = ball + (size_t)t * W; int cov = 1;
                    for (int w = 0; w < W; w++) if (unc[w] & ~bl[w]) { cov = 0; break; }
                    if (cov) extra = t; }
                if (extra >= 0) okc = 1;
            }
            if (!okc) continue;
            int p = np0, m = 0;
            for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) cand[p][m++] = lines[chosen[a]][y];
            if (extra >= 0) cand[p][m++] = extra;
            csz[p] = m; memset(KS[p], 0, sizeof KS[p]);
            for (int q = 0; q < m; q++) { int kk = keyof(cand[p][q]); KS[p][kk >> 6] |= 1ULL << (kk & 63); }
            { uint64_t *o = Sb + (size_t)p * W; memset(o, 0, W * 8);
              for (int q = 0; q < m; q++) { uint64_t *dd = d2 + (size_t)cand[p][q] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
            if (!selfcompat(p)) continue;
            int ok = 1;
            for (int q = 0; q < np0 && ok; q++) if (q != k && !(compat(p, q) && compat(q, p))) ok = 0;
            if (!ok) continue;
            if (!(compat(p, k) && compat(k, p))) sc1[k]++; else sc0[k]++;
        }
    }
    fprintf(stderr, "scoring %d orbits, R=%ld each: %.1fs\n", np0, R, now() - tb);
    FILE *of = fopen(argv[3], "w");
    for (int k = 0; k < np0; k++) fprintf(of, "%d %d %d\n", k, sc1[k], sc0[k]);
    fclose(of);
    printf("orbits %d (loaded)\n", np0);
    return 0;
}
