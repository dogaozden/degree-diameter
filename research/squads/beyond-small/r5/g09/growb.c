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

    /* alive: candidate pool entries compatible with the current packing (not in it) */
    int *alive = malloc(sizeof(int) * MAXC); int nalive = 0;
    int ncur = nfix; int round = 0;
    int best_ncur = ncur;
    while (now() - t0 < secs) {
        round++;
        /* 1. sample R covers */
        int added_here = 0; long cnt_okc = 0, cnt_self = 0, cnt_good = 0;
        for (long tr = 0; tr < R && now() - t0 < secs && npool < MAXC; tr++) {
            int ch[5], nch = 0; uint64_t KU[12]; memcpy(KU, KG, sizeof KU); int okc = 0;
            uint64_t unc[W]; memcpy(unc, full, sizeof unc);
            #define LFREE(i) ({ int _f = 1; for (int _l = 0; _l < 4 && _f; _l++) { int _k = keyof(lines[i][_l]); if ((KU[_k >> 6] >> (_k & 63)) & 1) _f = 0; } _f; })
            #define LADD(i) do { for (int _l = 0; _l < 4; _l++) { int _k = keyof(lines[i][_l]); KU[_k >> 6] |= 1ULL << (_k & 63); } ch[nch++] = (i); } while (0)
            int first, guard = 0; do { first = rnd() % nl; } while (!LFREE(first) && ++guard < 100000);
            if (guard >= 100000) break;
            uint64_t om[W];
            LADD(first); lor(first, om); for (int w = 0; w < W; w++) unc[w] &= ~om[w];
            for (int step = 1; step < 4; step++) {
                int best = -1, bg = -1;
                for (int s = 0; s < 3000; s++) { int i = rnd() % nl; if (!LFREE(i)) continue;
                    lor(i, om); int g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & om[w]);
                    if (g > bg) { bg = g; best = i; } }
                if (best < 0) break;
                LADD(best); lor(best, om); for (int w = 0; w < W; w++) unc[w] &= ~om[w];
                if (popw(unc) == 0) { okc = 1; break; }
            }
            int extra = -1;
            if (!okc && nch == 4) {
                for (int s = 0; s < 6000 && extra < 0; s++) { int t = rnd() % H; int k = keyof(t);
                    if ((KU[k >> 6] >> (k & 63)) & 1) continue;
                    uint64_t *bl = ball + (size_t)t * W; int cov = 1;
                    for (int w = 0; w < W; w++) if (unc[w] & ~bl[w]) { cov = 0; break; }
                    if (cov) extra = t; }
                if (extra >= 0) { okc = 1; int k = keyof(extra); KU[k >> 6] |= 1ULL << (k & 63); }
            }
            cnt_okc += okc;
            if (!okc) continue;
            int p = npool; int m = 0;
            for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) cand[p][m++] = lines[ch[a]][y];
            if (extra >= 0) cand[p][m++] = extra;
            csz[p] = m; memcpy(KS[p], KU, sizeof KU); /* KU includes KG: keep only cover keys */
            memset(KS[p], 0, sizeof KS[p]); for (int k = 0; k < m; k++) { int kk = keyof(cand[p][k]); KS[p][kk >> 6] |= 1ULL << (kk & 63); }
            { uint64_t *o = Sb + (size_t)p * W; memset(o, 0, W * 8);
              for (int k = 0; k < m; k++) { uint64_t *dd = d2 + (size_t)cand[p][k] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
            if (!selfcompat(p)) continue;
            cnt_self++;
            isCur[p] = 0;
            /* compatible with every member of the packing (keys already free by construction) */
            int good = 1;
            for (int q2 = 0; q2 < npool && good; q2++) if (isCur[q2] && !(compat(p, q2) && compat(q2, p))) good = 0;
            if (!good) continue;
            cnt_good++;
            npool++; alive[nalive++] = p;
        }
        /* 2. compat graph among alive and max clique (randomized greedy + plateau) */
        int na = nalive; int CW = (na + 63) / 64;
        uint64_t *C = calloc((size_t)na * CW + 1, 8);
        for (int a = 0; a < na; a++) for (int b = a + 1; b < na; b++) if (compat(alive[a], alive[b])) {
            C[(size_t)a * CW + (b >> 6)] |= 1ULL << (b & 63); C[(size_t)b * CW + (a >> 6)] |= 1ULL << (a & 63); }
        int *bestc = malloc(4 * (na + 1)), nbest = 0, *cur = malloc(4 * (na + 1)), nc = 0;
        int *inc = calloc(na + 1, 4), *cnt = calloc(na + 1, 4);
        double tcl = now() + 5.0; if (tcl > t0 + secs) tcl = t0 + secs;
        while (na > 0 && now() < tcl) {
            nc = 0; memset(inc, 0, 4 * na); memset(cnt, 0, 4 * na);
            for (int it = 0; it < na; it++) { int v = rnd() % na; if (inc[v] || cnt[v]) continue;
                inc[v] = 1; cur[nc++] = v; for (int x = 0; x < na; x++) if (x != v && !((C[(size_t)v * CW + (x >> 6)] >> (x & 63)) & 1)) cnt[x]++; }
            for (int rounds = 0; rounds < 20000 && now() < tcl; rounds++) {
                int add = 0;
                for (int x = 0; x < na; x++) if (!inc[x] && cnt[x] == 0) { inc[x] = 1; cur[nc++] = x;
                    for (int y = 0; y < na; y++) if (y != x && !((C[(size_t)x * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]++; add = 1; }
                if (nc > nbest) { nbest = nc; memcpy(bestc, cur, 4 * nc); }
                if (add) continue;
                int x = -1; for (int s = 0; s < 200; s++) { int y = rnd() % na; if (!inc[y] && cnt[y] == 1) { x = y; break; } }
                if (x < 0) break;
                int drop = -1; for (int a = 0; a < nc; a++) { int m2 = cur[a]; if (!((C[(size_t)x * CW + (m2 >> 6)] >> (m2 & 63)) & 1)) { drop = a; break; } }
                int m2 = cur[drop]; inc[m2] = 0; cur[drop] = cur[--nc];
                for (int y = 0; y < na; y++) if (y != m2 && !((C[(size_t)m2 * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]--;
                inc[x] = 1; cur[nc++] = x;
                for (int y = 0; y < na; y++) if (y != x && !((C[(size_t)x * CW + (y >> 6)] >> (y & 63)) & 1)) cnt[y]++;
            }
        }
        /* 3. add the clique (mutually compatible by construction) */
        for (int a = 0; a < nbest; a++) { int p = alive[bestc[a]]; isCur[p] = 1; addkeys(KG, p); ncur++; added_here++; }
        /* 4. rebuild alive: remaining pool entries compatible with the whole packing */
        int nn = 0;
        for (int a = 0; a < na; a++) { int p = alive[a]; if (isCur[p]) continue; int good = 1;
            for (int q2 = 0; q2 < npool && good; q2++) if (isCur[q2] && !(compat(p, q2) && compat(q2, p))) good = 0;
            if (good) alive[nn++] = p; }
        nalive = nn;
        free(C); free(bestc); free(cur); free(inc); free(cnt);
        if (ncur > best_ncur) best_ncur = ncur;
        fprintf(stderr, "round %d: covers %ld selfok %ld compat %ld; alive %d (pool %d), clique +%d, B-orbits %d (t=%.0fs)\n", round, cnt_okc, cnt_self, cnt_good, na, npool, nbest, ncur, now() - t0);
        /* write current packing */
        FILE *og = fopen(argv[3], "w");
        for (int p = 0; p < npool; p++) if (isCur[p]) { for (int k = 0; k < csz[p]; k++) fprintf(og, "%d ", cand[p][k]); fprintf(og, "\n"); }
        fclose(og);
        if (npool >= MAXC - 2000) { /* recycle pool: keep only the packing */
            int np = 0; for (int p = 0; p < npool; p++) if (isCur[p]) {
                if (np != p) { memcpy(cand[np], cand[p], sizeof cand[p]); csz[np] = csz[p]; memcpy(KS[np], KS[p], sizeof KS[p]);
                    memcpy(Sb + (size_t)np * W, Sb + (size_t)p * W, W * 8); }
                isCur[np] = 1; np++; }
            npool = np; nalive = 0;
        }
    }
    FILE *og = fopen(argv[3], "w");
    int nout = 0;
    for (int p = 0; p < npool; p++) if (isCur[p]) { for (int k = 0; k < csz[p]; k++) fprintf(og, "%d ", cand[p][k]); fprintf(og, "\n"); nout++; }
    fclose(og);
    printf("B-orbits %d (fixed %d, added %d); B-hubs %d\n", nout, nfix, nout - nfix, 22 * nout);
    return 0;
}
