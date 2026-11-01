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
#define MAXN 400000
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
    if (argc < 7) { fprintf(stderr, "usage: online EDGES SIDE INITPACK SECS SEED OUTPACK\n"); return 2; }
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

    /* lines as in d06/orb.c (K best directions per controller vertex) */
    cand = malloc(sizeof(int[16]) * MAXN); KS = calloc(MAXN, sizeof(*KS)); Sb = calloc((size_t)MAXN * W, 8);
    JB = malloc(sizeof(int) * 16 * (size_t)MAXN); HH = malloc(sizeof(int) * 16 * (size_t)MAXN); YY = malloc(sizeof(int) * 16 * (size_t)MAXN);
    for (int u2 = 0; u2 < 22; u2++) for (int h = 0; h < 22; h++) hoff[u2][h] = ((h + u2) % 22) * 256;
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    static int MULS[4][4]; (void)MULS;
    #define SCAL(l,a) ({ int _r = 0; for (int _k = 0; _k < 4; _k++) _r |= MUL4[l][((a) >> (2 * _k)) & 3] << (2 * _k); _r; })
    int nl = 0; int (*lines)[4] = malloc(sizeof(int[4]) * 66 * 6 * 64);
    uint64_t *lball = malloc((size_t)66 * 6 * 64 * W * 8);
    for (int cv = 0; cv < 66; cv++) {
        double sc2[85];
        for (int di = 0; di < nd; di++) { long tot = 0; static uint64_t tmp[W];
            for (int s = 0; s < 8; s++) { int y = rnd() & 255; memset(tmp, 0, sizeof tmp);
                for (int l = 0; l < 4; l++) { int t = cv * 256 + (y ^ SCAL(l, dirs[di])); uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) tmp[w] |= bl[w]; }
                for (int w = 0; w < W; w++) tot += __builtin_popcountll(tmp[w]); }
            sc2[di] = tot / 8.0; }
        for (int k = 0; k < 6; k++) { int bi = 0; for (int di = 1; di < nd; di++) if (sc2[di] > sc2[bi]) bi = di; sc2[bi] = -1;
            int c = dirs[bi], seen[256] = {0};
            for (int y = 0; y < 256; y++) if (!seen[y]) { for (int l = 0; l < 4; l++) { int z = y ^ SCAL(l, c); seen[z] = 1; lines[nl][l] = cv * 256 + z; } nl++; } }
    }
    for (int i = 0; i < nl; i++) { uint64_t *o = lball + (size_t)i * W; memset(o, 0, W * 8);
        for (int l = 0; l < 4; l++) { uint64_t *bl = ball + (size_t)lines[i][l] * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; } }
    /* initial packing (global ids, 16 per line), key set KP */
    uint64_t KP[12]; memset(KP, 0, sizeof KP); int *pk = malloc(4 * MAXN), np_ = 0, npk = 0;   /* pk: indices of packed covers */
    FILE *ip = fopen(argv[3], "r"); char buf[512];
    while (ip && fgets(buf, sizeof buf, ip)) { int m = 0, x, off; char *q = buf; uint64_t KU[12]; memset(KU, 0, sizeof KU); int okp = 1;
        while (sscanf(q, "%d%n", &x, &off) == 1 && m < 16) { q += off; int t = x - (side == 0 ? H : 0); int k = keyof(t);
            if ((KU[k >> 6] >> (k & 63)) & 1) okp = 0; KU[k >> 6] |= 1ULL << (k & 63); cand[np_][m++] = t; }
        int clash = 0; for (int w = 0; w < 12; w++) if (KU[w] & KP[w]) clash = 1;
        if (!okp || m != 16 || clash) { fprintf(stderr, "bad init line\n"); continue; }
        for (int w = 0; w < 12; w++) KP[w] |= KU[w];
        memcpy(KS[np_], KU, sizeof KU);
        for (int k = 0; k < 16; k++) { int t = cand[np_][k], blk = t >> 8, j = blk / 22, h = blk % 22;
            JB[np_ * 16 + k] = j * 22 * 256; HH[np_ * 16 + k] = h; YY[np_ * 16 + k] = t & 255; }
        for (int k = 0; k < 16; k++) { uint64_t *dd = d2 + (size_t)cand[np_][k] * W; for (int w = 0; w < W; w++) Sb[(size_t)np_ * W + w] |= dd[w]; }
        pk[npk++] = np_; np_++; }
    if (ip) fclose(ip);
    int nInit = npk; fprintf(stderr, "init packing %d covers\n", nInit);
    uint64_t full[W]; for (int w = 0; w < W; w++) full[w] = ~0ULL;
    long gen = 0, selfok = 0, added = 0, tried_compat = 0;
    static uint64_t unc[W], o_[W];
    while (now() < T0 + secs && np_ < MAXN - 1) {
        gen++;
        memcpy(unc, full, sizeof unc);
        int ch[5], nch = 0; uint64_t KU[12]; memcpy(KU, KP, sizeof KU); int ok = 0;
        #define LFREE(i) ({ int _f = 1; for (int _l = 0; _l < 4 && _f; _l++) { int _k = keyof(lines[i][_l]); if ((KU[_k >> 6] >> (_k & 63)) & 1) _f = 0; } _f; })
        #define LADD(i) do { for (int _l = 0; _l < 4; _l++) { int _k = keyof(lines[i][_l]); KU[_k >> 6] |= 1ULL << (_k & 63); } ch[nch++] = (i); } while (0)
        int first = -1; for (int s = 0; s < 2000 && first < 0; s++) { int c = rnd() % nl; if (LFREE(c)) first = c; }
        if (first < 0) break;
        LADD(first); { uint64_t *o = lball + (size_t)first * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w]; }
        for (int step = 1; step < 4; step++) {
            int best = -1, bg = -1;
            for (int s = 0; s < 3000; s++) { int i = rnd() % nl; if (!LFREE(i)) continue;
                uint64_t *o = lball + (size_t)i * W; int g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & o[w]);
                if (g > bg) { bg = g; best = i; } }
            if (best < 0) break;
            LADD(best); uint64_t *o = lball + (size_t)best * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w];
            int z = 1; for (int w = 0; w < W && z; w++) if (unc[w]) z = 0;
            if (z) { ok = 1; break; }
        }
        if (!ok && nch == 4) {
            int extra = -1;
            for (int s = 0; s < 6000 && extra < 0; s++) { int t = rnd() % H; int k = keyof(t);
                if ((KU[k >> 6] >> (k & 63)) & 1) continue;
                uint64_t *bl = ball + (size_t)t * W; int cov = 1;
                for (int w = 0; w < W; w++) if (unc[w] & ~bl[w]) { cov = 0; break; }
                if (cov) extra = t; }
            if (extra >= 0) { ok = 1; int k = keyof(extra); KU[k >> 6] |= 1ULL << (k & 63); }
            /* extra-vertex covers have 17 keys: skipped here (cap 48 needs 16-key covers) */
            if (ok) { ok = 0; }
        }
        if (!ok) continue;
        /* build candidate at slot np_ (temporary) */
        int m = 0; for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) cand[np_][m++] = lines[ch[a]][y];
        if (m != 16) continue;
        for (int w = 0; w < 12; w++) if (KU[w] & ~KS[np_][w] & 0) ;
        { uint64_t KC[12]; memset(KC, 0, sizeof KC); for (int k = 0; k < 16; k++) { int kk = keyof(cand[np_][k]); KC[kk >> 6] |= 1ULL << (kk & 63); } memcpy(KS[np_], KC, sizeof KC); }
        for (int k = 0; k < 16; k++) { int t = cand[np_][k], blk = t >> 8, j = blk / 22, h = blk % 22;
            JB[np_ * 16 + k] = j * 22 * 256; HH[np_ * 16 + k] = h; YY[np_ * 16 + k] = t & 255; }
        uint64_t *Sx = Sb + (size_t)np_ * W; memset(Sx, 0, W * 8);
        for (int k = 0; k < 16; k++) { uint64_t *dd = d2 + (size_t)cand[np_][k] * W; for (int w = 0; w < W; w++) Sx[w] |= dd[w]; }
        int good = 1; for (int uu = 1; uu < 22 && good; uu++) { int hit = 0;
            for (int k = 0; k < 16 && !hit; k++) if (bit(Sx, shT[uu][cand[np_][k]])) hit = 1; if (!hit) good = 0; }
        if (!good) continue;
        selfok++;
        /* compatible with every packed cover (key-disjoint already) */
        int all = 1;
        for (int a = 0; a < npk && all; a++) { tried_compat++; int i = pk[a]; if (!compat(np_, i) || !compat(i, np_)) all = 0; }
        if (all) { pk[npk++] = np_; for (int w = 0; w < 12; w++) KP[w] |= KS[np_][w]; np_++; added++;
            fprintf(stderr, "packing %d (%.1fs, gen %ld)\n", npk, now() - T0, gen); }
    }
    FILE *g = fopen(argv[6], "w");
    for (int a = 0; a < npk; a++) { int i = pk[a]; for (int k = 0; k < 16; k++) fprintf(g, "%d ", cand[i][k] + (side == 0 ? H : 0)); fprintf(g, "\n"); }
    fclose(g);
    printf("online side %d: init %d, generated %ld, self-compat %ld, compat tests %ld, final packing %d orbits = %d hubs\n",
           side, nInit, gen, selfok, tried_compat, npk, 22 * npk);
    return 0;
}
