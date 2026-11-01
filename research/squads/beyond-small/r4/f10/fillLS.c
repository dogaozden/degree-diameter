/* f10 (round 4): fill the free keys of side B with single hubs (not Z22 orbits).
 * Side-B hub N = set of A-vertices (global ids < H), |N| <= 17, every A-vertex in at most one hub.
 * Vertex (j,h,y) of A-local id (blk*256+y), blk = j*22+h, key = (j,y). Orbits (startB) own whole keys (all 22 h).
 * A single hub is accepted iff: all vertices free (key not used by an orbit, vertex not used by a single),
 * cover: ball3 union = all 16896 B-vertices, and compat with every existing hub:
 *   for each orbit M (22 translates M+uu): d2(N) meets every translate; for each single S: d2(N) meets S.
 * Candidates: 4 affine fibre lines (r1/c03 style, from all 66 controller blocks, any direction) + optional extra vertex,
 * greedy max coverage, as in growb (r3/e02). Accepted singles are added one by one (greedy, time-limited).
 * usage: fillB EDGES ORBFILE SINGLES_IN|- SINGLES_OUT SECS SEED [SAMPLES=600]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>
#define H 16896
#define W 264
#define MAXSG 1200
static int adjA[H][16], adjB[H][16];
static uint64_t *ball, *d2;
static int shT[22][H];
static const int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static inline int keyof(int t) { return ((t >> 8) / 22) * 256 + (t & 255); }
static inline int shl(int t, int u) { int blk = t >> 8; int j = blk / 22, h = blk % 22; return ((j * 22 + (h + u) % 22) << 8) | (t & 255); }
static inline int bit(const uint64_t *a, int t) { return (a[t >> 6] >> (t & 63)) & 1; }

static int norb, orbN[64][17], orbSz[64];
static uint64_t KG[12];          /* keys owned by orbits */
static int nsg, sgN[MAXSG][17], sgSz[MAXSG];
static uint64_t *sgD2;           /* d2 union of each single, W words each */
static char vused[H];            /* vertices used by singles */
static int (*L)[4]; static int nL;
static int *freeL; static int nfree;

static inline int isfree(int t) { int k = keyof(t); return !bit(KG, k) && !vused[t]; }
static void build_freelist(void) {
    nfree = 0;
    for (int i = 0; i < nL; i++) { int ok = 1; for (int l = 0; l < 4 && ok; l++) if (!isfree(L[i][l])) ok = 0; if (ok) freeL[nfree++] = i; }
}
/* compat: d2N meets all 22 translates of orbit m, and d2N meets every single */
static int compatN_unused(const uint64_t *D, int *Nv, int n) {
    (void)Nv; (void)n;
    for (int m = 0; m < norb; m++) {
        for (int uu = 0; uu < 22; uu++) { int hit = 0;
            for (int k = 0; k < orbSz[m] && !hit; k++) if (bit(D, shT[uu][orbN[m][k]])) hit = 1;
            if (!hit) return 0; }
    }
    for (int s = 0; s < nsg; s++) { int hit = 0;
        for (int k = 0; k < sgSz[s] && !hit; k++) if (bit(D, sgN[s][k])) hit = 1;
        if (!hit) return 0; }
    return 1;
}
static void lor(int i, uint64_t *o) { memset(o, 0, W * 8);
    for (int l = 0; l < 4; l++) { uint64_t *bl = ball + (size_t)L[i][l] * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; } }


static int nfail(const uint64_t *D) {
    int nf = 0;
    for (int m = 0; m < norb; m++) for (int uu = 0; uu < 22; uu++) { int hit = 0;
        for (int k = 0; k < orbSz[m] && !hit; k++) if (bit(D, shT[uu][orbN[m][k]])) hit = 1;
        if (!hit) nf++; }
    for (int s = 0; s < nsg; s++) { int hit = 0;
        for (int k = 0; k < sgSz[s] && !hit; k++) if (bit(D, sgN[s][k])) hit = 1;
        if (!hit) nf++; }
    return nf;
}
/* state: 4 line indices (into L) + one extra vertex (or -1) */
static int st_ch[4], st_ex;
static double evalst(int *ch, int ex, int *nf_out, int *unc_out) {
    uint64_t c[W]; memset(c, 0, sizeof c);
    int N[17], nn = 0;
    for (int a = 0; a < 4; a++) { uint64_t *bl; for (int y = 0; y < 4; y++) { int t = L[ch[a]][y]; int dup = 0;
        for (int z = 0; z < nn; z++) if (N[z] == t) dup = 1; if (!dup) N[nn++] = t; } }
    for (int a = 0; a < nn; a++) { uint64_t *bl = ball + (size_t)N[a] * W; for (int w = 0; w < W; w++) c[w] |= bl[w]; }
    if (ex >= 0) { uint64_t *bl = ball + (size_t)ex * W; for (int w = 0; w < W; w++) c[w] |= bl[w]; N[nn++] = ex; }
    int unc = 0; for (int w = 0; w < W; w++) unc += __builtin_popcountll(~c[w]);
    uint64_t dN[W]; memset(dN, 0, sizeof dN);
    for (int a = 0; a < nn; a++) { uint64_t *dd = d2 + (size_t)N[a] * W; for (int w = 0; w < W; w++) dN[w] |= dd[w]; }
    int nf = nfail(dN);
    *nf_out = nf; *unc_out = unc;
    return nf + unc / 30.0;
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: fillLS EDGES ORBFILE SINGLES_IN|- SINGLES_OUT SECS SEED [ITERS=3000]\n"); return 2; }
    double secs = atof(argv[5]);
    rs ^= (unsigned long long)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    long ITERS = argc > 7 ? atol(argv[7]) : 3000;
    uint64_t *cov = malloc(8 * W);
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (!f || fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    for (int u2 = 0; u2 < 22; u2++) for (int t = 0; t < H; t++) shT[u2][t] = shl(t, u2);
    ball = calloc((size_t)H * W, 8); d2 = calloc((size_t)H * W, 8);
    double t0 = now();
    for (int t = 0; t < H; t++) {
        uint64_t *bl = ball + (size_t)t * W, *dd = d2 + (size_t)t * W;
        dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjA[t][i]; bl[s >> 6] |= 1ULL << (s & 63);
            for (int j = 0; j < 16; j++) { int t2 = adjB[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) { int s = adjA[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } }
    }
    /* all affine fibre lines: 66 controller blocks x 85 directions x 64 lines */
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    nL = 66 * nd * 64; L = malloc(sizeof(int[4]) * nL); freeL = malloc(sizeof(int) * nL);
    int q = 0;
    for (int cv = 0; cv < 66; cv++) for (int di = 0; di < nd; di++) { int seen[256] = {0};
        for (int y = 0; y < 256; y++) if (!seen[y]) { for (int l = 0; l < 4; l++) { int z = y ^ scal(l, dirs[di]); seen[z] = 1; L[q][l] = cv * 256 + z; } q++; } }
    nL = q;
    sgD2 = calloc((size_t)MAXSG * W, 8);
    /* orbits */
    FILE *fo = fopen(argv[2], "r"); char buf[1024];
    while (fo && fgets(buf, sizeof buf, fo)) {
        int m = 0; char *p = buf; int x, off; int ok = 1; uint64_t K[12]; memset(K, 0, sizeof K);
        while (sscanf(p, "%d%n", &x, &off) == 1) { p += off; if (x < 0 || x >= H || m >= 17) { ok = 0; break; }
            int k = keyof(x); if (bit(K, k)) ok = 0; K[k >> 6] |= 1ULL << (k & 63); orbN[norb][m++] = x; }
        if (!ok || m == 0) continue;
        orbSz[norb] = m; for (int w = 0; w < 12; w++) KG[w] |= K[w]; norb++;
    }
    if (fo) fclose(fo);
    /* existing singles */
    nsg = 0;
    if (strcmp(argv[3], "-") != 0) { FILE *fs = fopen(argv[3], "r");
        while (fs && fgets(buf, sizeof buf, fs)) { int m = 0; char *p = buf; int x, off;
            while (sscanf(p, "%d%n", &x, &off) == 1) { p += off; sgN[nsg][m++] = x; vused[x] = 1; }
            if (m == 0) continue; sgSz[nsg] = m;
            for (int k = 0; k < m; k++) { uint64_t *dd = d2 + (size_t)sgN[nsg][k] * W; for (int w = 0; w < W; w++) sgD2[(size_t)nsg * W + w] |= dd[w]; }
            nsg++; }
        if (fs) fclose(fs); }
    fprintf(stderr, "setup %.2fs: %d lines, %d orbits, %d singles loaded\n", now() - t0, nL, norb, nsg);
    int nsg0 = nsg;
    uint64_t full[W]; for (int w = 0; w < W; w++) full[w] = ~0ULL;
    long tries = 0, found = 0, rounds = 0; int bestnf = 1 << 30; long lsi = 0;
    build_freelist();
    fprintf(stderr, "free lines: %d\n", nfree);
    while (now() - t0 < secs && nfree >= 4) {
        rounds++;
        /* random start */
        tries++;
        int ch[4]; for (int a = 0; a < 4; a++) ch[a] = freeL[rnd() % nfree];
        int ex = -1; { int s = 0; while (s++ < 1000) { int t = rnd() % H; if (isfree(t)) { ex = t; break; } } }
        int nf, unc; double cur = evalst(ch, ex, &nf, &unc);
        double T0 = 2.0, T1 = 0.05; int success = 0;
        for (long it = 0; it < ITERS && now() - t0 < secs; it++, lsi++) {
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            int nch[4], nex = ex; memcpy(nch, ch, sizeof nch);
            int slot = rnd() % 5;
            if (slot < 4) nch[slot] = freeL[rnd() % nfree];
            else { int s = 0; while (s++ < 1000) { int t = rnd() % H; if (isfree(t)) { nex = t; break; } } }
            int nnf, nunc; double c2 = evalst(nch, nex, &nnf, &nunc);
            double dl = c2 - cur;
            if (dl <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-dl / T)) {
                memcpy(ch, nch, sizeof ch); ex = nex; cur = c2; nf = nnf; unc = nunc;
                if (nf < bestnf) bestnf = nf;
                if (nf == 0 && unc == 0) { success = 1; break; }
            }
        }
        if (!success) continue;
        found++;
        /* build N */
        int N[17], nn = 0;
        for (int a = 0; a < 4; a++) for (int y = 0; y < 4; y++) { int t = L[ch[a]][y]; int dup = 0;
            for (int z = 0; z < nn; z++) if (N[z] == t) dup = 1; if (!dup) N[nn++] = t; }
        if (ex >= 0) N[nn++] = ex;
        memset(cov, 0, W * 8); for (int a = 0; a < nn; a++) { uint64_t *dd = d2 + (size_t)N[a] * W; for (int w = 0; w < W; w++) cov[w] |= dd[w]; }
        sgSz[nsg] = nn; memcpy(sgN[nsg], N, sizeof(int) * nn); memcpy(sgD2 + (size_t)nsg * W, cov, W * 8);
        for (int a = 0; a < nn; a++) vused[N[a]] = 1;
        nsg++;
        fprintf(stderr, "accepted single %d (n=%d) at t=%.1fs, tries %ld, ls iters %ld\n", nsg, nn, now() - t0, tries, lsi);
        build_freelist();
    }
    int bad = 0;
    for (int s = 0; s < nsg; s++) {
        uint64_t *b3 = calloc(W, 8);
        for (int k = 0; k < sgSz[s]; k++) { uint64_t *bl = ball + (size_t)sgN[s][k] * W; for (int w = 0; w < W; w++) b3[w] |= bl[w]; }
        for (int w = 0; w < W; w++) if (b3[w] != ~0ULL) { bad++; break; }
        free(b3);
    }
    FILE *og = fopen(argv[4], "w");
    for (int s = 0; s < nsg; s++) { for (int k = 0; k < sgSz[s]; k++) fprintf(og, "%d ", sgN[s][k]); fprintf(og, "\n"); }
    fclose(og);
    printf("singles %d (loaded %d, new %d); cover failures %d; restarts %ld, successes %ld, best nf %d, free lines left %d\n",
           nsg, nsg0, nsg - nsg0, bad, tries, found, bestnf, nfree);
    return 0;
}
