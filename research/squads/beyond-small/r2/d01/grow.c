/* d01: adaptive hub growth on side A of G (16,5 route-chart graph, 33,792 vertices).
 * Joint greedy: a new A-hub is N = 4 disjoint affine fibre lines (16 vertices of B, optionally + 1 more, |N| <= 17)
 * such that (1) the distance-3 balls of N cover all of A, (2) N meets R(h) = dist<=2 set of N(h) for every
 * existing A-hub h, (3) N avoids every vertex already used by an A-hub.
 * Lines are sampled at random each step and scored by (new A-coverage)/|A| + wH * (new hubs hit)/m + noise.
 *
 * usage: grow EDGES HUBS_IN OUT SECS SEED K NOISE WH
 *   HUBS_IN: one A-hub per line, global B ids (>= 16896). OUT: same format, rewritten on every success.
 * The loaded hub set is verified first (coverage and pairwise condition). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define H 16896
#define W 264
#define MAXH 1400
#define HW 22

static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static uint64_t ballB[H][W];   /* A-vertices within distance 3 of B-vertex t (local ids) */
static uint64_t d2B[H][W];     /* B-vertices within distance 2 of B-vertex t */
static uint64_t S[H][HW];      /* bit h of S[v]: v in R(h) */
static int used[H];
static int hubN[MAXH][17], hubSz[MAXH], m = 0;
static int (*lines)[4]; static int NL = 0;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int popc(uint64_t x) { return __builtin_popcountll(x); }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static inline void setb(uint64_t *a, int i) { a[i >> 6] |= 1ULL << (i & 63); }

static const char *OUTF;
static uint64_t hmaskG[HW];   /* bits < m, refreshed before each attempt */

static void write_out(void) {
    FILE *g = fopen(OUTF, "w");
    for (int h = 0; h < m; h++) {
        for (int k = 0; k < hubSz[h]; k++) fprintf(g, "%d ", hubN[h][k] + H);
        fprintf(g, "\n");
    }
    fclose(g);
}

static void add_hub(const int *N, int sz) {
    int h = m;
    hubSz[h] = sz;
    for (int k = 0; k < sz; k++) { hubN[h][k] = N[k]; used[N[k]] = 1; }
    for (int k = 0; k < sz; k++) {
        uint64_t *dd = d2B[N[k]];
        for (int w = 0; w < W; w++) { uint64_t mm = dd[w]; while (mm) { int b = __builtin_ctzll(mm); mm &= mm - 1; setb(S[w * 64 + b], h); } }
    }
    m++;
}

/* one randomized greedy attempt; returns 1 and fills out[] (size 16 or 17) on success */
static int try_build(int K, double noise, double wH, int *out, int *osz) {
    uint64_t covA[W], hit[HW];
    memset(hmaskG, 0, sizeof hmaskG); for (int h = 0; h < m; h++) setb(hmaskG, h);
    memset(covA, 0, sizeof covA); memset(hit, 0, sizeof hit);
    int chosen[17], nc = 0;
    for (int step = 0; step < 4; step++) {
        int bi = -1; double bs = -1e18;
        if (step == 3) {   /* exhaustive last line: first line (from a random start) that completes A and the hubs */
            int off = (int)(rnd64() % (unsigned long long)NL);
            for (int jj = 0; jj < NL; jj++) {
                int i = (jj + off) % NL; int *L = lines[i];
                if (used[L[0]] || used[L[1]] || used[L[2]] || used[L[3]]) continue;
                int clash = 0;
                for (int k = 0; k < 4 && !clash; k++) for (int q = 0; q < nc; q++) if (chosen[q] == L[k]) { clash = 1; break; }
                if (clash) continue;
                int ok = 1;
                for (int w = 0; w < W && ok; w++) {
                    uint64_t u = ballB[L[0]][w] | ballB[L[1]][w] | ballB[L[2]][w] | ballB[L[3]][w];
                    if (~covA[w] & ~u) ok = 0;
                }
                for (int w = 0; w < HW && ok; w++) {
                    uint64_t hh = S[L[0]][w] | S[L[1]][w] | S[L[2]][w] | S[L[3]][w];
                    if (~hit[w] & ~hh & hmaskG[w]) ok = 0;
                }
                if (ok) { bi = i; break; }
            }
            if (bi < 0) return 0;
            for (int k = 0; k < 4; k++) chosen[nc++] = lines[bi][k];
            break;
        }
        int valid = 0;
        for (long tries = 0; valid < K && tries < 60LL * K; tries++) {
            int i = (int)(rnd64() % (unsigned long long)NL); int *L = lines[i];
            if (used[L[0]] || used[L[1]] || used[L[2]] || used[L[3]]) continue;
            int clash = 0;
            for (int k = 0; k < 4 && !clash; k++) for (int q = 0; q < nc; q++) if (chosen[q] == L[k]) { clash = 1; break; }
            if (clash) continue;
            valid++;
            int newA = 0, newH = 0;
            for (int w = 0; w < W; w++) {
                uint64_t u = ballB[L[0]][w] | ballB[L[1]][w] | ballB[L[2]][w] | ballB[L[3]][w];
                newA += popc(u & ~covA[w]);
            }
            for (int w = 0; w < HW; w++) {
                uint64_t hh = S[L[0]][w] | S[L[1]][w] | S[L[2]][w] | S[L[3]][w];
                newH += popc(hh & ~hit[w]);
            }
            double sc = newA / (double)H + wH * newH / (double)(m > 0 ? m : 1) + noise * urand();
            if (sc > bs) { bs = sc; bi = i; }
        }
        if (bi < 0) return 0;
        for (int k = 0; k < 4; k++) chosen[nc++] = lines[bi][k];
        for (int w = 0; w < W; w++) covA[w] |= ballB[lines[bi][0]][w] | ballB[lines[bi][1]][w] | ballB[lines[bi][2]][w] | ballB[lines[bi][3]][w];
        for (int w = 0; w < HW; w++) hit[w] |= S[lines[bi][0]][w] | S[lines[bi][1]][w] | S[lines[bi][2]][w] | S[lines[bi][3]][w];
    }
    /* hub bits missing */
    int missH = 0;
    for (int h = 0; h < m; h++) if (!((hit[h >> 6] >> (h & 63)) & 1)) { missH = 1; break; }
    int missA = 0;
    for (int w = 0; w < W; w++) if (~covA[w]) { missA = 1; break; }
    if (!missH && !missA) { memcpy(out, chosen, sizeof(int) * 16); *osz = 16; return 1; }
    /* one extra vertex (|N| = 17): must cover the residual A and hit the residual hubs */
    uint64_t hmask[HW]; memset(hmask, 0, sizeof hmask);
    for (int h = 0; h < m; h++) setb(hmask, h);
    uint64_t resH[HW];
    for (int w = 0; w < HW; w++) resH[w] = hmask[w] & ~hit[w];
    for (int v = 0; v < H; v++) {
        if (used[v]) continue;
        int clash = 0; for (int q = 0; q < nc; q++) if (chosen[q] == v) { clash = 1; break; }
        if (clash) continue;
        int ok = 1;
        for (int w = 0; w < W && ok; w++) if (~covA[w] & ~ballB[v][w]) ok = 0;
        for (int w = 0; w < HW && ok; w++) if (resH[w] & ~S[v][w]) ok = 0;
        if (ok) { memcpy(out, chosen, sizeof(int) * 16); out[16] = v; *osz = 17; return 1; }
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: grow EDGES HUBS_IN OUT SECS SEED K NOISE WH\n"); return 2; }
    OUTF = argv[3];
    double secs = atof(argv[4]); rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    int K = atoi(argv[6]); double noise = atof(argv[7]), wH = atof(argv[8]);
    double t0 = now();

    FILE *f = fopen(argv[1], "r"); long n, u, v;
    if (!f || fscanf(f, "%ld", &n) != 1 || n != 2 * H) { fprintf(stderr, "bad edges\n"); return 3; }
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) {
        if (u > v) { long t = u; u = v; v = t; }
        v -= H; adjA[u][da[u]++] = (int)v; adjB[v][db[v]++] = (int)u;
    }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }

    for (int t = 0; t < H; t++) {
        uint64_t *bl = ballB[t], *dd = d2B[t];
        setb(dd, t);
        for (int i = 0; i < 16; i++) { int s = adjB[t][i]; setb(bl, s);
            for (int j = 0; j < 16; j++) setb(dd, adjA[s][j]); }
        for (int w = 0; w < W; w++) { uint64_t mm = dd[w]; while (mm) { int b = __builtin_ctzll(mm); mm &= mm - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) setb(bl, adjB[t2][i]); } }
    }

    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    lines = malloc(sizeof(int[4]) * 66 * 85 * 64);
    for (int cv = 0; cv < 66; cv++) for (int di = 0; di < nd; di++) {
        int seen[256] = {0};
        for (int y = 0; y < 256; y++) if (!seen[y]) {
            for (int l = 0; l < 4; l++) { int z = y ^ scal(l, dirs[di]); seen[z] = 1; lines[NL][l] = cv * 256 + z; }
            NL++;
        }
    }

    /* load and verify the starting hub set */
    FILE *hf = fopen(argv[2], "r"); char buf[8192];
    if (!hf) { fprintf(stderr, "no hub file\n"); return 3; }
    while (fgets(buf, sizeof buf, hf)) {
        int tmp[32], k = 0; char *p = buf; char *e;
        for (;;) { long x = strtol(p, &e, 10); if (e == p) break; tmp[k++] = (int)x; p = e; }
        if (k == 0) continue;
        int N[17];
        for (int q = 0; q < k; q++) { int loc = tmp[q] - H; if (loc < 0 || loc >= H || used[loc]) { fprintf(stderr, "bad hub id %d\n", tmp[q]); return 3; } N[q] = loc; }
        add_hub(N, k);
    }
    fclose(hf);
    /* verify: each hub covers A, pairwise hits */
    int badc = 0, badp = 0;
    for (int h = 0; h < m; h++) {
        uint64_t cov[W]; memset(cov, 0, sizeof cov); uint64_t hh[HW]; memset(hh, 0, sizeof hh);
        for (int k = 0; k < hubSz[h]; k++) { for (int w = 0; w < W; w++) cov[w] |= ballB[hubN[h][k]][w]; for (int w = 0; w < HW; w++) hh[w] |= S[hubN[h][k]][w]; }
        for (int w = 0; w < W; w++) if (~cov[w]) { badc++; break; }
        for (int j = 0; j < m; j++) if (j != h && !((hh[j >> 6] >> (j & 63)) & 1)) { badp++; }
    }
    fprintf(stderr, "loaded %d hubs, lines %d, uncovered-hub flags %d, pair misses %d (%.1fs)\n", m, NL, badc, badp, now() - t0);
    if (badc || badp) { fprintf(stderr, "starting set invalid, abort\n"); return 4; }
    write_out();

    long att = 0, succ = 0; int start = m;
    int out[17], osz = 0;
    while (now() - t0 < secs) {
        att++;
        if (try_build(K, noise, wH, out, &osz)) {
            add_hub(out, osz); succ++;
            write_out();
        }
    }
    printf("K=%d noise=%.3f wH=%.2f: attempts %ld, successes %ld, hubs %d -> %d (%.1fs)\n",
           K, noise, wH, att, succ, start, m, now() - t0);
    return 0;
}
