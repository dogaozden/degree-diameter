/* d09: non-line hubs for (17,5) on G (16,5, 33,792 vertices). Hubs on side A (side 0): N subset of B.
 * Conditions as in hubpack: coverage (every A-vertex within distance 3 of N), and pairwise compatibility
 * (N(h') meets R(h) = distance-<=2 set of N(h)) plus disjointness of N-sets.
 *
 *  d09 gen   EDGES SIDE SECS SEED M MU ITERS OUT   simulated annealing over M-sets N, feasible = full cover,
 *                                                    objective U - MU*|R| (U = uncovered vertices).
 *  d09 lines EDGES SIDE SECS SEED NCAND OUT        hubpack-style 4-line covers (for comparison).
 *  d09 stats EDGES SIDE POOL                       mean |R| and compatibility density of a pool file.
 *  d09 pack  EDGES SIDE SECS SEED FIXED|- POOL... OUT   max clique (fixed hubs kept; OUT is the last argument).
 * Files: one hub per line, global vertex ids of the old neighbours. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define H 16896
#define W 264

static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static int (*adjT)[16], (*adjS)[16];
static uint64_t *ball, *d2;
static int OFF;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline double urand(void) { return (rnd() & 0xFFFFFFu) / 16777216.0; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }

static void load(const char *fn, int side) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "no edges\n"); exit(1); }
    long n, u, v; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) { fprintf(stderr, "bad n\n"); exit(1); }
    static int da[H], db[H];
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = (int)v; adjB[v][db[v]++] = (int)u; }
    fclose(f);
    OFF = side == 0 ? H : 0;
    adjT = side == 0 ? adjB : adjA; adjS = side == 0 ? adjA : adjB;
    ball = calloc((size_t)H * W, 8); d2 = calloc((size_t)H * W, 8);
    for (int t = 0; t < H; t++) {
        uint64_t *bl = ball + (size_t)t * W, *dd = d2 + (size_t)t * W;
        dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjT[t][i]; bl[s >> 6] |= 1ULL << (s & 63);
            for (int j = 0; j < 16; j++) { int t2 = adjS[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) { int s = adjT[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } }
    }
}

/* ---------- SA over N ---------- */
static int cov[H], rc[H], inN[H];
static int Ucnt, Rcnt; static int last_U, last_R;
static void upd(int t, int sg) {
    uint64_t *bl = ball + (size_t)t * W;
    for (int w = 0; w < W; w++) { uint64_t m = bl[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int s = w * 64 + b;
        if (sg > 0) { if (cov[s]++ == 0) Ucnt--; } else { if (--cov[s] == 0) Ucnt++; } } }
    uint64_t *dd = d2 + (size_t)t * W;
    for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int x = w * 64 + b;
        if (sg > 0) { if (rc[x]++ == 0) Rcnt++; } else { if (--rc[x] == 0) Rcnt--; } } }
}
/* returns 1 and fills bestN (local ids) if a feasible state with |R| > -1 was seen */
static int sa_run(int m, int nfix, const int *init, double mu, long iters, double T0, double T1, int *bestN, int *bestR) {
    memset(cov, 0, sizeof cov); memset(rc, 0, sizeof rc); memset(inN, 0, sizeof inN); Ucnt = H; Rcnt = 0;
    int N[17];
    for (int k = 0; k < m; k++) { int t; if (k < nfix) t = init[k]; else { do t = rnd() % H; while (inN[t]); }
        inN[t] = 1; N[k] = t; upd(t, +1); }
    int U0 = Ucnt;
    double cost = Ucnt - mu * Rcnt; *bestR = -1;
    if (nfix == m) { if (Ucnt == 0) { *bestR = Rcnt; memcpy(bestN, N, m * sizeof(int)); } return *bestR >= 0; }
    for (long it = 0; it < iters; it++) {
        double T = T0 * pow(T1 / T0, (double)it / iters);
        int k = nfix + rnd() % (m - nfix), t_in;
        if (Ucnt > 0) { int s; do s = rnd() % H; while (cov[s]); t_in = adjS[s][rnd() % 16]; if (inN[t_in]) continue; }
        else { do t_in = rnd() % H; while (inN[t_in]); }
        int t_out = N[k];
        upd(t_out, -1); upd(t_in, +1);
        double nc = Ucnt - mu * Rcnt, d = nc - cost;
        if (d <= 0 || urand() < exp(-d / T)) {
            cost = nc; inN[t_out] = 0; inN[t_in] = 1; N[k] = t_in;
            if (Ucnt == 0 && Rcnt > *bestR) { *bestR = Rcnt; memcpy(bestN, N, m * sizeof(int)); }
        } else { upd(t_in, -1); upd(t_out, +1); }
    }
    last_U = Ucnt; last_R = Rcnt; (void)U0;
    return *bestR >= 0;
}

/* ---------- lines (hubpack style) ---------- */
static int nlines; static int (*lines)[4]; static uint64_t *lball;
static void make_lines(void) {
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    int K = 6; nlines = 0; lines = malloc(sizeof(int[4]) * 66 * K * 64);
    uint64_t tmp[W];
    for (int cv = 0; cv < 66; cv++) {
        double sc[85];
        for (int di = 0; di < nd; di++) { long tot = 0;
            for (int s = 0; s < 8; s++) { int y = rnd() & 255; memset(tmp, 0, sizeof tmp);
                for (int l = 0; l < 4; l++) { int t = cv * 256 + (y ^ scal(l, dirs[di])); uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) tmp[w] |= bl[w]; }
                tot += popw(tmp); }
            sc[di] = tot / 8.0; }
        for (int k = 0; k < K; k++) { int bi = 0; for (int di = 1; di < nd; di++) if (sc[di] > sc[bi]) bi = di; sc[bi] = -1;
            int c = dirs[bi], seen[256] = {0};
            for (int y = 0; y < 256; y++) if (!seen[y]) { for (int l = 0; l < 4; l++) { int z = y ^ scal(l, c); seen[z] = 1; lines[nlines][l] = cv * 256 + z; } nlines++; }
        }
    }
    lball = malloc((size_t)nlines * W * 8);
    for (int i = 0; i < nlines; i++) { uint64_t *o = lball + (size_t)i * W; memset(o, 0, W * 8);
        for (int l = 0; l < 4; l++) { uint64_t *bl = ball + (size_t)lines[i][l] * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; } }
}
/* one hubpack-style cover; returns size, fills out (local ids) */
static int line_cover(int *out) {
    uint64_t unc[W], full[W];
    for (;;) {
        for (int w = 0; w < W; w++) full[w] = ~0ULL;
        memcpy(unc, full, sizeof unc); int ch[5], nch = 0, ok = 0;
        int first = rnd() % nlines; ch[nch++] = first; { uint64_t *o = lball + (size_t)first * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w]; }
        for (int step = 1; step < 4; step++) {
            int best = -1, bg = -1;
            for (int s = 0; s < 3000; s++) { int i = rnd() % nlines; int clash = 0;
                for (int a = 0; a < nch && !clash; a++) for (int x = 0; x < 4 && !clash; x++) for (int y = 0; y < 4; y++) if (lines[i][x] == lines[ch[a]][y]) { clash = 1; break; }
                if (clash) continue;
                uint64_t *o = lball + (size_t)i * W; int g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & o[w]);
                if (g > bg) { bg = g; best = i; } }
            if (best < 0) break; ch[nch++] = best; uint64_t *o = lball + (size_t)best * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w];
            if (popw(unc) == 0) { ok = 1; break; }
        }
        int extra = -1;
        if (!ok && nch == 4) {
            for (int s = 0; s < 4000 && extra < 0; s++) { int t = rnd() % H; uint64_t *bl = ball + (size_t)t * W; int cov1 = 1;
                for (int w = 0; w < W; w++) if (unc[w] & ~bl[w]) { cov1 = 0; break; }
                if (cov1) { int clash = 0; for (int a = 0; a < 4; a++) for (int y = 0; y < 4; y++) if (lines[ch[a]][y] == t) clash = 1; if (!clash) extra = t; } }
            if (extra >= 0) ok = 1;
        }
        if (!ok) continue;
        int k = 0; for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) out[k++] = lines[ch[a]][y];
        if (extra >= 0) out[k++] = extra;
        return k;
    }
}

/* ---------- pool IO and compatibility ---------- */
static int nc, *csz; static int (*cand)[17]; static uint64_t *R;
static int read_pool(const char *fn, int cap_start) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    char buf[1024]; int cnt = 0;
    while (fgets(buf, sizeof buf, f)) {
        char *p = buf; int k = 0; char *e;
        for (;;) { long v = strtol(p, &e, 10); if (e == p) break; p = e; if (k < 17) cand[cap_start + cnt][k] = (int)v - OFF; k++; }
        if (k == 0) continue;
        csz[cap_start + cnt] = k; cnt++;
    }
    fclose(f); return cnt;
}
static void build_R(void) {
    R = malloc((size_t)nc * W * 8);
    for (int i = 0; i < nc; i++) { uint64_t *o = R + (size_t)i * W; memset(o, 0, W * 8);
        for (int k = 0; k < csz[i]; k++) { uint64_t *dd = d2 + (size_t)cand[i][k] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
}
/* compat bit matrix: C[i][j] = disjoint && R(i) meets N(j) */
static uint64_t *C; static int CW;
static long build_compat(void) {
    CW = (nc + 63) / 64; C = calloc((size_t)nc * CW, 8);
    int *stamp = calloc(H, 4); long ncomp = 0;
    for (int i = 0; i < nc; i++) {
        for (int l = 0; l < csz[i]; l++) stamp[cand[i][l]] = i + 1;
        uint64_t *o = R + (size_t)i * W;
        for (int j = i + 1; j < nc; j++) {
            int meet = 0, dis = 1;
            for (int k = 0; k < csz[j]; k++) { int t = cand[j][k]; if (stamp[t] == i + 1) { dis = 0; break; } if ((o[t >> 6] >> (t & 63)) & 1) meet = 1; }
            if (meet && dis) { C[(size_t)i * CW + (j >> 6)] |= 1ULL << (j & 63); C[(size_t)j * CW + (i >> 6)] |= 1ULL << (i & 63); ncomp++; }
        }
    }
    free(stamp); return ncomp;
}
static inline int adjc(int a, int b) { return (C[(size_t)a * CW + (b >> 6)] >> (b & 63)) & 1; }

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: see header\n"); return 2; }
    const char *mode = argv[1];
    if (!strcmp(mode, "gen")) {
        if (argc < 11) return 2;
        int klines = atoi(argv[10]);
        int side = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
        int m = atoi(argv[6]); double mu = atof(argv[7]); long iters = atol(argv[8]);
        load(argv[2], side);
        if (klines > 0) make_lines();
        { double s = 0; for (int t = 0; t < H; t += 97) s += popw(ball + (size_t)t * W); fprintf(stderr, "mean ball %.1f\n", s / (H / 97 + 1)); }
        { double s = 0; for (int t = 0; t < H; t += 97) s += popw(d2 + (size_t)t * W); fprintf(stderr, "mean d2 %.1f\n", s / (H / 97 + 1)); }
        FILE *g = fopen(argv[9], "w");
        int bestN[17]; double t0 = now(); int nfeas = 0, nrun = 0; double sumR = 0; int minR = 1 << 30, maxR = 0;
        while (now() - t0 < secs) {
            int bR; nrun++;
            int init[17], nfix = 0;
            if (klines > 0) { int lc[17]; int k = line_cover(lc); nfix = 4 * klines; if (nfix > k) nfix = k; for (int q = 0; q < nfix; q++) init[q] = lc[q]; }
            int ok = sa_run(m, nfix, init, mu, iters, 2.0, 0.05, bestN, &bR);
            if (nrun <= 3) fprintf(stderr, "run %d nfix %d end U %d R %d best %d\n", nrun, nfix, last_U, last_R, bR);
            if (ok) {
                nfeas++; sumR += bR; if (bR < minR) minR = bR; if (bR > maxR) maxR = bR;
                for (int k = 0; k < m; k++) fprintf(g, "%d ", bestN[k] + OFF); fprintf(g, "\n"); fflush(g);
            }
        }
        fclose(g);
        fprintf(stderr, "gen: runs %d feasible %d meanR %.1f minR %d maxR %d (%.1fs)\n", nrun, nfeas, nfeas ? sumR / nfeas : 0.0, minR, maxR, now() - t0);
        printf("gen side %d m %d feasible %d/%d\n", side, m, nfeas, nrun);
        return 0;
    }
    if (!strcmp(mode, "lines")) {
        int side = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
        int NC = atoi(argv[6]);
        load(argv[2], side); make_lines();
        FILE *g = fopen(argv[7], "w"); double t0 = now(); int nc2 = 0; long sz = 0;
        int out[17];
        while (nc2 < NC && now() - t0 < secs) { int k = line_cover(out); sz += k; nc2++;
            for (int i = 0; i < k; i++) fprintf(g, "%d ", out[i] + OFF); fprintf(g, "\n"); }
        fclose(g); printf("lines: %d covers, mean size %.2f (%.1fs)\n", nc2, nc2 ? (double)sz / nc2 : 0.0, now() - t0);
        return 0;
    }
    if (!strcmp(mode, "stats") || !strcmp(mode, "pack")) {
        int isPack = !strcmp(mode, "pack");
        int side = atoi(argv[3]);
        load(argv[2], side);
        cand = malloc(sizeof(int[17]) * 20000); csz = malloc(4 * 20000);
        nc = 0; int nf = 0; double secs = 0;
        if (isPack) {
            secs = atof(argv[4]); rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
            if (strcmp(argv[6], "-")) nf = read_pool(argv[6], 0);
            nc = nf;
            for (int a = 7; a < argc - 1; a++) nc += read_pool(argv[a], nc);
            /* output file is last arg */
        } else {
            for (int a = 4; a < argc; a++) nc += read_pool(argv[a], nc);
        }
        if (nc == 0) { fprintf(stderr, "empty pool\n"); return 3; }
        build_R();
        double sr = 0; for (int i = 0; i < nc; i++) sr += popw(R + (size_t)i * W);
        long ncomp = build_compat(); double dens = nc > 1 ? 2.0 * ncomp / ((double)nc * (nc - 1)) : 0;
        printf("pool %d (fixed %d) meanR %.1f density %.4f\n", nc, nf, sr / nc, dens);
        if (!isPack) return 0;
        /* max clique: fixed first, greedy random + plateau swaps; fixed never dropped */
        int *best = malloc(4 * nc), nbest = 0, *cur = malloc(4 * nc), ncur; int *inc = calloc(nc, 4), *cnt = calloc(nc, 4);
        double t0 = now();
        while (now() - t0 < secs) {
            ncur = 0; memset(inc, 0, 4 * nc); memset(cnt, 0, 4 * nc);
            #define ADDV(v) do { inc[v] = 1; cur[ncur++] = (v); for (int y = 0; y < nc; y++) if (y != (v) && !adjc((v), y)) cnt[y]++; } while (0)
            for (int i = 0; i < nf; i++) ADDV(i);
            for (int it = 0; it < nc; it++) { int v = rnd() % nc; if (inc[v] || cnt[v]) continue; ADDV(v); }
            for (int rounds = 0; rounds < 20000 && now() - t0 < secs; rounds++) {
                int added = 0;
                for (int x = 0; x < nc; x++) if (!inc[x] && cnt[x] == 0) { ADDV(x); added = 1; }
                if (ncur > nbest) { nbest = ncur; memcpy(best, cur, 4 * ncur); if (nbest % 20 == 0) fprintf(stderr, "clique %d (%.1fs)\n", nbest, now() - t0); }
                if (added) continue;
                int x = -1; for (int s = 0; s < 200; s++) { int y = rnd() % nc; if (!inc[y] && cnt[y] == 1) { x = y; break; } }
                if (x < 0) break;
                int drop = -1; for (int a = 0; a < ncur; a++) { int mm = cur[a]; if (!adjc(x, mm)) { drop = a; break; } }
                int mm = cur[drop]; if (mm < nf) continue;
                /* remove mm */
                inc[mm] = 0; cur[drop] = cur[--ncur];
                for (int y = 0; y < nc; y++) if (y != mm && !adjc(mm, y)) cnt[y]--;
                ADDV(x);
            }
        }
        FILE *g = fopen(argv[argc - 1], "w");
        for (int a = 0; a < nbest; a++) { int i = best[a]; for (int k = 0; k < csz[i]; k++) fprintf(g, "%d ", cand[i][k] + OFF); fprintf(g, "\n"); }
        fclose(g);
        printf("pack side %d: best clique %d hubs (fixed %d) density %.4f\n", side, nbest, nf, dens);
        return 0;
    }
    fprintf(stderr, "unknown mode\n"); return 2;
}
