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

    /* ---- card f11: sample covers compatible with the fixed packing, then max clique on them (exact B&B, time-limited) ---- */
    long NS = argc > 8 ? atol(argv[8]) : 40000;
    double CLQ = argc > 9 ? atof(argv[9]) : 60;
    const char *OUT = argv[3];
    int nfixed = npool;
    int *alive = malloc(sizeof(int) * MAXC); int nalive = 0;
    #define LFREE2(i,KU) ({ int _f = 1; for (int _l = 0; _l < 4 && _f; _l++) { int _k = keyof(lines[i][_l]); if ((KU[_k >> 6] >> (_k & 63)) & 1) _f = 0; } _f; })
    #define LADD2(i,KU) do { for (int _l = 0; _l < 4; _l++) { int _k = keyof(lines[i][_l]); KU[_k >> 6] |= 1ULL << (_k & 63); } } while (0)
    long nsamp = 0, ncov = 0, nself = 0;
    double ts = now();
    for (long tr = 0; tr < NS && npool < MAXC - 2; tr++) {
        nsamp++;
        int ch[5], nch = 0; uint64_t KU[12]; memcpy(KU, KG, sizeof KU); int okc = 0;
        uint64_t unc[W]; memcpy(unc, full, sizeof unc);
        int first, guard = 0; do { first = rnd() % nl; } while (!LFREE2(first, KU) && ++guard < 100000);
        if (guard >= 100000) break;
        uint64_t om[W];
        LADD2(first, KU); ch[nch++] = first; lor(first, om); for (int w = 0; w < W; w++) unc[w] &= ~om[w];
        for (int step = 1; step < 4; step++) {
            int best = -1, bg = -1;
            for (int s = 0; s < 3000; s++) { int i = rnd() % nl; if (!LFREE2(i, KU)) continue;
                lor(i, om); int g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & om[w]);
                if (g > bg) { bg = g; best = i; } }
            if (best < 0) break;
            LADD2(best, KU); ch[nch++] = best; lor(best, om); for (int w = 0; w < W; w++) unc[w] &= ~om[w];
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
        if (!okc) continue;
        ncov++;
        int p = npool; int m = 0;
        for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) cand[p][m++] = lines[ch[a]][y];
        if (extra >= 0) cand[p][m++] = extra;
        csz[p] = m;
        memset(KS[p], 0, sizeof KS[p]); for (int k = 0; k < m; k++) { int kk = keyof(cand[p][k]); KS[p][kk >> 6] |= 1ULL << (kk & 63); }
        { uint64_t *o = Sb + (size_t)p * W; memset(o, 0, W * 8);
          for (int k = 0; k < m; k++) { uint64_t *dd = d2 + (size_t)cand[p][k] * W; for (int w = 0; w < W; w++) o[w] |= dd[w]; } }
        if (!selfcompat(p)) continue;
        nself++;
        int good = 1;
        for (int q2 = 0; q2 < nfixed && good; q2++) if (!(compat(p, q2) && compat(q2, p))) good = 0;
        if (!good) continue;
        alive[nalive++] = p; npool++;
    }
    fprintf(stderr, "sampled %ld: covers %ld, self-ok %ld, compatible with fixed %d (%.1fs)\n", nsamp, ncov, nself, nalive, now() - ts);

    /* compat graph among alive (both directions) */
    int na = nalive; int CW = (na + 63) / 64; if (CW == 0) CW = 1;
    uint64_t *C = calloc((size_t)na * CW + 1, 8);
    long nedge = 0;
    for (int a = 0; a < na; a++) for (int b = a + 1; b < na; b++) if (compat(alive[a], alive[b]) && compat(alive[b], alive[a])) {
        C[(size_t)a * CW + (b >> 6)] |= 1ULL << (b & 63); C[(size_t)b * CW + (a >> 6)] |= 1ULL << (a & 63); nedge++; }
    fprintf(stderr, "compat graph: %d vertices, %ld edges, density %.3f (%.1fs)\n", na, nedge,
            na > 1 ? 2.0 * nedge / ((double)na * (na - 1)) : 0.0, now() - ts);

    /* max clique: greedy-randomized incumbent, then Tomita-style colour-bound B&B until CLQ seconds */
    int *bestc = calloc(na + 1, 4), nbest = 0, *cur = calloc(na + 1, 4), nc = 0;
    int *inc = calloc(na + 1, 4), *cnt = calloc(na + 1, 4);
    double tcl = now() + CLQ;
    for (int it = 0; it < 200 && na > 0; it++) { /* quick randomized greedy starts */
        nc = 0; int nperm = 0; memset(inc, 0, 4 * na);
        int *cand2 = malloc(4 * na); for (int x = 0; x < na; x++) cand2[nperm++] = x;
        while (nperm > 0) { int r = rnd() % nperm; int v = cand2[r]; cand2[r] = cand2[--nperm]; cur[nc++] = v;
            int k = 0; for (int x = 0; x < nperm; x++) { int u = cand2[x]; if ((C[(size_t)v * CW + (u >> 6)] >> (u & 63)) & 1) cand2[k++] = u; } nperm = k; }
        free(cand2);
        if (nc > nbest) { nbest = nc; memcpy(bestc, cur, 4 * nc); }
    }
    fprintf(stderr, "greedy incumbent clique %d\n", nbest);
    /* B&B on bitsets */
    int *stackR = calloc(na + 1, 4); int depthMax = 64;
    uint64_t **Pd = malloc(sizeof(uint64_t*) * depthMax), **Qd = malloc(sizeof(uint64_t*) * depthMax);
    for (int d = 0; d < depthMax; d++) { Pd[d] = calloc(CW, 8); Qd[d] = calloc(CW, 8); }
    int *ordv = malloc(4 * (na + 1)), *colv = malloc(4 * (na + 1));
    long nodes = 0; int timed_out = 0;
    /* iterative-free recursion via function pointer-less nested style: implement with explicit recursion helper */
    int *colbuf[64]; for (int d = 0; d < 64; d++) colbuf[d] = malloc(4 * (na + 1));
    int *ordbuf[64]; for (int d = 0; d < 64; d++) ordbuf[d] = malloc(4 * (na + 1));
    /* recursive lambda-like expansion */
    void expand(int depth, uint64_t *P) {
        if (timed_out) return;
        if ((++nodes & 1023) == 0 && now() > tcl) { timed_out = 1; return; }
        /* colour P greedily into independent classes */
        uint64_t *Q = Qd[depth]; memcpy(Q, P, CW * 8);
        uint64_t *Qc = Pd[depth]; int nord = 0; int col = 0;
        int *ord = ordbuf[depth], *colr = colbuf[depth];
        int remaining = 0; for (int w = 0; w < CW; w++) remaining += __builtin_popcountll(Q[w]);
        while (remaining > 0) {
            col++; memcpy(Qc, Q, CW * 8);
            for (int w = 0; w < CW; w++) while (Qc[w]) {
                int b = __builtin_ctzll(Qc[w]); int v = w * 64 + b;
                Qc[w] &= Qc[w] - 1; Q[w] &= ~(1ULL << b); remaining--;
                const uint64_t *Av = C + (size_t)v * CW;
                for (int x = 0; x < CW; x++) Qc[x] &= ~Av[x];
                ord[nord] = v; colr[nord] = col; nord++;
            }
        }
        /* branch on vertices with highest colour first */
        uint64_t *Pn = P; /* P is owned by caller at this depth; we modify a private copy */
        uint64_t *Pl = Pd[depth]; /* reuse: copy P into a working set */
        (void)Pl; (void)Pn;
        uint64_t *Work = malloc(CW * 8); memcpy(Work, P, CW * 8);
        for (int i = nord - 1; i >= 0; i--) {
            if (nc + colr[i] <= nbest) break;
            int v = ord[i];
            stackR[nc++] = v;
            uint64_t *Np = malloc(CW * 8); const uint64_t *Av = C + (size_t)v * CW; int any = 0;
            for (int w = 0; w < CW; w++) { Np[w] = Work[w] & Av[w]; if (Np[w]) any = 1; }
            if (!any) { if (nc > nbest) { nbest = nc; memcpy(bestc, stackR, 4 * nc); } }
            else if (depth + 1 < 60) expand(depth + 1, Np);
            free(Np);
            nc--;
            Work[v >> 6] &= ~(1ULL << (v & 63));
            if (timed_out) break;
        }
        free(Work);
    }
    uint64_t *P0 = calloc(CW, 8); for (int a = 0; a < na; a++) P0[a >> 6] |= 1ULL << (a & 63);
    nc = 0;
    if (na > 0) expand(0, P0);
    fprintf(stderr, "B&B: nodes %ld, %s, best clique %d (%.1fs)\n", nodes, timed_out ? "TIMED OUT (heuristic)" : "exact", nbest, now() - ts);

    /* write fixed + clique */
    FILE *og = fopen(OUT, "w"); int nout = 0;
    for (int p = 0; p < nfixed; p++) { for (int k = 0; k < csz[p]; k++) fprintf(og, "%d ", cand[p][k]); fprintf(og, "\n"); nout++; }
    for (int a = 0; a < nbest; a++) { int p = alive[bestc[a]]; for (int k = 0; k < csz[p]; k++) fprintf(og, "%d ", cand[p][k]); fprintf(og, "\n"); nout++; }
    fclose(og);
    printf("B-orbits %d (fixed %d, clique %d, exact %d)\n", nout, nfixed, nbest, timed_out ? 0 : 1);
    return 0;
}
