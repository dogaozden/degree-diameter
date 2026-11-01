/* e04: strong max-clique search on the Z22-orbit compatibility graph (round 3, card e04).
 * Pool: key-distinct 4-line covers (generation as in r2/d06/orb.c, plus preloaded cover files).
 * Compatibility of covers N, M (same side): keys of N and M disjoint, and for every shift u in Z22 some
 * element of M+u within distance 2 of N. Self-compatibility = same test with M = N (u = 0 is trivial).
 * Test by masks: Hn[N][key] = set of h (block mod 22) of T-vertices within distance 2 of N with that key.
 * Clique search: DLS-MC style (penalty delay, plateau swaps, perturbation).
 * usage: e04 EDGES SIDE POOL SECS SEED OUTFILE [PRELOAD ...]
 *   SIDE 0 = hubs on A (cover subset of B, global ids >= H); SIDE 1 = hubs on B.
 *   OUTFILE: best clique covers, one per line, global ids. Overwritten only if it beats the file already there.
 *   env: SAMP (line samples per step, default 800), PD (penalty delay, default 2), GENFRAC (default 0.45).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <limits.h>
#include <time.h>

#define H 16896
#define W 264
#define KW 12
#define NKEY 768
#define MAXP 40000
#define HS (1 << 17)
#define FULL22 ((1u << 22) - 1)

static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static uint64_t *ball, *d2;
static int (*adjT)[16], (*adjS)[16];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static inline int keyof(int t) { return ((t >> 8) / 22) * 256 + (t & 255); }
static inline int hof(int t) { return (t >> 8) % 22; }
static inline int bitw(const uint64_t *a, int t) { return (a[t >> 6] >> (t & 63)) & 1; }
static uint64_t mix(uint64_t x) { x += 0x9E3779B97F4A7C15ULL; x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL; x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL; return x ^ (x >> 31); }

/* pool */
static int nc = 0;
static int cov[MAXP][17], csz[MAXP];
static uint64_t KS[MAXP][KW];
static uint64_t *hset;
static uint64_t full[W];

static int keysfree_and_set(const int *ids, int m, uint64_t *KU) {
    for (int i = 0; i < m; i++) { int k = keyof(ids[i]); if ((KU[k >> 6] >> (k & 63)) & 1) return 0; KU[k >> 6] |= 1ULL << (k & 63); }
    return 1;
}
/* add a cover (internal ids) if key-distinct, not a duplicate, and (if check) covering the whole other side */
static int addcover(const int *ids, int m, int check) {
    if (nc >= MAXP || m < 1 || m > 17) return 0;
    uint64_t KU[KW] = {0}; if (!keysfree_and_set(ids, m, KU)) return 0;
    uint64_t hs = 0; for (int i = 0; i < m; i++) hs += mix((uint64_t)ids[i] + 1);
    uint64_t hv = hs | 1; unsigned idx = (unsigned)(hv & (HS - 1));
    while (hset[idx]) { if (hset[idx] == hv) return 0; idx = (idx + 1) & (HS - 1); }
    if (check) { uint64_t u[W]; memset(u, 0, sizeof u);
        for (int i = 0; i < m; i++) { uint64_t *bl = ball + (size_t)ids[i] * W; for (int w = 0; w < W; w++) u[w] |= bl[w]; }
        for (int w = 0; w < W; w++) if (u[w] != full[w]) return 0; }
    hset[idx] = hv;
    for (int i = 0; i < m; i++) cov[nc][i] = ids[i];
    csz[nc] = m; memcpy(KS[nc], KU, sizeof KU); nc++;
    return 1;
}

/* DLS-MC state */
static uint64_t *Adj; static int CW, n;
static int *miss, *inC, *cl, *pos, ncl, *pen, *tabu, *smark;
static inline int adjq(int a, int b) { return (Adj[(size_t)a * CW + (b >> 6)] >> (b & 63)) & 1; }
static void addv(int v) {
    inC[v] = 1; pos[v] = ncl; cl[ncl++] = v;
    const uint64_t *row = Adj + (size_t)v * CW;
    for (int x = 0; x < n; x++) if (x != v && !((row[x >> 6] >> (x & 63)) & 1)) miss[x]++;
}
static void remv(int v) {
    inC[v] = 0; int p = pos[v]; cl[p] = cl[--ncl]; pos[cl[p]] = p;
    const uint64_t *row = Adj + (size_t)v * CW;
    for (int x = 0; x < n; x++) if (x != v && !((row[x >> 6] >> (x & 63)) & 1)) miss[x]--;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: e04 EDGES SIDE POOL SECS SEED OUTFILE [PRELOAD...]\n"); return 2; }
    double t0 = now();
    int side = atoi(argv[2]), P = atoi(argv[3]); double secs = atof(argv[4]);
    rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    const char *outf = argv[6];
    int SAMP = getenv("SAMP") ? atoi(getenv("SAMP")) : 800;
    int PD = getenv("PD") ? atoi(getenv("PD")) : 2;
    double GENFRAC = getenv("GENFRAC") ? atof(getenv("GENFRAC")) : 0.45;
    int KD = 6;
    if (P > MAXP) P = MAXP;
    FILE *f = fopen(argv[1], "r"); long nn, u, v; if (!f || fscanf(f, "%ld", &nn) != 1 || nn != 2 * H) return 3;
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
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
    for (int w = 0; w < W; w++) full[w] = ~0ULL;
    hset = calloc(HS, 8);
    fprintf(stderr, "setup %.2fs\n", now() - t0);

    /* preloaded covers (global ids; keep only lines on this side) */
    int off = side == 0 ? H : 0;
    for (int a = 7; a < argc; a++) {
        FILE *pf = fopen(argv[a], "r"); if (!pf) continue; char buf[1024]; int before = nc, bad = 0;
        while (fgets(buf, sizeof buf, pf)) { int ids[17], m = 0, x, o; char *q = buf;
            while (m < 17 && sscanf(q, "%d%n", &x, &o) == 1) { q += o; int t = x - off; if (t < 0 || t >= H) { bad = 1; break; } ids[m++] = t; }
            if (bad || m == 0) { bad = 0; continue; }
            addcover(ids, m, 1); }
        fclose(pf);
        fprintf(stderr, "preload %s: +%d covers\n", argv[a], nc - before);
    }

    /* lines (as orb: KD best directions per controller vertex) */
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

    /* generation: random greedy covers from 4 lines (+1 extra vertex) */
    double tgen = t0 + secs * GENFRAC;
    long tries = 0;
    while (nc < P && now() < tgen) {
        tries++;
        uint64_t unc[W]; memcpy(unc, full, sizeof unc);
        int ch[5], nch = 0, ok = 0; uint64_t KU[KW]; memset(KU, 0, sizeof KU);
        #define LFREE(i) ({ int _f = 1; for (int _l = 0; _l < 4 && _f; _l++) { int _k = keyof(lines[i][_l]); if ((KU[_k >> 6] >> (_k & 63)) & 1) _f = 0; } _f; })
        #define LADD(i) do { for (int _l = 0; _l < 4; _l++) { int _k = keyof(lines[i][_l]); KU[_k >> 6] |= 1ULL << (_k & 63); } ch[nch++] = (i); } while (0)
        int first; do { first = rnd() % nl; } while (!LFREE(first));
        LADD(first); { uint64_t *o = lball + (size_t)first * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w]; }
        for (int step = 1; step < 4; step++) {
            int best = -1, bg = -1;
            for (int s = 0; s < SAMP; s++) { int i = rnd() % nl; if (!LFREE(i)) continue;
                uint64_t *o = lball + (size_t)i * W; int g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & o[w]);
                if (g > bg) { bg = g; best = i; } }
            if (best < 0) break;
            LADD(best); uint64_t *o = lball + (size_t)best * W; for (int w = 0; w < W; w++) unc[w] &= ~o[w];
            if (popw(unc) == 0) { ok = 1; break; }
        }
        int ids[17], m = 0;
        if (!ok && nch == 4) {
            int extra = -1;
            for (int s = 0; s < 6000 && extra < 0; s++) { int t = rnd() % H; int k = keyof(t);
                if ((KU[k >> 6] >> (k & 63)) & 1) continue;
                uint64_t *bl = ball + (size_t)t * W; int cov1 = 1;
                for (int w = 0; w < W; w++) if (unc[w] & ~bl[w]) { cov1 = 0; break; }
                if (cov1) extra = t; }
            if (extra >= 0) ok = 1, ids[16] = extra;
            if (ok) { for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) ids[m++] = lines[ch[a]][y]; m = 17; }
        }
        if (!ok) continue;
        if (m == 0) for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) ids[m++] = lines[ch[a]][y];
        addcover(ids, m, 0);
    }
    fprintf(stderr, "pool: %d covers (%ld tries, %.1fs)\n", nc, tries, now() - t0);
    if (getenv("POOLOUT")) { FILE *po = fopen(getenv("POOLOUT"), "w");
        for (int c = 0; c < nc; c++) { for (int k = 0; k < csz[c]; k++) fprintf(po, "%d ", cov[c][k] + off); fprintf(po, "\n"); }
        fclose(po); }
    if (getenv("GENONLY")) { fprintf(stderr, "GENONLY: stop after pool\n"); return 0; }

    /* self-compatibility masks: Hn[c][key] = bit h for T-vertices t of key/h within distance 2 of cover c */
    uint32_t *Hn = calloc((size_t)nc * NKEY, 4);
    int *ok2 = malloc(4 * (size_t)nc); int n2 = 0; int *map = malloc(4 * (size_t)nc);
    #define ACC(a, m_, mm, acc_) do { acc_ = 0; for (int _i = 0; _i < mm; _i++) { int _t = (m_)[_i]; uint32_t _v = Hn[(size_t)(a) * NKEY + keyof(_t)]; int _h = hof(_t); \
        uint32_t _r = _h ? (((_v >> _h) | (_v << (22 - _h))) & FULL22) : _v; acc_ |= _r; if (acc_ == FULL22) break; } } while (0)
    for (int c = 0; c < nc; c++) {
        uint64_t S[W]; memset(S, 0, sizeof S);
        for (int k = 0; k < csz[c]; k++) { uint64_t *dd = d2 + (size_t)cov[c][k] * W; for (int w = 0; w < W; w++) S[w] |= dd[w]; }
        for (int w = 0; w < W; w++) { uint64_t mm = S[w]; while (mm) { int b = __builtin_ctzll(mm); mm &= mm - 1; int t = w * 64 + b;
            Hn[(size_t)c * NKEY + keyof(t)] |= 1u << hof(t); } }
        uint32_t acc; ACC(c, cov[c], csz[c], acc);
        ok2[c] = (acc == FULL22);
        if (ok2[c]) map[n2++] = c;
    }
    fprintf(stderr, "self-compatible orbits: %d / %d (%.1fs)\n", n2, nc, now() - t0);
    if (n2 < 2) { fprintf(stderr, "too few\n"); return 0; }

    /* compatibility graph */
    n = n2; CW = (n + 63) / 64;
    Adj = calloc((size_t)n * CW, 8);
    long ne = 0; int aborted = 0;
    for (int a = 0; a < n && !aborted; a++) { int i = map[a];
        for (int b = a + 1; b < n; b++) { int j = map[b];
            int dis = 1; for (int w = 0; w < KW; w++) if (KS[i][w] & KS[j][w]) { dis = 0; break; }
            if (!dis) continue;
            uint32_t acc; ACC(i, cov[j], csz[j], acc);
            if (acc != FULL22) continue;
            Adj[(size_t)a * CW + (b >> 6)] |= 1ULL << (b & 63); Adj[(size_t)b * CW + (a >> 6)] |= 1ULL << (a & 63); ne++; }
        if (now() - t0 > secs * 0.8) { aborted = 1; fprintf(stderr, "compat build cut at row %d\n", a); }
    }
    if (aborted) { fprintf(stderr, "compat incomplete, no search\n"); return 4; }
    double dens = n > 1 ? 2.0 * ne / ((double)n * (n - 1)) : 0;
    fprintf(stderr, "compat: %ld edges, density %.4f (%.1fs)\n", ne, dens, now() - t0);

    /* DLS-MC */
    miss = calloc(n, 4); inC = calloc(n, 4); cl = malloc(4 * (size_t)n); pos = malloc(4 * (size_t)n); ncl = 0;
    pen = calloc(n, 4); tabu = calloc(n, 4); smark = calloc(n, 4);
    int *bestcl = malloc(4 * (size_t)n), nbest = 0;
    for (int i = 0; i < n; i++) tabu[i] = 0;
    addv(rnd() % n);
    int lastadd = cl[0];
    long cycles = 0; int phase = 0;
    while (now() < t0 + secs && ncl >= 0) {
        phase++;
        for (int i = 0; i < ncl; i++) smark[cl[i]] = phase;
        int startcnt = ncl;
        while (1) {
            /* expansion */
            while (1) {
                int bv = -1, bp = INT_MAX, ties = 0;
                for (int x = 0; x < n; x++) if (!inC[x] && miss[x] == 0) {
                    if (pen[x] < bp) { bp = pen[x]; bv = x; ties = 1; }
                    else if (pen[x] == bp) { ties++; if (rnd() % ties == 0) bv = x; } }
                if (bv < 0) break;
                addv(bv); lastadd = bv;
            }
            if (ncl > nbest) { nbest = ncl; memcpy(bestcl, cl, 4 * (size_t)ncl);
                fprintf(stderr, "clique %d (%.1fs, cycle %ld)\n", nbest, now() - t0, cycles); }
            /* plateau swap */
            int bv = -1, bp = INT_MAX, ties = 0;
            for (int x = 0; x < n; x++) if (!inC[x] && miss[x] == 1 && tabu[x] != phase) {
                if (pen[x] < bp) { bp = pen[x]; bv = x; ties = 1; }
                else if (pen[x] == bp) { ties++; if (rnd() % ties == 0) bv = x; } }
            if (bv < 0) break;
            int uu = -1; for (int i = 0; i < ncl; i++) if (!adjq(cl[i], bv)) { uu = cl[i]; break; }
            if (uu < 0) break; /* cannot happen */
            remv(uu); tabu[uu] = phase; if (smark[uu] == phase) startcnt--;
            addv(bv); lastadd = bv;
            if (startcnt <= 0) break;
        }
        cycles++;
        for (int i = 0; i < ncl; i++) pen[cl[i]]++;
        if (PD > 0 && cycles % PD == 0) for (int x = 0; x < n; x++) if (pen[x] > 0) pen[x]--;
        /* perturbation */
        if (PD > 1) {
            while (ncl > 0) { int v = cl[0]; if (v == lastadd && ncl == 1) break; if (v == lastadd) v = cl[1]; remv(v); }
            if (!inC[lastadd]) addv(lastadd);
        } else {
            int v; do { v = rnd() % n; } while (inC[v]);
            for (int i = ncl - 1; i >= 0; i--) { int c = cl[i]; if (!adjq(c, v)) remv(c); }
            addv(v); lastadd = v;
        }
    }
    /* verify the best clique independently */
    int okc = 1;
    for (int a = 0; a < nbest && okc; a++) for (int b = a + 1; b < nbest && okc; b++) {
        int i = map[bestcl[a]], j = map[bestcl[b]];
        if (!adjq(bestcl[a], bestcl[b])) okc = 0;
        for (int w = 0; w < KW; w++) if (KS[i][w] & KS[j][w]) okc = 0; }
    fprintf(stderr, "best clique %d (verified pairwise %s), cycles %ld, %.1fs\n", nbest, okc ? "yes" : "NO", cycles, now() - t0);
    /* write output if better than existing file */
    int old = 0; FILE *of = fopen(outf, "r");
    if (of) { char buf[1024]; while (fgets(buf, sizeof buf, of)) if (strlen(buf) > 3) old++; fclose(of); }
    printf("side %d pool %d selfcompat %d density %.4f best %d orbits = %d hubs (file had %d)\n",
           side, nc, n2, dens, nbest, 22 * nbest, old);
    if (okc && nbest > old) {
        FILE *g = fopen(outf, "w");
        for (int a = 0; a < nbest; a++) { int c = map[bestcl[a]];
            { for (int k = 0; k < csz[c]; k++) fprintf(g, "%d ", cov[c][k] + off); fprintf(g, "\n"); } }
        fclose(g);
        printf("wrote %s\n", outf);
    }
    return 0;
}
