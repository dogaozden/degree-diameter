/* e01 (round 3, beyond-small): adaptive Z22-orbit growth on side A.
 * Orbit = base hub N (16 or 17 vertices of B, key-distinct), hubs N+t, t = 0..21.
 * Conditions for a new A-orbit N (checked on the base only, since shifts are automorphisms):
 *   cover:  balls (distance 3) of N cover all of A;
 *   keys:   keys (j,y) of N unused by existing A-orbits and distinct within N (so the 22 translates are disjoint);
 *   cross:  N meets R(O+s) = d2(O)+s for every existing A-hub translate (all O, all s in Z22);
 *   self:   N meets R(N+s) for s = 1..21.
 * Joint greedy as in r2/d01/grow.c: three random-sampled lines scored by new-coverage/H + wH*new-hub-hits/hubs + noise,
 * then an exhaustive fourth line that completes cover and hub hits (else 17th vertex). Backtrack: after FAILLIM failed
 * attempts in a row, drop a random added orbit.
 * usage: grow_orb EDGES ORBFILE OUTDIR SECS SEED K NOISE WH FAILLIM
 * ORBFILE: one orbit per line, global ids. Lines with ids >= 16896 are A-orbits (N in B), lines < 16896 are B-orbits
 * (N in A), copied verbatim to the output (they never interact with A-orbits).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>

#define H 16896
#define W 264
#define HW 22
#define MAXO 64
#define NTR 22
#define MAXB 64

static int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static uint64_t ballB[H][W];   /* A-vertices within distance 3 of B-vertex */
static uint64_t d2B[H][W];     /* B-vertices within distance 2 of B-vertex */
static uint64_t S[H][HW];      /* bit hI of S[v]: v in R(hub hI), hI = orbit*22 + shift */
static int shT[NTR][H];
static unsigned char used[H];
static int orb[MAXO][17], osz[MAXO], NO = 0, NBASE = 0;
static char *bline[MAXB]; static int nb = 0;
static int (*lines)[4]; static int NL = 0;
static unsigned long long rs = 88172645463325252ULL;
static uint64_t hm[HW];
static int NHB = 0;
static long stat_fail[5];

static inline unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline void setb(uint64_t *a, int i) { a[i >> 6] |= 1ULL << (i & 63); }
static inline int bitq(const uint64_t *a, int i) { return (a[i >> 6] >> (i & 63)) & 1; }
static inline int keyof(int t) { return ((t >> 8) / 22) * 256 + (t & 255); }
static inline int shl(int t, int u) { int blk = t >> 8; int j = blk / 22, h = blk % 22; return ((j * 22 + (h + u) % 22) << 8) | (t & 255); }
static int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }

static void build_hm(void) { memset(hm, 0, sizeof hm); NHB = 22 * NO; for (int i = 0; i < NHB; i++) setb(hm, i); }

static void add_orbit(const int *N, int sz) {
    int o = NO;
    memcpy(orb[o], N, sizeof(int) * sz); osz[o] = sz;
    for (int u = 0; u < NTR; u++) for (int k = 0; k < sz; k++) used[shT[u][N[k]]] = 1;
    for (int u = 0; u < NTR; u++) {
        int hI = o * 22 + u;
        for (int k = 0; k < sz; k++) {
            uint64_t *dd = d2B[shT[u][N[k]]];
            for (int w = 0; w < W; w++) { uint64_t mm = dd[w]; while (mm) { int b = __builtin_ctzll(mm); mm &= mm - 1; setb(S[w * 64 + b], hI); } }
        }
    }
    NO++; build_hm();
}

static void remove_orbit(int r) {
    static int tmp[MAXO][17], tsz[MAXO];
    int n = NO; memcpy(tmp, orb, sizeof tmp); memcpy(tsz, osz, sizeof tsz);
    NO = 0; memset(used, 0, sizeof used); memset(S, 0, sizeof S);
    for (int o = 0; o < n; o++) if (o != r) add_orbit(tmp[o], tsz[o]);
}

/* number of violated conditions over the current orbit set (0 = valid) */
static int verify(void) {
    int bad = 0; uint64_t KU[12]; memset(KU, 0, sizeof KU);
    for (int o = 0; o < NO; o++) {
        for (int k = 0; k < osz[o]; k++) { int kk = keyof(orb[o][k]); if (bitq(KU, kk)) bad++; setb(KU, kk); }
        uint64_t c[W]; memset(c, 0, sizeof c); uint64_t M[HW]; memset(M, 0, sizeof M);
        for (int k = 0; k < osz[o]; k++) { for (int w = 0; w < W; w++) c[w] |= ballB[orb[o][k]][w]; for (int w = 0; w < HW; w++) M[w] |= S[orb[o][k]][w]; }
        for (int w = 0; w < W; w++) if (~c[w]) { bad++; break; }
        for (int o2 = 0; o2 < NO; o2++) for (int s = 0; s < 22; s++) { if (o2 == o && s == 0) continue; if (!bitq(M, o2 * 22 + s)) bad++; }
    }
    return bad;
}

static inline int freeline(const int *L, const uint64_t *KU) {
    for (int k = 0; k < 4; k++) { int v = L[k]; if (used[v]) return 0; if (bitq(KU, keyof(v))) return 0; }
    return 1;
}
static inline int gainA(const uint64_t *covA, const int *L) {
    int g = 0; for (int w = 0; w < W; w++) g += __builtin_popcountll((ballB[L[0]][w] | ballB[L[1]][w] | ballB[L[2]][w] | ballB[L[3]][w]) & ~covA[w]);
    return g;
}
static inline int gainH(const uint64_t *hit, const int *L) {
    int g = 0; for (int w = 0; w < HW; w++) g += __builtin_popcountll((S[L[0]][w] | S[L[1]][w] | S[L[2]][w] | S[L[3]][w]) & ~hit[w] & hm[w]);
    return g;
}
static inline int complete(const uint64_t *covA, const uint64_t *hit, const int *L) {
    for (int w = 0; w < W; w++) if ((covA[w] | ballB[L[0]][w] | ballB[L[1]][w] | ballB[L[2]][w] | ballB[L[3]][w]) != ~0ULL) return 0;
    for (int w = 0; w < HW; w++) if (((hit[w] | S[L[0]][w] | S[L[1]][w] | S[L[2]][w] | S[L[3]][w]) & hm[w]) != hm[w]) return 0;
    return 1;
}
static void addl(const int *L, int *chosen, int *nc, uint64_t *KU, uint64_t *covA, uint64_t *hit) {
    for (int k = 0; k < 4; k++) {
        chosen[(*nc)++] = L[k]; setb(KU, keyof(L[k]));
        for (int w = 0; w < W; w++) covA[w] |= ballB[L[k]][w];
        for (int w = 0; w < HW; w++) hit[w] |= S[L[k]][w];
    }
}
/* N meets R(N+s) for s = 1..21: some n in N with n - s in D2(N) */
static int selfok(const int *N, int sz) {
    static uint64_t D2[W]; memset(D2, 0, sizeof D2);
    for (int k = 0; k < sz; k++) for (int w = 0; w < W; w++) D2[w] |= d2B[N[k]][w];
    for (int s = 1; s < 22; s++) {
        int f = 0;
        for (int k = 0; k < sz && !f; k++) if (bitq(D2, shT[(22 - s) % 22][N[k]])) f = 1;
        if (!f) return 0;
    }
    return 1;
}

static int NLS = 40, NSAMP = 30000;
static inline double objf(const uint64_t *covO, const uint64_t *hitO, const int *L, double wH) {
    int uA = 0, uH = 0;
    for (int w = 0; w < W; w++) uA += __builtin_popcountll(~(covO[w] | ballB[L[0]][w] | ballB[L[1]][w] | ballB[L[2]][w] | ballB[L[3]][w]));
    for (int w = 0; w < HW; w++) uH += __builtin_popcountll(hm[w] & ~(hitO[w] | S[L[0]][w] | S[L[1]][w] | S[L[2]][w] | S[L[3]][w]));
    return uA / (double)H + wH * uH / (double)(NHB > 0 ? NHB : 1);
}
/* joint greedy (3 lines) then min-conflict local search over 4 lines (sampled candidates) */
static int attempt(int K, double noise, double wH, int *outN, int *outSz) {
    uint64_t covA[W], hit[HW], KU[12];
    memset(covA, 0, sizeof covA); memset(hit, 0, sizeof hit); memset(KU, 0, sizeof KU);
    int chosen[17], nc = 0;
    for (int step = 0; step < 3; step++) {
        int best = -1; double bs = -1e18; long valid = 0;
        for (long tries = 0; valid < K && tries < 60L * K; tries++) {
            int i = (int)(rnd64() % (unsigned long long)NL); int *L = lines[i];
            if (!freeline(L, KU)) continue;
            valid++;
            double sc = gainA(covA, L) / (double)H + wH * gainH(hit, L) / (double)(NHB > 0 ? NHB : 1) + noise * urand();
            if (sc > bs) { bs = sc; best = i; }
        }
        if (best < 0) { stat_fail[0]++; return 0; }
        addl(lines[best], chosen, &nc, KU, covA, hit);
    }
    /* four line indices: the 3 greedy lines are chosen[0..11] as vertex lists; recover them as line-vertex groups */
    int ln[4][4]; memset(ln, 0, sizeof ln);
    for (int q = 0; q < 3; q++) for (int k = 0; k < 4; k++) ln[q][k] = chosen[4 * q + k];
    /* local search: position p gets the best sampled replacement (ties random) */
    double cur = -1;
    for (int it = 0; it < NLS; it++) {
        int p = (it < 3) ? 3 : (it % 4);  /* first fill position 3 from the samples, then cycle */
        uint64_t cO[W], hO[HW], KO[12]; memset(cO, 0, sizeof cO); memset(hO, 0, sizeof hO); memset(KO, 0, sizeof KO);
        int oth[4][4], no = 0;
        for (int q = 0; q < 4; q++) if (q != p) { memcpy(oth[no], ln[q], sizeof(int) * 4); no++; }
        for (int q = 0; q < 3; q++) for (int k = 0; k < 4; k++) { int v = oth[q][k]; setb(KO, keyof(v));
            for (int w = 0; w < W; w++) cO[w] |= ballB[v][w]; for (int w = 0; w < HW; w++) hO[w] |= S[v][w]; }
        double bo = 1e18; int bi = -1, nt = 0;
        for (int s = 0; s < NSAMP; s++) {
            int i = (int)(rnd64() % (unsigned long long)NL); int *L = lines[i];
            if (!freeline(L, KO)) continue;
            double o = objf(cO, hO, L, wH);
            if (o < bo - 1e-12) { bo = o; bi = i; nt = 1; }
            else if (fabs(o - bo) <= 1e-12 && (rnd64() % (unsigned long long)(++nt)) == 0) bi = i;
        }
        if (bi < 0) continue;
        memcpy(ln[p], lines[bi], sizeof(int) * 4); cur = bo;
        if (bo <= 0.0) break;
    }
    /* verify final 4 lines: key-distinct, free, complete */
    uint64_t covF[W], hitF[HW], KF[12]; memset(covF, 0, sizeof covF); memset(hitF, 0, sizeof hitF); memset(KF, 0, sizeof KF);
    int fin[16], nf = 0;
    for (int q = 0; q < 4; q++) for (int k = 0; k < 4; k++) {
        int v = ln[q][k];
        if (used[v] || bitq(KF, keyof(v))) { stat_fail[0]++; return 0; }
        setb(KF, keyof(v)); fin[nf++] = v;
        for (int w = 0; w < W; w++) covF[w] |= ballB[v][w];
        for (int w = 0; w < HW; w++) hitF[w] |= S[v][w];
    }
    for (int w = 0; w < W; w++) if (~covF[w]) { stat_fail[1]++; return 0; }
    for (int w = 0; w < HW; w++) if ((hitF[w] & hm[w]) != hm[w]) { stat_fail[1]++; return 0; }
    if (!selfok(fin, 16)) { stat_fail[2]++; return 0; }
    memcpy(outN, fin, sizeof(int) * 16); *outSz = 16;
    (void)cur;
    return 1;
}

static void write_out(const char *path) {
    FILE *g = fopen(path, "w"); if (!g) return;
    for (int o = 0; o < NO; o++) { for (int k = 0; k < osz[o]; k++) fprintf(g, "%d ", orb[o][k] + H); fprintf(g, "\n"); }
    for (int b = 0; b < nb; b++) fputs(bline[b], g);
    fclose(g);
}

int main(int argc, char **argv) {
    if (argc < 12) { fprintf(stderr, "usage: grow_orb EDGES ORBFILE OUTDIR SECS SEED K NOISE WH FAILLIM NLS NSAMP\n"); return 2; }
    double secs = atof(argv[4]);
    rs ^= (unsigned long long)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    int K = atoi(argv[6]); double noise = atof(argv[7]), wH = atof(argv[8]); long FAILLIM = atol(argv[9]); NLS = atoi(argv[10]); NSAMP = atoi(argv[11]);
    double t0 = now();
    FILE *f = fopen(argv[1], "r"); long n, u, v;
    if (!f || fscanf(f, "%ld", &n) != 1 || n != 2 * H) { fprintf(stderr, "bad edges\n"); return 3; }
    int da[H] = {0}, db[H] = {0};
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = (int)v; adjB[v][db[v]++] = (int)u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    for (int t = 0; t < H; t++) {
        uint64_t *bl = ballB[t], *dd = d2B[t];
        setb(dd, t);
        for (int i = 0; i < 16; i++) { int s = adjB[t][i]; setb(bl, s); for (int j = 0; j < 16; j++) setb(dd, adjA[s][j]); }
        for (int w = 0; w < W; w++) { uint64_t mm = dd[w]; while (mm) { int b = __builtin_ctzll(mm); mm &= mm - 1; int t2 = w * 64 + b; for (int i = 0; i < 16; i++) setb(bl, adjB[t2][i]); } }
    }
    for (int u2 = 0; u2 < 22; u2++) for (int t = 0; t < H; t++) shT[u2][t] = shl(t, u2);
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    lines = malloc(sizeof(int[4]) * 66 * 85 * 64);
    for (int cv = 0; cv < 66; cv++) for (int di = 0; di < nd; di++) {
        int seen[256] = {0};
        for (int y = 0; y < 256; y++) if (!seen[y]) { for (int l = 0; l < 4; l++) { int z = y ^ scal(l, dirs[di]); seen[z] = 1; lines[NL][l] = cv * 256 + z; } NL++; }
    }
    /* load orbits */
    FILE *hf = fopen(argv[2], "r"); if (!hf) { fprintf(stderr, "no orbit file\n"); return 3; }
    char buf[1024];
    while (fgets(buf, sizeof buf, hf)) {
        int tmp[32], k = 0; char *p = buf, *e;
        for (;;) { long x = strtol(p, &e, 10); if (e == p) break; if (k < 32) tmp[k] = (int)x; k++; p = e; }
        if (k == 0) continue;
        if (tmp[0] < H) { bline[nb] = strdup(buf); nb++; continue; }
        int N[17]; for (int q = 0; q < k && q < 17; q++) N[q] = tmp[q] - H;
        if (NO >= MAXO) { fprintf(stderr, "too many orbits\n"); return 3; }
        /* keep the orbit in orb[] without touching state yet: state is rebuilt below */
        memcpy(orb[NO], N, sizeof(int) * k); osz[NO] = k; NO++;
    }
    fclose(hf);
    { int cnt = NO; NO = 0; memset(used, 0, sizeof used); memset(S, 0, sizeof S);
      static int tmp[MAXO][17], tsz[MAXO]; memcpy(tmp, orb, sizeof tmp); memcpy(tsz, osz, sizeof tsz);
      for (int o = 0; o < cnt; o++) add_orbit(tmp[o], tsz[o]); }
    build_hm();
    NBASE = NO;
    int bad = verify();
    fprintf(stderr, "loaded %d A-orbits, %d B-lines, verify violations %d (setup %.1fs, lines %d)\n", NO, nb, bad, now() - t0, NL);
    if (bad) { fprintf(stderr, "invalid start\n"); return 4; }
    int bestNO = NO; char path[512];
    snprintf(path, sizeof path, "%s/orbAB_M%d.txt", argv[3], NO); write_out(path);
    long att = 0, succ = 0, fails = 0, backs = 0;
    int N[17], sz = 0;
    while (now() - t0 < secs) {
        att++;
        if (attempt(K, noise, wH, N, &sz)) {
            add_orbit(N, sz); succ++; fails = 0;
            fprintf(stderr, "+orbit -> NO=%d (att %ld, %.1fs)\n", NO, att, now() - t0);
            if (NO > bestNO) { bestNO = NO; snprintf(path, sizeof path, "%s/orbAB_M%d.txt", argv[3], NO); write_out(path); }
            continue;
        }
        fails++;
        if (fails > FAILLIM && NO > NBASE) {
            int r = NBASE + (int)(rnd64() % (unsigned long long)(NO - NBASE));
            remove_orbit(r); backs++; fails = 0;
            fprintf(stderr, "backtrack: removed orbit %d -> NO=%d\n", r, NO);
        }
    }
    snprintf(path, sizeof path, "%s/orbAB_last.txt", argv[3]); write_out(path);
    printf("NA=%d (best %d, base %d) B-orbits %d | attempts %ld successes %ld backtracks %ld | fails: nofree %ld nocover17 %ld selfchk %ld | verify %d | %.1fs\n",
           NO, bestNO, NBASE, nb, att, succ, backs, stat_fail[0], stat_fail[1], stat_fail[2], verify(), now() - t0);
    return 0;
}
