/* joint.c: joint annealing of both sides' Z22-orbit hub packings (card r3/e15).
 * usage: joint EDGES OUTFILE INITFILE SECS LAMBDA SEED CYCLE_SECS POOLFILE...
 * EDGES: base (16,5) graph (n=33792, A = 0..H-1, B = H..2H-1). INITFILE: orbit lines (global ids), first lines N in B.
 * Pool: INIT orbits first (must be self-compatible and key-disjoint), then every line of the POOLFILEs.
 * Side of a candidate: ids >= H -> side 0 (hubs on A, N in B); ids < H -> side 1 (hubs on B, N in A).
 * Conflict(i,j) on one side: keys overlap, or some shift u of N_j misses S_i = d2(N_i) (same test as r2/d06 orb.c).
 * Energy E = -(orbits on both sides) + LAM * (conflicting pairs inside both packings).
 * Moves: add a conflict-free candidate; 1-swap (add v with exactly one conflict x, remove x: plateau move);
 * Metropolis remove; Metropolis add of a conflicting candidate. Best conflict-free state is saved to OUTFILE.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define H 16896
#define W 264
#define KW 12
#define ML 17
#define MAXRAW 120000
#define NBASE 33792

static int adjA[H][16], adjB[H][16];
static uint64_t *D2[2];
static int shT[22][H];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long R(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double U(void) { return (R() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int keyof(int t) { return ((t >> 8) / 22) * 256 + (t & 255); }
static inline int shl(int t, int u) { int blk = t >> 8; int j = blk / 22, h = blk % 22; return ((j * 22 + (h + u) % 22) << 8) | (t & 255); }
static inline int bitS(const uint64_t *a, int t) { return (a[t >> 6] >> (t & 63)) & 1; }

static int rawN[2], ninit[2];
static int rawc[2][MAXRAW];
static int rawv[2][MAXRAW][ML];
static int *newidx[2];

static int P[2], Ws[2];
static int *pc[2], *pv[2];
static uint64_t *pk[2], *CF[2];
static int *conf[2], *inX[2], *memb[2], *pos[2];
static int nX[2], Cc[2];
static double LAM;
static const char *OUTF;

static int parse_line(char *line, int *ids) {
    int m = 0; char *q = line, *e;
    while (1) { long x = strtol(q, &e, 10); if (e == q) break; if (m >= ML) return -1; ids[m++] = (int)x; q = e; }
    return m;
}

/* returns 1 if the line was added to raw pool of its side */
static int add_raw(int *ids, int m) {
    if (m < 1) return 0;
    int s = ids[0] >= H ? 0 : 1;
    int t[ML]; uint64_t KU[KW]; memset(KU, 0, sizeof KU);
    for (int k = 0; k < m; k++) {
        int sk = ids[k] >= H ? 0 : 1;
        if (sk != s || ids[k] < 0 || ids[k] >= 2 * H) return 0;
        t[k] = s == 0 ? ids[k] - H : ids[k];
        int kk = keyof(t[k]);
        if ((KU[kk >> 6] >> (kk & 63)) & 1ULL) return 0;
        KU[kk >> 6] |= 1ULL << (kk & 63);
    }
    if (rawN[s] >= MAXRAW) return 0;
    int r = rawN[s]++;
    rawc[s][r] = m;
    for (int k = 0; k < m; k++) rawv[s][r][k] = t[k];
    return 1;
}

static void build_S(int s, const int *t, int m, uint64_t *S) {
    memset(S, 0, W * 8);
    for (int k = 0; k < m; k++) { const uint64_t *d = D2[s] + (size_t)t[k] * W; for (int w = 0; w < W; w++) S[w] |= d[w]; }
}

static void addv(int s, int v) {
    uint64_t *row = CF[s] + (size_t)v * Ws[s];
    Cc[s] += conf[s][v];
    for (int w = 0; w < Ws[s]; w++) { uint64_t m = row[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; conf[s][w * 64 + b]++; } }
    inX[s][v] = 1; pos[s][v] = nX[s]; memb[s][nX[s]++] = v;
}

static void remv(int s, int x) {
    uint64_t *row = CF[s] + (size_t)x * Ws[s];
    for (int w = 0; w < Ws[s]; w++) { uint64_t m = row[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; conf[s][w * 64 + b]--; } }
    Cc[s] -= conf[s][x];
    inX[s][x] = 0; int idx = pos[s][x]; int last = memb[s][--nX[s]]; memb[s][idx] = last; pos[s][last] = idx;
}

static void save(void) {
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", OUTF);
    FILE *f = fopen(tmp, "w"); if (!f) return;
    for (int s = 0; s < 2; s++) for (int a = 0; a < nX[s]; a++) {
        int v = memb[s][a];
        for (int k = 0; k < pc[s][v]; k++) fprintf(f, "%d ", pv[s][v * ML + k] + (s == 0 ? H : 0));
        fprintf(f, "\n");
    }
    fclose(f); rename(tmp, OUTF);
}

static inline int pick_v(int s, int want) { /* random non-member with conf == want (want<0: any) */
    for (int tries = 0; tries < 20000; tries++) {
        int v = (int)(R() % (unsigned long long)P[s]);
        if (inX[s][v]) continue;
        if (want < 0 || conf[s][v] == want) return v;
    }
    return -1;
}

static inline int accept(double dE, double T) { return dE <= 0 || U() < exp(-dE / T); }

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: joint EDGES OUTFILE INITFILE SECS LAMBDA SEED CYCLE_SECS POOLFILE...\n"); return 2; }
    OUTF = argv[2];
    double secs = atof(argv[4]); LAM = atof(argv[5]); double cyc = atof(argv[7]);
    rs ^= (unsigned long long)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) R();
    /* base graph */
    FILE *f = fopen(argv[1], "r"); long n, u, v; if (!f || fscanf(f, "%ld", &n) != 1 || n != 2 * H) { fprintf(stderr, "bad edges\n"); return 3; }
    static int da[H], db[H];
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = (int)v; adjB[v][db[v]++] = (int)u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    for (int s = 0; s < 2; s++) {
        int (*aT)[16] = s == 0 ? adjB : adjA, (*aS)[16] = s == 0 ? adjA : adjB;
        D2[s] = calloc((size_t)H * W, 8);
        for (int t = 0; t < H; t++) { uint64_t *dd = D2[s] + (size_t)t * W; dd[t >> 6] |= 1ULL << (t & 63);
            for (int i = 0; i < 16; i++) { int sv = aT[t][i]; for (int j = 0; j < 16; j++) { int t2 = aS[sv][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } } }
    }
    for (int u2 = 0; u2 < 22; u2++) for (int t = 0; t < H; t++) shT[u2][t] = shl(t, u2);
    double t0 = now();
    /* read init orbits then pool files */
    static char line[8192]; int ids[ML + 4];
    FILE *fi = fopen(argv[3], "r"); if (!fi) { fprintf(stderr, "no init\n"); return 3; }
    while (fgets(line, sizeof line, fi)) { int m = parse_line(line, ids); if (m <= 0) continue; if (!add_raw(ids, m)) { fprintf(stderr, "bad init line\n"); return 3; } }
    fclose(fi);
    ninit[0] = rawN[0]; ninit[1] = rawN[1];
    int nread = 0;
    for (int a = 9; a < argc; a++) {
        FILE *fp = fopen(argv[a], "r"); if (!fp) { fprintf(stderr, "skip %s\n", argv[a]); continue; }
        while (fgets(line, sizeof line, fp)) { int m = parse_line(line, ids); if (m <= 0) continue; nread += add_raw(ids, m); }
        fclose(fp);
    }
    fprintf(stderr, "raw candidates: side0 %d side1 %d (init %d %d, lines read %d)\n", rawN[0], rawN[1], ninit[0], ninit[1], nread);
    /* self-compatible filter, pool arrays */
    uint64_t *S = malloc(W * 8);
    for (int s = 0; s < 2; s++) {
        newidx[s] = malloc(sizeof(int) * (rawN[s] + 1));
        pc[s] = malloc(sizeof(int) * (rawN[s] + 1)); pv[s] = malloc(sizeof(int) * ML * (rawN[s] + 1));
        pk[s] = malloc(sizeof(uint64_t) * KW * (rawN[s] + 1)); P[s] = 0;
        for (int r = 0; r < rawN[s]; r++) {
            int m = rawc[s][r]; const int *t = rawv[s][r];
            build_S(s, t, m, S);
            int ok = 1;
            for (int uu = 1; uu < 22 && ok; uu++) { int found = 0; for (int k = 0; k < m && !found; k++) if (bitS(S, shT[uu][t[k]])) found = 1; if (!found) ok = 0; }
            if (!ok) { newidx[s][r] = -1; continue; }
            int p = P[s]++; newidx[s][r] = p; pc[s][p] = m;
            for (int k = 0; k < m; k++) pv[s][p * ML + k] = t[k];
            for (int w = 0; w < KW; w++) pk[s][p * KW + w] = 0;
            for (int k = 0; k < m; k++) { int kk = keyof(t[k]); pk[s][p * KW + (kk >> 6)] |= 1ULL << (kk & 63); }
        }
        for (int r = 0; r < ninit[s]; r++) if (newidx[s][r] < 0) { fprintf(stderr, "init orbit not self-compatible\n"); return 3; }
        fprintf(stderr, "side %d: pool %d self-compatible of %d (%.1fs)\n", s, P[s], rawN[s], now() - t0);
    }
    /* conflict matrices */
    for (int s = 0; s < 2; s++) {
        Ws[s] = (P[s] + 63) / 64; CF[s] = calloc((size_t)P[s] * Ws[s], 8);
        long nconf = 0;
        for (int i = 0; i < P[s]; i++) {
            build_S(s, pv[s] + i * ML, pc[s][i], S);
            for (int j = i + 1; j < P[s]; j++) {
                int conflict = 0;
                for (int w = 0; w < KW; w++) if (pk[s][i * KW + w] & pk[s][j * KW + w]) { conflict = 1; break; }
                if (!conflict) {
                    for (int uu = 0; uu < 22 && !conflict; uu++) {
                        int found = 0; const int *tj = pv[s] + j * ML;
                        for (int k = 0; k < pc[s][j] && !found; k++) if (bitS(S, shT[uu][tj[k]])) found = 1;
                        if (!found) conflict = 1;
                    }
                }
                if (conflict) { CF[s][(size_t)i * Ws[s] + (j >> 6)] |= 1ULL << (j & 63); CF[s][(size_t)j * Ws[s] + (i >> 6)] |= 1ULL << (i & 63); nconf++; }
            }
        }
        fprintf(stderr, "side %d: conflict pairs %ld of %ld (%.1fs)\n", s, nconf, (long)P[s] * (P[s] - 1) / 2, now() - t0);
        conf[s] = calloc(P[s] + 1, sizeof(int)); inX[s] = calloc(P[s] + 1, sizeof(int));
        memb[s] = malloc(sizeof(int) * (P[s] + 1)); pos[s] = calloc(P[s] + 1, sizeof(int)); nX[s] = 0; Cc[s] = 0;
    }
    for (int s = 0; s < 2; s++) for (int r = 0; r < ninit[s]; r++) addv(s, newidx[s][r]);
    int best = -1;
    fprintf(stderr, "init: side0 %d side1 %d Cc %d %d\n", nX[0], nX[1], Cc[0], Cc[1]);
    if (Cc[0] == 0 && Cc[1] == 0) { best = nX[0] + nX[1]; save(); }
    double cycStart = now(), tend = now() + secs; long it = 0; long nacc = 0;
    while (1) {
        if ((it & 255) == 0) {
            double tn = now(); if (tn >= tend) break;
            if (tn - cycStart >= cyc) { cycStart = tn;
                fprintf(stderr, "[%.0fs] cur %d+%d Cc %d+%d best %d (n=%d) acc %ld\n", tn - t0, nX[0], nX[1], Cc[0], Cc[1], best, NBASE + 22 * best, nacc); }
        }
        it++;
        double frac = (now() - cycStart) / cyc; if (frac > 1) frac = 1;
        double T = 0.6 * pow(0.1 / 0.6, frac);
        int s = (int)(R() & 1); double r = U();
        if (r < 0.35) {                         /* add a conflict-free candidate */
            int v = pick_v(s, 0); if (v >= 0) { addv(s, v); nacc++; }
        } else if (r < 0.70) {                  /* 1-swap: add v whose only conflict is x, remove x */
            int v = pick_v(s, 1);
            if (v >= 0 && nX[s] > 0) {
                int x = -1; uint64_t *row = CF[s] + (size_t)v * Ws[s];
                for (int a = 0; a < nX[s]; a++) { int m = memb[s][a]; if ((row[m >> 6] >> (m & 63)) & 1ULL) { x = m; break; } }
                if (x >= 0) { remv(s, x); addv(s, v); nacc++; }
            }
        } else if (r < 0.80) {                  /* Metropolis remove */
            if (nX[s] > 0) { int x = memb[s][R() % (unsigned long long)nX[s]];
                double dE = 1.0 - LAM * conf[s][x];
                if (accept(dE, T)) { remv(s, x); nacc++; } }
        } else {                                /* Metropolis add of a candidate with conflicts */
            int v = pick_v(s, -1);
            if (v >= 0) { double dE = -1.0 + LAM * conf[s][v]; if (accept(dE, T)) { addv(s, v); nacc++; } }
        }
        if (Cc[0] == 0 && Cc[1] == 0 && nX[0] + nX[1] > best) {
            best = nX[0] + nX[1]; save();
            fprintf(stderr, "[%.1fs] NEW BEST %d orbits (side0 %d side1 %d) n=%d\n", now() - t0, best, nX[0], nX[1], NBASE + 22 * best);
        }
    }
    fprintf(stderr, "done: best %d orbits, n=%d, cur %d+%d Cc %d+%d, iters %ld\n", best, NBASE + 22 * best, nX[0], nX[1], Cc[0], Cc[1], it);
    printf("best %d\n", best);
    return 0;
}
