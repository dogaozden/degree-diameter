/* anneal: Metropolis annealing over packings of A-hubs on G (d15 card; builds on director/hubpack.c).
 *
 * State: a set of hubs on side A, each a set N of old B-vertices (|N| <= 17). A hub covers A if the union of the
 * distance-3 balls of N is all of A. Two hubs conflict if they share an old vertex, or if no x in N(h), x' in N(h')
 * has d(x,x') <= 2. Energy E = -K + LAM * C, C = number of conflicting pairs.
 * Moves: insert a new greedy 4-line hub; delete a hub; replace a hub by a new greedy hub; replace one line of a hub
 * by another pool line that keeps the cover (one extra old vertex allowed if the hub has none).
 * A chunk runs for SECS seconds at fixed temperature T, resumes from STATE_IN (hub file, global B ids), writes the
 * raw state to STATE_OUT and a conflict-free packing (best seen, cleaned and greedily filled) to VALID_OUT.
 *
 * usage: anneal EDGES DIRS SECS SEED TEMP LAMBDA STATE_IN STATE_OUT VALID_OUT [WT]
 *   STATE_IN may be a missing file (start empty). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define H 16896
#define W 264
#define MAXK 1100
#define MAXN 17
#define NSAMP 1000

static const int MUL4[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static int adjA[H][16], adjB[H][16];
static uint64_t *ball, *d2;               /* ball[t]: A-vertices within 3 of t (t in B); d2[t]: B-vertices within 2 */
static int nl;
static int (*lines)[4];
static uint64_t *lball;
static uint64_t full[W];
static unsigned long long rs = 88172645463325252ULL;
static int mk[H];
static int stamp = 0;

static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline double urand(void) { return rnd() / 4294967296.0; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int scal(int l, int a) { int r = 0; for (int k = 0; k < 4; k++) r |= MUL4[l][(a >> (2 * k)) & 3] << (2 * k); return r; }
static inline int popw(const uint64_t *a) { int c = 0; for (int i = 0; i < W; i++) c += __builtin_popcountll(a[i]); return c; }
static inline int covers(const uint64_t *S, const uint64_t *B) { for (int w = 0; w < W; w++) if (S[w] & ~B[w]) return 0; return 1; }

typedef struct { int N[MAXN]; int nn; int Q[4][4]; int nq; int E; } Cand;   /* N = Q quads (+E) */

static int K = 0, C = 0;
static int sN[MAXK][MAXN], snn[MAXK], sQ[MAXK][4][4], snq[MAXK], sE[MAXK], cc[MAXK];
static uint64_t sR[MAXK][W];              /* R = d2 of N: B-vertices within 2 of N */
static int bestN[MAXK][MAXN], bestnn[MAXK], bestK = 0;

static void flatten(Cand *c) {
    int k = 0;
    for (int q = 0; q < c->nq; q++) for (int v = 0; v < 4; v++) c->N[k++] = c->Q[q][v];
    if (c->E >= 0) c->N[k++] = c->E;
    c->nn = k;
}

static void computeR(uint64_t *R, const int *N, int nn) {
    memset(R, 0, W * 8);
    for (int k = 0; k < nn; k++) { const uint64_t *dd = d2 + (size_t)N[k] * W; for (int w = 0; w < W; w++) R[w] |= dd[w]; }
}

/* 1 if the hub with neighbours N (vertices marked with the current stamp) conflicts with state hub i */
static inline int badpair(const int *N, int nn, int i) {
    int meets = 0;
    for (int k = 0; k < nn; k++) { int x = N[k]; if ((sR[i][x >> 6] >> (x & 63)) & 1) { meets = 1; break; } }
    if (!meets) return 1;
    for (int j = 0; j < snn[i]; j++) if (mk[sN[i][j]] == stamp) return 1;
    return 0;
}

/* conflicts of candidate N with all state hubs except excl; flags[i] = 1 for conflicting hubs */
static int conf_all(const int *N, int nn, int excl, int *flags) {
    stamp++;
    for (int k = 0; k < nn; k++) mk[N[k]] = stamp;
    int c = 0;
    for (int i = 0; i < K; i++) { if (i == excl) { flags[i] = 0; continue; } int b = badpair(N, nn, i); flags[i] = b; c += b; }
    return c;
}

static void recompute_C(void) { C = 0; for (int m = 0; m < K; m++) C += cc[m]; C /= 2; }

static void rebuild_cc(void) {
    for (int j = 0; j < K; j++) {
        cc[j] = 0; stamp++;
        for (int k = 0; k < snn[j]; k++) mk[sN[j][k]] = stamp;
        for (int i = 0; i < K; i++) if (i != j) cc[j] += badpair(sN[j], snn[j], i);
    }
    recompute_C();
}

static void add_state(const Cand *c, int bc) {
    int k = K;
    memcpy(sN[k], c->N, sizeof sN[k]); snn[k] = c->nn;
    memcpy(sQ[k], c->Q, sizeof sQ[k]); snq[k] = c->nq; sE[k] = c->E;
    computeR(sR[k], sN[k], snn[k]);
    cc[k] = bc; K++;
}

static void remove_state(int i) {
    int last = K - 1;
    if (i != last) {
        memcpy(sN[i], sN[last], sizeof sN[i]); snn[i] = snn[last];
        memcpy(sQ[i], sQ[last], sizeof sQ[i]); snq[i] = snq[last]; sE[i] = sE[last];
        memcpy(sR[i], sR[last], sizeof sR[i]); cc[i] = cc[last];
    }
    K = last;
}

/* delete hub i with incremental conflict bookkeeping */
static void delete_state(int i) {
    int oldf[MAXK];
    stamp++;
    for (int k = 0; k < snn[i]; k++) mk[sN[i][k]] = stamp;
    for (int m = 0; m < K; m++) if (m != i) { oldf[m] = badpair(sN[i], snn[i], m); cc[m] -= oldf[m]; }
    remove_state(i);
    recompute_C();
}

/* replace hub i by candidate c whose conflicts with the other hubs are flags (bc of them) */
static void replace_fast(int i, const Cand *c, const int *flags, int bc) {
    int oldf[MAXK];
    stamp++;
    for (int k = 0; k < snn[i]; k++) mk[sN[i][k]] = stamp;
    for (int m = 0; m < K; m++) oldf[m] = (m == i) ? 0 : badpair(sN[i], snn[i], m);
    memcpy(sN[i], c->N, sizeof sN[i]); snn[i] = c->nn;
    memcpy(sQ[i], c->Q, sizeof sQ[i]); snq[i] = c->nq; sE[i] = c->E;
    computeR(sR[i], sN[i], snn[i]);
    for (int m = 0; m < K; m++) if (m != i) cc[m] += flags[m] - oldf[m];
    cc[i] = bc;
    recompute_C();
}

static void snapshot(void) { memcpy(bestN, sN, sizeof sN); memcpy(bestnn, snn, sizeof snn); bestK = K; }

/* greedy 4-line cover (hubpack style): first line random, then best of NSAMP random lines per step */
static int gen(Cand *c) {
    uint64_t unc[W];
    int ch[4], nch = 0, ok = 0;
    int first = rnd() % nl; ch[nch++] = first;
    for (int w = 0; w < W; w++) unc[w] = full[w] & ~lball[(size_t)first * W + w];
    if (popw(unc) == 0) ok = 1;
    for (int step = 1; step < 4 && !ok; step++) {
        int best = -1, bg = 0;
        for (int s = 0; s < NSAMP; s++) {
            int i = rnd() % nl, clash = 0;
            for (int a = 0; a < nch && !clash; a++) for (int x = 0; x < 4 && !clash; x++) for (int y = 0; y < 4; y++)
                if (lines[i][y] == lines[ch[a]][x]) { clash = 1; break; }
            if (clash) continue;
            const uint64_t *o = lball + (size_t)i * W; int g = 0;
            for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & o[w]);
            if (g > bg) { bg = g; best = i; }
        }
        if (best < 0) break;
        ch[nch++] = best;
        for (int w = 0; w < W; w++) unc[w] &= ~lball[(size_t)best * W + w];
        if (popw(unc) == 0) ok = 1;
    }
    int E = -1;
    if (!ok) {
        if (nch < 4) return 0;
        for (int s = 0; s < 4000 && !ok; s++) {
            int t = rnd() % H, clash = 0;
            if (!covers(unc, ball + (size_t)t * W)) continue;
            for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) if (lines[ch[a]][y] == t) clash = 1;
            if (clash) continue;
            E = t; ok = 1;
        }
        if (!ok) return 0;
    }
    c->nq = nch;
    for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) c->Q[a][y] = lines[ch[a]][y];
    c->E = E; flatten(c);
    return 1;
}


/* conflict-aware greedy: lines avoid used old vertices; line score = coverage gain + Wt * (hubs it makes meet) */
static int usedv[H];
static int meetsLine(int h, int l) {
    for (int v = 0; v < 4; v++) { int x = lines[l][v]; if ((sR[h][x >> 6] >> (x & 63)) & 1) return 1; }
    return 0;
}
static int lineunused(int l) { for (int v = 0; v < 4; v++) if (usedv[lines[l][v]]) return 0; return 1; }
static int gen_aware(Cand *c, double Wt) {
    memset(usedv, 0, sizeof usedv);
    for (int i = 0; i < K; i++) for (int k = 0; k < snn[i]; k++) usedv[sN[i][k]]++;
    static int pbad[MAXK];
    uint64_t unc[W];
    int ch[4], nch = 0, ok = 0, first = -1;
    for (int s = 0; s < 4000 && first < 0; s++) { int i = rnd() % nl; if (lineunused(i)) first = i; }
    if (first < 0) return 0;
    ch[nch++] = first;
    for (int w = 0; w < W; w++) unc[w] = full[w] & ~lball[(size_t)first * W + w];
    for (int h = 0; h < K; h++) pbad[h] = !meetsLine(h, first);
    if (popw(unc) == 0) ok = 1;
    for (int step = 1; step < 4 && !ok; step++) {
        int best = -1; double bs = -1e18;
        for (int s = 0; s < NSAMP; s++) {
            int i = rnd() % nl, clash = 0;
            if (!lineunused(i)) continue;
            for (int a = 0; a < nch && !clash; a++) for (int x = 0; x < 4 && !clash; x++) for (int y = 0; y < 4; y++)
                if (lines[i][y] == lines[ch[a]][x]) { clash = 1; break; }
            if (clash) continue;
            const uint64_t *o = lball + (size_t)i * W; int g = 0;
            for (int w = 0; w < W; w++) g += __builtin_popcountll(unc[w] & o[w]);
            if (g == 0) continue;
            int red = 0;
            for (int h = 0; h < K; h++) if (pbad[h] && meetsLine(h, i)) red++;
            double sc = g + Wt * red;
            if (sc > bs) { bs = sc; best = i; }
        }
        if (best < 0) break;
        ch[nch++] = best;
        for (int w = 0; w < W; w++) unc[w] &= ~lball[(size_t)best * W + w];
        for (int h = 0; h < K; h++) if (pbad[h] && meetsLine(h, best)) pbad[h] = 0;
        if (popw(unc) == 0) ok = 1;
    }
    int E = -1;
    if (!ok) {
        if (nch < 4) return 0;
        for (int s = 0; s < 4000 && !ok; s++) {
            int t = rnd() % H, clash = 0;
            if (usedv[t] || !covers(unc, ball + (size_t)t * W)) continue;
            for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) if (lines[ch[a]][y] == t) clash = 1;
            if (clash) continue;
            E = t; ok = 1;
        }
        if (!ok) return 0;
    }
    c->nq = nch;
    for (int a = 0; a < nch; a++) for (int y = 0; y < 4; y++) c->Q[a][y] = lines[ch[a]][y];
    c->E = E; flatten(c);
    return 1;
}
static double WT = 0;
static int gen_c(Cand *c) { return WT > 0 ? gen_aware(c, WT) : gen(c); }

/* replace one line of hub i by a pool line that keeps the cover */
static int lineswap(int i, Cand *c) {
    int nq = snq[i];
    if (nq < 1) return 0;
    int j = rnd() % nq;
    uint64_t U[W];
    memcpy(U, full, sizeof U);
    stamp++;
    c->nq = 0;
    for (int q = 0; q < nq; q++) {
        if (q == j) continue;
        memcpy(c->Q[c->nq], sQ[i][q], sizeof c->Q[0]); c->nq++;
        for (int v = 0; v < 4; v++) { int t = sQ[i][q][v]; mk[t] = stamp; const uint64_t *bl = ball + (size_t)t * W;
            for (int w = 0; w < W; w++) U[w] &= ~bl[w]; }
    }
    c->E = sE[i];
    if (c->E >= 0) { int t = c->E; mk[t] = stamp; const uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) U[w] &= ~bl[w]; }
    int bestL = -1, bestm = 1 << 30;
    for (int s = 0; s < 4000; s++) {
        int l = rnd() % nl, clash = 0;
        for (int v = 0; v < 4; v++) if (mk[lines[l][v]] == stamp) { clash = 1; break; }
        if (clash) continue;
        const uint64_t *o = lball + (size_t)l * W; int m = 0;
        for (int w = 0; w < W; w++) m += __builtin_popcountll(U[w] & ~o[w]);
        if (m < bestm) { bestm = m; bestL = l; if (m == 0) break; }
    }
    if (bestL < 0) return 0;
    memcpy(c->Q[c->nq], lines[bestL], sizeof(int) * 4); c->nq++;
    if (bestm > 0) {
        if (c->E >= 0) return 0;
        uint64_t U2[W]; const uint64_t *o = lball + (size_t)bestL * W;
        for (int w = 0; w < W; w++) U2[w] = U[w] & ~o[w];
        for (int v = 0; v < 4; v++) mk[lines[bestL][v]] = stamp;
        int found = -1;
        for (int s = 0; s < 4000 && found < 0; s++) {
            int t = rnd() % H;
            if (mk[t] == stamp) continue;
            if (covers(U2, ball + (size_t)t * W)) found = t;
        }
        if (found < 0) return 0;
        c->E = found;
    }
    flatten(c);
    return 1;
}

/* decomposition of a hub into 4 disjoint pool-independent lines (+1 extra vertex); used for loaded hubs */
static int Lq[160][4], nLq, selq[4];
static int dfsq(int depth, int start) {
    if (depth == 4) return 1;
    for (int a = start; a < nLq; a++) {
        int dis = 1;
        for (int d = 0; d < depth && dis; d++) for (int x = 0; x < 4 && dis; x++) for (int y = 0; y < 4; y++)
            if (Lq[a][x] == Lq[selq[d]][y]) { dis = 0; break; }
        if (!dis) continue;
        selq[depth] = a;
        if (dfsq(depth + 1, a + 1)) return 1;
    }
    return 0;
}
static int decomp(Cand *c) {
    c->nq = 0; c->E = -1;
    if (c->nn < 16) return 0;
    stamp++;
    for (int k = 0; k < c->nn; k++) mk[c->N[k]] = stamp;
    nLq = 0;
    for (int a = 0; a < c->nn; a++) for (int b = a + 1; b < c->nn; b++) {
        int x = c->N[a], y = c->N[b];
        if (x / 256 != y / 256) continue;
        int ctrl = x / 256, fx = x % 256, d = fx ^ (y % 256), ok = 1;
        int pts[4];
        for (int l = 0; l < 4; l++) { pts[l] = ctrl * 256 + (fx ^ scal(l, d)); if (mk[pts[l]] != stamp) { ok = 0; break; } }
        if (!ok || nLq >= 160) continue;
        memcpy(Lq[nLq++], pts, sizeof pts);
    }
    if (!dfsq(0, 0)) return 0;
    c->nq = 4;
    for (int q = 0; q < 4; q++) memcpy(c->Q[q], Lq[selq[q]], sizeof c->Q[q]);
    if (c->nn == 17) {
        for (int k = 0; k < 17; k++) {
            int v = c->N[k], in = 0;
            for (int q = 0; q < 4 && !in; q++) for (int y = 0; y < 4; y++) if (c->Q[q][y] == v) { in = 1; break; }
            if (!in) { c->E = v; break; }
        }
    }
    flatten(c);
    return 1;
}

static void load_state(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "no state file %s: starting empty\n", path); return; }
    static char line[8192];
    while (fgets(line, sizeof line, f)) {
        Cand c; c.nn = 0; c.nq = 0; c.E = -1;
        char *p = line, *end; long v;
        while (1) {
            v = strtol(p, &end, 10);
            if (end == p) break;
            p = end;
            if (c.nn >= MAXN || v - H < 0 || v - H >= H) { fprintf(stderr, "bad hub line\n"); exit(3); }
            c.N[c.nn++] = (int)(v - H);
        }
        if (c.nn == 0) continue;
        if (!decomp(&c)) { c.nq = 0; c.E = -1; }
        if (K >= MAXK) { fprintf(stderr, "too many hubs\n"); exit(3); }
        add_state(&c, 0);
    }
    fclose(f);
    rebuild_cc();
}

static void write_hubs(const char *path, int (*N)[MAXN], const int *nn, int k) {
    FILE *f = fopen(path, "w");
    if (!f) { fprintf(stderr, "cannot write %s\n", path); exit(4); }
    for (int i = 0; i < k; i++) { for (int j = 0; j < nn[i]; j++) fprintf(f, "%d ", N[i][j] + H); fprintf(f, "\n"); }
    fclose(f);
}

static void make_valid(void) {
    while (C > 0) {
        int bi = -1, bv = -1;
        for (int i = 0; i < K; i++) if (cc[i] > bv || (cc[i] == bv && (rnd() & 1))) { bv = cc[i]; bi = i; }
        delete_state(bi);
    }
}

static void fill(int tries) {
    static int flags[MAXK];
    Cand c;
    for (int t = 0; t < tries && K < MAXK; t++) {
        if (!gen(&c)) continue;
        int bc = conf_all(c.N, c.nn, -1, flags);
        if (bc == 0) add_state(&c, 0);
    }
    rebuild_cc();
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: anneal EDGES DIRS SECS SEED TEMP LAMBDA STATE_IN STATE_OUT VALID_OUT [WT]\n"); return 2; }
    int DIRS = atoi(argv[2]); double secs = atof(argv[3]);
    rs ^= (unsigned long long)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    double T = atof(argv[5]), LAM = atof(argv[6]);
    if (argc > 10) WT = atof(argv[10]);
    const char *STIN = argv[7], *STOUT = argv[8], *VALOUT = argv[9];

    FILE *f = fopen(argv[1], "r"); long n, u, v;
    if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) { fprintf(stderr, "bad graph\n"); return 3; }
    static int da[H], db[H];
    while (fscanf(f, "%ld %ld", &u, &v) == 2) { if (u > v) { long t = u; u = v; v = t; } v -= H; adjA[u][da[u]++] = v; adjB[v][db[v]++] = u; }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[i] != 16 || db[i] != 16) { fprintf(stderr, "not 16-regular\n"); return 3; }
    for (int w = 0; w < W; w++) full[w] = ~0ULL;

    double t0 = now();
    ball = calloc((size_t)H * W, 8); d2 = calloc((size_t)H * W, 8);
    for (int t = 0; t < H; t++) {
        uint64_t *bl = ball + (size_t)t * W, *dd = d2 + (size_t)t * W;
        dd[t >> 6] |= 1ULL << (t & 63);
        for (int i = 0; i < 16; i++) { int s = adjB[t][i]; bl[s >> 6] |= 1ULL << (s & 63);
            for (int j = 0; j < 16; j++) { int t2 = adjA[s][j]; dd[t2 >> 6] |= 1ULL << (t2 & 63); } }
        for (int w = 0; w < W; w++) { uint64_t m = dd[w]; while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
            for (int i = 0; i < 16; i++) { int s = adjB[t2][i]; bl[s >> 6] |= 1ULL << (s & 63); } } }
    }
    /* pool of lines: best DIRS directions per controller vertex (as hubpack) */
    int dirs[85], nd = 0;
    for (int c = 1; c < 256; c++) { int lead = -1; for (int k = 0; k < 4; k++) if ((c >> (2 * k)) & 3) { lead = (c >> (2 * k)) & 3; break; } if (lead == 1) dirs[nd++] = c; }
    nl = 0; lines = malloc(sizeof(int[4]) * 66 * DIRS * 64); uint64_t tmp[W];
    for (int cv = 0; cv < 66; cv++) {
        double sc[85];
        for (int di = 0; di < nd; di++) { long tot = 0;
            for (int s = 0; s < 8; s++) { int y = rnd() & 255; memset(tmp, 0, sizeof tmp);
                for (int l = 0; l < 4; l++) { int t = cv * 256 + (y ^ scal(l, dirs[di])); uint64_t *bl = ball + (size_t)t * W; for (int w = 0; w < W; w++) tmp[w] |= bl[w]; }
                tot += popw(tmp); }
            sc[di] = tot / 8.0; }
        for (int k = 0; k < DIRS; k++) {
            int bi = 0; for (int di = 1; di < nd; di++) if (sc[di] > sc[bi]) bi = di;
            sc[bi] = -1; int c = dirs[bi]; int seen[256] = {0};
            for (int y = 0; y < 256; y++) if (!seen[y]) {
                for (int l = 0; l < 4; l++) { int z = y ^ scal(l, c); seen[z] = 1; lines[nl][l] = cv * 256 + z; }
                nl++; } }
    }
    lball = malloc((size_t)nl * W * 8);
    for (int i = 0; i < nl; i++) { uint64_t *o = lball + (size_t)i * W; memset(o, 0, W * 8);
        for (int l = 0; l < 4; l++) { uint64_t *bl = ball + (size_t)lines[i][l] * W; for (int w = 0; w < W; w++) o[w] |= bl[w]; } }
    fprintf(stderr, "setup %.1fs, %d pool lines\n", now() - t0, nl);

    load_state(STIN);
    int nq_dec = 0; for (int i = 0; i < K; i++) if (snq[i] == 4) nq_dec++;
    fprintf(stderr, "loaded K=%d conflicts=%d (decomposed %d)\n", K, C, nq_dec);
    if (C == 0 && K > bestK) snapshot();

    double tr = now(); long it = 0; long nt[4] = {0}, na[4] = {0};
    int flags[MAXK]; Cand c;
    while (1) {
        if ((it & 15) == 0 && now() - tr > secs) break;
        it++;
        double r = urand();
        if (r < 0.30) {                       /* insert */
            nt[0]++;
            if (K >= MAXK || !gen_c(&c)) continue;
            int bc = conf_all(c.N, c.nn, -1, flags);
            double dE = -1.0 + LAM * bc;
            if (dE <= 0 || urand() < exp(-dE / T)) {
                na[0]++;
                for (int m = 0; m < K; m++) cc[m] += flags[m];
                add_state(&c, bc); recompute_C();
            }
        } else if (r < 0.42) {                /* delete */
            nt[1]++;
            if (K == 0) continue;
            int i = rnd() % K;
            double dE = 1.0 - LAM * cc[i];
            if (dE <= 0 || urand() < exp(-dE / T)) { na[1]++; delete_state(i); }
        } else {                              /* replace: greedy new hub (2) or line swap (3) */
            int kind = r < 0.72 ? 2 : 3;
            nt[kind]++;
            if (K == 0) continue;
            int i = rnd() % K;
            int ok = (kind == 2) ? gen_c(&c) : lineswap(i, &c);
            if (!ok) continue;
            int bc = conf_all(c.N, c.nn, i, flags);
            double dE = LAM * (bc - cc[i]);
            if (dE <= 0 || urand() < exp(-dE / T)) { na[kind]++; replace_fast(i, &c, flags, bc); }
        }
        if (C == 0 && K > bestK) snapshot();
        if (it % 4000 == 0) fprintf(stderr, "it %ld t=%.0fs K=%d C=%d bestK=%d | ins %ld/%ld del %ld/%ld rep %ld/%ld swap %ld/%ld\n",
                it, now() - tr, K, C, bestK, na[0], nt[0], na[1], nt[1], na[2], nt[2], na[3], nt[3]);
    }
    fprintf(stderr, "chunk done: it %ld K=%d C=%d bestK=%d T=%g LAM=%g\n", it, K, C, bestK, T, LAM);
    write_hubs(STOUT, sN, snn, K);
    make_valid();
    fill(3000);
    if (C == 0 && K > bestK) snapshot();
    write_hubs(VALOUT, bestN, bestnn, bestK);
    printf("raw state K=%d; valid output (best seen) K=%d\n", K, bestK);
    return 0;
}
