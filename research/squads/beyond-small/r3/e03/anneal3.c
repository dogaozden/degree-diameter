/* anneal3 (card e03, squad r3): Metropolis annealing over Z22-orbit hub packings.
 *
 * Side s = 0: hubs on A, base N subset of B (T = B).  Side s = 1: hubs on B, base N subset of A (T = A).
 * An orbit base N (<= 17 local vertices of T, groups of 4 = lines, optional extra vertices last) must satisfy
 *   cover  (hard):   union of ball3(N) = whole S-side;
 *   keys   (hard):   keys (j,y) = (block/22, y) of the vertices of N are distinct, and no key is shared by two orbits
 *                    of the same side (this is exactly "no old vertex in two hubs" over all 22 translates);
 *   compat (soft):   compat(M,N) iff for every u in Z22 some x in M has sh_u(x) within distance 2 of N (S_N = d2 set).
 *                    compat(N,N) = self-compatibility.
 * Energy E = -K + LAM * C, K = number of orbits, C = incompatible pairs + self-incompatible orbits (same side).
 * Moves: insert (best of MS key-free pool covers), delete, replace (best of MS), line swap (one 4-line group replaced by
 * a random pool line with free keys that keeps the cover; MTRY samples).
 * At the end of each chunk the state is cleaned (orbits dropped until conflict-free), greedily filled from the pool,
 * and VALID_OUT is overwritten if it has more orbits than the file already there.
 *
 * usage: anneal3 EDGES POOL0 POOL1 INIT SECS SEED T0 T1 LAMBDA STATE VALID_OUT
 *   POOL0 / POOL1: candidate covers (global ids, one per line) for side 0 / side 1.
 *   STATE: read if the file exists (header line STATE), else INIT (global ids, one orbit base per line).
 *   STATE is overwritten at the end with the raw (unclean) state. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define H 16896
#define W 264
#define NKW 12
#define MAXK 160
#define MAXPOOL 90000
#define MAXLINES 400000
static int MS = 8;   /* best-of samples, env ANNEAL_MS */
#define MTRY 3000

static int ad[2][H][16];               /* ad[s][t]: S-side neighbours of t, for t in T_s (T_0 = B, T_1 = A) */
static uint64_t *ballS[2], *d2T[2];    /* ballS[s][t]: S-vertices within 3 of t; d2T[s][t]: T-vertices within 2 of t */
static int shT[22][H];

static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
static inline double urand(void) { return rnd() / 4294967296.0; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int bitq(const uint64_t *a, int t) { return (a[t >> 6] >> (t & 63)) & 1; }
static inline void setb(uint64_t *a, int t) { a[t >> 6] |= 1ULL << (t & 63); }
static inline int keyof(int t) { return ((t >> 8) / 22) * 256 + (t & 255); }
static int shl(int t, int u) { int blk = t >> 8, j = blk / 22, h = blk % 22; return ((j * 22 + (h + u) % 22) << 8) | (t & 255); }

typedef struct { int n, ng; int v[17]; } Cov;
static Cov pool[2][MAXPOOL];
static uint64_t poolKey[2][MAXPOOL][NKW];
static int npool[2];
static int lines[2][MAXLINES][4];
static int nlines[2];
static Cov st[2][MAXK];
static int K[2];
static uint64_t stS[2][MAXK][W], stKey[2][MAXK][NKW];
static double LAM, T;
static uint64_t Stmp[W], Snew[W];
static int cand_list[MAXPOOL];
static long tried[4], acc[4];

static int load_edges(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    long n; if (fscanf(f, "%ld", &n) != 1 || n != 2 * H) return 0;
    static int da[2][H];
    long u, v;
    while (fscanf(f, "%ld %ld", &u, &v) == 2) {
        if (u > v) { long t = u; u = v; v = t; }
        v -= H;
        if (da[1][u] >= 16 || da[0][v] >= 16) return 0;
        ad[1][u][da[1][u]++] = (int)v;   /* A-vertex u -> B-neighbour v */
        ad[0][v][da[0][v]++] = (int)u;   /* B-vertex v -> A-neighbour u */
    }
    fclose(f);
    for (int i = 0; i < H; i++) if (da[0][i] != 16 || da[1][i] != 16) return 0;
    return 1;
}

static void compute_balls(void) {
    for (int s = 0; s < 2; s++) {
        ballS[s] = calloc((size_t)H * W, 8); d2T[s] = calloc((size_t)H * W, 8);
        for (int t = 0; t < H; t++) {
            uint64_t *bl = ballS[s] + (size_t)t * W, *dd = d2T[s] + (size_t)t * W;
            setb(dd, t);
            for (int i = 0; i < 16; i++) { int x = ad[s][t][i]; setb(bl, x);
                for (int j = 0; j < 16; j++) setb(dd, ad[1 - s][x][j]); }
            for (int w = 0; w < W; w++) { uint64_t m = dd[w];
                while (m) { int b = __builtin_ctzll(m); m &= m - 1; int t2 = w * 64 + b;
                    for (int i = 0; i < 16; i++) setb(bl, ad[s][t2][i]); } }
        }
    }
    for (int u = 0; u < 22; u++) for (int t = 0; t < H; t++) shT[u][t] = shl(t, u);
}

static void build_S(int side, const int *v, int n, uint64_t *S) {
    memset(S, 0, W * 8);
    for (int k = 0; k < n; k++) { const uint64_t *d = d2T[side] + (size_t)v[k] * W; for (int w = 0; w < W; w++) S[w] |= d[w]; }
}
static void build_B(int side, const int *v, int n, uint64_t *B) {
    memset(B, 0, W * 8);
    for (int k = 0; k < n; k++) { const uint64_t *d = ballS[side] + (size_t)v[k] * W; for (int w = 0; w < W; w++) B[w] |= d[w]; }
}
static int build_K(const int *v, int n, uint64_t *kb) {
    memset(kb, 0, NKW * 8);
    for (int k = 0; k < n; k++) { int key = keyof(v[k]); if (bitq(kb, key)) return 0; setb(kb, key); }
    return 1;
}
static int covers(int side, const int *v, int n) {
    build_B(side, v, n, Stmp);
    for (int w = 0; w < W; w++) if (Stmp[w] != ~0ULL) return 0;
    return 1;
}

/* compat of candidate (v,n) with a base whose d2-set is Sj (symmetric; self-compat when Sj is the candidate's own set) */
static inline int compat(const int *v, int n, const uint64_t *Sj) {
    for (int u = 0; u < 22; u++) {
        int ok = 0;
        for (int k = 0; k < n; k++) if (bitq(Sj, shT[u][v[k]])) { ok = 1; break; }
        if (!ok) return 0;
    }
    return 1;
}

/* conflicts of candidate (v,n,S) with the state orbits of side (except index excl); self-incompat counts 1 */
static int confcount(int side, const int *v, int n, const uint64_t *S, int excl, int stop) {
    int c = compat(v, n, S) ? 0 : 1;
    if (stop && c) return c;
    for (int j = 0; j < K[side]; j++) if (j != excl && !compat(v, n, stS[side][j])) { c++; if (stop) return c; }
    return c;
}

static void add_orb(int side, const int *v, int n, int ng) {
    int i = K[side]++;
    st[side][i].n = n; st[side][i].ng = ng; memcpy(st[side][i].v, v, n * sizeof(int));
    build_S(side, v, n, stS[side][i]); build_K(v, n, stKey[side][i]);
}
static void set_orb(int side, int i, const int *v, int n, int ng) {
    st[side][i].n = n; st[side][i].ng = ng; memcpy(st[side][i].v, v, n * sizeof(int));
    build_S(side, v, n, stS[side][i]); build_K(v, n, stKey[side][i]);
}
static void del_orb(int side, int i) {
    int last = K[side] - 1;
    if (i != last) { st[side][i] = st[side][last];
        memcpy(stS[side][i], stS[side][last], W * 8); memcpy(stKey[side][i], stKey[side][last], NKW * 8); }
    K[side]--;
}

static int free_list(int side, const uint64_t *used) {
    int m = 0;
    for (int idx = 0; idx < npool[side]; idx++) {
        const uint64_t *pk = poolKey[side][idx]; int ok = 1;
        for (int w = 0; w < NKW; w++) if (pk[w] & used[w]) { ok = 0; break; }
        if (ok) cand_list[m++] = idx;
    }
    return m;
}

static int accept(double dE) { if (dE <= 0) return 1; return urand() < exp(-dE / T); }

static void load_pool(int side, const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "no pool %s\n", fn); exit(2); }
    static char buf[4096];
    int bad = 0, badc = 0, badcov = 0;
    npool[side] = 0; nlines[side] = 0;
    while (fgets(buf, sizeof buf, f)) {
        Cov c; c.n = 0; c.ng = 0; char *q = buf; int x, off, ok = 1;
        while (c.n < 17 && sscanf(q, "%d%n", &x, &off) == 1) { q += off; c.v[c.n++] = x - (side == 0 ? H : 0); }
        if (sscanf(q, "%d%n", &x, &off) == 1) ok = 0;   /* more than 17 entries */
        if (c.n == 0) continue;
        for (int k = 0; k < c.n; k++) if (c.v[k] < 0 || c.v[k] >= H) ok = 0;
        if (!ok) { bad++; continue; }
        uint64_t kb[NKW];
        if (!build_K(c.v, c.n, kb)) { badc++; continue; }
        if (!covers(side, c.v, c.n)) { badcov++; continue; }
        c.ng = c.n / 4;
        if (npool[side] >= MAXPOOL) break;
        pool[side][npool[side]] = c; memcpy(poolKey[side][npool[side]], kb, NKW * 8); npool[side]++;
        for (int g = 0; g < c.ng && nlines[side] < MAXLINES; g++)
            for (int q2 = 0; q2 < 4; q2++) lines[side][nlines[side]][q2] = c.v[4 * g + q2], (q2 == 3 ? nlines[side]++ : 0);
    }
    fclose(f);
    fprintf(stderr, "pool side %d: %d covers, %d lines (rejected: format %d, keys %d, cover %d)\n",
            side, npool[side], nlines[side], bad, badc, badcov);
}

static void load_init(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "no init %s\n", fn); exit(2); }
    static char buf[4096];
    while (fgets(buf, sizeof buf, f)) {
        int ids[17], n = 0, x, off; char *q = buf;
        while (n < 17 && sscanf(q, "%d%n", &x, &off) == 1) { q += off; ids[n++] = x; }
        if (n == 0) continue;
        int side = ids[0] >= H ? 0 : 1, v[17];
        for (int k = 0; k < n; k++) v[k] = ids[k] - (side == 0 ? H : 0);
        if (!build_K(v, n, Stmp) || !covers(side, v, n)) { fprintf(stderr, "init orbit invalid, skipped\n"); continue; }
        add_orb(side, v, n, n / 4);
    }
    fclose(f);
}

static int load_state(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    char hdr[32]; if (fscanf(f, "%31s", hdr) != 1 || strcmp(hdr, "STATE")) { fclose(f); return 0; }
    int s, ng, n;
    while (fscanf(f, "%d %d %d", &s, &ng, &n) == 3) {
        int v[17]; for (int k = 0; k < n; k++) if (fscanf(f, "%d", &v[k]) != 1) { fprintf(stderr, "bad state\n"); exit(3); }
        add_orb(s, v, n, ng);
    }
    fclose(f);
    return 1;
}

static void write_state(const char *fn) {
    FILE *f = fopen(fn, "w"); fprintf(f, "STATE\n");
    for (int s = 0; s < 2; s++) for (int i = 0; i < K[s]; i++) {
        fprintf(f, "%d %d %d", s, st[s][i].ng, st[s][i].n);
        for (int k = 0; k < st[s][i].n; k++) fprintf(f, " %d", st[s][i].v[k]);
        fprintf(f, "\n");
    }
    fclose(f);
}

static int count_lines(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return -1;
    int c = 0, ch, any = 0;
    while ((ch = fgetc(f)) != EOF) { if (ch == '\n') { if (any) c++; any = 0; } else if (ch != ' ' && ch != '\t' && ch != '\r') any = 1; }
    if (any) c++;
    fclose(f); return c;
}

/* ---- moves ---- */
static int best_pick(int side, int excl, int m, int *bc_out) {
    int bi = -1, bc = 1 << 30;
    for (int s = 0; s < MS && m > 0; s++) {
        int idx = cand_list[rnd() % m];
        build_S(side, pool[side][idx].v, pool[side][idx].n, Stmp);
        int c = confcount(side, pool[side][idx].v, pool[side][idx].n, Stmp, excl, 0);
        if (c < bc || (c == bc && (rnd() & 1))) { bc = c; bi = idx; }
    }
    *bc_out = bc;
    return bi;
}

static void move_insert(void) {
    int side = rnd() & 1;
    if (K[side] >= MAXK - 2) return;
    uint64_t used[NKW]; memset(used, 0, sizeof used);
    for (int i = 0; i < K[side]; i++) for (int w = 0; w < NKW; w++) used[w] |= stKey[side][i][w];
    int m = free_list(side, used); if (!m) return;
    int bc; int bi = best_pick(side, -1, m, &bc); if (bi < 0) return;
    double dE = -1.0 + LAM * bc; tried[0]++;
    if (accept(dE)) { add_orb(side, pool[side][bi].v, pool[side][bi].n, pool[side][bi].ng); acc[0]++; }
}

static void move_delete(void) {
    int side = rnd() & 1; if (K[side] == 0) return;
    int i = rnd() % K[side];
    int c = confcount(side, st[side][i].v, st[side][i].n, stS[side][i], i, 0);
    double dE = 1.0 - LAM * c; tried[1]++;
    if (accept(dE)) { del_orb(side, i); acc[1]++; }
}

static void move_replace(void) {
    int side = rnd() & 1; if (K[side] == 0) return;
    int i = rnd() % K[side];
    uint64_t used[NKW]; memset(used, 0, sizeof used);
    for (int j = 0; j < K[side]; j++) if (j != i) for (int w = 0; w < NKW; w++) used[w] |= stKey[side][j][w];
    int m = free_list(side, used); if (!m) return;
    int ci = confcount(side, st[side][i].v, st[side][i].n, stS[side][i], i, 0);
    int bc; int bi = best_pick(side, i, m, &bc); if (bi < 0) return;
    double dE = LAM * (bc - ci); tried[2]++;
    if (accept(dE)) { set_orb(side, i, pool[side][bi].v, pool[side][bi].n, pool[side][bi].ng); acc[2]++; }
}

static void move_line(void) {
    int side = rnd() & 1; if (K[side] == 0) return;
    int i = rnd() % K[side];
    Cov *o = &st[side][i]; if (o->ng == 0) return;
    int g = rnd() % o->ng;
    int vs[17], nv = 0;
    for (int k = 0; k < o->n; k++) if (!(k >= 4 * g && k < 4 * g + 4)) vs[nv++] = o->v[k];
    uint64_t cov[W]; memset(cov, 0, sizeof cov);
    for (int k = 0; k < nv; k++) { const uint64_t *d = ballS[side] + (size_t)vs[k] * W; for (int w = 0; w < W; w++) cov[w] |= d[w]; }
    uint64_t kr[NKW]; memset(kr, 0, sizeof kr);
    for (int j = 0; j < K[side]; j++) if (j != i) for (int w = 0; w < NKW; w++) kr[w] |= stKey[side][j][w];
    for (int k = 0; k < nv; k++) setb(kr, keyof(vs[k]));
    int found = -1;
    for (int t = 0; t < MTRY && found < 0; t++) {
        int L = rnd() % nlines[side]; const int *a = lines[side][L];
        int kk[4], bad = 0;
        for (int q = 0; q < 4; q++) { kk[q] = keyof(a[q]); if (bitq(kr, kk[q])) bad = 1; }
        for (int q = 0; q < 4 && !bad; q++) for (int q2 = q + 1; q2 < 4; q2++) if (kk[q] == kk[q2]) bad = 1;
        if (bad) continue;
        int ok = 1;
        for (int w = 0; w < W && ok; w++) {
            uint64_t b = ballS[side][(size_t)a[0] * W + w] | ballS[side][(size_t)a[1] * W + w] |
                         ballS[side][(size_t)a[2] * W + w] | ballS[side][(size_t)a[3] * W + w];
            if (~cov[w] & ~b) ok = 0;
        }
        if (ok) found = L;
    }
    if (found < 0) return;
    int nv2[17]; memcpy(nv2, o->v, o->n * sizeof(int));
    for (int q = 0; q < 4; q++) nv2[4 * g + q] = lines[side][found][q];
    build_S(side, nv2, o->n, Snew);
    int cn = confcount(side, nv2, o->n, Snew, i, 0);
    int ci = confcount(side, o->v, o->n, stS[side][i], i, 0);
    double dE = LAM * (cn - ci); tried[3]++;
    if (accept(dE)) { set_orb(side, i, nv2, o->n, o->ng); acc[3]++; }
}

static int total_conf(void) {
    int C = 0;
    for (int s = 0; s < 2; s++) for (int i = 0; i < K[s]; i++)
        C += confcount(s, st[s][i].v, st[s][i].n, stS[s][i], i, 0);
    return C;
}

/* drop orbits until conflict-free on each side */
static void clean_side(int side) {
    while (1) {
        int worst = -1, wc = 0, cnt = 0;
        for (int i = 0; i < K[side]; i++) {
            int c = confcount(side, st[side][i].v, st[side][i].n, stS[side][i], i, 0);
            if (c > 0) cnt++;
            if (c > wc || (c == wc && c > 0 && (rnd() & 1))) { wc = c; worst = i; }
        }
        if (cnt == 0) break;
        del_orb(side, worst);
    }
}

/* greedy fill from the pool with conflict-free key-free candidates, random order */
static void fill_side(int side) {
    uint64_t used[NKW]; memset(used, 0, sizeof used);
    for (int i = 0; i < K[side]; i++) for (int w = 0; w < NKW; w++) used[w] |= stKey[side][i][w];
    int start = npool[side] ? rnd() % npool[side] : 0;
    for (int s = 0; s < npool[side]; s++) {
        int idx = (start + s) % npool[side];
        const uint64_t *pk = poolKey[side][idx]; int ok = 1;
        for (int w = 0; w < NKW; w++) if (pk[w] & used[w]) { ok = 0; break; }
        if (!ok) continue;
        build_S(side, pool[side][idx].v, pool[side][idx].n, Stmp);
        if (confcount(side, pool[side][idx].v, pool[side][idx].n, Stmp, -1, 1) == 0) {
            add_orb(side, pool[side][idx].v, pool[side][idx].n, pool[side][idx].ng);
            for (int w = 0; w < NKW; w++) used[w] |= pk[w];
        }
    }
}

static void write_valid(const char *fn) {
    FILE *f = fopen(fn, "w");
    for (int s = 0; s < 2; s++) for (int i = 0; i < K[s]; i++) {
        for (int k = 0; k < st[s][i].n; k++) fprintf(f, "%d ", st[s][i].v[k] + (s == 0 ? H : 0));
        fprintf(f, "\n");
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 12) { fprintf(stderr, "usage: anneal3 EDGES POOL0 POOL1 INIT SECS SEED T0 T1 LAMBDA STATE VALID_OUT\n"); return 2; }
    double SECS = atof(argv[5]); unsigned long long seed = strtoull(argv[6], 0, 10);
    double T0 = atof(argv[7]), T1 = atof(argv[8]); LAM = atof(argv[9]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    if (getenv("ANNEAL_MS")) MS = atoi(getenv("ANNEAL_MS"));
    double t0 = now();
    if (!load_edges(argv[1])) { fprintf(stderr, "bad edges\n"); return 3; }
    compute_balls();
    fprintf(stderr, "setup %.2fs\n", now() - t0);
    load_pool(0, argv[2]); load_pool(1, argv[3]);
    if (!load_state(argv[10])) load_init(argv[4]);
    fprintf(stderr, "start: K0=%d K1=%d conflict-degree-sum=%d (%.2fs)\n", K[0], K[1], total_conf(), now() - t0);

    double ts = now(), tend = ts + SECS, lastlog = ts; long it = 0;
    T = T0;
    while (1) {
        if ((it & 127) == 0) {
            double tn = now(); if (tn >= tend) break;
            T = T0 * pow(T1 / T0, (tn - ts) / SECS);
            if (tn - lastlog >= 10) {
                fprintf(stderr, "t=%.0f T=%.3f K0=%d K1=%d C=%d | acc ins %ld/%ld del %ld/%ld rep %ld/%ld line %ld/%ld\n",
                        tn - ts, T, K[0], K[1], total_conf(), acc[0], tried[0], acc[1], tried[1], acc[2], tried[2], acc[3], tried[3]);
                lastlog = tn;
            }
        }
        it++;
        double r = urand();
        if (r < 0.30) move_insert();
        else if (r < 0.45) move_delete();
        else if (r < 0.80) move_replace();
        else move_line();
    }
    fprintf(stderr, "end: iterations %ld, raw K0=%d K1=%d C=%d\n", it, K[0], K[1], total_conf());
    write_state(argv[10]);
    /* clean and fill */
    clean_side(0); clean_side(1);
    fill_side(0); fill_side(1);
    int kv = K[0] + K[1];
    int prev = count_lines(argv[11]);
    printf("valid orbits %d (K0=%d K1=%d) hubs %d; file had %d orbits\n", kv, K[0], K[1], 22 * kv, prev);
    if (kv > prev) { write_valid(argv[11]); printf("wrote %s\n", argv[11]); }
    return 0;
}
