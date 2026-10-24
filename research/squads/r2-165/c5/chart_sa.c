/* chart_sa.c: simulated annealing and symmetric search for route charts over F_4^4 (card R2-C5).
   Encodings and conditions as in chart_search.c: F_4 = {0,1,w,w^2} -> 0..3, vectors packed 2 bits per coordinate,
   addition XOR.  Universal: 216 nonbacktracking patterns nonsingular.  Pencil: 24 conditions (chart2.py).
   usage: chart_sa MODE SECONDS SEED PW OUTDIR [T0 T1 L NSHARD]
     MODE free : A_0 = I (gauge), A_1..A_3 in GL_4, b_0..b_3 free.  Cost = U + PW*Pn.
     MODE p4 | p31 : cyclic symmetry A_{k+1} = P A_k P^-1, b_{k+1} = P b_k with P unipotent of Jordan type (4)
                 resp. (3,1) (so P^4 = I).  Free data: A_0 in GL_4, b_0.  Only colour-0 representatives of the
                 pattern and pencil orbits are evaluated, and the counts are multiplied by 4 (exact: the shift
                 permutes the conditions in orbits of size 4).  Jordan types (2,2),(2,1,1) give P^2 = I, which
                 forces a pencil violation, so they are not searched.
     MODE exh4 : exhaustive scan of the p4 family restricted to b_0 = e_1 (valuation-0 class; C(P) = F_4[N]^*
                 acts transitively on valuation-0 vectors, so this covers the whole class), A_0 over PGL_4(F_4).
                 SECONDS = time limit, SEED = shard index, NSHARD = number of shards.
   Output: every distinct chart (projectively normalised, gauge A_0 = I) with U + Pn <= 4 is written to OUTDIR as
   chart_U<U>_P<Pn>_<mode>_s<seed>_<hash>.txt (rows: A_0..A_3 row-major, then b_0..b_3).  The best weighted and the
   best raw chart are written as best_*.txt.
   Build: gcc -O3 -march=native -o chart_sa chart_sa.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double ur(void) { return (double)(xr() >> 11) * (1.0 / 9007199254740992.0); }

static const int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}}, INVF[4] = {0,1,3,2};
static int smul[4][256];
typedef struct { int c[4]; } mat;   /* columns as packed vectors */
static inline int coord(int v, int r) { return (v >> (2 * r)) & 3; }
static inline int mv(const mat *M, int v) { int o = 0; for (int j = 0; j < 4; j++) o ^= smul[coord(v, j)][M->c[j]]; return o; }
static inline void mm(const mat *X, const mat *Y, mat *R) { mat T; for (int j = 0; j < 4; j++) T.c[j] = mv(X, Y->c[j]); *R = T; }
static inline int dotf(int f, int z) { int o = 0; for (int r = 0; r < 4; r++) o ^= MUL[coord(f, r)][coord(z, r)]; return o; }

static int rank_n(const int *v, int n) {   /* rank of n <= 4 packed vectors */
    int a[4]; memcpy(a, v, n * sizeof(int)); int r = 0;
    for (int col = 0; col < 4 && r < n; col++) {
        int p = -1; for (int i = r; i < n; i++) if (coord(a[i], col)) { p = i; break; }
        if (p < 0) continue;
        int t = a[p]; a[p] = a[r]; a[r] = t;
        a[r] = smul[INVF[coord(a[r], col)]][a[r]];
        for (int i = 0; i < n; i++) if (i != r && coord(a[i], col)) a[i] ^= smul[coord(a[i], col)][a[r]];
        r++;
    }
    return r;
}
static int inv_mat(const mat *M, mat *R) {
    int X[4][8];
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { X[r][c] = coord(M->c[c], r); X[r][4 + c] = (r == c); }
    for (int col = 0; col < 4; col++) {
        int p = -1; for (int r = col; r < 4; r++) if (X[r][col]) { p = r; break; }
        if (p < 0) return 0;
        for (int c = 0; c < 8; c++) { int t = X[p][c]; X[p][c] = X[col][c]; X[col][c] = t; }
        int iv = INVF[X[col][col]]; for (int c = 0; c < 8; c++) X[col][c] = MUL[iv][X[col][c]];
        for (int r = 0; r < 4; r++) if (r != col && X[r][col]) { int f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] ^= MUL[f][X[col][c]]; }
    }
    for (int c = 0; c < 4; c++) { int v = 0; for (int r = 0; r < 4; r++) v |= X[r][4 + c] << (2 * r); R->c[c] = v; }
    return 1;
}

/* ---- pencil tables: 2-dim subspaces S of F_4^4, spid[v1][v2] = id of span(v1,v2), tabS[S][z] = point of z mod S
        in PG(1,4) (0..4), -1 if z in S.  Point p = index of the annihilator class annr[S][p]. ---- */
#define NSUB 357
static int nsub = 0; static int sb1[NSUB], sb2[NSUB]; static uint64_t smk[NSUB][4];
static int16_t spid[256][256];
static int8_t tabS[NSUB][256];
static int annr[NSUB][5];
static inline int inS(int s, int v) { return (int)((smk[s][v >> 6] >> (v & 63)) & 1); }
static void init_subspaces(void) {
    for (int a = 0; a < 256; a++) for (int b = 0; b < 256; b++) spid[a][b] = -1;
    for (int v1 = 1; v1 < 256; v1++) for (int v2 = 1; v2 < 256; v2++) {
        int pr[2] = {v1, v2};
        if (rank_n(pr, 2) < 2) continue;
        uint64_t m[4] = {0, 0, 0, 0};
        for (int a = 0; a < 4; a++) for (int b = 0; b < 4; b++) { int x = smul[a][v1] ^ smul[b][v2]; m[x >> 6] |= 1ULL << (x & 63); }
        int id = -1;
        for (int s = 0; s < nsub; s++) if (!memcmp(smk[s], m, sizeof m)) { id = s; break; }
        if (id < 0) { id = nsub++; memcpy(smk[id], m, sizeof m); sb1[id] = v1; sb2[id] = v2; }
        spid[v1][v2] = (int16_t)id;
    }
    for (int s = 0; s < nsub; s++) {
        int k = 0;
        for (int f0 = 1; f0 < 256; f0++) {
            if (dotf(f0, sb1[s]) || dotf(f0, sb2[s])) continue;
            int r = 0; while (!coord(f0, r)) r++;
            int f = smul[INVF[coord(f0, r)]][f0];
            int dup = 0; for (int q = 0; q < k; q++) if (annr[s][q] == f) dup = 1;
            if (!dup && k < 5) annr[s][k++] = f;
        }
        for (int z = 0; z < 256; z++) {
            if (inS(s, z)) { tabS[s][z] = -1; continue; }
            int p = -1; for (int q = 0; q < 5; q++) if (dotf(annr[s][q], z) == 0) { p = q; break; }
            tabS[s][z] = (int8_t)p;
        }
    }
}
static inline int pen_ok(int S, const int *z) {   /* 8 vectors hit all 5 points mod the subspace S */
    if (S < 0) return 0;
    int m = 0;
    for (int k = 0; k < 8; k++) { int t = tabS[S][z[k]]; if (t >= 0) m |= 1 << t; }
    return m == 31;
}

/* ---- patterns: 108 colour words i1..i4 with consecutive colours distinct; each gives an A-side and a B-side test ---- */
static int npat = 0; static int PAT[108][4];
static void init_patterns(void) {
    for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1)
    for (int i3 = 0; i3 < 4; i3++) if (i3 != i2) for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) {
        PAT[npat][0] = i1; PAT[npat][1] = i2; PAT[npat][2] = i3; PAT[npat][3] = i4; npat++; }
}

/* ---- chart state ---- */
static int PW = 3;
static int MODE_SYM = 0; static mat PM, PMi;
typedef struct {
    mat Ap[4]; int bp[4];              /* free data (free: Ap[0] = I; sym: only Ap[0], bp[0]) */
    mat A[4], Ai[4]; int b[4];         /* chart */
    int Y[4][4], Z[4][4], cc[4];       /* Y[k][l] = A_k^-1 b_l, cc[l] = A_l^-1 b_l, Z[k][l] = A_k cc[l] */
    int U, Pn;                         /* violation counts (full units) */
} St;

static void set_P(int jordan4) {
    if (jordan4) { PM.c[0] = 5; PM.c[1] = 20; PM.c[2] = 80; PM.c[3] = 64; }   /* I+N, one Jordan block of size 4 */
    else         { PM.c[0] = 5; PM.c[1] = 20; PM.c[2] = 16; PM.c[3] = 64; }   /* I+N, Jordan type (3,1) */
    if (!inv_mat(&PM, &PMi)) { fprintf(stderr, "P singular\n"); exit(1); }
    mat Q = PM; for (int k = 0; k < 3; k++) mm(&Q, &PM, &Q);
    for (int j = 0; j < 4; j++) if (Q.c[j] != (1 << (2 * j))) { fprintf(stderr, "P^4 != I\n"); exit(1); }
}

static int build(St *s) {
    if (!MODE_SYM) {
        for (int l = 0; l < 4; l++) if (!s->bp[l]) return 0;
        s->A[0] = s->Ap[0]; s->Ai[0] = s->Ap[0];
        for (int k = 1; k < 4; k++) { s->A[k] = s->Ap[k]; if (!inv_mat(&s->A[k], &s->Ai[k])) return 0; }
        for (int l = 0; l < 4; l++) s->b[l] = s->bp[l];
    } else {
        if (!s->bp[0]) return 0;
        s->A[0] = s->Ap[0];
        if (!inv_mat(&s->A[0], &s->Ai[0])) return 0;
        s->b[0] = s->bp[0];
        for (int k = 0; k < 3; k++) {
            mat T;
            mm(&PM, &s->A[k], &T); mm(&T, &PMi, &s->A[k + 1]);
            mm(&PM, &s->Ai[k], &T); mm(&T, &PMi, &s->Ai[k + 1]);
            s->b[k + 1] = mv(&PM, s->b[k]);
        }
    }
    return 1;
}

static int univ_cnt(const St *s, int only0) {
    int U = 0;
    for (int p = 0; p < npat; p++) {
        int i1 = PAT[p][0], i2 = PAT[p][1], i3 = PAT[p][2], i4 = PAT[p][3];
        if (only0 && i1) continue;
        int v[4] = {s->Y[i2][i1], s->Y[i2][i2], s->Y[i3][i3], s->Y[i3][i4]};        /* A side */
        if (rank_n(v, 4) < 4) U++;
        int w[4] = {s->Z[i2][i1], s->b[i2], s->b[i3], s->Z[i3][i4]};               /* B side */
        if (rank_n(w, 4) < 4) U++;
    }
    return U;
}

static int pencil_cnt(const St *s, int only0) {
    int Pn = 0;
    for (int i = 0; i < 4; i++) {
        if (only0 && i) continue;
        for (int j = 0; j < 4; j++) if (j != i) {
            int z[8], n = 0;
            for (int k = 0; k < 4; k++) if (k != i) z[n++] = s->Z[i][k];              /* A_i A_k^-1 b_k */
            for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = s->b[l];
            for (int k = 0; k < 4; k++) if (k != j) z[n++] = s->Z[j][k];
            if (!pen_ok(spid[s->b[i]][s->b[j]], z)) Pn++;
            n = 0;
            for (int k = 0; k < 4; k++) if (k != i) z[n++] = s->Y[i][k];              /* A_i^-1 b_k */
            for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = s->cc[l];
            for (int k = 0; k < 4; k++) if (k != j) z[n++] = s->Y[j][k];
            if (!pen_ok(spid[s->cc[i]][s->cc[j]], z)) Pn++;
        }
    }
    return Pn;
}

static void evaluate(St *s) {
    for (int k = 0; k < 4; k++) for (int l = 0; l < 4; l++) s->Y[k][l] = mv(&s->Ai[k], s->b[l]);
    for (int l = 0; l < 4; l++) s->cc[l] = s->Y[l][l];
    for (int k = 0; k < 4; k++) for (int l = 0; l < 4; l++) s->Z[k][l] = mv(&s->A[k], s->cc[l]);
    if (!MODE_SYM) { s->U = univ_cnt(s, 0); s->Pn = pencil_cnt(s, 0); }
    else { s->U = 4 * univ_cnt(s, 1); s->Pn = 4 * pencil_cnt(s, 1); }
}

/* ---- output: gauge A_0 = I, each A_k and b_k projectively normalised (first nonzero entry 1); cost is invariant ---- */
static void normalized(const St *s, mat X[4], int bo[4]) {
    for (int k = 0; k < 4; k++) {
        mm(&s->A[k], &s->Ai[0], &X[k]);
        int e = 0;
        for (int r = 0; r < 4 && !e; r++) for (int c = 0; c < 4 && !e; c++) e = coord(X[k].c[c], r);
        if (e != 1) for (int c = 0; c < 4; c++) X[k].c[c] = smul[INVF[e]][X[k].c[c]];
    }
    for (int l = 0; l < 4; l++) {
        int v = s->b[l], e = 0;
        for (int r = 0; r < 4 && !e; r++) e = coord(v, r);
        bo[l] = smul[INVF[e]][v];
    }
}
static uint64_t hkey(const mat X[4], const int bo[4]) {
    uint64_t h = 1469598103934665603ULL;
    for (int k = 0; k < 4; k++) for (int c = 0; c < 4; c++) { h ^= (uint64_t)X[k].c[c]; h *= 1099511628211ULL; }
    for (int l = 0; l < 4; l++) { h ^= (uint64_t)bo[l]; h *= 1099511628211ULL; }
    return h ? h : 1;
}
static void write_chart_file(const char *path, const mat X[4], const int bo[4]) {
    FILE *f = fopen(path, "w"); if (!f) { perror(path); return; }
    for (int k = 0; k < 4; k++) { for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) fprintf(f, "%d ", coord(X[k].c[c], r)); fprintf(f, "\n"); }
    for (int k = 0; k < 4; k++) { for (int r = 0; r < 4; r++) fprintf(f, "%d ", coord(bo[k], r)); fprintf(f, "\n"); }
    fclose(f);
}
static uint64_t *HS; static uint64_t HM; static long hcount = 0, nrec = 0;
#define NREC_CAP 20000
static void record(const St *s, const char *outdir, const char *tag, unsigned long long seed) {
    mat X[4]; int bo[4]; normalized(s, X, bo);
    uint64_t h = hkey(X, bo), i = h & HM;
    while (HS[i]) { if (HS[i] == h) return; i = (i + 1) & HM; }
    if (hcount > (long)(HM * 0.7) || nrec >= NREC_CAP) return;
    HS[i] = h; hcount++; nrec++;
    char path[1024];
    snprintf(path, sizeof path, "%s/chart_U%d_P%d_%s_s%llu_%016llx.txt", outdir, s->U, s->Pn, tag, seed, (unsigned long long)h);
    write_chart_file(path, X, bo);
}

static double now_s(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return (double)t.tv_sec + 1e-9 * (double)t.tv_nsec; }
static void rand_gl(mat *M) { mat R; do { for (int j = 0; j < 4; j++) M->c[j] = (int)(xr() & 255); } while (!inv_mat(M, &R)); }
static int rand_nz(void) { int v; do v = (int)(xr() & 255); while (!v); return v; }
static void init_state(St *s) {
    if (!MODE_SYM) {
        s->Ap[0].c[0] = 1; s->Ap[0].c[1] = 4; s->Ap[0].c[2] = 16; s->Ap[0].c[3] = 64;   /* identity */
        for (int k = 1; k < 4; k++) rand_gl(&s->Ap[k]);
        for (int l = 0; l < 4; l++) s->bp[l] = rand_nz();
    } else { rand_gl(&s->Ap[0]); s->bp[0] = rand_nz(); }
}
/* one random move on the free data */
static void propose(St *s) {
    int nm = MODE_SYM ? 1 : 3, mb = MODE_SYM ? 0 : 1;
    int m = mb + (int)(xr() % (uint64_t)nm);
    int l = MODE_SYM ? 0 : (int)(xr() % 4);
    int t = (int)(xr() % 100);
    if (t < 40) {                       /* single entry of a matrix */
        int row = (int)(xr() % 4), col = (int)(xr() % 4), val = (int)(xr() % 4);
        s->Ap[m].c[col] = (s->Ap[m].c[col] & ~(3 << (2 * row))) | (val << (2 * row));
    } else if (t < 65) {                /* whole column of a matrix */
        int col = (int)(xr() % 4);
        s->Ap[m].c[col] = (int)(xr() & 255);
    } else if (t < 85) {                /* whole b-vector */
        s->bp[l] = rand_nz();
    } else {                            /* single coordinate of a b-vector */
        int row = (int)(xr() % 4), val = (int)(xr() % 4);
        s->bp[l] = (s->bp[l] & ~(3 << (2 * row))) | (val << (2 * row));
    }
}

/* ---- exhaustive scan (exh4) ---- */
static void run_exh(const char *outdir, double secs, int shard, int nshard) {
    MODE_SYM = 1; set_P(1);
    static St s; memset(&s, 0, sizeof s); s.bp[0] = 1;                /* b_0 = e_1 */
    static long long hist[55][7];
    long long ncand = 0, ninv = 0, n_p0 = 0; int bestU0 = 1 << 30; long long bestU0cnt = 0;
    double t0 = now_s(); uint64_t idx; uint64_t last = 0;
    const uint64_t total = 1ULL << 32;                              /* 4^16 digits: A_0 entry (r,c) = digit 4r+c */
    for (idx = (uint64_t)shard; idx < total; idx += (uint64_t)nshard) {
        last = idx;
        if (idx == 0) continue;
        int tz = __builtin_ctzll(idx);
        if (tz & 1) continue;                                       /* lowest nonzero digit must be 1 (PGL normal form) */
        if ((idx >> (tz + 1)) & 1) continue;
        for (int c = 0; c < 4; c++) { int v = 0; for (int r = 0; r < 4; r++) v |= (int)((idx >> (2 * (4 * r + c))) & 3) << (2 * r); s.Ap[0].c[c] = v; }
        ncand++;
        if (!build(&s)) continue;
        ninv++;
        evaluate(&s);
        if (s.U <= 4 * 54 && s.Pn <= 4 * 6) hist[s.U / 4][s.Pn / 4]++;
        if (s.Pn == 0) { n_p0++; if (s.U < bestU0) { bestU0 = s.U; bestU0cnt = 1; } else if (s.U == bestU0) bestU0cnt++; }
        if (s.U + s.Pn <= 4) record(&s, outdir, "exh4", (unsigned long long)shard);
        if ((ncand & ((1 << 22) - 1)) == 0 && now_s() - t0 > secs) break;
    }
    printf("exh4 shard %d/%d: last index %llu (%.2f%% of digit range), candidates %lld, invertible PGL %lld, time %.1f s\n",
           shard, nshard, (unsigned long long)last, 100.0 * (double)last / (double)total, ncand, ninv, now_s() - t0);
    printf("exh4 pencil-0 charts %lld; min orbit-univ among pencil-0 = %d (count %lld) (full univ %d)\n",
           n_p0, bestU0 == (1 << 30) ? -1 : bestU0 / 4, bestU0cnt, bestU0 == (1 << 30) ? -1 : bestU0);
    printf("histogram hist[orbit univ][orbit pencil] (orbit univ 0..12, pencil 0..2):\n");
    for (int u = 0; u <= 12; u++) { printf("  U=%2d:", 4 * u); for (int p = 0; p <= 2; p++) printf(" %8lld", hist[u][p]); printf("\n"); }
    fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: chart_sa MODE SECONDS SEED PW OUTDIR [T0 T1 L NSHARD]\n"); return 1; }
    const char *mode = argv[1];
    double secs = atof(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    PW = atoi(argv[4]);
    const char *outdir = argv[5];
    double T0 = argc > 6 ? atof(argv[6]) : 2.0, T1 = argc > 7 ? atof(argv[7]) : 0.1;
    long L = argc > 8 ? atol(argv[8]) : 200000;
    int nshard = argc > 9 ? atoi(argv[9]) : 1;
    rs ^= (seed + 1) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) xr();
    for (int l = 0; l < 4; l++) for (int v = 0; v < 256; v++) { int o = 0; for (int r = 0; r < 4; r++) o |= MUL[l][coord(v, r)] << (2 * r); smul[l][v] = o; }
    init_patterns(); init_subspaces();
    if (nsub != NSUB) { fprintf(stderr, "subspace count %d\n", nsub); return 1; }
    HS = calloc((size_t)1 << 20, sizeof(uint64_t)); HM = ((uint64_t)1 << 20) - 1;

    if (!strcmp(mode, "exh4")) { run_exh(outdir, secs, (int)seed, nshard); return 0; }
    MODE_SYM = strcmp(mode, "free") != 0;
    if (MODE_SYM) set_P(!strcmp(mode, "p4"));
    static St cur, nxt, bst, rbst;
    int bestW = 1 << 30, bestR = 1 << 30, haveB = 0, haveR = 0;
    double t0 = now_s(); long cycles = 0, steps = 0, acc = 0, nchk = 0, mism = 0;
    int stop = 0;
    while (!stop && now_s() - t0 < secs) {
        cycles++;
        do { init_state(&cur); } while (!build(&cur));
        evaluate(&cur);
        for (long st = 0; st < L; st++) {
            double T = T0 * pow(T1 / T0, (double)st / (double)L);
            nxt = cur;
            propose(&nxt);
            if (!build(&nxt)) continue;
            evaluate(&nxt);
            steps++;
            if (MODE_SYM && (steps & 4095) == 0) { nchk++; if (univ_cnt(&nxt, 0) != nxt.U || pencil_cnt(&nxt, 0) != nxt.Pn) mism++; }
            int cn = nxt.U + PW * nxt.Pn, co = cur.U + PW * cur.Pn, d = cn - co;
            if (d <= 0 || ur() < exp(-(double)d / T)) { cur = nxt; acc++; }
            if (nxt.U + nxt.Pn <= 4) record(&nxt, outdir, mode, seed);
            if (!haveB || cn < bestW) {
                bestW = cn; bst = nxt; haveB = 1;
                printf("best %d (univ %d, pencil %d) cycle %ld step %ld t %.1fs\n", cn, nxt.U, nxt.Pn, cycles, steps, now_s() - t0);
                fflush(stdout);
            }
            if (!haveR || nxt.U + nxt.Pn < bestR) {
                bestR = nxt.U + nxt.Pn; rbst = nxt; haveR = 1;
                printf("raw best (univ %d, pencil %d) cycle %ld step %ld t %.1fs\n", nxt.U, nxt.Pn, cycles, steps, now_s() - t0);
                fflush(stdout);
            }
            if ((steps & 1023) == 0 && now_s() - t0 >= secs) { stop = 1; break; }
        }
    }
    if (haveB) { mat X[4]; int bo[4]; normalized(&bst, X, bo); char p[1024]; snprintf(p, sizeof p, "%s/best_W_%s_s%llu_U%d_P%d.txt", outdir, mode, seed, bst.U, bst.Pn); write_chart_file(p, X, bo); }
    if (haveR) { mat X[4]; int bo[4]; normalized(&rbst, X, bo); char p[1024]; snprintf(p, sizeof p, "%s/best_R_%s_s%llu_U%d_P%d.txt", outdir, mode, seed, rbst.U, rbst.Pn); write_chart_file(p, X, bo); }
    printf("final: best weighted %d (univ %d, pencil %d) [PW=%d]; best raw (univ %d, pencil %d)\n", bestW, bst.U, bst.Pn, PW, rbst.U, rbst.Pn);
    printf("cycles %ld steps %ld accepted %.3f charts(U+P<=4) written %ld", cycles, steps, steps ? (double)acc / (double)steps : 0.0, nrec);
    if (MODE_SYM) printf(" symcheck mismatches %ld/%ld", mism, nchk);
    printf("\n");
    return 0;
}
