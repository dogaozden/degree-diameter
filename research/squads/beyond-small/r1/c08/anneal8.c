/* c08: (17,5) by deleting scalars from the F_5 route chart (20,5 chart of beyond/r1/c04).
   Controller: 3+3 base, 4-regular, letter c = colour c (K3,3 colour (i+j) mod 3, doubled matching colour 3),
   lifted by Z_N (voltages volt[e], e = 0..11). Fibre F_5^4. Letter c keeps the scalar set {0..4} minus drop[c]
   (the letter `full` keeps all 5). Degree = 5+4+4+4 = 17. n = 6*N*625 = 3750*N.
   Cost = number of (source, vertex) pairs at distance > 5, sources = one rep per Z_N orbit (3750 reps).
   Bitset BFS over a subset of K reps (annealing), full K = 3750 for verification.
   usage: anneal8 N seconds seed Ksub state_in|- state_out [edges_out]
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define P 5
#define NF 625
#define MD 24
#define NREP 3750
#define FREE_N 7

static int N;
static int Ac[4][4][4], bc[4][4];
static const int BI[12] = {0,0,0,1,1,1,2,2,2,0,1,2};
static const int BJ[12] = {0,1,2,0,1,2,0,1,2,0,1,2};
static const int BC[12] = {0,1,2,1,2,0,2,0,1,3,3,3};
static const int FREE_E[FREE_N] = {4,5,7,8,9,10,11};
static int T3[4][NF][5];           /* T3[c][xid][lam] = id(A_c x + lam b_c) */
static int unpackx[NF][4];

typedef struct { int volt[12]; int full; int drop[4]; } state;

static int *adj; static int *cnt; static int nV;
static uint64_t *cu, *nx;

static int fid(const int *x) { return x[0] + 5 * x[1] + 25 * x[2] + 125 * x[3]; }

static void init_tables(void) {
    for (int id = 0; id < NF; id++) {
        int t = id; for (int k = 0; k < 4; k++) { unpackx[id][k] = t % 5; t /= 5; }
    }
    for (int c = 0; c < 4; c++) for (int id = 0; id < NF; id++) {
        int *x = unpackx[id];
        for (int lam = 0; lam < 5; lam++) {
            int y[4];
            for (int r = 0; r < 4; r++) {
                int s = 0; for (int k = 0; k < 4; k++) s += Ac[c][r][k] * x[k];
                s += lam * bc[c][r];
                y[r] = ((s % P) + P) % P;
            }
            T3[c][id][lam] = fid(y);
        }
    }
}

static int load_chart(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) return 0;
    for (int c = 0; c < 4; c++) for (int r = 0; r < 4; r++) for (int k = 0; k < 4; k++) if (fscanf(f, "%d", &Ac[c][r][k]) != 1) return 0;
    for (int c = 0; c < 4; c++) for (int r = 0; r < 4; r++) if (fscanf(f, "%d", &bc[c][r]) != 1) return 0;
    fclose(f); return 1;
}

/* build adjacency; returns 0 if the lift is not a simple 17-regular graph */
/* degree of the lift = sum over letters of |S_c| (the controller is 4-regular, one edge per letter per vertex) */
static int deg_target(const state *S) {
    int t = 0;
    for (int c = 0; c < 4; c++) for (int lam = 0; lam < 5; lam++)
        if (c == S->full || S->drop[c] < 0 || lam != S->drop[c]) t++;
    return t;
}
static int build(const state *S) {
    int off = 3 * N * NF;
    nV = 6 * N * NF;
    memset(cnt, 0, sizeof(int) * nV);
    for (int e = 0; e < 12; e++) {
        int i = BI[e], j = BJ[e], c = BC[e], v = S->volt[e];
        for (int g = 0; g < N; g++) {
            int gw = (g + v) % N;
            for (int xid = 0; xid < NF; xid++) {
                int u = (g * 3 + i) * NF + xid;
                for (int lam = 0; lam < 5; lam++) {
                    if (c != S->full && S->drop[c] >= 0 && lam == S->drop[c]) continue;
                    int w = off + (gw * 3 + j) * NF + T3[c][xid][lam];
                    if (cnt[u] >= MD || cnt[w] >= MD) return 0;
                    adj[u * MD + cnt[u]++] = w;
                    adj[w * MD + cnt[w]++] = u;
                }
            }
        }
    }
    for (int v = 0; v < nV; v++) if (cnt[v] != deg_target(S)) return 0;
    if (!getenv("NODUP")) for (int u = 0; u < off; u++) {          /* simple: no repeated neighbour (checked on A side) */
        int *a = adj + u * MD;
        for (int p = 0; p < cnt[u]; p++) for (int q = p + 1; q < cnt[u]; q++) if (a[p] == a[q]) return 0;
    }
    return 1;
}

static inline int rep_vertex(int r) {
    if (r < 1875) return (r / NF) * NF + (r % NF);            /* A(0,i,x) */
    r -= 1875; return 3 * N * NF + r;                          /* B(0,j,y) */
}

/* returns number of uncovered (source,vertex) pairs for the K sources given in subset (rep indices) */
static long eval_cost(const int *subset, int K) {
    int W = (K + 63) / 64;
    size_t sz = (size_t)nV * W;
    memset(cu, 0, sizeof(uint64_t) * sz);
    for (int k = 0; k < K; k++) { int v = rep_vertex(subset[k]); cu[(size_t)v * W + k / 64] |= 1ULL << (k % 64); }
    for (int it = 0; it < 5; it++) {
        for (int v = 0; v < nV; v++) {
            uint64_t *o = nx + (size_t)v * W; const uint64_t *s = cu + (size_t)v * W;
            for (int w = 0; w < W; w++) o[w] = s[w];
            const int *a = adj + (size_t)v * MD;
            for (int p = 0; p < cnt[v]; p++) {
                const uint64_t *t = cu + (size_t)a[p] * W;
                for (int w = 0; w < W; w++) o[w] |= t[w];
            }
        }
        uint64_t *tmp = cu; cu = nx; nx = tmp;
    }
    long covered = 0;
    for (int v = 0; v < nV; v++) for (int w = 0; w < W; w++) covered += __builtin_popcountll(cu[(size_t)v * W + w]);
    return (long)nV * K - covered;
}

static double wall(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void random_state(state *S) {
    for (int e = 0; e < 12; e++) S->volt[e] = 0;
    for (int k = 0; k < FREE_N; k++) S->volt[FREE_E[k]] = xr() % N;
    S->full = xr() % 4;
    for (int c = 0; c < 4; c++) S->drop[c] = xr() % 5;
}

static int write_edges(const state *S, const char *path) {
    FILE *f = fopen(path, "w"); if (!f) return 0;
    fprintf(f, "%d\n", nV);
    int off = 3 * N * NF;
    for (int u = 0; u < off; u++) for (int p = 0; p < cnt[u]; p++) {
        int w = adj[u * MD + p]; fprintf(f, "%d %d\n", u, w);
    }
    fclose(f); (void)S; return 1;
}

static void print_state(FILE *f, const state *S) {
    fprintf(f, "N %d full %d drop %d %d %d %d volt", N, S->full, S->drop[0], S->drop[1], S->drop[2], S->drop[3]);
    for (int e = 0; e < 12; e++) fprintf(f, " %d", S->volt[e]);
    fprintf(f, "\n");
}

static int read_state(const char *path, state *S) {
    FILE *f = fopen(path, "r"); if (!f) return 0;
    int n; char buf[16];
    if (fscanf(f, "%s %d %s %d %s %d %d %d %d %s", buf, &n, buf, &S->full, buf, &S->drop[0], &S->drop[1], &S->drop[2], &S->drop[3], buf) != 10) { fclose(f); return 0; }
    for (int e = 0; e < 12; e++) if (fscanf(f, "%d", &S->volt[e]) != 1) { fclose(f); return 0; }
    fclose(f); return n == N;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: anneal8 N seconds seed Ksub state_in|- state_out [edges_out]\n"); return 1; }
    N = atoi(argv[1]); double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    int Ksub = atoi(argv[4]); const char *sin = argv[5], *sout = argv[6]; const char *eout = argc > 7 ? argv[7] : NULL;
    if (!load_chart("chart5_s11.txt")) { fprintf(stderr, "chart load failed\n"); return 1; }
    init_tables();
    int maxV = 6 * N * NF;
    adj = malloc(sizeof(int) * (size_t)maxV * MD); cnt = malloc(sizeof(int) * maxV);
    cu = malloc(sizeof(uint64_t) * (size_t)maxV * 64); nx = malloc(sizeof(uint64_t) * (size_t)maxV * 64);
    /* subset of reps for annealing */
    int *all = malloc(sizeof(int) * NREP), *sub = malloc(sizeof(int) * NREP);
    for (int r = 0; r < NREP; r++) all[r] = r;
    for (int k = 0; k < NREP; k++) { int j = k + xr() % (NREP - k); int t = all[k]; all[k] = all[j]; all[j] = t; }
    for (int k = 0; k < Ksub; k++) sub[k] = all[k];

    state cur, best, rnd;
    if (strcmp(sin, "-") != 0 && read_state(sin, &cur)) { }
    else { do random_state(&cur); while (!build(&cur)); }
    if (!build(&cur)) { fprintf(stderr, "input state not simple\n"); return 1; }
    long cc = eval_cost(sub, Ksub), bc_sub = cc; best = cur;
    long bestfull = -1;
    double t0 = wall(); double T0 = getenv("T0") ? atof(getenv("T0")) : 300.0, Te = getenv("TE") ? atof(getenv("TE")) : 0.3; long it = 0, acc = 0;
    double el = 0;
    while ((el = wall() - t0) < secs && bc_sub > 0) {
        double frac = el / secs;
        double T = T0 * pow(Te / T0, frac);
        rnd = cur;
        double u = (xr() % 1000000) / 1e6;
        if (u < 0.80) { int e = FREE_E[xr() % FREE_N]; rnd.volt[e] = xr() % N; }
        else if (u < 0.97) { int c = xr() % 4; if (c == rnd.full) c = (c + 1) % 4; rnd.drop[c] = xr() % 5; }
        else rnd.full = xr() % 4;
        if (!build(&rnd)) continue;
        long nc = eval_cost(sub, Ksub); it++;
        if (nc <= cc || exp((double)(cc - nc) / T) > (double)(xr() % 1000000) / 1e6) {
            cur = rnd; cc = nc; acc++;
            if (cc < bc_sub) { bc_sub = cc; best = cur; }
        }
    }
    /* best state: verify on all reps */
    build(&best);
    for (int k = 0; k < NREP; k++) sub[k] = all[k];
    bestfull = eval_cost(sub, NREP);
    { int W = (NREP + 63) / 64; long ua = 0, ub = 0; int off2 = 3 * N * NF;
      long q[2][2] = {{0,0},{0,0}};
      for (int v = 0; v < nV; v++) for (int r = 0; r < NREP; r++) { int bit = (cu[(size_t)v * W + r / 64] >> (r % 64)) & 1; if (!bit) q[r >= 1875][v >= off2] ++; }
      printf("uncovered: repA->A %ld repA->B %ld repB->A %ld repB->B %ld\n", q[0][0], q[0][1], q[1][0], q[1][1]); (void)ua; (void)ub; }
    printf("N %d n %d evals %ld acc %ld best_sub %ld (K=%d) best_full_uncovered %ld\n", N, nV, it, acc, bc_sub, Ksub, bestfull);
    print_state(stdout, &best);
    FILE *f = fopen(sout, "w"); if (f) { print_state(f, &best); fclose(f); }
    if (bestfull == 0 && eout) {
        build(&best); write_edges(&best, eout);
        printf("WROTE %s\n", eout);
    }
    return 0;
}
