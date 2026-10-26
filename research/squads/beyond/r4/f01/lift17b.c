/* f01 (round 4): (17,5) route-chart lift with the (16,5) record's chart (charts/chart_u8.txt, letters 0..3)
   plus a plain fifth letter (letter 4: one neighbour per fibre point, x -> A4 x + t4).
   Controller: 3+3 base multigraph, 15 edges, properly 5-edge-coloured:
     colour 0: (i,i), colour 1: (i,i), colour 2: (i,i+1), colour 3: (i,i+2), colour 4 (plain): (i,i+1).
   Voltage lift by Z_N (N = 23 gives m = 69, n = 35,328). Fibre F4^4 (256 points), degree 4*4+1 = 17.
   Lift: (i,g,x)_A ~ (j,g+v, A_c x + lam b_c)_B for chart colours (lam in F4), and
         (i,g,x)_A ~ (j,g+v, A4 x + t4)_B for the plain colour.
   Cost = number of ordered (source, target) pairs at lift distance > 5, sources (s,0,x), s = 0..5, x in F4^4.
   By Z_N symmetry cost 0 <=> diameter <= 5. Exact bitset BFS. Simulated annealing on the 15 voltages, the plain
   letter's offset t4 and matrix A4.
   usage: lift17b chart.txt N seed iters T0 T1 out.edges */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static const int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};
static const int INV[4] = {0,1,3,2};
static uint64_t rs;
static uint64_t rnd(void) { uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define F 256
#define DEG 17
#define NS 6
#define NB 15
#define NC 5

int N, nA, nV;
int bi[NB], bj[NB], bc[NB], bt[NB], bv[NB];
int Am[NC][4][4];      /* A_0..A_3 from chart, A_4 = plain */
int bvec[NC];          /* b_0..b_3 from chart, t_4 = plain offset (as vector id) */
int Ax[NC][F];         /* id of A_c x (+ bvec[4] for plain is applied at build) */
int LB[4][4];          /* id of lam * b_c, chart letters */
int *nb, *cnt;
uint64_t *R0, *R1;
int failb;

static void vec_of(int id, int *v) { for (int k = 0; k < 4; k++) v[k] = (id >> (2 * k)) & 3; }
static int id_of(const int *v) { return v[0] | (v[1] << 2) | (v[2] << 4) | (v[3] << 6); }

static int invertible(int M0[4][4]) {
    int T[4][4]; memcpy(T, M0, sizeof T);
    int row = 0;
    for (int col = 0; col < 4; col++) {
        int p = -1;
        for (int r = row; r < 4; r++) if (T[r][col]) { p = r; break; }
        if (p < 0) return 0;
        if (p != row) for (int k = 0; k < 4; k++) { int t = T[p][k]; T[p][k] = T[row][k]; T[row][k] = t; }
        int iv = INV[T[row][col]];
        for (int r = 0; r < 4; r++) if (r != row && T[r][col]) {
            int f = MUL[T[r][col]][iv];
            for (int k = 0; k < 4; k++) T[r][k] ^= MUL[f][T[row][k]];
        }
        row++;
    }
    return 1;
}

static void recompute_letter(int c) {
    for (int x = 0; x < F; x++) {
        int v[4], o[4]; vec_of(x, v);
        for (int r = 0; r < 4; r++) { int s = 0; for (int k = 0; k < 4; k++) s ^= MUL[Am[c][r][k]][v[k]]; o[r] = s; }
        Ax[c][x] = id_of(o);
    }
}

static void setup_chart(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror("chart"); exit(1); }
    int rows[8][16];
    for (int r = 0; r < 8; r++) for (int k = 0; k < (r < 4 ? 16 : 4); k++) if (fscanf(f, "%d", &rows[r][k]) != 1) { fprintf(stderr, "chart read\n"); exit(1); }
    fclose(f);
    for (int c = 0; c < 4; c++) {
        for (int r = 0; r < 4; r++) for (int k = 0; k < 4; k++) Am[c][r][k] = rows[c][4 * r + k];
        if (!invertible(Am[c])) { fprintf(stderr, "chart A%d singular\n", c); exit(1); }
        bvec[c] = rows[4 + c][0] | (rows[4 + c][1] << 2) | (rows[4 + c][2] << 4) | (rows[4 + c][3] << 6);
        recompute_letter(c);
        int b[4]; vec_of(bvec[c], b);
        for (int l = 0; l < 4; l++) { int o[4]; for (int k = 0; k < 4; k++) o[k] = MUL[l][b[k]]; LB[c][l] = id_of(o); }
    }
}

static void random_invertible(int M[4][4]) {
    do { for (int r = 0; r < 4; r++) for (int k = 0; k < 4; k++) M[r][k] = rndi(4); } while (!invertible(M));
}

static void setup_base(void) {
    int e = 0;
    for (int i = 0; i < 3; i++) { bi[e] = i; bj[e] = i;           bc[e] = 0; e++; }
    for (int i = 0; i < 3; i++) { bi[e] = i; bj[e] = i;           bc[e] = 1; e++; }
    for (int i = 0; i < 3; i++) { bi[e] = i; bj[e] = (i + 1) % 3; bc[e] = 2; e++; }
    for (int i = 0; i < 3; i++) { bi[e] = i; bj[e] = (i + 1) % 3; bc[e] = 4; e++; }
    for (int i = 0; i < 3; i++) { bi[e] = i; bj[e] = (i + 2) % 3; bc[e] = 3; e++; }
    for (e = 0; e < NB; e++) bt[e] = (bc[e] == 4);
    for (e = 0; e < NB; e++) bv[e] = rndi(N);
}

static int volt_ok(int e) {
    for (int f = 0; f < NB; f++) if (f != e && bi[f] == bi[e] && bj[f] == bj[e] && bv[f] == bv[e]) return 0;
    return 1;
}

static void add_edge(int u, int v) {
    if (cnt[u] >= DEG || cnt[v] >= DEG) { failb = 1; return; }
    nb[u * DEG + cnt[u]++] = v; nb[v * DEG + cnt[v]++] = u;
}

static int build(void) {
    memset(cnt, 0, nV * sizeof(int)); failb = 0;
    for (int e = 0; e < NB; e++) {
        int c = bc[e];
        for (int g = 0; g < N; g++) {
            int a = bi[e] * N + g, b = bj[e] * N + (g + bv[e]) % N;
            for (int x = 0; x < F; x++) {
                int au = a * F + x;
                if (bt[e]) add_edge(au, nA + b * F + (Ax[4][x] ^ bvec[4]));
                else for (int l = 0; l < 4; l++) add_edge(au, nA + b * F + (Ax[c][x] ^ LB[c][l]));
            }
        }
    }
    if (failb) return 0;
    for (int v = 0; v < nV; v++) if (cnt[v] != DEG) return 0;
    return 1;
}

static long cost(void) {
    long total = 0;
    for (int s = 0; s < NS; s++) {
        int src = (s < 3) ? (s * N) * F : nA + ((s - 3) * N) * F;
        memset(R0, 0, (size_t)nV * 4 * sizeof(uint64_t));
        for (int x = 0; x < F; x++) R0[(size_t)(src + x) * 4 + x / 64] |= 1ULL << (x % 64);
        for (int r = 0; r < 5; r++) {
            for (int v = 0; v < nV; v++) {
                uint64_t a0 = R0[v * 4], a1 = R0[v * 4 + 1], a2 = R0[v * 4 + 2], a3 = R0[v * 4 + 3];
                const int *p = nb + (size_t)v * DEG;
                for (int k = 0; k < DEG; k++) { const uint64_t *q = R0 + (size_t)p[k] * 4; a0 |= q[0]; a1 |= q[1]; a2 |= q[2]; a3 |= q[3]; }
                R1[v * 4] = a0; R1[v * 4 + 1] = a1; R1[v * 4 + 2] = a2; R1[v * 4 + 3] = a3;
            }
            uint64_t *t = R0; R0 = R1; R1 = t;
        }
        for (int v = 0; v < nV; v++) total += F - (__builtin_popcountll(R0[v * 4]) + __builtin_popcountll(R0[v * 4 + 1]) +
                                                    __builtin_popcountll(R0[v * 4 + 2]) + __builtin_popcountll(R0[v * 4 + 3]));
    }
    return total;
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", nV);
    for (int u = 0; u < nA; u++) for (int k = 0; k < DEG; k++) fprintf(f, "%d %d\n", u, nb[(size_t)u * DEG + k]);
    fclose(f);
}

static void print_state(const char *tag, long c) {
    printf("%s cost %ld | t4=%d A4=", tag, c, bvec[4]);
    for (int r = 0; r < 4; r++) for (int k = 0; k < 4; k++) printf("%d", Am[4][r][k]);
    printf(" | base (i j volt col):");
    for (int e = 0; e < NB; e++) printf(" (%d %d %d %d)", bi[e], bj[e], bv[e], bc[e]);
    printf("\n"); fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: lift17b chart.txt N seed iters T0 T1 out.edges\n"); return 1; }
    N = atoi(argv[2]); rs = strtoull(argv[3], 0, 10) * 7919ULL + 17; long iters = atol(argv[4]);
    double T0 = atof(argv[5]), T1 = atof(argv[6]);
    nA = 3 * N * F; nV = 2 * nA;
    nb = malloc((size_t)nV * DEG * sizeof(int)); cnt = malloc(nV * sizeof(int));
    R0 = malloc((size_t)nV * 4 * 8); R1 = malloc((size_t)nV * 4 * 8);
    setup_chart(argv[1]); setup_base();
    random_invertible(Am[4]); bvec[4] = rndi(256); recompute_letter(4);
    while (1) { int ok = 1; for (int e = 0; e < NB; e++) if (!volt_ok(e)) ok = 0; if (ok) break; for (int e = 0; e < NB; e++) bv[e] = rndi(N); }
    if (!build()) { printf("RESULT build failed\n"); return 1; }
    long cur = cost(), best = cur;
    int bbv[NB], bt4; int bA4[4][4];
    memcpy(bbv, bv, sizeof bv); bt4 = bvec[4]; memcpy(bA4, Am[4], sizeof bA4);
    printf("N=%d m=%d n=%d start ", N, 3 * N, nV); print_state("", cur);
    for (long it = 0; it < iters && cur > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int kind = rndi(10);
        int ev = -1, ov = 0, ot4 = bvec[4], oA4[4][4]; memcpy(oA4, Am[4], sizeof oA4);
        if (kind < 8) {                                   /* move one voltage */
            ev = rndi(NB); ov = bv[ev];
            int nvv = rndi(N); if (nvv == ov) continue;
            bv[ev] = nvv; if (!volt_ok(ev)) { bv[ev] = ov; continue; }
        } else if (kind < 9) {                            /* move the plain offset */
            int nt = rndi(256); if (nt == bvec[4]) continue;
            bvec[4] = nt;
        } else {                                          /* one entry of the plain matrix */
            int r = rndi(4), k = rndi(4), nv = rndi(4); if (nv == Am[4][r][k]) continue;
            Am[4][r][k] = nv; if (!invertible(Am[4])) { Am[4][r][k] = oA4[r][k]; continue; }
        }
        if (kind >= 9 || kind == 8) recompute_letter(4);
        if (!build()) goto revert;
        {
            long nw = cost();
            if (nw <= cur || rndu() < exp((double)(cur - nw) / T)) {
                cur = nw;
                if (cur < best) { best = cur; memcpy(bbv, bv, sizeof bv); bt4 = bvec[4]; memcpy(bA4, Am[4], sizeof bA4); }
                if (it % 50 == 0) { printf("it %ld T %.0f ", it, T); print_state("", cur); }
                continue;
            }
        }
    revert:
        if (ev >= 0) bv[ev] = ov;
        bvec[4] = ot4; memcpy(Am[4], oA4, sizeof oA4); recompute_letter(4);
        build();
    }
    memcpy(bv, bbv, sizeof bv); bvec[4] = bt4; memcpy(Am[4], bA4, sizeof bA4); recompute_letter(4);
    if (!build()) { printf("RESULT rebuild failed\n"); return 1; }
    long fin = cost();
    print_state("FINAL", fin);
    if (fin == 0) { write_edges(argv[7]); printf("WROTE %s n=%d\n", argv[7], nV); }
    return 0;
}
