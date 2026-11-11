/* d04: route-chart lift with a fifth plain letter, degree 17 = 4*4 + 1, bipartite, diameter 5 target.
   Controller: base multigraph on 3+3 vertices (K33 + doubled matching, 4 chart letters 0..3; plain matching, letter 4),
   voltage lift by Z_N, so the controller has m = 3N vertices per side.  Lift: fibre F_4^4 (256 points).
   A-vertex (i,g,x) ~ (j,g+v,A_c x + lam b_c), lam in F_4 (chart letter c: 4 neighbours);
   plain letter: (i,g,x) ~ (j,g+v, A_4 x + off)  (1 neighbour).
   Cost = number of ordered (source, target) pairs at lift distance > 5, sources (s,0,x) for the 6 base vertices s.
   By Z_N symmetry cost 0 <=> diameter <= 5.  Simulated annealing on voltages and chart letters.
   usage: lift17 N seed iters T0 T1 out.edges      (out written when cost reaches 0) */
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

#define NC 5
#define NB 15
#define F 256
#define DEG 17
#define NS 6

int N, nA, nV;
int bi[NB], bj[NB], bv[NB], bc[NB], bt[NB];   /* bt: 0 chart letter, 1 plain */
int Mx[NC][4][4];      /* A_c over F4 */
int bvec[NC];          /* b_c (chart) or offset (plain), as vector id */
int Ax[NC][F];         /* id of A_c x */
int LB[NC][4];         /* id of lam * b_c */
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

static void setup_chart(void) {
    for (int c = 0; c < NC; c++) {
        do { for (int r = 0; r < 4; r++) for (int k = 0; k < 4; k++) Mx[c][r][k] = rndi(4); } while (!invertible(Mx[c]));
        bvec[c] = (c < 4) ? 1 + rndi(255) : rndi(256);
    }
    for (int c = 0; c < NC; c++) {
        for (int x = 0; x < F; x++) {
            int v[4], o[4]; vec_of(x, v);
            for (int r = 0; r < 4; r++) { int s = 0; for (int k = 0; k < 4; k++) s ^= MUL[Mx[c][r][k]][v[k]]; o[r] = s; }
            Ax[c][x] = id_of(o);
        }
        int b[4]; vec_of(bvec[c], b);
        for (int l = 0; l < 4; l++) { int o[4]; for (int k = 0; k < 4; k++) o[k] = MUL[l][b[k]]; LB[c][l] = id_of(o); }
    }
}

static void add_edge(int u, int v) {
    if (cnt[u] >= DEG || cnt[v] >= DEG) { failb = 1; return; }
    nb[u * DEG + cnt[u]++] = v; nb[v * DEG + cnt[v]++] = u;
}

static void setup_base(void) {
    int e = 0;
    for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { bi[e] = i; bj[e] = j; bt[e] = 0; bc[e] = rndi(4); e++; }
    for (int i = 0; i < 3; i++) { bi[e] = i; bj[e] = i; bt[e] = 0; bc[e] = rndi(4); e++; }
    for (int i = 0; i < 3; i++) { bi[e] = i; bj[e] = (i + 1) % 3; bt[e] = 1; bc[e] = 4; e++; }
    for (e = 0; e < NB; e++) bv[e] = rndi(N);
}

/* parallel base edges (same (i,j)) must have distinct voltages, else the lift has repeated edges */
static int volt_ok(int e) {
    for (int f = 0; f < NB; f++) if (f != e && bi[f] == bi[e] && bj[f] == bj[e] && bv[f] == bv[e]) return 0;
    return 1;
}

static int build(void) {
    memset(cnt, 0, nV * sizeof(int)); failb = 0;
    for (int e = 0; e < NB; e++) {
        for (int g = 0; g < N; g++) {
            int a = bi[e] * N + g, b = bj[e] * N + (g + bv[e]) % N;
            for (int x = 0; x < F; x++) {
                int au = a * F + x;
                if (bt[e] == 1) add_edge(au, nA + b * F + (Ax[bc[e]][x] ^ bvec[bc[e]]));
                else for (int l = 0; l < 4; l++) add_edge(au, nA + b * F + (Ax[bc[e]][x] ^ LB[bc[e]][l]));
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

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: lift17 N seed iters T0 T1 out.edges\n"); return 1; }
    N = atoi(argv[1]); rs = strtoull(argv[2], 0, 10) * 7919ULL + 17; long iters = atol(argv[3]);
    double T0 = atof(argv[4]), T1 = atof(argv[5]);
    nA = 3 * N * F; nV = 2 * nA;
    nb = malloc((size_t)nV * DEG * sizeof(int)); cnt = malloc(nV * sizeof(int));
    R0 = malloc((size_t)nV * 4 * 8); R1 = malloc((size_t)nV * 4 * 8);
    setup_chart(); setup_base();
    while (1) { int ok = 1; for (int e = 0; e < NB; e++) if (!volt_ok(e)) ok = 0; if (ok) break; for (int e = 0; e < NB; e++) bv[e] = rndi(N); }
    if (!build()) { printf("RESULT build failed\n"); return 1; }
    long cur = cost(), best = cur;
    int bbv[NB], bbc[NB]; memcpy(bbv, bv, sizeof bv); memcpy(bbc, bc, sizeof bc);
    printf("N=%d m=%d n=%d start cost %ld\n", N, 3 * N, nV, cur); fflush(stdout);
    for (long it = 0; it < iters && cur > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int e = rndi(NB); int ov = bv[e], oc = bc[e];
        if (bt[e] == 0 && rndi(5) == 0) { bc[e] = rndi(4); if (bc[e] == oc) continue; }
        else { bv[e] = rndi(N); if (bv[e] == ov || !volt_ok(e)) { bv[e] = ov; continue; } }
        if (!build()) { bv[e] = ov; bc[e] = oc; build(); continue; }
        long nw = cost();
        if (nw <= cur || rndu() < exp((double)(cur - nw) / T)) {
            cur = nw;
            if (cur < best) { best = cur; memcpy(bbv, bv, sizeof bv); memcpy(bbc, bc, sizeof bc); }
        } else { bv[e] = ov; bc[e] = oc; build(); }
        if (it % 100 == 0) { printf("it %ld T %.2f cur %ld best %ld\n", it, T, cur, best); fflush(stdout); }
    }
    memcpy(bv, bbv, sizeof bv); memcpy(bc, bbc, sizeof bc);
    if (!build()) { printf("RESULT rebuild failed\n"); return 1; }
    long fin = cost();
    printf("FINAL cost %ld (best %ld)\n", fin, best);
    printf("base (i j volt letter type):");
    for (int e = 0; e < NB; e++) printf(" (%d %d %d %d %d)", bi[e], bj[e], bv[e], bc[e], bt[e]);
    printf("\n");
    if (fin == 0) { write_edges(argv[6]); printf("WROTE %s n=%d\n", argv[6], nV); }
    return 0;
}
