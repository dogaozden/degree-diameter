/* c5sa.c: simulated annealing over MIXED chart lifts of a bi-circulant 5-regular controller.
 *
 * Controller (1+1 base, voltage lift over Z_m): sides L, R; L_i ~ R_{i+s_c} for colours c = 0..4, the five shifts
 * s_c distinct mod m (so the controller is simple, 5-regular, bipartite, 5-edge-coloured).
 *   colours 0,1 = letters over F_4:  (L,i,x) ~ (R, i+s_c, A_c x + lam b_c) for all lam in F_4   (4 neighbours each)
 *   colours 2,3,4 = units:           (L,i,x) ~ (R, i+s_j, M_j x + t_j)                         (1 neighbour each)
 * Degree 2*4+3 = 11, order 2*m*256. A fibre point x in F_4^4 is packed in 8 bits, coordinate k in bits 2k,2k+1,
 * with F_4 = {0,1,2,3}, addition = XOR, multiplication table of gf.py (2 = w, 3 = w+1).
 * Both A_c and M_j are invertible (checked by the table being a permutation), so the forward edge list is symmetric.
 *
 * Z_m acts on the lift, so the sources (L,0,x) and (R,0,y) (512 of them) decide the diameter exactly.
 * Cost = number of (source, vertex) pairs at distance > 5, summed over a sample of sources (switching to all 512 when
 * the sample reaches 0).
 *
 * Usage: c5sa m seed iters nsrc T0 [outprefix]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define DIM 4
#define FIB 256
#define DEG 11
#define DIAM 5
#define MAXM 40
#define MAXN (2 * MAXM * FIB)

static const uint8_t MUL[4][4] = {{0, 0, 0, 0}, {0, 1, 2, 3}, {0, 2, 3, 1}, {0, 3, 1, 2}};

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

typedef struct {
    int s[5];                 /* shifts: colours 0..4 */
    uint8_t A[2][DIM][DIM];   /* letter matrices A_0, A_1 over F_4 */
    uint8_t b[2];             /* letter directions b_0, b_1 (packed, nonzero) */
    uint8_t U[3][DIM][DIM];   /* unit matrices M_2, M_3, M_4 */
    uint8_t t[3];             /* unit translations t_2, t_3, t_4 (packed) */
} Chart;

typedef struct {
    uint8_t Ta[2][FIB], Tai[2][FIB], Tu[3][FIB], Tui[3][FIB];
    int sb[2][4];             /* lam * b_c for lam in F_4 */
} Tabs;

static inline int coord(int x, int k) { return (x >> (2 * k)) & 3; }

static void mat_table(const uint8_t (*M)[DIM], uint8_t *tab) {
    for (int x = 0; x < FIB; x++) {
        int y = 0;
        for (int i = 0; i < DIM; i++) {
            int acc = 0;
            for (int j = 0; j < DIM; j++) acc ^= MUL[M[i][j]][coord(x, j)];
            y |= acc << (2 * i);
        }
        tab[x] = (uint8_t)y;
    }
}

static int invert_table(const uint8_t *tab, uint8_t *inv) {
    int seen[FIB];
    memset(seen, 0, sizeof seen);
    for (int x = 0; x < FIB; x++) {
        if (seen[tab[x]]) return 0;
        seen[tab[x]] = 1;
        inv[tab[x]] = (uint8_t)x;
    }
    return 1;
}

static inline int smul(int lam, int v) {
    int r = 0;
    for (int k = 0; k < DIM; k++) r |= (int)MUL[lam][coord(v, k)] << (2 * k);
    return r;
}

static int make_tabs(const Chart *C, Tabs *T) {
    for (int c = 0; c < 2; c++) {
        mat_table(C->A[c], T->Ta[c]);
        if (!invert_table(T->Ta[c], T->Tai[c])) return 0;
        for (int l = 0; l < 4; l++) T->sb[c][l] = smul(l, C->b[c]);
    }
    for (int j = 0; j < 3; j++) {
        mat_table(C->U[j], T->Tu[j]);
        if (!invert_table(T->Tu[j], T->Tui[j])) return 0;
    }
    return 1;
}

static int valid_chart(const Chart *C, int m) {
    for (int a = 0; a < 5; a++) {
        if (C->s[a] < 0 || C->s[a] >= m) return 0;
        for (int c = a + 1; c < 5; c++) if (C->s[a] == C->s[c]) return 0;
    }
    for (int c = 0; c < 2; c++) if (!C->b[c]) return 0;
    uint8_t tab[FIB], inv[FIB];
    for (int c = 0; c < 2; c++) { mat_table(C->A[c], tab); if (!invert_table(tab, inv)) return 0; }
    for (int j = 0; j < 3; j++) { mat_table(C->U[j], tab); if (!invert_table(tab, inv)) return 0; }
    return 1;
}

/* group G of order m: Z_m (GT[a][b] = a+b) or dihedral D_n with m = 2n (index g = f*n + r, (r,f)(r',f') =
 * (r + (-1)^f r', f xor f')). Bi-Cayley controller: L_g ~ R_{g v_c}, v_c = shift s_c. Left translations act regularly
 * on L, so sources (L,e,x) and (R,e,y) still decide the diameter. */
static int GT[MAXM][MAXM];
static int set_group(char type, int m) {
    if (type == 'Z') {
        for (int a = 0; a < m; a++) for (int b = 0; b < m; b++) GT[a][b] = (a + b) % m;
        return 1;
    }
    if (type == 'D') {
        if (m % 2) return 0;
        int n = m / 2;
        for (int g = 0; g < m; g++) for (int h = 0; h < m; h++) {
            int f1 = g / n, r1 = g % n, f2 = h / n, r2 = h % n;
            int r = (f1 ? (r1 - r2 + n) % n : (r1 + r2) % n);
            GT[g][h] = (f1 ^ f2) * n + r;
        }
        return 1;
    }
    return 0;
}
static char GTYPE = 'Z';

/* forward edge list from the L side: L index i*FIB+x, R index m*FIB + i*FIB + y */
static int gen_edges(const Chart *C, const Tabs *T, int m, int *eu, int *ev) {
    int ne = 0;
    for (int i = 0; i < m; i++)
        for (int x = 0; x < FIB; x++) {
            int u = i * FIB + x;
            for (int c = 0; c < 2; c++) {
                int base = T->Ta[c][x];
                int ii = GT[i][C->s[c]];
                for (int l = 0; l < 4; l++) {
                    eu[ne] = u;
                    ev[ne] = m * FIB + ii * FIB + (base ^ T->sb[c][l]);
                    ne++;
                }
            }
            for (int j = 0; j < 3; j++) {
                int ii = GT[i][C->s[2 + j]];
                eu[ne] = u;
                ev[ne] = m * FIB + ii * FIB + (T->Tu[j][x] ^ C->t[j]);
                ne++;
            }
        }
    return ne;
}

static int adjv[MAXN * DEG];
static int degc[MAXN];
static int EU[MAXN * DEG / 2 + 16], EV[MAXN * DEG / 2 + 16];

static int build_adj(const Chart *C, const Tabs *T, int m) {
    int N = 2 * m * FIB;
    int ne = gen_edges(C, T, m, EU, EV);
    memset(degc, 0, sizeof(int) * N);
    for (int e = 0; e < ne; e++) {
        int u = EU[e], v = EV[e];
        if (degc[u] >= DEG || degc[v] >= DEG) return 0;
        adjv[u * DEG + degc[u]++] = v;
        adjv[v * DEG + degc[v]++] = u;
    }
    for (int v = 0; v < N; v++) if (degc[v] != DEG) return 0;
    return N;
}

static unsigned stampv[MAXN];
static unsigned curstamp = 0;
static int Q[MAXN];

/* number of vertices within distance DIAM of src (src included) */
static int reach5(int src) {
    curstamp++;
    int head = 0, tail = 0;
    Q[tail++] = src;
    stampv[src] = curstamp;
    for (int lev = 0; lev < DIAM; lev++) {
        int end = tail;
        if (head == end) break;
        for (; head < end; head++) {
            int u = Q[head];
            for (int k = 0; k < DEG; k++) {
                int v = adjv[u * DEG + k];
                if (stampv[v] != curstamp) { stampv[v] = curstamp; Q[tail++] = v; }
            }
        }
    }
    return tail;
}

/* far pairs summed over the given sources; -1 if the chart is not a valid lift */
static long eval_srcs(const Chart *C, int m, const int *srcs, int ns) {
    Tabs T;
    if (!valid_chart(C, m)) return -1;
    if (!make_tabs(C, &T)) return -1;
    int N = build_adj(C, &T, m);
    if (!N) return -1;
    long far = 0;
    for (int q = 0; q < ns; q++) far += N - reach5(srcs[q]);
    return far;
}

static void random_mat(uint8_t M[DIM][DIM]) {
    for (int i = 0; i < DIM; i++) for (int j = 0; j < DIM; j++) M[i][j] = (uint8_t)rndint(4);
}

static void random_inv_mat(uint8_t M[DIM][DIM]) {
    uint8_t tab[FIB], inv[FIB];
    for (;;) {
        random_mat(M);
        mat_table(M, tab);
        if (invert_table(tab, inv)) return;
    }
}

static void random_chart(Chart *C, int m) {
    int perm[MAXM];
    for (int i = 0; i < m; i++) perm[i] = i;
    for (int i = m - 1; i > 0; i--) { int j = rndint(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int k = 0; k < 5; k++) C->s[k] = perm[k];
    for (int c = 0; c < 2; c++) { random_inv_mat(C->A[c]); C->b[c] = (uint8_t)(1 + rndint(255)); }
    for (int j = 0; j < 3; j++) { random_inv_mat(C->U[j]); C->t[j] = (uint8_t)rndint(256); }
}

static void mutate(Chart *C, int m) {
    double r = rnd01();
    if (r < 0.10) {
        C->s[rndint(5)] = rndint(m);
    } else if (r < 0.75) {
        int w = rndint(5), i = rndint(DIM), j = rndint(DIM), v = rndint(4);
        if (w < 2) C->A[w][i][j] = (uint8_t)v; else C->U[w - 2][i][j] = (uint8_t)v;
    } else {
        int w = rndint(5);
        if (w < 2) C->b[w] = (uint8_t)(1 + rndint(255)); else C->t[w - 2] = (uint8_t)rndint(256);
    }
}

static void write_chart(FILE *f, const Chart *C, int m) {
    fprintf(f, "m %d\nshifts %d %d %d %d %d\n", m, C->s[0], C->s[1], C->s[2], C->s[3], C->s[4]);
    for (int c = 0; c < 2; c++) {
        fprintf(f, "A%d", c);
        for (int i = 0; i < DIM; i++) for (int j = 0; j < DIM; j++) fprintf(f, " %d", C->A[c][i][j]);
        fprintf(f, "\nb%d %d\n", c, C->b[c]);
    }
    for (int j = 0; j < 3; j++) {
        fprintf(f, "M%d", j + 2);
        for (int i = 0; i < DIM; i++) for (int k = 0; k < DIM; k++) fprintf(f, " %d", C->U[j][i][k]);
        fprintf(f, "\nt%d %d\n", j + 2, C->t[j]);
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: c5sa m seed iters nsrc T0 [outprefix]\n"); return 2; }
    /* usage: c5g G m seed iters nsrc T0 [outprefix]   with G = Z (cyclic) or D (dihedral, m even) */
    if (argc < 7) { fprintf(stderr, "usage: c5g G m seed iters nsrc T0 [outprefix]\n"); return 2; }
    GTYPE = argv[1][0];
    int m = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], 0, 10);
    long iters = atol(argv[4]);
    int nsrc = atoi(argv[5]);
    double T0 = atof(argv[6]);
    const char *outp = argc > 7 ? argv[7] : NULL;
    if (m < 5 || m > MAXM) { fprintf(stderr, "m out of range\n"); return 2; }
    if (!set_group(GTYPE, m)) { fprintf(stderr, "bad group\n"); return 2; }
    rs ^= seed * 0x2545F4914F6CDD1DULL + 12345;
    for (int k = 0; k < 20; k++) rnd();

    int N = 2 * m * FIB;
    int allsrc[2 * FIB];
    for (int x = 0; x < FIB; x++) { allsrc[x] = x; allsrc[FIB + x] = m * FIB + x; }

    /* fixed sample: nsrc random fibre points on each side (switches to all 512 once the sample hits 0) */
    int srcs[2 * FIB];
    int ns = 0;
    {
        int px[FIB], py[FIB];
        for (int x = 0; x < FIB; x++) { px[x] = x; py[x] = x; }
        for (int x = FIB - 1; x > 0; x--) { int j = rndint(x + 1); int t = px[x]; px[x] = px[j]; px[j] = t; }
        for (int x = FIB - 1; x > 0; x--) { int j = rndint(x + 1); int t = py[x]; py[x] = py[j]; py[j] = t; }
        if (nsrc > FIB) nsrc = FIB;
        for (int q = 0; q < nsrc; q++) { srcs[ns++] = px[q]; srcs[ns++] = m * FIB + py[q]; }
    }

    Chart cur, best;
    random_chart(&cur, m);
    long cc = eval_srcs(&cur, m, srcs, ns);
    best = cur;
    long bc = cc;
    fprintf(stderr, "m=%d N=%d init sample-cost=%ld\n", m, N, cc);

    long acc = 0, valid_moves = 0;
    int full_mode = 0;
    for (long it = 0; it < iters; it++) {
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.05;
        Chart nc = cur;
        mutate(&nc, m);
        if (!valid_chart(&nc, m)) continue;
        long ncost = eval_srcs(&nc, m, srcs, ns);
        if (ncost < 0) continue;
        valid_moves++;
        if (ncost <= cc || rnd01() < exp(-(double)(ncost - cc) / T)) {
            cur = nc; cc = ncost; acc++;
            if (cc < bc) { bc = cc; best = cur; }
        }
        if (cc == 0 && !full_mode) {
            /* sample is clean: switch to all 512 sources and recompute the current cost */
            full_mode = 1;
            memcpy(srcs, allsrc, sizeof(int) * 2 * FIB);
            ns = 2 * FIB;
            cc = eval_srcs(&cur, m, srcs, ns);
            bc = cc; best = cur;
            fprintf(stderr, "it %ld: sample clean, full cost %ld\n", it, cc);
            if (cc == 0) break;
        }
        if (it % 2000 == 0) fprintf(stderr, "it %ld T %.3f cur %ld best %ld acc %ld valid %ld\n", it, T, cc, bc, acc, valid_moves);
    }

    /* final exact check of the best chart on all 512 sources */
    long full = eval_srcs(&best, m, allsrc, 2 * FIB);
    printf("m=%d N=%d iters=%ld best_cost_run=%ld full_far_pairs=%ld (sources=512, far = ordered pairs at distance>5)\n",
           m, N, iters, bc, full);
    write_chart(stdout, &best, m);
    fflush(stdout);
    if ((full == 0 || getenv("C5_FORCE")) && outp) {
        char fn[512];
        snprintf(fn, sizeof fn, "%s_m%d_edges.txt", outp, m);
        FILE *f = fopen(fn, "w");
        Tabs T;
        make_tabs(&best, &T);
        int ne = gen_edges(&best, &T, m, EU, EV);
        fprintf(f, "%d\n", N);
        for (int e = 0; e < ne; e++) fprintf(f, "%d %d\n", EU[e], EV[e]);
        fclose(f);
        snprintf(fn, sizeof fn, "%s_m%d_chart.txt", outp, m);
        f = fopen(fn, "w");
        write_chart(f, &best, m);
        fclose(f);
        printf("wrote %s (n=%d, %d edges)\n", fn, N, ne);
    }
    return full == 0 ? 0 : 1;
}
