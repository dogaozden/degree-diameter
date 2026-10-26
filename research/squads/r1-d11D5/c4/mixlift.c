/* mixlift.c: search for MIXED chart lifts over F_3^4 with degree 11.
 *
 * Controller: bipartite base multigraph on R+R vertices, voltage-lifted over Z_N.
 * Each controller vertex has 3 letter edges (colours 0,1,2) and 2 unit edges (colours 0,1).
 * Lift vertices (u,x), u in controller, x in F_3^4.
 *   letter edge u-v colour c:  (u,x) ~ (v, A_c x + l b_c) for l in F_3   (3 neighbours)
 *   unit edge u-v colour j:    (u,x) ~ (v, M_j x + t_j)                  (1 neighbour)
 * A_0 = I is WLOG. Lift order = 2 * R * N * 81 = 162 m with m = R*N.
 *
 * Diameter <= 5 iff every same-side pair is within distance 4. The lift is invariant under
 * the Z_N shift, so starts only need g = 0. For each rep start, a bitmask over the 81 start
 * points is propagated for 4 steps; cost = number of (start, same-side target) pairs at distance > 4.
 *
 * usage: mixlift <base 55|44|33> <N> <iters> <seed> <T0> <outprefix>
 * writes <outprefix>.params always, and <outprefix>.edges if cost reaches 0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

typedef unsigned __int128 u128;

#define NX 81
#define DEG 11
#define MAXNE 64

static int R, N, NE;
static int bi[MAXNE], bj[MAXNE], bt[MAXNE], bc[MAXNE];
static int NVc, NVl;
static int dig[NX][4];
static int addt[NX][NX];
static int smul[3][NX];

static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int ri(int n) { return (int)(rnd() % (uint64_t)n); }
static double ru(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

typedef struct {
    int volt[MAXNE];
    int A[3][4][4];   /* A[0] = identity (WLOG) */
    int M[2][4][4];
    int b[3][4];
    int t[2][4];
} State;

static State S, BEST;
static int *adj, *cnt, overflow;
static u128 *cur, *nxt;
static int imgA[3][NX], imgM[2][NX];

static void init_tables(void) {
    for (int x = 0; x < NX; x++) { int y = x; for (int k = 0; k < 4; k++) { dig[x][k] = y % 3; y /= 3; } }
    for (int x = 0; x < NX; x++) for (int y = 0; y < NX; y++) {
        int z = 0, p = 1;
        for (int k = 0; k < 4; k++) { z += ((dig[x][k] + dig[y][k]) % 3) * p; p *= 3; }
        addt[x][y] = z;
    }
    for (int l = 0; l < 3; l++) for (int x = 0; x < NX; x++) {
        int z = 0, p = 1;
        for (int k = 0; k < 4; k++) { z += ((l * dig[x][k]) % 3) * p; p *= 3; }
        smul[l][x] = z;
    }
}

static int idx_of(const int *v) { return v[0] + 3 * v[1] + 9 * v[2] + 27 * v[3]; }

static int matvec(int M[4][4], int x) {
    int y[4];
    for (int k = 0; k < 4; k++) {
        int s = 0;
        for (int j = 0; j < 4; j++) s += M[k][j] * dig[x][j];
        y[k] = s % 3;
    }
    return idx_of(y);
}

/* invertible over F_3 by Gaussian elimination; entries assumed in 0..2 */
static int invertible(int M[4][4]) {
    int a[4][4];
    memcpy(a, M, sizeof a);
    int rank = 0;
    for (int c = 0; c < 4; c++) {
        int piv = -1;
        for (int r = rank; r < 4; r++) if (a[r][c] % 3) { piv = r; break; }
        if (piv < 0) return 0;
        for (int k = 0; k < 4; k++) { int tmp = a[rank][k]; a[rank][k] = a[piv][k]; a[piv][k] = tmp; }
        int inv = (a[rank][c] % 3 == 1) ? 1 : 2;
        for (int k = 0; k < 4; k++) a[rank][k] = (a[rank][k] * inv) % 3;
        for (int r = 0; r < 4; r++) if (r != rank && a[r][c] % 3) {
            int f = a[r][c] % 3;
            for (int k = 0; k < 4; k++) a[r][k] = ((a[r][k] - f * a[rank][k]) % 3 + 3) % 3;
        }
        rank++;
    }
    return 1;
}

static void rand_inv(int M[4][4]) {
    do {
        for (int k = 0; k < 4; k++) for (int j = 0; j < 4; j++) M[k][j] = ri(3);
    } while (!invertible(M));
}

static void setup_base(int type, int n) {
    NE = 0; N = n;
    if (type == 55) {            /* K_{5,5}, colour (i+j) mod 5: letters 0,1,2 and units 0,1 */
        R = 5;
        for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) {
            int c = (i + j) % 5;
            bi[NE] = i; bj[NE] = j;
            if (c < 3) { bt[NE] = 0; bc[NE] = c; } else { bt[NE] = 1; bc[NE] = c - 3; }
            NE++;
        }
    } else if (type == 44) {     /* K_{4,4} colour (i+j) mod 4 plus a doubled matching (unit 1) */
        R = 4;
        for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) {
            int c = (i + j) % 4;
            bi[NE] = i; bj[NE] = j;
            if (c < 3) { bt[NE] = 0; bc[NE] = c; } else { bt[NE] = 1; bc[NE] = 0; }
            NE++;
        }
        for (int i = 0; i < 4; i++) { bi[NE] = i; bj[NE] = i; bt[NE] = 1; bc[NE] = 1; NE++; }
    } else {                     /* 33: K_{3,3} letters plus two matchings as units */
        R = 3;
        for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) {
            bi[NE] = i; bj[NE] = j; bt[NE] = 0; bc[NE] = (i + j) % 3; NE++;
        }
        for (int i = 0; i < 3; i++) { bi[NE] = i; bj[NE] = i; bt[NE] = 1; bc[NE] = 0; NE++; }
        for (int i = 0; i < 3; i++) { bi[NE] = i; bj[NE] = (i + 1) % 3; bt[NE] = 1; bc[NE] = 1; NE++; }
    }
    NVc = 2 * R * N;
    NVl = NVc * NX;
}

static inline void add_edge(int v, int w) {
    if (cnt[v] >= DEG) { overflow = 1; return; }
    adj[v * DEG + cnt[v]++] = w;
}

static void build(void) {
    int lamb[3][3], tidx[2], bidx[3];
    for (int c = 0; c < 3; c++) {
        for (int x = 0; x < NX; x++) imgA[c][x] = matvec(S.A[c], x);
        bidx[c] = idx_of(S.b[c]);
        for (int l = 0; l < 3; l++) lamb[c][l] = smul[l][bidx[c]];
    }
    for (int u = 0; u < 2; u++) {
        for (int x = 0; x < NX; x++) imgM[u][x] = matvec(S.M[u], x);
        tidx[u] = idx_of(S.t[u]);
    }
    memset(cnt, 0, NVl * sizeof(int));
    overflow = 0;
    for (int e = 0; e < NE; e++) for (int g = 0; g < N; g++) {
        int p = bi[e] * N + g;                       /* side A controller index */
        int h = (g + S.volt[e]) % N;
        int q = (R + bj[e]) * N + h;                 /* side B controller index */
        for (int x = 0; x < NX; x++) {
            int P = p * NX + x;
            if (bt[e] == 0) {
                int c = bc[e];
                for (int l = 0; l < 3; l++) {
                    int y = addt[imgA[c][x]][lamb[c][l]];
                    int Q = q * NX + y;
                    add_edge(P, Q); add_edge(Q, P);
                }
            } else {
                int u = bc[e];
                int y = addt[imgM[u][x]][tidx[u]];
                int Q = q * NX + y;
                add_edge(P, Q); add_edge(Q, P);
            }
        }
    }
}

static long dupcount(void) {
    long d = 0;
    if (overflow) d += 100000;
    for (int v = 0; v < NVl; v++) {
        if (cnt[v] != DEG) { d += 1000; continue; }
        for (int a = 0; a < DEG; a++) for (int b = a + 1; b < DEG; b++)
            if (adj[v * DEG + a] == adj[v * DEG + b]) d++;
    }
    return d;
}

/* far = number of (start x at rep, same-side target) pairs at distance > 4, summed over reps */
static long cost(void) {
    build();
    long dup = dupcount();
    long far = 0;
    for (int s = 0; s < 2 * R; s++) {
        int side = s / R, i = s % R;
        int c0 = (side * R + i) * N;
        memset(cur, 0, NVl * sizeof(u128));
        for (int x = 0; x < NX; x++) cur[c0 * NX + x] = (u128)1 << x;
        for (int step = 0; step < 4; step++) {
            for (int v = 0; v < NVl; v++) {
                u128 m = cur[v];
                const int *a = adj + v * DEG;
                for (int k = 0; k < DEG; k++) m |= cur[a[k]];
                nxt[v] = m;
            }
            u128 *tmp = cur; cur = nxt; nxt = tmp;
        }
        int lo = side * R * N, hi = lo + R * N;
        for (int c = lo; c < hi; c++) for (int x = 0; x < NX; x++) {
            u128 m = cur[c * NX + x];
            int pc = __builtin_popcountll((unsigned long long)m) + __builtin_popcountll((unsigned long long)(m >> 64));
            far += NX - pc;
        }
    }
    return far + 1000000L * dup;
}

static int mutate(void) {
    int mt = ri(100);
    if (mt < 35) {
        if (NE == 0) return 0;
        int e = ri(NE);
        S.volt[e] = ri(N);
        return 1;
    } else if (mt < 65) {
        int which = ri(4);
        int (*Mp)[4] = (which == 0) ? S.A[1] : (which == 1) ? S.A[2] : (which == 2) ? S.M[0] : S.M[1];
        int r = ri(4), c = ri(4);
        Mp[r][c] = ri(3);
        return invertible(Mp);
    } else if (mt < 85) {
        int c = ri(3), k = ri(4);
        S.b[c][k] = ri(3);
        int nz = 0;
        for (int j = 0; j < 4; j++) if (S.b[c][j]) nz = 1;
        return nz;
    } else {
        int u = ri(2), k = ri(4);
        S.t[u][k] = ri(3);
        return 1;
    }
}

static void write_params(const char *fn, long best, long iters_done) {
    FILE *f = fopen(fn, "w");
    if (!f) return;
    fprintf(f, "# mixlift params: R=%d N=%d m=%d lift_order=%d cost=%ld iters=%ld\n", R, N, R * N, NVl, best, iters_done);
    fprintf(f, "base_edges:");
    for (int e = 0; e < NE; e++) fprintf(f, " (%d,%d,%s%d,v=%d)", bi[e], bj[e], bt[e] ? "U" : "L", bc[e], BEST.volt[e]);
    fprintf(f, "\n");
    for (int c = 0; c < 3; c++) {
        fprintf(f, "A%d=", c);
        for (int k = 0; k < 4; k++) for (int j = 0; j < 4; j++) fprintf(f, "%d", BEST.A[c][k][j]);
        fprintf(f, "\n");
    }
    for (int u = 0; u < 2; u++) {
        fprintf(f, "M%d=", u);
        for (int k = 0; k < 4; k++) for (int j = 0; j < 4; j++) fprintf(f, "%d", BEST.M[u][k][j]);
        fprintf(f, "\n");
    }
    for (int c = 0; c < 3; c++) {
        fprintf(f, "b%d=", c);
        for (int k = 0; k < 4; k++) fprintf(f, "%d", BEST.b[c][k]);
        fprintf(f, "\n");
    }
    for (int u = 0; u < 2; u++) {
        fprintf(f, "t%d=", u);
        for (int k = 0; k < 4; k++) fprintf(f, "%d", BEST.t[u][k]);
        fprintf(f, "\n");
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: mixlift <55|44|33> <N> <iters> <seed> <T0> <outprefix>\n");
        return 1;
    }
    int type = atoi(argv[1]);
    int n = atoi(argv[2]);
    long iters = atol(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double T0 = atof(argv[5]);
    const char *out = argv[6];
    rs ^= seed * 0x2545F4914F6CDD1DULL + 12345;
    for (int i = 0; i < 20; i++) rnd();
    setup_base(type, n);
    init_tables();
    adj = malloc(sizeof(int) * NVl * DEG);
    cnt = malloc(sizeof(int) * NVl);
    cur = malloc(sizeof(u128) * NVl);
    nxt = malloc(sizeof(u128) * NVl);

    memset(&S, 0, sizeof S);
    for (int e = 0; e < NE; e++) S.volt[e] = ri(N);
    for (int k = 0; k < 4; k++) for (int j = 0; j < 4; j++) S.A[0][k][j] = (k == j);
    rand_inv(S.A[1]); rand_inv(S.A[2]);
    rand_inv(S.M[0]); rand_inv(S.M[1]);
    for (int c = 0; c < 3; c++) { int nz = 0; while (!nz) { for (int k = 0; k < 4; k++) S.b[c][k] = ri(3); for (int k = 0; k < 4; k++) if (S.b[c][k]) nz = 1; } }
    for (int u = 0; u < 2; u++) for (int k = 0; k < 4; k++) S.t[u][k] = ri(3);

    long cc = cost();
    long best = cc;
    BEST = S;
    long it;
    for (it = 0; it < iters; it++) {
        double T = T0 * (1.0 - (double)it / (double)iters) + 1e-6;
        State old = S;
        if (!mutate()) { S = old; continue; }
        long nc = cost();
        long d = nc - cc;
        if (d <= 0 || ru() < exp(-(double)d / T)) {
            cc = nc;
            if (cc < best) { best = cc; BEST = S; }
            if (best == 0) break;
        } else {
            S = old;
        }
    }
    printf("type=%d N=%d m=%d lift_order=%d iters=%ld best_cost=%ld\n", type, N, R * N, NVl, it, best);
    char fn[512];
    snprintf(fn, sizeof fn, "%s.params", out);
    write_params(fn, best, it);
    if (best == 0) {
        S = BEST;
        build();
        snprintf(fn, sizeof fn, "%s.edges", out);
        FILE *f = fopen(fn, "w");
        fprintf(f, "%d\n", NVl);
        long m = 0;
        for (int v = 0; v < NVl; v++) for (int k = 0; k < DEG; k++) {
            int w = adj[v * DEG + k];
            if (w > v) { fprintf(f, "%d %d\n", v, w); m++; }
        }
        fclose(f);
        printf("wrote %s (%ld edges)\n", fn, m);
    }
    return 0;
}
