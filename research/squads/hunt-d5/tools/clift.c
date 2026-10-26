/* clift: coset lifts for D = 5 (hunt-d5).  A cubic (or any) bipartite controller C (m + m vertices) and a group G
   (table, identity 0).  Each controller edge e = uv (u on side A) carries a voltage SET S_e = g_e <h_e>, a left coset of
   a subgroup of order k = ord(h_e) (default k = 3: degree 3 * deg_C).  Lift: (u,x) ~ (v, s x), s in S_e.  G acts by
   right multiplication, so the roots (w, e) suffice.  Diameter <= 5 iff from every root every same-side lift vertex is
   reached by a walk of length exactly 4 (walks may backtrack, so length 0 and 2 are included).
   cost = sum over roots of unreached same-side lift vertices.
   Usage: clift CTRL.edges TABLE.bin seconds seed [OUT] [k]
   CTRL.edges: "2m" then "u v" lines (A = 0..m-1).  Env T0 (2.0), COOL (seconds per halving, 20), REHEAT (60).
   OUT gets the voltages (lines "u v g h") and OUT.edges the lift edge list (vertex (w,x) = w*N + x) when cost is 0. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#define W 4                     /* 64-bit words per fibre: N <= 256 */
static int N, m, ne, eu[1024], ev[1024], g[1024], h[1024], K = 3;
static uint16_t *MT; static int *INV;
static int *ordk, nordk;        /* elements of order exactly K */
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static inline int mul(int x, int y) { return MT[x * N + y]; }
typedef struct { uint64_t w[W]; } bs;
static int S[1024][8], Si[1024][8];   /* coset elements and inverses */
static void mkS(int e) { int x = g[e]; for (int i = 0; i < K; i++) { S[e][i] = x; Si[e][i] = INV[x]; x = mul(x, h[e]); } }
static inline void leftmul(bs *out, const bs *in, int s) {   /* out |= s * in */
    for (int wi = 0; wi < W; wi++) { uint64_t b = in->w[wi]; while (b) { int t = __builtin_ctzll(b); b &= b - 1; int y = mul(s, wi * 64 + t); out->w[y >> 6] |= 1ULL << (y & 63); } }
}
static int adjA[256][16], adjAn[256], adjB[256][16], adjBn[256]; /* incident edges */
static bs F[2][512];
static long root_cost(int r) {
    int n2 = 2 * m; memset(F[0], 0, sizeof(bs) * n2);
    F[0][r].w[0] = 1;                               /* identity */
    int cur = 0;
    for (int step = 0; step < 4; step++) {
        int nx = cur ^ 1; memset(F[nx], 0, sizeof(bs) * n2);
        for (int x = 0; x < n2; x++) {
            int any = 0; for (int wi = 0; wi < W; wi++) any |= F[cur][x].w[wi] != 0; if (!any) continue;
            if (x < m) { for (int k = 0; k < adjAn[x]; k++) { int e = adjA[x][k]; for (int i = 0; i < K; i++) leftmul(&F[nx][ev[e]], &F[cur][x], S[e][i]); } }
            else { for (int k = 0; k < adjBn[x - m]; k++) { int e = adjB[x - m][k]; for (int i = 0; i < K; i++) leftmul(&F[nx][eu[e]], &F[cur][x], Si[e][i]); } }
        }
        cur = nx;
    }
    long un = 0; int lo = r < m ? 0 : m;
    for (int x = lo; x < lo + m; x++) { int c = 0; for (int wi = 0; wi < W; wi++) c += __builtin_popcountll(F[cur][x].w[wi]); un += N - c; }
    return un;
}
static long total_cost(void) { long c = 0; for (int r = 0; r < 2 * m; r++) c += root_cost(r); return c; }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: clift CTRL.edges TABLE.bin seconds seed [OUT] [k]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); int n2; if (fscanf(f, "%d", &n2) != 1) return 2; m = n2 / 2; ne = 0;
    int a, b; while (fscanf(f, "%d %d", &a, &b) == 2) { if (a >= m) { int t = a; a = b; b = t; } eu[ne] = a; ev[ne] = b; ne++; } fclose(f);
    for (int e = 0; e < ne; e++) { adjA[eu[e]][adjAn[eu[e]]++] = e; adjB[ev[e] - m][adjBn[ev[e] - m]++] = e; }
    f = fopen(argv[2], "rb"); if (fread(&N, 4, 1, f) != 1) return 2; if (N > 64 * W) { fprintf(stderr, "N too big\n"); return 2; }
    MT = malloc(2 * N * N); if (fread(MT, 2, N * N, f) != (size_t)(N * N)) return 2; fclose(f);
    INV = malloc(N * sizeof(int)); for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul(x, y) == 0) INV[x] = y;
    double secs = atof(argv[3]); rs ^= strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 30; i++) rnd();
    const char *out = argc > 5 ? argv[5] : NULL; if (argc > 6) K = atoi(argv[6]);
    ordk = malloc(N * sizeof(int)); nordk = 0;
    for (int x = 1; x < N; x++) { int y = x, o = 1; while (y != 0) { y = mul(y, x); o++; } if (o == K) ordk[nordk++] = x; }
    if (!nordk) { fprintf(stderr, "no elements of order %d\n", K); return 2; }
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, COOL = getenv("COOL") ? atof(getenv("COOL")) : 20, REHEAT = getenv("REHEAT") ? atof(getenv("REHEAT")) : 60;
    for (int e = 0; e < ne; e++) { g[e] = rnd() % N; h[e] = ordk[rnd() % nordk]; mkS(e); }
    long cur = total_cost(), best = cur; int bg[1024], bh[1024]; memcpy(bg, g, sizeof g); memcpy(bh, h, sizeof h);
    double t0 = now(), tl = t0, tc = t0; long ev_ = 1;
    while (best > 0 && now() - t0 < secs) {
        double T = T0 * pow(0.5, (now() - tc) / COOL) * N * 0.05;
        int e = rnd() % ne, og = g[e], oh = h[e];
        if (rnd() & 1) g[e] = rnd() % N; else h[e] = ordk[rnd() % nordk];
        mkS(e); long c = total_cost(); ev_++;
        if (c <= cur || rnd01() < exp(-(c - cur) / fmax(T, 1e-9))) { cur = c; if (c < best) { best = c; memcpy(bg, g, sizeof g); memcpy(bh, h, sizeof h); tl = now();
            fprintf(stderr, "t=%.1f evals=%ld best=%ld\n", now() - t0, ev_, best); } }
        else { g[e] = og; h[e] = oh; mkS(e); }
        if (now() - tl > REHEAT) { memcpy(g, bg, sizeof g); memcpy(h, bh, sizeof h); for (int i = 0; i < ne; i++) mkS(i); cur = best; tl = tc = now(); }
    }
    memcpy(g, bg, sizeof g); memcpy(h, bh, sizeof h); for (int i = 0; i < ne; i++) mkS(i);
    printf("RESULT clift ctrl=%s table=%s m=%d N=%d k=%d n=%d best=%ld evals=%ld time=%.1f\n", argv[1], argv[2], m, N, K, 2 * m * N, best, ev_, now() - t0);
    if (out && best == 0) {
        FILE *o = fopen(out, "w"); for (int i = 0; i < ne; i++) fprintf(o, "%d %d %d %d\n", eu[i], ev[i], g[i], h[i]); fclose(o);
        char fn[1024]; snprintf(fn, sizeof fn, "%s.edges", out); o = fopen(fn, "w"); fprintf(o, "%d\n", 2 * m * N);
        for (int i = 0; i < ne; i++) for (int x = 0; x < N; x++) for (int j = 0; j < K; j++) fprintf(o, "%d %d\n", eu[i] * N + x, ev[i] * N + mul(S[i][j], x));
        fclose(o);
    }
    return best == 0 ? 0 : 1;
}
