/* c6 (round 2), step 3: permutation-voltage lifts of the 3-edge dipole over PGL(2,q) acting on the projective line.
   Points 0..q-1 and infinity = q (q+1 points). Vertices x (side 0) and (q+1)+x (side 1).
   Edges x ~ x', x ~ g2(x)', x ~ g3(x)' with g2, g3 Moebius maps (ad - bc != 0 mod q).
   Random sampling plus a hill climb / annealing on the 8 matrix entries. Cost as in research/d3D7/sa3.c.
   Usage: pgl q seed secs samples [out.edges]                                                       */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 512
#define W ((MAXN + 63) / 64)
static int n, q, P, D = 7, nb[MAXN][3], nw;
static uint64_t ra[MAXN][W], rb[MAXN][W];
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static inline double ur(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }

static long cost(void) {
    uint64_t (*cur)[W] = ra, (*nx)[W] = rb;
    for (int x = 0; x < n; x++) { memset(cur[x], 0, nw * 8); cur[x][x >> 6] |= 1ULL << (x & 63); }
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) {
            const uint64_t *a = cur[nb[x][0]], *b = cur[nb[x][1]], *c = cur[nb[x][2]], *s = cur[x];
            for (int w = 0; w < nw; w++) nx[x][w] = s[w] | a[w] | b[w] | c[w];
        }
        uint64_t (*tmp)[W] = cur; cur = nx; nx = tmp;
    }
    long reached = 0;
    for (int x = 0; x < n; x++) for (int w = 0; w < nw; w++) reached += __builtin_popcountll(cur[x][w]);
    return (long)n * n - reached;
}

static long pw(long b, long e) { long r = 1; b %= q; if (b < 0) b += q; while (e) { if (e & 1) r = r * b % q; b = b * b % q; e >>= 1; } return r; }
static long inv(long a) { a %= q; if (a < 0) a += q; return pw(a, q - 2); }

typedef struct { int m[4]; } mob;   /* a b c d */
static int perm[2][MAXN];           /* perm tables of the two maps on P points */

static int mob_ok(const mob *g) { long det = ((long)g->m[0] * g->m[3] - (long)g->m[1] * g->m[2]) % q; if (det < 0) det += q; return det != 0; }
static void mob_table(const mob *g, int *t) {
    long a = g->m[0], b = g->m[1], c = g->m[2], d = g->m[3];
    for (int x = 0; x < q; x++) {
        long num = (a * x + b) % q, den = (c * x + d) % q;
        if (num < 0) num += q;
        if (den < 0) den += q;
        t[x] = den == 0 ? q : (int)(num * inv(den) % q);
    }
    /* infinity */
    t[q] = c % q == 0 ? q : (int)(((a % q + q) % q) * inv(c) % q);
}

static void setg(const mob *g2, const mob *g3) {
    mob_table(g2, perm[0]); mob_table(g3, perm[1]);
    for (int x = 0; x < P; x++) {
        nb[x][0] = P + x; nb[x][1] = P + perm[0][x]; nb[x][2] = P + perm[1][x];
    }
    /* inverse maps for side-1 vertices */
    static int inv0[MAXN], inv1[MAXN];
    for (int x = 0; x < P; x++) { inv0[perm[0][x]] = x; inv1[perm[1][x]] = x; }
    for (int y = 0; y < P; y++) { nb[P + y][0] = y; nb[P + y][1] = inv0[y]; nb[P + y][2] = inv1[y]; }
}

static void randmob(mob *g) { do { for (int i = 0; i < 4; i++) g->m[i] = (int)(xr() % q); } while (!mob_ok(g)); }

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w"); if (!f) return;
    fprintf(f, "%d\n", n);
    for (int x = 0; x < P; x++) {
        int seen[3], k2 = 0;
        for (int k = 0; k < 3; k++) {
            int y = nb[x][k], dup = 0;
            for (int j = 0; j < k; j++) if (nb[x][j] == y) dup = 1;
            if (!dup) fprintf(f, "%d %d\n", x, y);
        }
        (void)seen; (void)k2;
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: pgl q seed secs samples [out.edges]\n"); return 2; }
    q = atoi(argv[1]); P = q + 1; n = 2 * P; nw = (n + 63) / 64;
    rng ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[3]); long samples = atol(argv[4]);
    const char *out = argc > 5 ? argv[5] : NULL;
    mob g2, g3, bg2, bg3; long best = -1;
    clock_t st = clock();
    /* random sampling */
    for (long s = 0; s < samples; s++) {
        randmob(&g2); randmob(&g3); setg(&g2, &g3);
        long v = cost();
        if (best < 0 || v < best) { best = v; bg2 = g2; bg3 = g3; }
        if (v == 0) break;
    }
    double tsamp = (double)(clock() - st) / CLOCKS_PER_SEC;
    long bs_best = best; printf("q=%d n=%d random sampling %ld pairs: best %ld (%.1fs)\n", q, n, samples, best, tsamp); fflush(stdout);
    /* annealing on the 8 entries */
    g2 = bg2; g3 = bg3; setg(&g2, &g3); long cur = cost();
    long cbest = cur; mob cg2 = g2, cg3 = g3;
    long it = 0;
    for (;;) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC;
        if (el > secs || cbest == 0) break;
        double T = 30.0 * pow(0.5 / 30.0, fmod(el, 10.0) / 10.0);
        mob n2 = g2, n3 = g3;
        mob *tg = (xr() & 1) ? &n2 : &n3;
        int k = xr() % 4;
        tg->m[k] = (int)(xr() % q);
        if (xr() % 4 == 0) tg->m[(k + 1) % 4] = (int)(xr() % q);
        if (!mob_ok(&n2) || !mob_ok(&n3)) continue;
        setg(&n2, &n3); long v = cost(); it++;
        if (v <= cur || ur() < exp((cur - v) / T)) {
            g2 = n2; g3 = n3; cur = v;
            if (cur < cbest) { cbest = cur; cg2 = g2; cg3 = g3; }
        }
    }
    if (cbest < bs_best) bs_best = cbest;
    setg(&cg2, &cg3);
    printf("q=%d n=%d anneal its=%ld best=%ld  g2=(%d,%d,%d,%d) g3=(%d,%d,%d,%d) (overall best %ld)\n", q, n, it, cbest,
           cg2.m[0], cg2.m[1], cg2.m[2], cg2.m[3], cg3.m[0], cg3.m[1], cg3.m[2], cg3.m[3], bs_best);
    if (cbest == 0 && out) write_edges(out);
    return 0;
}
