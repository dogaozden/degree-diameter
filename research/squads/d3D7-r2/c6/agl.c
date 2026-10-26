/* c6 (round 2): permutation-voltage lifts of the 3-edge dipole over AGL(1,q), q prime.
   Vertices x (side 0) and q+x (side 1). Edges x ~ q+x, x ~ q+alpha(x), x ~ q+beta(x),
   alpha(x) = a x + b, beta(x) = c x + d (mod q). n = 2q.
   Conjugation by an affine map allows b = 0 when a != 1, and b = 1 when a = 1 (b = 0 with a = 1 is degenerate).
   Enumerated: alpha in {(a,0): a = 2..q-1} U {(1,1)}, beta = (c,d) for c = 1..q-1, d = 0..q-1, skipping a = c = 1
   (Haar graphs of Z_q, already exhaustively negative). Fixed points of alpha/beta give repeated edges: these are
   kept as degree-2 vertices (the OR-based BFS ignores duplicates).
   Cost = number of ordered vertex pairs at distance > 7 (bit-parallel all-pairs BFS, same as research/d3D7/sa3.c).
   Usage: agl q [out.edges]   (out.edges is written if a cost-0 graph is found with n >= 170)            */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

#define MAXN 512
#define W ((MAXN + 63) / 64)
static int n, q, D = 7, nb[MAXN][3], nw;
static uint64_t ra[MAXN][W], rb[MAXN][W];

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

static int md(long v) { v %= q; return (int)(v < 0 ? v + q : v); }
static int inv(int a) { long r = 1, bb = a, e = q - 2; while (e) { if (e & 1) r = r * bb % q; bb = bb * bb % q; e >>= 1; } return (int)r; }

static void setg(int a, int b, int c, int d) {
    int ia = inv(a), ic = inv(c);
    for (int x = 0; x < q; x++) {
        nb[x][0] = q + x;
        nb[x][1] = q + md((long)a * x + b);
        nb[x][2] = q + md((long)c * x + d);
        nb[q + x][0] = x;
        nb[q + x][1] = md((long)(x - b) * ia);
        nb[q + x][2] = md((long)(x - d) * ic);
    }
}

static int ndistinct_deficit(void) { /* number of vertices with fewer than 3 distinct neighbours */
    int k = 0;
    for (int x = 0; x < n; x++) {
        int u0 = nb[x][0], u1 = nb[x][1], u2 = nb[x][2];
        int d = 1 + (u1 != u0) + (u2 != u0 && u2 != u1);
        if (d < 3) k++;
    }
    return k;
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w"); if (!f) return;
    fprintf(f, "%d\n", n);
    for (int x = 0; x < n; x++) for (int k = 0; k < 3; k++) {
        int y = nb[x][k], dup = 0;
        if (x >= q) continue;                       /* each edge once: from side 0 */
        for (int j = 0; j < k; j++) if (nb[x][j] == y) dup = 1;
        if (!dup) fprintf(f, "%d %d\n", x, y);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: agl q [out.edges]\n"); return 2; }
    q = atoi(argv[1]); n = 2 * q; nw = (n + 63) / 64;
    const char *out = argc > 2 ? argv[2] : NULL;
    static int AA[MAXN][2]; int na = 0;
    for (int a = 2; a < q; a++) { AA[na][0] = a; AA[na][1] = 0; na++; }
    AA[na][0] = 1; AA[na][1] = 1; na++;
    long count = 0, best = -1, nbest = 0, bpar[4] = {0, 0, 0, 0};
    clock_t st = clock();
    for (int i = 0; i < na; i++)
        for (int c = 1; c < q; c++)
            for (int d = 0; d < q; d++) {
                int a = AA[i][0], b = AA[i][1];
                if (a == 1 && c == 1) continue;
                setg(a, b, c, d);
                long v = cost(); count++;
                if (best < 0 || v < best) { best = v; nbest = 1; bpar[0] = a; bpar[1] = b; bpar[2] = c; bpar[3] = d; }
                else if (v == best) nbest++;
                if (v == 0 && out) { write_edges(out); }
            }
    double el = (double)(clock() - st) / CLOCKS_PER_SEC;
    setg((int)bpar[0], (int)bpar[1], (int)bpar[2], (int)bpar[3]);
    printf("q=%d n=%d graphs=%ld min_cost=%ld (attained by %ld) best a=%ld b=%ld c=%ld d=%ld deg-deficient=%d time=%.1fs\n",
           q, n, count, best, nbest, bpar[0], bpar[1], bpar[2], bpar[3], ndistinct_deficit(), el);
    return 0;
}
