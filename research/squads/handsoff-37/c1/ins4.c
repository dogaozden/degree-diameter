/* c1: random insertion of TWO A-side and TWO B-side new vertices (a1,a2 in A; b1,b2 in B), n0 -> n0+4.
   Internal edges H = subset of {a1b1, a1b2, a2b1, a2b2}; k = 6 - |H| base edges x_i y_i (x in A, y in B) are deleted,
   the k y-ends are distributed to a1,a2 (3 - deg_H slots each), the k x-ends to b1,b2 likewise.
   Random sampling: for each H, SAMPLES random choices of the k base edges (distinct x's, distinct y's) and distributions.
   Usage: ins4 BASE SAMPLES SEED OUTPREFIX  */
#include "g37.h"
#include <math.h>

static int side[MAXN];
static void bip(const G *g) {
    for (int i = 0; i < g->n; i++) side[i] = -1;
    int q[MAXN], h = 0, t = 0; side[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int i = 0; i < g->deg[x]; i++) { int y = g->nb[x][i]; if (side[y] < 0) { side[y] = 1 - side[x]; q[t++] = y; } } }
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ins4 BASE SAMPLES SEED OUTPREFIX\n"); return 2; }
    G base; if (g_load(&base, argv[1]) < 0) return 2;
    long S = atol(argv[2]); rng_seed(strtoull(argv[3], 0, 10)); const char *pre = argv[4];
    bip(&base);
    static int EX[MAXN * 2], EY[MAXN * 2]; int NE = 0;
    for (int x = 0; x < base.n; x++) for (int i = 0; i < base.deg[x]; i++) { int y = base.nb[x][i]; if (x < y) { if (side[x] == 0) { EX[NE] = x; EY[NE] = y; } else { EX[NE] = y; EY[NE] = x; } NE++; } }
    int n0 = base.n; int N = n0 + 4;
    /* new vertices: a1 = n0, a2 = n0+1 (side A), b1 = n0+2, b2 = n0+3 (side B) ; H bit mask over (a1b1,a1b2,a2b1,a2b2) */
    long bestAll = 1L << 40; int bestH = -1;
    for (int H = 0; H < 16; H++) {
        int hA[2][2]; int I = 0;
        for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) { hA[i][j] = (H >> (i * 2 + j)) & 1; I += hA[i][j]; }
        int k = 6 - I;
        if (k < 2) continue;
        int dA[2], dB[2];
        for (int i = 0; i < 2; i++) dA[i] = 3 - (hA[i][0] + hA[i][1]);
        for (int j = 0; j < 2; j++) dB[j] = 3 - (hA[0][j] + hA[1][j]);
        long best = 1L << 40, bestNonzeroHist = 0; long hist0 = 0;
        for (long s = 0; s < S; s++) {
            /* choose k distinct base edges with distinct x and distinct y */
            int idx[16]; int nk = 0, tries = 0;
            while (nk < k && tries < 1000) { tries++; int e = rng_int(NE); int ok = 1;
                for (int t = 0; t < nk; t++) if (EX[idx[t]] == EX[e] || EY[idx[t]] == EY[e] || idx[t] == e) { ok = 0; break; }
                if (ok) idx[nk++] = e; }
            if (nk < k) continue;
            /* y-ends to A-new vertices: shuffle then fill slots */
            int ys[16], xs[16];
            for (int t = 0; t < k; t++) { ys[t] = EY[idx[t]]; xs[t] = EX[idx[t]]; }
            for (int t = k - 1; t > 0; t--) { int u = rng_int(t + 1); int tmp = ys[t]; ys[t] = ys[u]; ys[u] = tmp; }
            for (int t = k - 1; t > 0; t--) { int u = rng_int(t + 1); int tmp = xs[t]; xs[t] = xs[u]; xs[u] = tmp; }
            G g; g_init(&g, N);
            for (int x = 0; x < n0; x++) for (int i = 0; i < base.deg[x]; i++) { int y = base.nb[x][i]; if (x < y) g_add(&g, x, y); }
            for (int t = 0; t < k; t++) g_del(&g, EX[idx[t]], EY[idx[t]]);
            int p = 0;
            for (int i = 0; i < 2; i++) for (int t = 0; t < dA[i]; t++) g_add(&g, n0 + i, ys[p++]);
            p = 0;
            for (int j = 0; j < 2; j++) for (int t = 0; t < dB[j]; t++) g_add(&g, n0 + 2 + j, xs[p++]);
            for (int i = 0; i < 2; i++) for (int j = 0; j < 2; j++) if (hA[i][j]) g_add(&g, n0 + i, n0 + 2 + j);
            int okd = 1; for (int v = 0; v < N; v++) if (g.deg[v] != 3) okd = 0;
            if (!okd) continue;
            /* simple? */
            int simple = 1; for (int v = 0; v < N && simple; v++) for (int i = 0; i < g.deg[v]; i++) for (int j = i + 1; j < g.deg[v]; j++) if (g.nb[v][i] == g.nb[v][j]) simple = 0;
            if (!simple) continue;
            long f = far_cost(&g);
            if (f == 0) { char fn[600]; snprintf(fn, sizeof fn, "%s_H%d_FAR0.edges", pre, H); g_write(&g, fn); }
            if (f < best) { best = f; }
            if (f == best) { /* keep one copy of the best for this H */
                char fn[600]; snprintf(fn, sizeof fn, "%s_H%d_best.edges", pre, H); g_write(&g, fn); }
        }
        printf("H=%X internal=%d k=%d best far at n=%d over %ld samples: %ld\n", H, I, k, N, S, best);
        if (best < bestAll) { bestAll = best; bestH = H; }
    }
    printf("overall best far=%ld (H=%X)\n", bestAll, bestH);
    return 0;
}
