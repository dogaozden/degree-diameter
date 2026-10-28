/* wgr_eval.c: count "bad pairs" for whole-graph repair (D5_QUADRANGLE.md, Section 10).
   Graph: V vertices, adjacency as V x DEG int32 array (-1 = empty slot).
   Sources: S entries (vertex, target level); a pair (source, t) is bad when t lies in the target level
   (vertices lev_lo[L] .. lev_lo[L]+lev_n-1) and dist(source, t) > DMAX.
   Bit-parallel BFS, 64 sources per word, all words at once.  Writes per-source bad counts into badc[S];
   returns the total.  Build: cc -O3 -march=native -shared -fPIC -o wgr_eval.so wgr_eval.c */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

long wgr_bad(int V, int DEG, const int32_t *adj, int S, const int32_t *src, const int32_t *tlev,
             int lev_n, int DMAX, int32_t *badc, int32_t *badv, int maxbadv) {
    int W = (S + 63) / 64;
    uint64_t *vis = calloc((size_t)V * W, 8), *fr = calloc((size_t)V * W, 8), *nx = calloc((size_t)V * W, 8);
    for (int s = 0; s < S; s++) { vis[(size_t)src[s] * W + s / 64] |= 1ULL << (s % 64); fr[(size_t)src[s] * W + s / 64] |= 1ULL << (s % 64); }
    for (int d = 0; d < DMAX; d++) {
        for (int x = 0; x < V; x++) {
            uint64_t *o = nx + (size_t)x * W; memset(o, 0, 8 * W);
            const int32_t *a = adj + (size_t)x * DEG;
            for (int k = 0; k < DEG; k++) { int y = a[k]; if (y < 0) continue; const uint64_t *f = fr + (size_t)y * W; for (int w = 0; w < W; w++) o[w] |= f[w]; }
            uint64_t *vv = vis + (size_t)x * W; for (int w = 0; w < W; w++) { o[w] &= ~vv[w]; vv[w] |= o[w]; }
        }
        uint64_t *t = fr; fr = nx; nx = t;
    }
    long total = 0; int nb = 0;
    for (int s = 0; s < S; s++) {
        int lo = tlev[s] * lev_n, c = 0; uint64_t bit = 1ULL << (s % 64); int w = s / 64;
        for (int v = lo; v < lo + lev_n; v++) if (!(vis[(size_t)v * W + w] & bit)) { c++; if (nb < maxbadv) { badv[2 * nb] = s; badv[2 * nb + 1] = v; nb++; } }
        badc[s] = c; total += c;
    }
    free(vis); free(fr); free(nx);
    return total;
}
