/* ldual.c: randomized greedy for "locally dualizable" freed sets (hexagon-family project).
   The diameter-7 construction needs: R a set of pairwise non-collinear points, sigma a bijection points -> lines with
   sigma(G2(r)) = G2(sigma(r)) for every r in R (G2 = elements at distance 2). Equivalently: S = sigma(R) lines with
   d(r,r') = d(sigma r, sigma r') in {4,6} for all pairs, and the midpoint -> midline map well defined and injective.
   Pure partial ovoids (all distances 6) are the special case. This greedy builds (R, S, mu) pair by pair.
   Usage: ldual HEXBIN seed restarts [pure]   (pure = only pairwise opposite R and S, for comparison) */
#include "../tools/q6.h"
#include <time.h>
static int N, Q1, NV;
static int32_t *adjoff; static int32_t *adj;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static Hex h;
static int *que;
static void bfs(int src, uint8_t *d) {   /* vertices: points 0..N-1, lines N..2N-1 */
    memset(d, 255, NV); int hd = 0, tl = 0; que[tl++] = src; d[src] = 0;
    while (hd < tl) { int v = que[hd++]; if (d[v] >= 6) continue;
        for (int k = 0; k < Q1; k++) { int w = v < N ? N + h.PL[(size_t)v * Q1 + k] : h.LP[(size_t)(v - N) * Q1 + k]; if (d[w] == 255) { d[w] = d[v] + 1; que[tl++] = w; } } }
}
int main(int argc, char **argv) {
    h = hex_load(argv[1]); N = h.N; Q1 = h.q + 1; NV = 2 * N; que = malloc(sizeof(int) * NV);
    rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    int restarts = atoi(argv[3]), pure = argc > 4;
    int cap = 4 * N; uint8_t **dR = malloc(sizeof(uint8_t *) * cap), **dS = malloc(sizeof(uint8_t *) * cap);
    int *R = malloc(sizeof(int) * cap), *S = malloc(sizeof(int) * cap);
    int *mu = malloc(sizeof(int) * N), *muinv = malloc(sizeof(int) * N);
    uint8_t *blockP = malloc(N), *blockL = malloc(N), *dr = malloc(NV), *ds = malloc(NV);
    int *order = malloc(sizeof(int) * N), *lorder = malloc(sizeof(int) * N);
    int *pm = malloc(sizeof(int) * cap), *pn = malloc(sizeof(int) * cap);   /* partner index, its midpoint */
    int bestn = 0; long d4best = 0;
    for (int rr = 0; rr < restarts; rr++) {
        int n = 0; for (int i = 0; i < N; i++) { mu[i] = muinv[i] = -1; blockP[i] = blockL[i] = 0; order[i] = lorder[i] = i; }
        for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = order[i]; order[i] = order[j]; order[j] = t; }
        long d4 = 0;
        for (int oi = 0; oi < N; oi++) {
            int r = order[oi]; if (blockP[r]) continue;
            bfs(r, dr);
            int np = 0, bad = 0;
            for (int k = 0; k < n; k++) { int d = dr[R[k]]; if (d == 2 || d == 0) { bad = 1; break; } if (d == 4) { if (pure) { bad = 1; break; } pm[np] = k; np++; } }
            if (bad) continue;
            for (int t = 0; t < np; t++) {   /* midpoint of r and R[pm[t]]: the point of G2(r) at distance 2 from R[pm[t]] */
                int m = -1; uint8_t *dd = dR[pm[t]];
                for (int k = 0; k < Q1 && m < 0; k++) { int l = h.PL[(size_t)r * Q1 + k]; for (int u = 0; u < Q1; u++) { int y = h.LP[(size_t)l * Q1 + u]; if (y != r && dd[y] == 2) { m = y; break; } } }
                pn[t] = m;
            }
            /* find a line s */
            for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1), t = lorder[i]; lorder[i] = lorder[j]; lorder[j] = t; }
            int found = -1;
            for (int li = 0; li < N && found < 0; li++) {
                int s = lorder[li]; if (blockL[s]) continue;
                int ok = 1, t = 0;
                for (int k = 0; k < n && ok; k++) { int d = dS[k][N + s]; int want = (t < np && pm[t] == k) ? 4 : 6; if (want == 4) t++; if (d != want) ok = 0; }
                if (!ok) continue;
                if (np == 0) { found = s; break; }
                bfs(N + s, ds);
                /* midline of s and S[pm[t]]: line of G2(s) at distance 2 from S[pm[t]] */
                int mlv[512];
                for (int t2 = 0; t2 < np && ok; t2++) {
                    int M = -1; uint8_t *dd = dS[pm[t2]];
                    for (int k = 0; k < Q1 && M < 0; k++) { int x = h.LP[(size_t)s * Q1 + k]; for (int u = 0; u < Q1; u++) { int l = h.PL[(size_t)x * Q1 + u]; if (l != s && dd[N + l] == 2) { M = l; break; } } }
                    mlv[t2] = M;
                    int m = pn[t2];
                    if (mu[m] >= 0 && mu[m] != M) ok = 0;
                    if (mu[m] < 0 && muinv[M] >= 0) ok = 0;
                    for (int t3 = 0; t3 < t2 && ok; t3++) if ((pn[t3] == m) != (mlv[t3] == M)) ok = 0;
                }
                if (ok) found = s;
                if (ok) for (int t2 = 0; t2 < np; t2++) { mu[pn[t2]] = mlv[t2]; muinv[mlv[t2]] = pn[t2]; }
            }
            if (found < 0) continue;
            int s = found;
            R[n] = r; S[n] = s; dR[n] = malloc(NV); memcpy(dR[n], dr, NV); dS[n] = malloc(NV); bfs(N + s, dS[n]); n++; d4 += np;
            for (int y = 0; y < N; y++) { if (dr[y] <= 2) blockP[y] = 1; if (dS[n - 1][N + y] <= 2) blockL[y] = 1; }
        }
        if (n > bestn) {
            bestn = n; d4best = d4;
            char fn[256]; snprintf(fn, sizeof fn, "ld_q%d_%s_%d.txt", h.q, pure ? "pure" : "mixed", n); FILE *f = fopen(fn, "w");
            for (int k = 0; k < n; k++) fprintf(f, "%d %d\n", R[k], S[k]); fclose(f);
        }
        printf("restart %d: |R| = %d, distance-4 pairs %ld (best %d)\n", rr, n, d4, bestn); fflush(stdout);
        for (int k = 0; k < n; k++) { free(dR[k]); free(dS[k]); }
    }
    printf("BEST %d (distance-4 pairs %ld)\n", bestn, d4best);
    return 0;
}
