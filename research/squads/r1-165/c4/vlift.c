/* vlift.c -- exhaustive search over Z_K voltage lifts of 4-regular bipartite base multigraphs on 2+2 vertices
   (two orbits per side, so m = 2K controller vertices per side).

   Base vertices: A1 = 0, A2 = 1 (side A), B1 = 2, B2 = 3 (side B). Each base dart is an edge A -> B with a voltage
   in Z_K. Controller C (simple bipartite 4-regular graph on m + m vertices):
       A-vertex a*K+g  ~  B-vertex (beta)*K + ((g+v) mod K)      for every base dart a -> beta with voltage v.
   Same-side ordered pairs of C are joined by an NB walk of length 4 iff, for each same-side base pair (s,t), the set
   W(s,t) of signed voltage sums over NB-4 base walks s -> t is all of Z_K (sign +v for an A->B step, -v for B->A).

   Base types (multiplicities of A1B1, A1B2, A2B1, A2B2), up to relabelling:
     type 1: (1,3,3,1)     type 2: (2,2,2,2)
   Voltages: a spanning tree of the base is normalised to 0; the first free voltage is normalised to a divisor of K
   (scaling by a unit of Z_K), so the enumeration covers every lift up to switching and automorphisms.
   Parallel base edges get distinct voltages (simple lift).

   usage: vlift K TYPE [out.edges]
     prints: best cost (uncovered (base pair, element) count summed over the 8 same-side base pairs), number of
     perfect (cost 0) voltage assignments, and the first perfect one; writes the controller edge list "a b" (a, b in
     0..m-1, 4m lines, m = 2K) of the first perfect assignment (or of the best one if none) to out.edges. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int K, TYPE, nd = 8;
static int dt[8], dh[8], dv[8];          /* tail, head, variable index (-1 = zero voltage) */
static int NWK[4][4];
static signed char WC[4][4][108][5];     /* per (start, end): coefficient vector of each NB-4 walk over the 5 vars */

static void set_type(int type) {
    int T2[8][3] = { {0,2,-1}, {0,2,0}, {0,3,-1}, {0,3,1}, {1,2,-1}, {1,2,2}, {1,3,3}, {1,3,4} };
    int T1[8][3] = { {0,2,-1}, {0,3,-1}, {0,3,0}, {0,3,1}, {1,2,-1}, {1,2,2}, {1,2,3}, {1,3,4} };
    int (*T)[3] = type == 2 ? T2 : T1;
    for (int d = 0; d < 8; d++) { dt[d] = T[d][0]; dh[d] = T[d][1]; dv[d] = T[d][2]; }
}

/* NB walks of length 4 from every base vertex s; a step may traverse a dart in either direction (A->B is +v,
   B->A is -v); consecutive darts must differ (non-backtracking). 4*3*3*3 = 108 walks per start vertex. */
static void build_walks(void) {
    memset(NWK, 0, sizeof NWK);
    for (int s = 0; s < 4; s++)
    for (int d1 = 0; d1 < nd; d1++) { if (!(dt[d1] == s || dh[d1] == s)) continue;
      int x1 = dt[d1] == s ? dh[d1] : dt[d1];
      for (int d2 = 0; d2 < nd; d2++) { if (d2 == d1 || !(dt[d2] == x1 || dh[d2] == x1)) continue;
        int x2 = dt[d2] == x1 ? dh[d2] : dt[d2];
        for (int d3 = 0; d3 < nd; d3++) { if (d3 == d2 || !(dt[d3] == x2 || dh[d3] == x2)) continue;
          int x3 = dt[d3] == x2 ? dh[d3] : dt[d3];
          for (int d4 = 0; d4 < nd; d4++) { if (d4 == d3 || !(dt[d4] == x3 || dh[d4] == x3)) continue;
            int t = dt[d4] == x3 ? dh[d4] : dt[d4];
            int ds[4] = {d1, d2, d3, d4}, xs[4] = {s, x1, x2, x3};
            signed char c[5] = {0, 0, 0, 0, 0};
            for (int i = 0; i < 4; i++) { int d = ds[i]; if (dv[d] < 0) continue; c[dv[d]] += (xs[i] < 2) ? 1 : -1; }
            memcpy(WC[s][t][NWK[s][t]++], c, 5);
          } } } }
}

static uint64_t FULL;
/* uncovered count summed over the same-side base pairs; cov[s][t] gets the covered mask if non-NULL */
static int eval_cost(const int *val, uint64_t *cov) {
    int cost = 0;
    for (int s = 0; s < 4; s++) for (int t = 0; t < 4; t++) {
        if ((s < 2) != (t < 2)) continue;
        uint64_t mask = 0;
        for (int i = 0; i < NWK[s][t]; i++) {
            int x = 0;
            for (int j = 0; j < 5; j++) x += WC[s][t][i][j] * val[j];
            x %= K; if (x < 0) x += K;
            mask |= 1ULL << x;
        }
        if (cov) cov[s * 4 + t] = mask;
        cost += K - __builtin_popcountll(mask);
    }
    return cost;
}

static void write_controller(const char *fn, const int *val) {
    FILE *f = fopen(fn, "w");
    if (!f) { perror(fn); return; }
    for (int d = 0; d < 8; d++) {
        if (dt[d] >= 2) continue;   /* each base dart once, from its A end */
        int a = dt[d], beta = dh[d] - 2, v = dv[d] < 0 ? 0 : val[dv[d]];
        for (int g = 0; g < K; g++) fprintf(f, "%d %d\n", a * K + g, beta * K + (g + v) % K);
    }
    /* B-side darts (tail in B) are the same edges; the loop above already emits all 4*(2K) edges because the
       base has 8 darts with tail in A, so nothing more to write */
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: vlift K TYPE [out]\n"); return 1; }
    K = atoi(argv[1]); TYPE = atoi(argv[2]);
    if (K < 2 || K > 64) { fprintf(stderr, "K must be in 2..64\n"); return 1; }
    FULL = K == 64 ? ~0ULL : ((1ULL << K) - 1);
    set_type(TYPE);
    build_walks();
    int nw = 0; for (int s = 0; s < 4; s++) for (int t = 0; t < 4; t++) nw += NWK[s][t];
    int divs[64], nds = 0;
    for (int d = 1; d < K; d++) if (K % d == 0) divs[nds++] = d;
    int val[5], best = 1 << 30, bestval[5] = {0}, nperf = 0, firstval[5] = {0}, have_first = 0;
    long nev = 0, nlow = 0;
    long hist[1024] = {0};
    for (int i0 = 0; i0 < nds; i0++) {
        val[0] = divs[i0];
        for (val[1] = 0; val[1] < K; val[1]++)
        for (val[2] = 0; val[2] < K; val[2]++)
        for (val[3] = 0; val[3] < K; val[3]++)
        for (val[4] = 0; val[4] < K; val[4]++) {
            /* distinctness of parallel base edges (simple lift) */
            if (TYPE == 2) {
                if (val[1] == 0 || val[2] == 0 || val[4] == val[3]) continue;   /* q, r != 0; t != s */
            } else {
                if (val[1] == 0 || val[1] == val[0]) continue;                  /* q2 != 0, q1 */
                if (val[2] == 0 || val[3] == 0 || val[3] == val[2]) continue;   /* r1, r2 != 0; r1 != r2 */
            }
            nev++;
            int c = eval_cost(val, NULL);
            if (c < 1024) hist[c]++;
            if (c < best) { best = c; memcpy(bestval, val, sizeof val); }
            if (c <= 2) nlow++;
            if (c == 0) { if (!have_first) { have_first = 1; memcpy(firstval, val, sizeof val); } nperf++; }
        }
    }
    printf("K=%d type=%d m=%d base_walks=%d evals=%ld best_cost=%d perfect=%d cost<=2:%ld\n", K, TYPE, 2 * K, nw,
           nev, best, nperf, nlow);
    printf("hist:");
    for (int c = 0; c < 12; c++) printf(" %d:%ld", c, hist[c]);
    printf("\n");
    const int *vv = have_first ? firstval : bestval;
    uint64_t cov[16];
    eval_cost(vv, cov);
    printf("%s voltages: %d %d %d %d %d\n", have_first ? "PERFECT" : "best", vv[0], vv[1], vv[2], vv[3], vv[4]);
    for (int s = 0; s < 4; s++) for (int t = 0; t < 4; t++)
        if ((s < 2) == (t < 2)) printf("  pair (%d,%d): uncovered %d\n", s, t, K - __builtin_popcountll(cov[s * 4 + t]));
    if (argc > 3) write_controller(argv[3], vv);
    return 0;
}
