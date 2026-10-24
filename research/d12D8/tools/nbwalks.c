/* nbwalks.c: count non-backtracking walks of length <= MAXLEN (odd lengths) from a point source to every line,
   in a base multigraph (liftcheck format, voltages in Z_m read as "levels"), separately per level.
   Usage: nbwalks BASE src [MAXLEN]
   Prints a histogram of walk counts per (line, level) target, split by hexagon distance if HEX=q is set
   (base must then be hexagon edges first). Only for cyclic groups. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int NP, NL, m;
int main(int argc, char **argv) {
    int src = atoi(argv[2]); int maxlen = argc > 3 ? atoi(argv[3]) : 7;
    FILE *f = fopen(argv[1], "r"); char gs[32];
    if (fscanf(f, "%d %d %d %31s", &NP, &NL, &m, gs) != 4) return 1;
    int cap = 1 << 21, ne = 0; int *E = malloc(sizeof(int) * 3 * cap); int p, l, g;
    while (fscanf(f, "%d %d %d", &p, &l, &g) == 3) { if (ne == cap) { cap *= 2; E = realloc(E, sizeof(int) * 3 * cap); } E[3*ne] = p; E[3*ne+1] = l; E[3*ne+2] = g; ne++; }
    fclose(f);
    /* edge-state DP: state = (edge id, direction, level). cnt[dir][e][x]: number of NB walks ending by traversing edge e
       in direction dir (0: point->line, 1: line->point) with current level x. */
    int *pst = calloc(NP + 1, sizeof(int)), *lst = calloc(NL + 1, sizeof(int));
    for (int i = 0; i < ne; i++) { pst[E[3*i]+1]++; lst[E[3*i+1]+1]++; }
    for (int i = 0; i < NP; i++) pst[i+1] += pst[i];
    for (int i = 0; i < NL; i++) lst[i+1] += lst[i];
    int *pe = malloc(sizeof(int) * ne), *le = malloc(sizeof(int) * ne), *pc = calloc(NP, sizeof(int)), *lc = calloc(NL, sizeof(int));
    for (int i = 0; i < ne; i++) { pe[pst[E[3*i]] + pc[E[3*i]]++] = i; le[lst[E[3*i+1]] + lc[E[3*i+1]]++] = i; }
    double *c0 = calloc((size_t)ne * m, sizeof(double)), *c1 = calloc((size_t)ne * m, sizeof(double));
    double *n0 = calloc((size_t)ne * m, sizeof(double)), *n1 = calloc((size_t)ne * m, sizeof(double));
    double *tot = calloc((size_t)NL * m, sizeof(double));
    /* step 1: from src along its edges */
    for (int k = pst[src]; k < pst[src+1]; k++) { int e = pe[k]; c0[(size_t)e * m + E[3*e+2] % m] += 1; }
    for (int len = 1; len <= maxlen; len++) {
        if (len & 1) {
            /* c0 holds walks ending at a line via edge e (point->line). record totals */
            for (int e = 0; e < ne; e++) for (int x = 0; x < m; x++) tot[(size_t)E[3*e+1] * m + x] += c0[(size_t)e*m+x];
            if (len == maxlen) break;
            /* extend line -> point along edge e2 != e */
            memset(n1, 0, sizeof(double) * ne * m);
            for (int y = 0; y < NL; y++) {
                for (int a = lst[y]; a < lst[y+1]; a++) { int e = le[a];
                    for (int b = lst[y]; b < lst[y+1]; b++) { int e2 = le[b]; if (e2 == e) continue;
                        int v = E[3*e2+2];
                        for (int x = 0; x < m; x++) { double c = c0[(size_t)e*m+x]; if (c) n1[(size_t)e2*m + ((x - v) % m + m) % m] += c; } } }
            }
            double *t = c1; c1 = n1; n1 = t;
        } else {
            memset(n0, 0, sizeof(double) * ne * m);
            for (int pp = 0; pp < NP; pp++) {
                for (int a = pst[pp]; a < pst[pp+1]; a++) { int e = pe[a];
                    for (int b = pst[pp]; b < pst[pp+1]; b++) { int e2 = pe[b]; if (e2 == e) continue;
                        int v = E[3*e2+2];
                        for (int x = 0; x < m; x++) { double c = c1[(size_t)e*m+x]; if (c) n0[(size_t)e2*m + (x + v) % m] += c; } } }
            }
            double *t = c0; c0 = n0; n0 = t;
        }
    }
    /* histogram of tot */
    int H[64] = {0}; double mn = 1e18, sum = 0; long cntz = 0;
    for (size_t i = 0; i < (size_t)NL * m; i++) { double v = tot[i]; sum += v; if (v < mn) mn = v; int b = v < 1 ? 0 : (v < 2 ? 1 : (v < 4 ? 2 : (v < 8 ? 3 : (v < 16 ? 4 : (v < 32 ? 5 : (v < 64 ? 6 : (v < 128 ? 7 : (v < 256 ? 8 : 9)))))))); H[b]++; if (v < 1) cntz++; }
    printf("src %d: targets %d, mean walks %.1f, min %.0f, zero %ld\n", src, NL * m, sum / ((double)NL * m), mn, cntz);
    const char *lab[] = {"0", "1", "2-3", "4-7", "8-15", "16-31", "32-63", "64-127", "128-255", ">=256"};
    for (int b = 0; b < 10; b++) printf("  %-7s %d\n", lab[b], H[b]);
    if (getenv("DUMP")) { FILE *g = fopen(getenv("DUMP"), "w"); for (size_t i = 0; i < (size_t)NL * m; i++) fprintf(g, "%.0f\n", tot[i]); fclose(g); }
    return 0;
}
