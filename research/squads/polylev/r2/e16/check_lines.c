/* check_lines.c: independent certifier for K disjoint 4-dominating classes of lines of H(q), q prime (here q = 7).
   Written separately from e16_dom.c: it does not use its ball tables.
   For each class B: multi-source BFS in the incidence graph (points and lines) from the lines of B up to distance 4;
   the class is 4-dominating when every line is reached at distance <= 4. Also checks:
   - every line of the hexagon has q+1 points that lie on Q and are pairwise orthogonal (totally singular),
   - the classes are pairwise disjoint (each line has at most one colour).
   Usage: check_lines HEXBIN SOL(int32 per line, -1 free)
   Prints: valid classes K (classes that are 4-dominating, nonempty), sizes min/max/avg, and the total number of lines used. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: check_lines HEXBIN SOL\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3];
    if (!f || fread(h, 4, 3, f) != 3) { fprintf(stderr, "bad hex\n"); return 1; }
    int q = h[0], N = h[1], Q1 = q + 1;
    int32_t *LP = malloc(4 * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) { fprintf(stderr, "short\n"); return 1; }
    uint8_t *X = malloc((size_t)N * 7);
    if (fread(X, 1, (size_t)N * 7, f) != (size_t)N * 7) { fprintf(stderr, "short coords\n"); return 1; }
    fclose(f);
    /* point -> lines, built here from scratch */
    int32_t *PL = malloc(4 * (size_t)N * Q1); int *deg = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int a = 0; a < Q1; a++) { int p = LP[(size_t)l * Q1 + a]; if (p < 0 || p >= N) { fprintf(stderr, "bad point id\n"); return 1; } PL[(size_t)p * Q1 + deg[p]++] = l; }
    for (int p = 0; p < N; p++) if (deg[p] != Q1) { fprintf(stderr, "point %d on %d lines\n", p, deg[p]); return 1; }
    /* geometry: Q(x) = x0x4 + x1x5 + x2x6 - x3^2 = 0 and b(x,y) = 0 for distinct points of a line, mod q (prime) */
    #define C(p, i) ((int)X[(size_t)(p) * 7 + (i)])
    #define QF(p) ((C(p,0)*C(p,4) + C(p,1)*C(p,5) + C(p,2)*C(p,6) - C(p,3)*C(p,3)) % q)
    #define BF(p, r) ((C(p,0)*C(r,4) + C(p,4)*C(r,0) + C(p,1)*C(r,5) + C(p,5)*C(r,1) + C(p,2)*C(r,6) + C(p,6)*C(r,2) - 2*C(p,3)*C(r,3)) % q)
    long geobad = 0;
    for (int l = 0; l < N; l++) {
        for (int a = 0; a < Q1; a++) { int p = LP[(size_t)l * Q1 + a]; if (((QF(p) % q) + q) % q != 0) geobad++;
            for (int b = a + 1; b < Q1; b++) { int r = LP[(size_t)l * Q1 + b]; if (((BF(p, r) % q) + q) % q != 0) geobad++; } }
    }
    /* solution */
    int32_t *sol = malloc(4 * (size_t)N); f = fopen(argv[2], "rb");
    if (!f || fread(sol, 4, N, f) != (size_t)N) { fprintf(stderr, "bad solution file\n"); return 1; }
    fclose(f);
    int K = 0; for (int l = 0; l < N; l++) if (sol[l] + 1 > K) K = sol[l] + 1;
    long *size = calloc(K + 1, sizeof(long));
    for (int l = 0; l < N; l++) if (sol[l] >= 0) size[sol[l]]++;
    int *dist = malloc(sizeof(int) * (2 * (size_t)N)); int *queue = malloc(sizeof(int) * 2 * (size_t)N);
    int valid = 0; long used = 0, mn = 1L << 30, mx = 0;
    for (int k = 0; k < K; k++) {
        if (size[k] == 0) continue;
        used += size[k]; if (size[k] < mn) mn = size[k]; if (size[k] > mx) mx = size[k];
        for (int v = 0; v < 2 * N; v++) dist[v] = -1;
        int qh = 0, qt = 0;
        for (int l = 0; l < N; l++) if (sol[l] == k) { dist[l] = 0; queue[qt++] = l; }   /* lines are 0..N-1 */
        while (qh < qt) {
            int v = queue[qh++]; int d = dist[v];
            if (d >= 4) continue;
            if (v < N) { for (int a = 0; a < Q1; a++) { int p = N + LP[(size_t)v * Q1 + a]; if (dist[p] < 0) { dist[p] = d + 1; queue[qt++] = p; } } }
            else { int p = v - N; for (int a = 0; a < Q1; a++) { int m = PL[(size_t)p * Q1 + a]; if (dist[m] < 0) { dist[m] = d + 1; queue[qt++] = m; } } }
        }
        int ok = 1; for (int l = 0; l < N && ok; l++) if (dist[l] < 0 || dist[l] > 4) ok = 0;
        if (ok) valid++;
        else fprintf(stderr, "class %d is NOT 4-dominating\n", k);
    }
    printf("hex q=%d N=%d geometry_violations=%ld\n", q, N, geobad);
    int nonempty = 0; for (int k = 0; k < K; k++) if (size[k] > 0) nonempty++;
    printf("nonempty_classes=%d valid_4_dominating=%d lines_used=%ld size_min=%ld size_max=%ld avg=%.3f\n",
           nonempty, valid, used, mn, mx, nonempty ? (double)used / nonempty : 0.0);
    return 0;
}
