/* hxexpand.c: expand a compact export (hx_export_pc.g) into the haarex input format (N, N x N table, k, automorphisms).
 * a * b for b = g_1^e_1 ... g_k^e_k is a followed by e_1 right multiplications by g_1, then e_2 by g_2, ...
 * Checks: identity row/column, every row and column a permutation, every automorphism a bijection preserving the table.
 * usage: hxexpand IN OUT   (exit 3 if a check fails) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    int n, k; if (fscanf(f, "%d %d", &n, &k) != 2) return 2;
    int *R = malloc(sizeof(int) * n * k), *E = malloc(sizeof(int) * n * k), *M = malloc(sizeof(int) * n * n);
    for (int i = 0; i < n * k; i++) if (fscanf(f, "%d", &R[i]) != 1) return 2;
    for (int i = 0; i < n * k; i++) if (fscanf(f, "%d", &E[i]) != 1) return 2;
    int m; if (fscanf(f, "%d", &m) != 1) return 2;
    int *A = malloc(sizeof(int) * n * (m > 0 ? m : 1));
    for (int i = 0; i < n * m; i++) if (fscanf(f, "%d", &A[i]) != 1) return 2;
    fclose(f);
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) {
        int x = a; for (int i = 0; i < k; i++) for (int t = 0; t < E[b * k + i]; t++) x = R[i * n + x];
        M[a * n + b] = x;
    }
    char *seen = malloc(n);
    for (int a = 0; a < n; a++) {
        if (M[a] != a || M[a * n] != a) { fprintf(stderr, "identity check failed\n"); return 3; }
        memset(seen, 0, n); for (int b = 0; b < n; b++) seen[M[a * n + b]] = 1;
        for (int b = 0; b < n; b++) if (!seen[b]) { fprintf(stderr, "row not a permutation\n"); return 3; }
        memset(seen, 0, n); for (int b = 0; b < n; b++) seen[M[b * n + a]] = 1;
        for (int b = 0; b < n; b++) if (!seen[b]) { fprintf(stderr, "column not a permutation\n"); return 3; }
    }
    for (int j = 0; j < m; j++) { const int *g = A + j * n;
        for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (g[M[a * n + b]] != M[g[a] * n + g[b]]) { fprintf(stderr, "automorphism check failed\n"); return 3; } }
    FILE *o = fopen(argv[2], "w"); if (!o) return 2;
    fprintf(o, "%d\n", n);
    for (int a = 0; a < n; a++) { for (int b = 0; b < n; b++) fprintf(o, b ? " %d" : "%d", M[a * n + b]); fputc('\n', o); }
    fprintf(o, "%d\n", m);
    for (int j = 0; j < m; j++) { for (int a = 0; a < n; a++) fprintf(o, a ? " %d" : "%d", A[j * n + a]); fputc('\n', o); }
    fclose(o);
    return 0;
}
