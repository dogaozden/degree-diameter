/* counts.c: the counting constants of OMEGA_REPAIR.md Lemma 3.1, checked on H(q).  For a vertex t of the incidence
   graph I(H(q)) (points, then lines, as sources) and every vertex z, count the vertices x of t's type with
   d(x,t) = 6 and d(x,z) <= R (R = 4, 2 for z of t's type; R = 3, 1 for z of the other type), and print the distinct
   values seen for each d(t,z).  usage: counts hex.txt [sources per type] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int q, n, Q1, *Lp, *Pl;
int nb(int v, int j) { return v < n ? n + Pl[v * Q1 + j] : Lp[(v - n) * Q1 + j]; }
void bfs(int s, int *d) { for (int i = 0; i < 2 * n; i++) d[i] = -1; int *Qu = malloc(sizeof(int) * 2 * n), h = 0, tl = 0; d[s] = 0; Qu[tl++] = s;
    while (h < tl) { int v = Qu[h++]; for (int j = 0; j < Q1; j++) { int w = nb(v, j); if (d[w] < 0) { d[w] = d[v] + 1; Qu[tl++] = w; } } } free(Qu); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int nl; if (fscanf(f, "%d %d %d", &q, &n, &nl) != 3) return 1; Q1 = q + 1;
    Lp = malloc(sizeof(int) * n * Q1); Pl = malloc(sizeof(int) * n * Q1); int *c = calloc(n, 4);
    for (int l = 0; l < n; l++) for (int j = 0; j < Q1; j++) { int p; if (fscanf(f, "%d", &p) != 1) return 1; Lp[l * Q1 + j] = p; Pl[p * Q1 + c[p]++] = l; }
    int S = argc > 2 ? atoi(argv[2]) : 3;
    int *dt = malloc(sizeof(int) * 2 * n), *dz = malloc(sizeof(int) * 2 * n);
    /* table[type of t][d(t,z)][R] -> min, max */
    long mn[2][7][5], mx[2][7][5]; for (int a = 0; a < 2; a++) for (int b = 0; b < 7; b++) for (int r = 0; r < 5; r++) { mn[a][b][r] = 1L << 60; mx[a][b][r] = -1; }
    for (int side = 0; side < 2; side++) for (int s = 0; s < S; s++) {
        int t = side * n + (s * 7919) % n; bfs(t, dt);
        for (int z = 0; z < 2 * n; z++) { if ((z * 2654435761u) % (n < 2000 ? 1 : 7)) continue; bfs(z, dz); int D = dt[z];
            long cnt[5] = {0};
            for (int x = side * n; x < side * n + n; x++) if (dt[x] == 6 && dz[x] <= 4) cnt[dz[x]]++;
            /* cumulative: dz <= R with parity of R */
            for (int R = 0; R <= 4; R++) { long v = 0; for (int r = R & 1; r <= R; r += 2) v += cnt[r]; if (v < mn[side][D][R]) mn[side][D][R] = v; if (v > mx[side][D][R]) mx[side][D][R] = v; }
        }
    }
    for (int side = 0; side < 2; side++) for (int D = 0; D <= 6; D++) {
        printf("q=%d t=%s d(t,z)=%d:", q, side ? "line " : "point", D);
        for (int R = (D & 1); R <= 4; R += 2) printf("  |B(z,%d) & opp(t)| in [%ld,%ld]", R, mn[side][D][R], mx[side][D][R]);
        printf("\n"); }
    return 0;
}
