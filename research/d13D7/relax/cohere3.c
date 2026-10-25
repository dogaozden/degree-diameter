/* cohere3.c: like cohere.c but the middle m is at depth 3 from the centre (centre c, e1 = depth 1, e2 = depth 2,
   m = depth 3), the choices are the depth-5 children of the depth-4 children a of m.  Targets: depth-5 elements
   (same type as the choices) whose depth-2 ancestor differs from e2 (MODE 1: same depth-1 ancestor e1;
   MODE 2: different depth-1 ancestor).  usage: cohere3 HEXFILE DUAL centre MODE */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int q, N, Q1; int32_t *lp, *pl; int DUAL;
static const int32_t *nbrs(int x, int *off) {
    if (!DUAL) { if (x < N) { *off = N; return &pl[(size_t)x * Q1]; } *off = 0; return &lp[(size_t)(x - N) * Q1]; }
    else { if (x < N) { *off = N; return &lp[(size_t)x * Q1]; } *off = 0; return &pl[(size_t)(x - N) * Q1]; }
}
static void bfs(int s, uint8_t *d, int32_t *Qu) {
    memset(d, 255, 2 * (size_t)N); int h = 0, t = 0; d[s] = 0; Qu[t++] = s;
    while (h < t) { int x = Qu[h++]; int off; const int32_t *nb = nbrs(x, &off);
        for (int k = 0; k < Q1; k++) { int y = nb[k] + off; if (d[y] == 255) { d[y] = d[x] + 1; Qu[t++] = y; } } }
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) return 1; q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    lp = malloc(4L * N * Q1); if (fread(lp, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1; fclose(f);
    pl = malloc(4L * N * Q1); int *c = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = lp[(size_t)l * Q1 + k]; pl[(size_t)p * Q1 + c[p]++] = l; }
    DUAL = atoi(argv[2]); int cen = atoi(argv[3]), MODE = atoi(argv[4]);
    uint8_t *d0 = malloc(2L * N); int32_t *Qu = malloc(8L * N);
    bfs(cen, d0, Qu);
    int off; int e1 = nbrs(cen, &off)[0] + off;
    int e2 = -1; { const int32_t *nn = nbrs(e1, &off); for (int k = 0; k < Q1; k++) if (nn[k] + off != cen) { e2 = nn[k] + off; break; } }
    int m = -1; { const int32_t *nn = nbrs(e2, &off); for (int k = 0; k < Q1; k++) if (nn[k] + off != e1) { m = nn[k] + off; break; } }
    /* ancestors at depth 1 and 2 (unique for depth <= 5) */
    int *a1 = malloc(sizeof(int) * 2 * N), *a2 = malloc(sizeof(int) * 2 * N);
    for (int i = 0; i < 2 * N; i++) { a1[i] = a2[i] = -1; if (d0[i] == 1) a1[i] = i; if (d0[i] == 2) a2[i] = i; }
    for (int dep = 2; dep <= 5; dep++) for (int i = 0; i < 2 * N; i++) if (d0[i] == dep) {
        const int32_t *nn = nbrs(i, &off); for (int k = 0; k < Q1; k++) { int y = nn[k] + off; if (d0[y] == dep - 1) { a1[i] = a1[y]; if (dep > 2) a2[i] = a2[y]; break; } } }
    int A[16], na = 0; { const int32_t *nn = nbrs(m, &off); for (int k = 0; k < Q1; k++) { int a = nn[k] + off; if (a != e2) A[na++] = a; } }
    int Sch[16][16]; for (int i = 0; i < na; i++) { const int32_t *nn = nbrs(A[i], &off); int t = 0; for (int k = 0; k < Q1; k++) { int s = nn[k] + off; if (s != m) Sch[i][t++] = s; } }
    uint8_t **ds = malloc(sizeof(uint8_t *) * na * q);
    for (int i = 0; i < na; i++) for (int j = 0; j < q; j++) { ds[i * q + j] = malloc(2L * N); bfs(Sch[i][j], ds[i * q + j], Qu); }
    static int pairs[16][16][16][16]; long ntar = 0, nfar = 0, nnear = 0; int forb[16];
    long hist[16] = {0};
    for (int t = 0; t < 2 * N; t++) {
        if (d0[t] != 5 || a2[t] == e2) continue;
        if (MODE == 1 && a1[t] != e1) continue;
        if (MODE == 2 && a1[t] == e1) continue;
        ntar++; int ok = 1;
        for (int i = 0; i < na; i++) { int cnt = 0, w = -1; for (int j = 0; j < q; j++) if (ds[i * q + j][t] <= 4) { cnt++; w = j; } if (cnt != 1) ok = 0; forb[i] = w; hist[cnt > 15 ? 15 : cnt]++; }
        if (!ok) { nnear++; continue; }
        nfar++;
        for (int i = 0; i < na; i++) for (int k = 0; k < na; k++) pairs[i][k][forb[i]][forb[k]] = 1;
    }
    printf("DUAL=%d MODE=%d: targets %ld, exactly-one-forbidden-everywhere %ld, others %ld; hist of #forbidden per a:", DUAL, MODE, ntar, nfar, nnear);
    for (int k = 0; k < 13; k++) printf(" %d:%ld", k, hist[k]); printf("\n");
    long mn = 999, mx = 0;
    for (int i = 0; i < na; i++) for (int k = i + 1; k < na; k++) { int cnt = 0; for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) cnt += pairs[i][k][x][y]; if (cnt < mn) mn = cnt; if (cnt > mx) mx = cnt; }
    printf("distinct forbidden pairs per (a1,a2): min %ld max %ld (coherent %d, random %d)\n", mn, mx, q, q * q);
    return 0;
}
