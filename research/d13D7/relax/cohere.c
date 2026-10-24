/* cohere.c: is the "forbidden choice" coherent along a middle element?  Work in H (DUAL=0: centre is a point) or in
   the dual H^D (DUAL=1: centre is a line of H).  Centre c; branch b1 (neighbour of c); middle m (neighbour of b1,
   m != c, depth 2); for each depth-3 child a of m (a != b1) the 11 depth-4 children s of a (s != m) are the choices.
   For every depth-4 element t in another branch, and every a: which child s of a is at distance 4 from t (the
   forbidden one).  Report, for pairs (a1, a2), how many distinct (forbidden_a1, forbidden_a2) pairs occur.
   usage: cohere HEXFILE DUAL centre */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int q, N, Q1; int32_t *lp, *pl;
/* generic adjacency in the incidence graph: ids 0..N-1 "points", N..2N-1 "lines" of the chosen geometry */
int DUAL;
static const int32_t *nbrs(int x, int *off) {
    /* in H: point x -> lines pl[x]; line x-N -> points lp[x-N].  In H^D swap roles */
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
    DUAL = atoi(argv[2]); int cen = atoi(argv[3]);
    uint8_t *d0 = malloc(2L * N), *d = malloc(2L * N); int32_t *Qu = malloc(8L * N);
    bfs(cen, d0, Qu);
    int off; const int32_t *nb = nbrs(cen, &off); int b1 = nb[0] + off;
    const int32_t *nb2 = nbrs(b1, &off); int m = -1; for (int k = 0; k < Q1; k++) if (nb2[k] + off != cen) { m = nb2[k] + off; break; }
    /* branch of every element: the depth-1 element on its geodesic from cen (unique for depth <= 5) */
    int *br = malloc(sizeof(int) * 2 * N); for (int i = 0; i < 2 * N; i++) br[i] = -1;
    for (int i = 0; i < 2 * N; i++) if (d0[i] == 1) br[i] = i;
    for (int dep = 2; dep <= 5; dep++) for (int i = 0; i < 2 * N; i++) if (d0[i] == dep) {
        const int32_t *nn = nbrs(i, &off); for (int k = 0; k < Q1; k++) { int y = nn[k] + off; if (d0[y] == dep - 1) { br[i] = br[y]; break; } } }
    /* children a of m, and their children s */
    int A[16], na = 0; const int32_t *nm = nbrs(m, &off); for (int k = 0; k < Q1; k++) { int a = nm[k] + off; if (a != b1) A[na++] = a; }
    int Sch[16][16]; for (int i = 0; i < na; i++) { const int32_t *nn = nbrs(A[i], &off); int t = 0; for (int k = 0; k < Q1; k++) { int s = nn[k] + off; if (s != m) Sch[i][t++] = s; } }
    /* distances from each choice s to everything */
    uint8_t **ds = malloc(sizeof(uint8_t *) * na * q);
    for (int i = 0; i < na; i++) for (int j = 0; j < q; j++) { ds[i * q + j] = malloc(2L * N); bfs(Sch[i][j], ds[i * q + j], Qu); }
    /* targets: depth-4 elements of the same type as the choices, other branch */
    static int pairs[16][16][16][16]; long ntar = 0, nfar = 0, nnear = 0; long bad_unique = 0;
    for (int t = 0; t < 2 * N; t++) {
        if (d0[t] != 4 || br[t] == b1) continue;
        ntar++;
        bfs(0, d, Qu); /* placeholder to keep compiler quiet */ break;
    }
    ntar = 0;
    int forb[16];
    for (int t = 0; t < 2 * N; t++) {
        if (d0[t] != 4 || br[t] == b1) continue;
        ntar++;
        int ok = 1;
        for (int i = 0; i < na; i++) { int cnt = 0, w = -1; for (int j = 0; j < q; j++) if (ds[i * q + j][t] <= 4) { cnt++; w = j; } if (cnt != 1) ok = 0; forb[i] = w; }
        if (!ok) { nnear++; continue; }
        nfar++;
        for (int i = 0; i < na; i++) for (int k = 0; k < na; k++) pairs[i][k][forb[i]][forb[k]] = 1;
    }
    printf("DUAL=%d centre %d: depth-4 targets in other branches %ld, with exactly one forbidden choice at every a: %ld, others %ld\n", DUAL, cen, ntar, nfar, nnear);
    long tot = 0, mn = 999, mx = 0;
    for (int i = 0; i < na; i++) for (int k = i + 1; k < na; k++) { int cnt = 0; for (int x = 0; x < q; x++) for (int y = 0; y < q; y++) cnt += pairs[i][k][x][y]; tot += cnt; if (cnt < mn) mn = cnt; if (cnt > mx) mx = cnt; }
    printf("distinct (forbidden_a1, forbidden_a2) pairs per (a1,a2): min %ld max %ld (coherent = %d, random = %d)\n", mn, mx, q, q * q);
    return 0;
}
