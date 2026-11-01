/* Chart search for a GIVEN properly 4-edge-coloured bipartite controller (lines "a b colour", A-vertex a, B-vertex b,
   0-based, 4m lines).  A same-side controller pair (u, v) is covered in the route-chart lift if
     - some nonbacktracking walk of length 4 from u to v has a nonsingular colour pattern, or
     - u != v share a neighbour w whose edges to u, v have colours i, j, and the pencil condition P(i, j) holds
       (A side: P_A(i,j); B side: P_B(i,j); see chart_search.c / chart2.py).
   Cost = number of uncovered same-side ordered pairs (0 = the lift has diameter <= 5).
   The chart is annealed: A_1..A_3 (A_0 = I) and b_0..b_3 over F_4.
   usage: chart_for_ctrl CTRL seconds seed [T0] [out]   (out: chart in chart_search.c's text format) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static const int MUL[4][4] = {{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}}, INVF[4] = {0,1,3,2};
static int smul[4][256];
typedef struct { int c[4]; } mat;
static inline int coord(int v, int r) { return (v >> (2 * r)) & 3; }
static inline int mv(const mat *M, int v) { int out = 0; for (int j = 0; j < 4; j++) out ^= smul[coord(v, j)][M->c[j]]; return out; }
static int rank4(const int *v, int n) {
    int a[8]; memcpy(a, v, n * sizeof(int)); int r = 0;
    for (int col = 0; col < 4 && r < n; col++) {
        int p = -1; for (int i = r; i < n; i++) if (coord(a[i], col)) { p = i; break; }
        if (p < 0) continue;
        int t = a[p]; a[p] = a[r]; a[r] = t;
        int iv = INVF[coord(a[r], col)]; a[r] = smul[iv][a[r]];
        for (int i = 0; i < n; i++) if (i != r && coord(a[i], col)) a[i] ^= smul[coord(a[i], col)][a[r]];
        r++;
    }
    return r;
}
static int inv_mat(const mat *M, mat *R) {
    int X[4][8];
    for (int r = 0; r < 4; r++) for (int c = 0; c < 4; c++) { X[r][c] = coord(M->c[c], r); X[r][4 + c] = (r == c); }
    for (int col = 0; col < 4; col++) {
        int p = -1; for (int r = col; r < 4; r++) if (X[r][col]) { p = r; break; }
        if (p < 0) return 0;
        for (int c = 0; c < 8; c++) { int t = X[p][c]; X[p][c] = X[col][c]; X[col][c] = t; }
        int iv = INVF[X[col][col]]; for (int c = 0; c < 8; c++) X[col][c] = MUL[iv][X[col][c]];
        for (int r = 0; r < 4; r++) if (r != col && X[r][col]) { int f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] ^= MUL[f][X[col][c]]; }
    }
    for (int c = 0; c < 4; c++) { int v = 0; for (int r = 0; r < 4; r++) v |= X[r][4 + c] << (2 * r); R->c[c] = v; }
    return 1;
}
static int quot_point(int w1, int w2, int z) {
    int basis[4] = {w1, w2, 0, 0}, nb = 2;
    for (int r = 0; r < 4 && nb < 4; r++) { basis[nb] = 1 << (2 * r); if (rank4(basis, nb + 1) == nb + 1) nb++; }
    if (nb < 4) return -1;
    mat B, Bi; for (int j = 0; j < 4; j++) B.c[j] = basis[j];
    if (!inv_mat(&B, &Bi)) return -1;
    int x = mv(&Bi, z); int x3 = coord(x, 2), x4 = coord(x, 3);
    if (!x3 && !x4) return -1;
    if (!x3) return 4;
    return MUL[INVF[x3]][x4];
}
static int pencil_ok(int w1, int w2, const int *z, int nz) {
    int wv[2] = {w1, w2}; if (rank4(wv, 2) < 2) return 0;
    int seen = 0; for (int i = 0; i < nz; i++) { int p = quot_point(w1, w2, z[i]); if (p >= 0) seen |= 1 << p; }
    return seen == 31;
}
static mat A[4], Ai[4]; static int b[4];
static int pidx[4][4][4][4];            /* pattern index 0..107 */
static int okA[108], okB[108], penA[4][4], penB[4][4];
static void eval_chart(void) {
    int v[4];
    for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1) for (int i3 = 0; i3 < 4; i3++) if (i3 != i2)
    for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) {
        int p = pidx[i1][i2][i3][i4];
        v[0] = mv(&Ai[i2], b[i1]); v[1] = mv(&Ai[i2], b[i2]); v[2] = mv(&Ai[i3], b[i3]); v[3] = mv(&Ai[i3], b[i4]);
        okA[p] = rank4(v, 4) == 4;
        v[0] = mv(&A[i2], mv(&Ai[i1], b[i1])); v[1] = b[i2]; v[2] = b[i3]; v[3] = mv(&A[i3], mv(&Ai[i4], b[i4]));
        okB[p] = rank4(v, 4) == 4;
    }
    int z[8], c[4]; for (int l = 0; l < 4; l++) c[l] = mv(&Ai[l], b[l]);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) {
        int n = 0;
        for (int k = 0; k < 4; k++) if (k != i) z[n++] = mv(&A[i], c[k]);
        for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = b[l];
        for (int k = 0; k < 4; k++) if (k != j) z[n++] = mv(&A[j], c[k]);
        penA[i][j] = pencil_ok(b[i], b[j], z, n);
        n = 0;
        for (int k = 0; k < 4; k++) if (k != i) z[n++] = mv(&Ai[i], b[k]);
        for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = c[l];
        for (int k = 0; k < 4; k++) if (k != j) z[n++] = mv(&Ai[j], b[k]);
        penB[i][j] = pencil_ok(c[i], c[j], z, n);
    }
}
/* controller pairs: for each same-side ordered pair, a list of pattern indices and pencil colour pairs */
typedef struct { int side; int np; int pats[64]; int nq; int pq[16]; } pairinfo;
static pairinfo *P; static int npairs;
static int cost(void) {
    for (int i = 0; i < 4; i++) if (!inv_mat(&A[i], &Ai[i])) return 1 << 28;
    eval_chart();
    int c = 0;
    for (int k = 0; k < npairs; k++) {
        pairinfo *q = &P[k]; int ok = 0;
        const int *okp = q->side ? okB : okA;
        for (int t = 0; t < q->np && !ok; t++) ok = okp[q->pats[t]];
        for (int t = 0; t < q->nq && !ok; t++) { int i = q->pq[t] >> 2, j = q->pq[t] & 3; ok = q->side ? penB[i][j] : penA[i][j]; }
        c += !ok;
    }
    return c;
}
static void rand_gl(mat *M) { mat R; do { for (int j = 0; j < 4; j++) M->c[j] = xr() & 255; } while (!inv_mat(M, &R)); }
static int rand_vec(void) { int v; do v = xr() & 255; while (!v); return v; }
int main(int argc, char **argv) {
    for (int l = 0; l < 4; l++) for (int v = 0; v < 256; v++) { int o = 0; for (int r = 0; r < 4; r++) o |= MUL[l][coord(v, r)] << (2 * r); smul[l][v] = o; }
    int np = 0; for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) for (int i3 = 0; i3 < 4; i3++) for (int i4 = 0; i4 < 4; i4++)
        pidx[i1][i2][i3][i4] = (i1 != i2 && i2 != i3 && i3 != i4) ? np++ : -1;
    FILE *f = fopen(argv[1], "r"); int ea[4096], eb[4096], ec[4096], ne = 0;
    while (ne < 4096 && fscanf(f, "%d %d %d", &ea[ne], &eb[ne], &ec[ne]) == 3) ne++;
    fclose(f);
    int m = 0; for (int i = 0; i < ne; i++) if (ea[i] + 1 > m) m = ea[i] + 1;
    int N = 2 * m; int (*nb)[4] = malloc(sizeof(int[4]) * N), (*nc)[4] = malloc(sizeof(int[4]) * N); int *dg = calloc(N, sizeof(int));
    for (int i = 0; i < ne; i++) { int a = ea[i], bb = m + eb[i];
        nb[a][dg[a]] = bb; nc[a][dg[a]++] = ec[i]; nb[bb][dg[bb]] = a; nc[bb][dg[bb]++] = ec[i]; }
    for (int x = 0; x < N; x++) if (dg[x] != 4) { printf("controller not 4-regular at %d\n", x); return 1; }
    double secs = atof(argv[2]); rs ^= (uint64_t)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    double T0 = argc > 4 ? atof(argv[4]) : 1.0; const char *out = argc > 5 ? argv[5] : NULL;
    /* collect pair info */
    P = calloc((size_t)2 * m * m, sizeof(pairinfo)); npairs = 0; int far = 0;
    int *slot = malloc(sizeof(int) * N);
    for (int side = 0; side < 2; side++) for (int u0 = 0; u0 < m; u0++) {
        int u = side ? m + u0 : u0, lo = side ? m : 0;
        for (int v = 0; v < N; v++) slot[v] = -1;
        for (int v0 = 0; v0 < m; v0++) { slot[lo + v0] = npairs; P[npairs].side = side; P[npairs].np = 0; P[npairs].nq = 0; npairs++; }
        for (int a = 0; a < 4; a++) { int x = nb[u][a], c1 = nc[u][a];
            for (int bq = 0; bq < 4; bq++) { int y = nb[x][bq], c2 = nc[x][bq]; if (c2 == c1) continue;
                /* distance-2 pencil pair: y != u shares neighbour x; colours (c1, c2) */
                pairinfo *q = &P[slot[y]];
                { int key = c1 * 4 + c2, dup = 0; for (int t = 0; t < q->nq; t++) if (q->pq[t] == key) dup = 1; if (!dup && q->nq < 16) q->pq[q->nq++] = key; }
                for (int cq = 0; cq < 4; cq++) { int z = nb[y][cq], c3 = nc[y][cq]; if (c3 == c2) continue;
                    for (int dq = 0; dq < 4; dq++) { int t = nb[z][dq], c4 = nc[z][dq]; if (c4 == c3) continue;
                        pairinfo *r = &P[slot[t]]; int pp = pidx[c1][c2][c3][c4], dup = 0;
                        for (int s = 0; s < r->np; s++) if (r->pats[s] == pp) dup = 1;
                        if (!dup && r->np < 64) r->pats[r->np++] = pp; } } } }
    }
    for (int k = 0; k < npairs; k++) if (P[k].np == 0 && P[k].nq == 0) far++;
    printf("controller m=%d: %d same-side ordered pairs, %d with no walk of length 2 or NB-4 at all (beyond reach)\n", m, npairs, far);
    /* anneal the chart */
    clock_t t0 = clock(); int best = 1 << 30; mat bA[4]; int bb[4]; long it = 0;
    for (int j = 0; j < 4; j++) A[0].c[j] = 1 << (2 * j);
    for (int i = 1; i < 4; i++) rand_gl(&A[i]); for (int i = 0; i < 4; i++) b[i] = rand_vec();
    int c = cost();
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs && best > far) {
        it++;
        double fr = (double)(clock() - t0) / CLOCKS_PER_SEC / secs, TT = T0 * pow(0.01, fr) + 1e-3;
        mat sA[4]; int sb[4]; memcpy(sA, A, sizeof A); memcpy(sb, b, sizeof b);
        if (xr() & 1) { int k = 1 + xr() % 3, col = xr() % 4, row = xr() % 4;
            A[k].c[col] = (A[k].c[col] & ~(3 << (2 * row))) | ((int)(xr() % 4) << (2 * row)); }
        else b[xr() % 4] = rand_vec();
        int c2 = cost();
        if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) { c = c2;
            if (c < best) { best = c; memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b); } }
        else { memcpy(A, sA, sizeof A); memcpy(b, sb, sizeof b); }
        if (it % 20000 == 0 && c > best + 30) { memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b); c = best; }
    }
    printf("best uncovered pairs %d (unreachable %d) iters %ld\n", best, far, it);
    if (out) { FILE *g = fopen(out, "w");
        for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) for (int cc = 0; cc < 4; cc++) fprintf(g, "%d ", coord(bA[i].c[cc], r)); fprintf(g, "\n"); }
        for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) fprintf(g, "%d ", coord(bb[i], r)); fprintf(g, "\n"); }
        fclose(g); }
    return 0;
}
