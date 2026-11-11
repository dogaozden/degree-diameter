/* Joint annealing of a multi-orbit controller and its route chart.
   Controller: voltage lift of a 4-regular bipartite base multigraph on k + k vertices (as in mlift_chart.c; the base is
   properly 4-edge-coloured by Konig, the controller edge inherits the base colour).  Chart: A_0 = I, A_1..A_3 in
   GL_4(F_4), b_0..b_3 in F_4^4 (as in chart_for_ctrl.c).  A same-side controller pair (u, v) counts as covered iff
     - u != v and some length-2 path u -i- x -j- v has the pencil property for u's side (penA / penB), or
     - some nonbacktracking walk of length 4 from u to v has a colour pattern that is nonsingular for u's side.
   Cost = uncovered (source orbit, target) pairs; 0 means the route-chart lift has diameter <= 5 (BEAT_16_5_SQUAD.md
   section 2.1).  Moves: one voltage (probability PV) or one chart entry / one b vector.
   usage: mlift_joint BASE TABLE seconds seed [T0] [PV] [out_prefix]
   env INIT_CHART=file starts from a chart (chart_search.c text format); out_prefix.edges ("a b colour", A-vertex
   (a_i, g) -> i*n+g, B-vertex (b_j, h) -> j*n+h) and out_prefix.chart are written for the best state when the cost
   is 0 or env WRITEBEST is set. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
/* ---- F_4^4 chart (copied from chart_for_ctrl.c) ---- */
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
static int pidx[4][4][4][4];
static unsigned char okA[108], okB[108], penA[16], penB[16];
static int nsing, npen;
static int eval_chart(void) {
    for (int i = 0; i < 4; i++) if (!inv_mat(&A[i], &Ai[i])) return 0;
    for (int i = 0; i < 4; i++) if (!b[i]) return 0;
    int v[4]; nsing = 0; npen = 0;
    for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) if (i2 != i1) for (int i3 = 0; i3 < 4; i3++) if (i3 != i2)
    for (int i4 = 0; i4 < 4; i4++) if (i4 != i3) {
        int p = pidx[i1][i2][i3][i4];
        v[0] = mv(&Ai[i2], b[i1]); v[1] = mv(&Ai[i2], b[i2]); v[2] = mv(&Ai[i3], b[i3]); v[3] = mv(&Ai[i3], b[i4]);
        okA[p] = rank4(v, 4) == 4;
        v[0] = mv(&A[i2], mv(&Ai[i1], b[i1])); v[1] = b[i2]; v[2] = b[i3]; v[3] = mv(&A[i3], mv(&Ai[i4], b[i4]));
        okB[p] = rank4(v, 4) == 4;
        nsing += !okA[p] + !okB[p];
    }
    int z[8], c[4]; for (int l = 0; l < 4; l++) c[l] = mv(&Ai[l], b[l]);
    for (int i = 0; i < 4; i++) for (int j = 0; j < 4; j++) if (i != j) {
        int n = 0;
        for (int k = 0; k < 4; k++) if (k != i) z[n++] = mv(&A[i], c[k]);
        for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = b[l];
        for (int k = 0; k < 4; k++) if (k != j) z[n++] = mv(&A[j], c[k]);
        penA[i * 4 + j] = pencil_ok(b[i], b[j], z, n);
        n = 0;
        for (int k = 0; k < 4; k++) if (k != i) z[n++] = mv(&Ai[i], b[k]);
        for (int l = 0; l < 4; l++) if (l != i && l != j) z[n++] = c[l];
        for (int k = 0; k < 4; k++) if (k != j) z[n++] = mv(&Ai[j], b[k]);
        penB[i * 4 + j] = pencil_ok(c[i], c[j], z, n);
        npen += !penA[i * 4 + j] + !penB[i * 4 + j];
    }
    return 1;
}
static void rand_gl(mat *M) { mat R; do { for (int j = 0; j < 4; j++) M->c[j] = xr() & 255; } while (!inv_mat(M, &R)); }
static int rand_vec(void) { int v; do v = xr() & 255; while (!v); return v; }
/* ---- voltage lift (as in mlift_chart.c) ---- */
int k, ne, EA[64], EB[64], col[64], n, *T, *Inv, e_id, istree[64], volt[64];
/* walk lists per source orbit: len, edges, end orbit, key (pattern index for len 4, colour pair for len 2) */
int nwA[32], wA[32][700][4], lenA[32][700], endA[32][700], keyA[32][700];
int nwB[32], wB[32][700][4], lenB[32][700], endB[32][700], keyB[32][700];
static inline int mul(int a, int b2) { return T[a * n + b2]; }
unsigned char *hit;
int cost(void) {
    int c = 0;
    for (int i = 0; i < k; i++) {
        memset(hit, 0, k * n);
        for (int w = 0; w < nwA[i]; w++) { int *E = wA[i][w], x;
            if (lenA[i][w] == 2) { if (!penA[keyA[i][w]]) continue; x = mul(Inv[volt[E[1]]], volt[E[0]]); if (endA[i][w] == i && x == e_id) continue; }
            else { if (!okA[keyA[i][w]]) continue; x = mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]]))); }
            hit[endA[i][w] * n + x] = 1; }
        for (int t = 0; t < k * n; t++) c += !hit[t];
    }
    for (int j = 0; j < k; j++) {
        memset(hit, 0, k * n);
        for (int w = 0; w < nwB[j]; w++) { int *E = wB[j][w], x;
            if (lenB[j][w] == 2) { if (!penB[keyB[j][w]]) continue; x = mul(volt[E[1]], Inv[volt[E[0]]]); if (endB[j][w] == j && x == e_id) continue; }
            else { if (!okB[keyB[j][w]]) continue; x = mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]]))); }
            hit[endB[j][w] * n + x] = 1; }
        for (int t = 0; t < k * n; t++) c += !hit[t];
    }
    return c;
}
int parallel_ok(void) { for (int a = 0; a < ne; a++) for (int b2 = a + 1; b2 < ne; b2++) if (EA[a] == EA[b2] && EB[a] == EB[b2] && volt[a] == volt[b2]) return 0; return 1; }
int used[64], matchB[32], visB[32];
int aug(int a) { for (int e = 0; e < ne; e++) if (!used[e] && EA[e] == a && !visB[EB[e]]) { visB[EB[e]] = 1;
        if (matchB[EB[e]] < 0 || aug(EA[matchB[EB[e]]])) { matchB[EB[e]] = e; return 1; } } return 0; }
void colour(void) {
    memset(used, 0, sizeof used);
    for (int c = 0; c < 4; c++) {
        for (int j = 0; j < k; j++) matchB[j] = -1;
        for (int a = 0; a < k; a++) { memset(visB, 0, sizeof visB); if (!aug(a)) { printf("colouring failed\n"); exit(9); } }
        for (int j = 0; j < k; j++) { col[matchB[j]] = c; used[matchB[j]] = 1; }
    }
}
static int load_chart(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    for (int i = 0; i < 4; i++) { int e[16]; for (int t = 0; t < 16; t++) if (fscanf(f, "%d", &e[t]) != 1) return 0;
        for (int cc = 0; cc < 4; cc++) { int v = 0; for (int r = 0; r < 4; r++) v |= e[r * 4 + cc] << (2 * r); A[i].c[cc] = v; } }
    for (int i = 0; i < 4; i++) { int v = 0; for (int r = 0; r < 4; r++) { int x; if (fscanf(f, "%d", &x) != 1) return 0; v |= x << (2 * r); } b[i] = v; }
    fclose(f); return 1;
}
static void write_chart(const char *fn, mat *M, int *bv) {
    FILE *g = fopen(fn, "w");
    for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) for (int cc = 0; cc < 4; cc++) fprintf(g, "%d ", coord(M[i].c[cc], r)); fprintf(g, "\n"); }
    for (int i = 0; i < 4; i++) { for (int r = 0; r < 4; r++) fprintf(g, "%d ", coord(bv[i], r)); fprintf(g, "\n"); }
    fclose(g);
}
int main(int argc, char **argv) {
    if (argc < 5) { printf("usage: mlift_joint BASE TABLE seconds seed [T0] [PV] [out_prefix]\n"); return 1; }
    for (int l = 0; l < 4; l++) for (int v = 0; v < 256; v++) { int o = 0; for (int r = 0; r < 4; r++) o |= MUL[l][coord(v, r)] << (2 * r); smul[l][v] = o; }
    int np = 0; for (int i1 = 0; i1 < 4; i1++) for (int i2 = 0; i2 < 4; i2++) for (int i3 = 0; i3 < 4; i3++) for (int i4 = 0; i4 < 4; i4++)
        pidx[i1][i2][i3][i4] = (i1 != i2 && i2 != i3 && i3 != i4) ? np++ : -1;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &k) != 1) return 2;
    ne = 4 * k; for (int i = 0; i < ne; i++) if (fscanf(f, "%d %d", &EA[i], &EB[i]) != 2) return 3; fclose(f);
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &n) != 1) return 4;
    T = malloc(sizeof(int) * n * n); Inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) return 5; fclose(f);
    for (int i = 0; i < n; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e_id = i; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i * n + j] == e_id) Inv[i] = j;
    double secs = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
    double T0 = argc > 5 ? atof(argv[5]) : 2.0, PV = argc > 6 ? atof(argv[6]) : 0.8; const char *out = argc > 7 ? argv[7] : NULL;
    hit = malloc(k * n + 1);
    colour();
    int seen[64] = {0}, q[64], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    while (h < t) { int x = q[h++];
        for (int i = 0; i < ne; i++) { int a = EA[i], bb = k + EB[i], y = -1;
            if (x == a && !seen[bb]) y = bb; else if (x == bb && !seen[a]) y = a;
            if (y >= 0) { seen[y] = 1; q[t++] = y; istree[i] = 1; } } }
    if (t != 2 * k) { printf("base disconnected\n"); return 7; }
    for (int i = 0; i < k; i++) { nwA[i] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EA[e1] == i)
        for (int e2 = 0; e2 < ne; e2++) if (EB[e2] == EB[e1] && e2 != e1) {
            { int w = nwA[i]++; wA[i][w][0] = e1; wA[i][w][1] = e2; lenA[i][w] = 2; endA[i][w] = EA[e2]; keyA[i][w] = col[e1] * 4 + col[e2]; }
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EA[e3] == EA[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EB[e4] == EB[e3]) {
                int w = nwA[i]++; wA[i][w][0] = e1; wA[i][w][1] = e2; wA[i][w][2] = e3; wA[i][w][3] = e4; lenA[i][w] = 4; endA[i][w] = EA[e4];
                keyA[i][w] = pidx[col[e1]][col[e2]][col[e3]][col[e4]]; } } }
    for (int j = 0; j < k; j++) { nwB[j] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EB[e1] == j)
        for (int e2 = 0; e2 < ne; e2++) if (EA[e2] == EA[e1] && e2 != e1) {
            { int w = nwB[j]++; wB[j][w][0] = e1; wB[j][w][1] = e2; lenB[j][w] = 2; endB[j][w] = EB[e2]; keyB[j][w] = col[e1] * 4 + col[e2]; }
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EB[e3] == EB[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EA[e4] == EA[e3]) {
                int w = nwB[j]++; wB[j][w][0] = e1; wB[j][w][1] = e2; wB[j][w][2] = e3; wB[j][w][3] = e4; lenB[j][w] = 4; endB[j][w] = EB[e4];
                keyB[j][w] = pidx[col[e1]][col[e2]][col[e3]][col[e4]]; } } }
    /* initial state */
    for (int j = 0; j < 4; j++) A[0].c[j] = 1 << (2 * j);
    if (getenv("INIT_CHART")) { if (!load_chart(getenv("INIT_CHART"))) { printf("cannot read chart\n"); return 8; } }
    else { for (int i = 1; i < 4; i++) rand_gl(&A[i]); for (int i = 0; i < 4; i++) b[i] = rand_vec(); }
    if (!eval_chart()) { printf("chart not invertible\n"); return 8; }
    do { for (int i = 0; i < ne; i++) volt[i] = istree[i] ? e_id : (int)(xr() % n); } while (!parallel_ok());
    int free_e[64], nf = 0; for (int i = 0; i < ne; i++) if (!istree[i]) free_e[nf++] = i;
    int c = cost(), best = c, bv[64]; mat bA[4]; int bb[4]; memcpy(bv, volt, sizeof volt); memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b);
    clock_t t0 = clock(); long it = 0, nchart = 0;
    while (best > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        double fr = (double)(clock() - t0) / CLOCKS_PER_SEC / secs, TT = T0 * pow(0.02, fr);
        int c2;
        if ((double)(xr() % 1000000) / 1e6 < PV) {
            int ei = free_e[xr() % nf], old = volt[ei]; volt[ei] = xr() % n;
            if (!parallel_ok()) { volt[ei] = old; continue; }
            c2 = cost();
            if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) c = c2; else volt[ei] = old;
        } else {
            nchart++;
            mat sA[4]; int sb[4]; memcpy(sA, A, sizeof A); memcpy(sb, b, sizeof b);
            int mv_t = xr() % 3;
            if (mv_t == 0) { int kk = 1 + xr() % 3, cc = xr() % 4, row = xr() % 4;
                A[kk].c[cc] = (A[kk].c[cc] & ~(3 << (2 * row))) | ((int)(xr() % 4) << (2 * row)); }
            else if (mv_t == 1) { int kk = xr() % 4, row = xr() % 4; b[kk] = (b[kk] & ~(3 << (2 * row))) | ((int)(xr() % 4) << (2 * row)); }
            else b[xr() % 4] = rand_vec();
            if (!eval_chart()) { memcpy(A, sA, sizeof A); memcpy(b, sb, sizeof b); eval_chart(); continue; }
            c2 = cost();
            if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) c = c2;
            else { memcpy(A, sA, sizeof A); memcpy(b, sb, sizeof b); eval_chart(); }
        }
        if (c < best) { best = c; memcpy(bv, volt, sizeof volt); memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b); }
        if (it % 200000 == 0 && c > best + 20) { memcpy(volt, bv, sizeof volt); memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b); eval_chart(); c = best; }
    }
    memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b); eval_chart(); memcpy(volt, bv, sizeof volt);
    printf("k=%d n=%d m=%d best_cost=%d (recheck %d) chart_singular=%d chart_pencil_viol=%d iters=%ld chart_moves=%ld volt=",
           k, n, k * n, best, cost(), nsing, npen, it, nchart);
    for (int i = 0; i < ne; i++) printf("%d%c", bv[i], i + 1 < ne ? ',' : '\n');
    if (out && (best == 0 || getenv("WRITEBEST"))) {
        char fn[1024]; snprintf(fn, sizeof fn, "%s.edges", out); FILE *g = fopen(fn, "w");
        for (int i = 0; i < ne; i++) for (int x = 0; x < n; x++) fprintf(g, "%d %d %d\n", EA[i] * n + x, EB[i] * n + mul(bv[i], x), col[i]);
        fclose(g); snprintf(fn, sizeof fn, "%s.chart", out); write_chart(fn, bA, bb); }
    return 0;
}
