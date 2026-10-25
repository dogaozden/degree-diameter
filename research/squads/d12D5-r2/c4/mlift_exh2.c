/* Per-edge chart version of mlift_joint3.c (cell-12-5, resumed session): every BASE edge e has its own letter
   (A_e, b_e) instead of one letter per colour, so a controller walk is singular iff its base projection is
   (conditions in echart.c / EDGECHART.md).  Joint annealing of voltages and the 4k letters.  Coverage criterion as in
   mlift_joint3.c: same-side controller pair (u, v) covered iff u != v and some length-2 path u-a-v has a complete
   pencil, or some nonbacktracking walk of length 4 from u to v is nonsingular.  Cost 0 => lift diameter <= 5.
   usage: mlift_ejoint BASE TABLE seconds seed [T0] [PV] [out_prefix]
   env INIT_CHART=colour chart (chart3 format) or INIT_ECHART=per-edge chart (echart format) as start;
   env INIT_VOLT=v0,v1,... start voltages.  out_prefix.edges: "a b e" (e = base edge, A-vertex (a_i, g) -> i*n+g,
   B-vertex (b_j, h) -> j*n+h); out_prefix.echart: per base edge 16 entries of A_e row-major then b_e. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <stdint.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
/* ---- F_3^4 chart (arithmetic from chart3.c) ---- */
#define NV 81
static int ADD[NV][NV], SMUL[3][NV], P3[4] = {1, 3, 9, 27};
typedef struct { int c[4]; } mat;
static inline int coord(int v, int r) { return (v / P3[r]) % 3; }
static inline int mv(const mat *M, int v) { int o = 0; for (int j = 0; j < 4; j++) o = ADD[o][SMUL[coord(v, j)][M->c[j]]]; return o; }
static int rank3(const int *v, int n) {
    int a[16]; memcpy(a, v, n * sizeof(int)); int r = 0;
    for (int col = 0; col < 4 && r < n; col++) {
        int p = -1; for (int i = r; i < n; i++) if (coord(a[i], col)) { p = i; break; }
        if (p < 0) continue;
        int t = a[p]; a[p] = a[r]; a[r] = t;
        if (coord(a[r], col) == 2) a[r] = SMUL[2][a[r]];
        for (int i = 0; i < n; i++) if (i != r && coord(a[i], col)) a[i] = ADD[a[i]][SMUL[3 - coord(a[i], col)][a[r]]];
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
        if (X[col][col] == 2) for (int c = 0; c < 8; c++) X[col][c] = (2 * X[col][c]) % 3;
        for (int r = 0; r < 4; r++) if (r != col && X[r][col]) { int f = X[r][col]; for (int c = 0; c < 8; c++) X[r][c] = (X[r][c] + 9 - f * X[col][c]) % 3; }
    }
    for (int c = 0; c < 4; c++) { int v = 0; for (int r = 0; r < 4; r++) v += X[r][4 + c] * P3[r]; R->c[c] = v; }
    return 1;
}
static int span2[NV][NV]; static uint64_t spm[130][2]; static signed char hyp[130][NV];
static void setbit(uint64_t *m, int v) { m[v >> 6] |= 1ULL << (v & 63); }
static int getbit(const uint64_t *m, int v) { return (m[v >> 6] >> (v & 63)) & 1; }
static void init_f3(void) {
    int nsp = 0;
    for (int u = 0; u < NV; u++) for (int v = 0; v < NV; v++) { int w = 0; for (int r = 0; r < 4; r++) w += ((coord(u, r) + coord(v, r)) % 3) * P3[r]; ADD[u][v] = w; }
    for (int l = 0; l < 3; l++) for (int v = 0; v < NV; v++) { int w = 0; for (int r = 0; r < 4; r++) w += ((l * coord(v, r)) % 3) * P3[r]; SMUL[l][v] = w; }
    for (int u = 0; u < NV; u++) for (int v = 0; v < NV; v++) {
        int pr[2] = {u, v}; if (rank3(pr, 2) < 2) { span2[u][v] = -1; continue; }
        uint64_t m[2] = {0, 0}; for (int a = 0; a < 3; a++) for (int b2 = 0; b2 < 3; b2++) setbit(m, ADD[SMUL[a][u]][SMUL[b2][v]]);
        int id = -1; for (int s = 0; s < nsp; s++) if (spm[s][0] == m[0] && spm[s][1] == m[1]) { id = s; break; }
        if (id < 0) { id = nsp++; spm[id][0] = m[0]; spm[id][1] = m[1]; }
        span2[u][v] = id;
    }
    for (int s = 0; s < nsp; s++) {
        int nh = 0; uint64_t H[4][2]; int base[2] = {-1, -1};
        for (int v = 1; v < NV && base[1] < 0; v++) if (getbit(spm[s], v)) { if (base[0] < 0) base[0] = v; else { int pr[2] = {base[0], v}; if (rank3(pr, 2) == 2) base[1] = v; } }
        for (int z = 0; z < NV; z++) {
            if (getbit(spm[s], z)) { hyp[s][z] = -1; continue; }
            int h = -1; for (int t = 0; t < nh; t++) if (getbit(H[t], z)) { h = t; break; }
            if (h < 0) { h = nh++; H[h][0] = H[h][1] = 0;
                for (int a = 0; a < 3; a++) for (int b2 = 0; b2 < 3; b2++) for (int c = 0; c < 3; c++) setbit(H[h], ADD[ADD[SMUL[a][base[0]]][SMUL[b2][base[1]]]][SMUL[c][z]]); }
            hyp[s][z] = h;
        }
    }
}
static int pencil_ok(int w1, int w2, const int *z, int nz) {
    int s = span2[w1][w2]; if (s < 0) return 0;
    int seen = 0; for (int i = 0; i < nz; i++) { int h = hyp[s][z[i]]; if (h >= 0) seen |= 1 << h; }
    return seen == 15;
}
/* ---- base and per-edge chart ---- */
int k, ne, EA[64], EB[64], col[64], n, *T, *Inv, e_id, istree[64], volt[64];
int atA[32][4], atB[32][4];
static mat A[64], Ai[64]; static int b[64], cvec[64];
/* walk lists per source orbit: len, edges, end orbit */
int nwA[32], wA[32][700][4], lenA[32][700], endA[32][700];
int nwB[32], wB[32][700][4], lenB[32][700], endB[32][700];
static unsigned char okA[32][700], okB[32][700], penA2[64][64], penB2[64][64];
static int nsing, npen, ndiag, DIAGBT = 0, FAKE = 0; static unsigned char diagA[32], diagB[32];
/* union of the 2-spaces <p_i, q_i> covers all of F_3^4? */
static int missA[32], missB[32], DGRAD = 0, PRUNC = 0;
static int planes_miss(const int *p, const int *q, int np) {   /* points of F_3^4 NOT in the union of the planes */
    uint64_t m[2] = {1, 0};
    for (int i = 0; i < np; i++) for (int a = 0; a < 3; a++) for (int c = 0; c < 3; c++) setbit(m, ADD[SMUL[a][p[i]]][SMUL[c][q[i]]]);
    return 81 - __builtin_popcountll(m[0]) - __builtin_popcountll(m[1]);
}
static int eval_chart(void) {
    for (int e = 0; e < ne; e++) { if (!inv_mat(&A[e], &Ai[e]) || !b[e]) return 0; cvec[e] = mv(&Ai[e], b[e]); }
    int v[4], z[16]; nsing = 0; npen = 0;
    for (int i = 0; i < k; i++) for (int w = 0; w < nwA[i]; w++) if (lenA[i][w] == 4) { int *E = wA[i][w];
        v[0] = mv(&Ai[E[1]], b[E[0]]); v[1] = cvec[E[1]]; v[2] = cvec[E[2]]; v[3] = mv(&Ai[E[2]], b[E[3]]);
        okA[i][w] = rank3(v, 4) == 4; nsing += !okA[i][w]; }
    for (int j = 0; j < k; j++) for (int w = 0; w < nwB[j]; w++) if (lenB[j][w] == 4) { int *E = wB[j][w];
        v[0] = mv(&A[E[1]], cvec[E[0]]); v[1] = b[E[1]]; v[2] = b[E[2]]; v[3] = mv(&A[E[2]], cvec[E[3]]);
        okB[j][w] = rank3(v, 4) == 4; nsing += !okB[j][w]; }
    for (int a = 0; a < k; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) if (x != y) {
        int e = atB[a][x], f = atB[a][y], u = EA[e], vv = EA[f], nz = 0;
        for (int t = 0; t < 4; t++) { int kk = atA[u][t]; if (kk != e) z[nz++] = mv(&A[e], cvec[kk]); }
        for (int t = 0; t < 4; t++) { int l = atB[a][t]; if (l != e && l != f) z[nz++] = b[l]; }
        for (int t = 0; t < 4; t++) { int kk = atA[vv][t]; if (kk != f) z[nz++] = mv(&A[f], cvec[kk]); }
        penA2[e][f] = pencil_ok(b[e], b[f], z, nz); if (x < y) npen += !penA2[e][f];
    }
    for (int a = 0; a < k; a++) for (int x = 0; x < 4; x++) for (int y = 0; y < 4; y++) if (x != y) {
        int e = atA[a][x], f = atA[a][y], u = EB[e], vv = EB[f], nz = 0;
        for (int t = 0; t < 4; t++) { int kk = atB[u][t]; if (kk != e) z[nz++] = mv(&Ai[e], b[kk]); }
        for (int t = 0; t < 4; t++) { int l = atA[a][t]; if (l != e && l != f) z[nz++] = cvec[l]; }
        for (int t = 0; t < 4; t++) { int kk = atB[vv][t]; if (kk != f) z[nz++] = mv(&Ai[f], b[kk]); }
        penB2[e][f] = pencil_ok(cvec[e], cvec[f], z, nz); if (x < y) npen += !penB2[e][f];
    }
    /* diagonal pairs through closed BACKTRACKING walks of length <= 4 (EDGECHART.md): A-vertex y reaches
       x + <c_e, c_f> (e, f at y) and x + <c_e, A_e^-1 b_l> (l != e at the B-end of e); B-vertex w reaches
       x + <b_e, b_f> and x + <b_e, A_e c_l> (l != e at the A-end of e). */
    ndiag = 0;
    for (int y = 0; y < k; y++) { int P[64], Q[64], np = 0;
        for (int x = 0; x < 4; x++) { int e = atA[y][x];
            for (int x2 = x + 1; x2 < 4; x2++) { P[np] = cvec[e]; Q[np++] = cvec[atA[y][x2]]; }
            for (int t = 0; t < 4; t++) { int l = atB[EB[e]][t]; if (l != e) { P[np] = cvec[e]; Q[np++] = mv(&Ai[e], b[l]); } } }
        missA[y] = planes_miss(P, Q, np); diagA[y] = !missA[y]; ndiag += !diagA[y]; }
    for (int w = 0; w < k; w++) { int P[64], Q[64], np = 0;
        for (int x = 0; x < 4; x++) { int e = atB[w][x];
            for (int x2 = x + 1; x2 < 4; x2++) { P[np] = b[e]; Q[np++] = b[atB[w][x2]]; }
            for (int t = 0; t < 4; t++) { int l = atA[EA[e]][t]; if (l != e) { P[np] = b[e]; Q[np++] = mv(&A[e], cvec[l]); } } }
        missB[w] = planes_miss(P, Q, np); diagB[w] = !missB[w]; ndiag += !diagB[w]; }
    if (FAKE) { memset(okA, 1, sizeof okA); memset(okB, 1, sizeof okB); memset(penA2, 1, sizeof penA2); memset(penB2, 1, sizeof penB2);
        memset(diagA, 1, sizeof diagA); memset(diagB, 1, sizeof diagB); }
    return 1;
}
static void rand_gl(mat *M) { mat R; do { for (int j = 0; j < 4; j++) M->c[j] = xr() % NV; } while (!inv_mat(M, &R)); }
static int rand_vec(void) { int v; do v = xr() % NV; while (!v); return v; }
static inline int mul(int a, int b2) { return T[a * n + b2]; }
unsigned char *hit;
int cost_g = 0;   /* graded part of the last cost() */
int cost(void) {
    int c = 0, cg = 0;
    for (int i = 0; i < k; i++) {
        memset(hit, 0, k * n);
        for (int w = 0; w < nwA[i]; w++) { int *E = wA[i][w], x;
            if (lenA[i][w] == 2) { if (!penA2[E[0]][E[1]]) continue; x = mul(Inv[volt[E[1]]], volt[E[0]]); if (endA[i][w] == i && x == e_id) continue; }
            else { if (!okA[i][w]) continue; x = mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]]))); }
            hit[endA[i][w] * n + x] = 1; }
        if (DIAGBT && diagA[i]) hit[i * n + e_id] = 1;
        for (int t = 0; t < k * n; t++) c += !hit[t];
        if (PRUNC) for (int t = 0; t < k * n; t++) if (!hit[t]) printf("UNCOV A a%d -> a%d g%d%s\n", i, t / n, t % n, (t / n == i && t % n == e_id) ? " DIAG" : "");
        if (DGRAD && !hit[i * n + e_id]) cg += missA[i];
    }
    for (int j = 0; j < k; j++) {
        memset(hit, 0, k * n);
        for (int w = 0; w < nwB[j]; w++) { int *E = wB[j][w], x;
            if (lenB[j][w] == 2) { if (!penB2[E[0]][E[1]]) continue; x = mul(volt[E[1]], Inv[volt[E[0]]]); if (endB[j][w] == j && x == e_id) continue; }
            else { if (!okB[j][w]) continue; x = mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]]))); }
            hit[endB[j][w] * n + x] = 1; }
        if (DIAGBT && diagB[j]) hit[j * n + e_id] = 1;
        for (int t = 0; t < k * n; t++) c += !hit[t];
        if (PRUNC) for (int t = 0; t < k * n; t++) if (!hit[t]) printf("UNCOV B b%d -> b%d g%d%s\n", j, t / n, t % n, (t / n == j && t % n == e_id) ? " DIAG" : "");
        if (DGRAD && !hit[j * n + e_id]) cg += missB[j];
    }
    cost_g = cg;
    return DGRAD ? 100 * c + cg : c;
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
static int read_mat_vec(FILE *f, mat *M, int *bv) {
    int e[16]; for (int t = 0; t < 16; t++) if (fscanf(f, "%d", &e[t]) != 1) return 0;
    for (int cc = 0; cc < 4; cc++) { int v = 0; for (int r = 0; r < 4; r++) v += (e[r * 4 + cc] % 3) * P3[r]; M->c[cc] = v; }
    if (bv) { int v = 0; for (int r = 0; r < 4; r++) { int x; if (fscanf(f, "%d", &x) != 1) return 0; v += (x % 3) * P3[r]; } *bv = v; }
    return 1;
}
static int load_colour_chart(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0; mat CA[4]; int cb[4];
    for (int i = 0; i < 4; i++) if (!read_mat_vec(f, &CA[i], NULL)) return 0;
    for (int i = 0; i < 4; i++) { int v = 0; for (int r = 0; r < 4; r++) { int x; if (fscanf(f, "%d", &x) != 1) return 0; v += (x % 3) * P3[r]; } cb[i] = v; }
    fclose(f); for (int e = 0; e < ne; e++) { A[e] = CA[col[e]]; b[e] = cb[col[e]]; } return 1;
}
static int load_echart(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) return 0;
    for (int e = 0; e < ne; e++) if (!read_mat_vec(f, &A[e], &b[e])) return 0;
    fclose(f); return 1;
}
static void write_echart(const char *fn, mat *M, int *bv) {
    FILE *g = fopen(fn, "w");
    for (int e = 0; e < ne; e++) { for (int r = 0; r < 4; r++) for (int cc = 0; cc < 4; cc++) fprintf(g, "%d ", coord(M[e].c[cc], r));
        for (int r = 0; r < 4; r++) fprintf(g, "%d%c", coord(bv[e], r), r < 3 ? ' ' : '\n'); }
    fclose(g);
}
int main(int argc, char **argv) {
    if (argc < 5) { printf("usage: mlift_ejoint BASE TABLE seconds seed [T0] [PV] [out_prefix]\n"); return 1; }
    init_f3(); DIAGBT = getenv("DIAGBT") ? atoi(getenv("DIAGBT")) : 0; DGRAD = getenv("DGRAD") ? atoi(getenv("DGRAD")) : 0; if (DGRAD) DIAGBT = 1; FAKE = getenv("FAKE") ? atoi(getenv("FAKE")) : 0;
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &k) != 1) return 2;
    ne = 4 * k; int dA[32] = {0}, dB[32] = {0};
    for (int i = 0; i < ne; i++) { if (fscanf(f, "%d %d", &EA[i], &EB[i]) != 2) return 3; atA[EA[i]][dA[EA[i]]++] = i; atB[EB[i]][dB[EB[i]]++] = i; }
    fclose(f);
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &n) != 1) return 4;
    T = malloc(sizeof(int) * n * n); Inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) if (fscanf(f, "%d", &T[i]) != 1) return 5; fclose(f);
    for (int i = 0; i < n; i++) { int ok = 1; for (int j = 0; j < n; j++) if (T[i * n + j] != j) { ok = 0; break; } if (ok) e_id = i; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) if (T[i * n + j] == e_id) Inv[i] = j;
    double secs = atof(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL;
    double T0 = (argc > 5 ? atof(argv[5]) : 2.0) * (getenv("DGRAD") && atoi(getenv("DGRAD")) ? 100 : 1), PV = argc > 6 ? atof(argv[6]) : 0.8; const char *out = argc > 7 ? argv[7] : NULL;
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
            { int w = nwA[i]++; wA[i][w][0] = e1; wA[i][w][1] = e2; lenA[i][w] = 2; endA[i][w] = EA[e2]; }
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EA[e3] == EA[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EB[e4] == EB[e3]) {
                int w = nwA[i]++; wA[i][w][0] = e1; wA[i][w][1] = e2; wA[i][w][2] = e3; wA[i][w][3] = e4; lenA[i][w] = 4; endA[i][w] = EA[e4]; } } }
    for (int j = 0; j < k; j++) { nwB[j] = 0;
        for (int e1 = 0; e1 < ne; e1++) if (EB[e1] == j)
        for (int e2 = 0; e2 < ne; e2++) if (EA[e2] == EA[e1] && e2 != e1) {
            { int w = nwB[j]++; wB[j][w][0] = e1; wB[j][w][1] = e2; lenB[j][w] = 2; endB[j][w] = EB[e2]; }
            for (int e3 = 0; e3 < ne; e3++) if (e3 != e2 && EB[e3] == EB[e2])
            for (int e4 = 0; e4 < ne; e4++) if (e4 != e3 && EA[e4] == EA[e3]) {
                int w = nwB[j]++; wB[j][w][0] = e1; wB[j][w][1] = e2; wB[j][w][2] = e3; wB[j][w][3] = e4; lenB[j][w] = 4; endB[j][w] = EB[e4]; } } }
    /* initial state */
    if (getenv("INIT_ECHART")) { if (!load_echart(getenv("INIT_ECHART"))) { printf("cannot read echart\n"); return 8; } }
    else if (getenv("INIT_CHART")) { if (!load_colour_chart(getenv("INIT_CHART"))) { printf("cannot read chart\n"); return 8; } }
    else { for (int e = 0; e < ne; e++) { rand_gl(&A[e]); b[e] = rand_vec(); } }
    if (!eval_chart()) { printf("chart not invertible\n"); return 8; }
    if (getenv("EXH")) {   /* c4 addition: exhaustive over the free voltages (k = 1: three free edges), exact min for this chart */
        int fr[64], nf2 = 0; for (int i = 0; i < ne; i++) { if (istree[i]) volt[i] = e_id; else fr[nf2++] = i; }
        if (nf2 != 3) { printf("EXH needs exactly 3 free edges\n"); return 9; }
        int bestc = 1 << 30, bcnt = 0, bvv[64]; long tot = 0;
        for (int x0 = 0; x0 < n; x0++) for (int x1 = 0; x1 < n; x1++) for (int x2 = 0; x2 < n; x2++) {
            volt[fr[0]] = x0; volt[fr[1]] = x1; volt[fr[2]] = x2;
            if (!getenv("NOPAR") && !parallel_ok()) continue;   /* c4: NOPAR=1 allows equal voltages on parallel edges (multigraph controller) */
            int cc = cost(); tot++;
            if (cc < bestc) { bestc = cc; bcnt = 1; memcpy(bvv, volt, sizeof volt); }
            else if (cc == bestc) bcnt++;
        }
        memcpy(volt, bvv, sizeof volt);
        printf("EXH n=%d m=%d FAKE=%d DIAGBT=%d tuples=%ld min_cost=%d count_at_min=%d volt=", n, k * n, FAKE, DIAGBT, tot, bestc, bcnt);
        for (int i = 0; i < ne; i++) printf("%d%c", bvv[i], i + 1 < ne ? ',' : '\n');
        if (out && (bestc == 0 || getenv("WRITEBEST"))) {
            char fn[1024]; snprintf(fn, sizeof fn, "%s.edges", out); FILE *g = fopen(fn, "w");
            for (int i = 0; i < ne; i++) for (int x = 0; x < n; x++) fprintf(g, "%d %d %d\n", EA[i] * n + x, EB[i] * n + mul(bvv[i], x), i);
            fclose(g); snprintf(fn, sizeof fn, "%s.echart", out); write_echart(fn, A, b); }
        return 0;
    }
    if (getenv("INIT_VOLT")) { char *s = getenv("INIT_VOLT"); for (int i = 0; i < ne; i++) { volt[i] = atoi(s) % n; s = strchr(s, ','); if (!s) break; s++; } }
    else do { for (int i = 0; i < ne; i++) volt[i] = istree[i] ? e_id : (int)(xr() % n); } while (!parallel_ok());
    int free_e[64], nf = 0; for (int i = 0; i < ne; i++) if (!istree[i]) free_e[nf++] = i;
    int c = cost(), best = c, bv[64]; mat bA[64]; int bb[64]; memcpy(bv, volt, sizeof volt); memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b);
    printf("start cost %d singular %d pencil_fail %d diag_incomplete %d\n", c, nsing, npen, ndiag); fflush(stdout);
    clock_t t0 = clock(); long it = 0, nchart = 0;
    while (best > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        double fr = (double)(clock() - t0) / CLOCKS_PER_SEC / secs, TT = T0 * pow(0.02, fr);
        int c2;
        if (FAKE || (double)(xr() % 1000000) / 1e6 < PV) {
            int ei = free_e[xr() % nf], old = volt[ei]; volt[ei] = xr() % n;
            if (!parallel_ok()) { volt[ei] = old; continue; }
            c2 = cost();
            if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) c = c2; else volt[ei] = old;
        } else {
            nchart++;
            int e = xr() % ne; mat sA = A[e]; int sb = b[e];
            int mv_t = xr() % 3;
            if (mv_t == 0) { int cc = xr() % 4, row = xr() % 4; int v = A[e].c[cc], old = coord(v, row), nw = (old + 1 + xr() % 2) % 3; A[e].c[cc] = v + (nw - old) * P3[row]; }
            else if (mv_t == 1) { int row = xr() % 4; int v = b[e], old = coord(v, row), nw = (old + 1 + xr() % 2) % 3; b[e] = v + (nw - old) * P3[row]; }
            else b[e] = rand_vec();
            if (!eval_chart()) { A[e] = sA; b[e] = sb; eval_chart(); continue; }
            c2 = cost();
            if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) c = c2;
            else { A[e] = sA; b[e] = sb; eval_chart(); }
        }
        if (c < best) { best = c; memcpy(bv, volt, sizeof volt); memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b); }
        if (it % 200000 == 0 && c > best + 20 * (DGRAD ? 100 : 1)) { memcpy(volt, bv, sizeof volt); memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b); eval_chart(); c = best; }
    }
    memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b); eval_chart(); memcpy(volt, bv, sizeof volt);
    if (getenv("PRUNC")) { PRUNC = 1; cost(); PRUNC = 0; }
    printf("k=%d n=%d m=%d best_cost=%d (recheck %d) chart_singular=%d chart_pencil_viol=%d diag_incomplete=%d iters=%ld chart_moves=%ld volt=",
           k, n, k * n, best, cost(), nsing, npen, ndiag, it, nchart);
    for (int i = 0; i < ne; i++) printf("%d%c", bv[i], i + 1 < ne ? ',' : '\n');
    if (out && (best == 0 || getenv("WRITEBEST"))) {
        char fn[1024]; snprintf(fn, sizeof fn, "%s.edges", out); FILE *g = fopen(fn, "w");
        for (int i = 0; i < ne; i++) for (int x = 0; x < n; x++) fprintf(g, "%d %d %d\n", EA[i] * n + x, EB[i] * n + mul(bv[i], x), i);
        fclose(g); snprintf(fn, sizeof fn, "%s.echart", out); write_echart(fn, bA, bb); }
    return 0;
}
