/* myanneal.c (squad card c6): mlift_ejoint.c with two changes; same usage, input and output.
   (a) incremental chart evaluation: a chart move on base edge e recomputes only the length-4 walk flags of the walks that
       pass through e (a walk's validity depends only on the letters of its own four edges) and the 72 pencil checks.
       A rejected move restores the saved flags instead of re-evaluating the whole chart.
   (b) targeted voltage moves (fraction TGT of the voltage moves, env, default 0.5): pick a random uncovered pair
       (orbit, endpoint, element), a random valid walk to that endpoint with a free edge, and set that edge's voltage to
       the unique value that makes the walk hit the element. Then the usual annealing accept/reject.
   usage: myanneal BASE TABLE seconds seed [T0] [PV] [out_prefix]     (same as mlift_ejoint)
   env: INIT_ECHART / INIT_CHART / INIT_VOLT as mlift_ejoint; TGT=fraction of targeted voltage moves; CHECK=1 compares the
   incremental state with a full evaluation every 20000 iterations (testing only).
   Output: the mlift_ejoint line, then one line with move statistics. out_prefix.edges / .echart as mlift_ejoint. */
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
static int nsing, npen;
static double PT = 0.5;
static void flag_walkA(int i, int w) { const int *E = wA[i][w]; int v[4];
    v[0] = mv(&Ai[E[1]], b[E[0]]); v[1] = cvec[E[1]]; v[2] = cvec[E[2]]; v[3] = mv(&Ai[E[2]], b[E[3]]);
    okA[i][w] = rank3(v, 4) == 4; }
static void flag_walkB(int j, int w) { const int *E = wB[j][w]; int v[4];
    v[0] = mv(&A[E[1]], cvec[E[0]]); v[1] = b[E[1]]; v[2] = b[E[2]]; v[3] = mv(&A[E[2]], cvec[E[3]]);
    okB[j][w] = rank3(v, 4) == 4; }
static void eval_pencils(void) {
    int z[16]; npen = 0;
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
}
static int eval_chart(void) {
    for (int e = 0; e < ne; e++) { if (!inv_mat(&A[e], &Ai[e]) || !b[e]) return 0; cvec[e] = mv(&Ai[e], b[e]); }
    nsing = 0;
    for (int i = 0; i < k; i++) for (int w = 0; w < nwA[i]; w++) if (lenA[i][w] == 4) { flag_walkA(i, w); nsing += !okA[i][w]; }
    for (int j = 0; j < k; j++) for (int w = 0; w < nwB[j]; w++) if (lenB[j][w] == 4) { flag_walkB(j, w); nsing += !okB[j][w]; }
    eval_pencils();
    return 1;
}
/* ---- (a) per-edge lists of the length-4 walks through each edge (walk id = (side*32 + orbit)*700 + walk) ---- */
#define WID(s, i, w) (((s) * 32 + (i)) * 700 + (w))
static int *wl[64], wln[64], maxwl;
static unsigned char *savef;
static inline void wid_decode(int id, int *s, int *i, int *w) { *s = id / (32 * 700); int r = id % (32 * 700); *i = r / 700; *w = r % 700; }
static void build_wl(void) {
    int cnt[64] = {0};
    for (int i = 0; i < k; i++) for (int w = 0; w < nwA[i]; w++) if (lenA[i][w] == 4) for (int t = 0; t < 4; t++) cnt[wA[i][w][t]]++;
    for (int j = 0; j < k; j++) for (int w = 0; w < nwB[j]; w++) if (lenB[j][w] == 4) for (int t = 0; t < 4; t++) cnt[wB[j][w][t]]++;
    maxwl = 1;
    for (int e = 0; e < ne; e++) { wl[e] = malloc(sizeof(int) * (cnt[e] + 1)); wln[e] = 0; if (cnt[e] > maxwl) maxwl = cnt[e]; }
    for (int i = 0; i < k; i++) for (int w = 0; w < nwA[i]; w++) if (lenA[i][w] == 4) for (int t = 0; t < 4; t++) { int e = wA[i][w][t]; wl[e][wln[e]++] = WID(0, i, w); }
    for (int j = 0; j < k; j++) for (int w = 0; w < nwB[j]; w++) if (lenB[j][w] == 4) for (int t = 0; t < 4; t++) { int e = wB[j][w][t]; wl[e][wln[e]++] = WID(1, j, w); }
    savef = malloc(maxwl + 1);
}
/* recompute the chart after A[e], b[e] changed; returns 0 (state possibly half-changed: caller restores) if A[e] singular or b[e]=0 */
static int inc_edge(int e) {
    if (!inv_mat(&A[e], &Ai[e]) || !b[e]) return 0;
    cvec[e] = mv(&Ai[e], b[e]);
    for (int t = 0; t < wln[e]; t++) { int s, i, w; wid_decode(wl[e][t], &s, &i, &w); if (s == 0) flag_walkA(i, w); else flag_walkB(i, w); }
    eval_pencils();
    return 1;
}
static mat sv_A, sv_Ai; static int sv_b, sv_cv;
static unsigned char svpA[64][64], svpB[64][64];
static void save_state(int e) {
    sv_A = A[e]; sv_Ai = Ai[e]; sv_b = b[e]; sv_cv = cvec[e];
    for (int t = 0; t < wln[e]; t++) { int s, i, w; wid_decode(wl[e][t], &s, &i, &w); savef[t] = s == 0 ? okA[i][w] : okB[i][w]; }
    memcpy(svpA, penA2, sizeof penA2); memcpy(svpB, penB2, sizeof penB2);
}
static void restore_state(int e) {
    A[e] = sv_A; Ai[e] = sv_Ai; b[e] = sv_b; cvec[e] = sv_cv;
    for (int t = 0; t < wln[e]; t++) { int s, i, w; wid_decode(wl[e][t], &s, &i, &w); if (s == 0) okA[i][w] = savef[t]; else okB[i][w] = savef[t]; }
    memcpy(penA2, svpA, sizeof penA2); memcpy(penB2, svpB, sizeof penB2);
}
static void rand_gl(mat *M) { mat R; do { for (int j = 0; j < 4; j++) M->c[j] = xr() % NV; } while (!inv_mat(M, &R)); }
static int rand_vec(void) { int v; do v = xr() % NV; while (!v); return v; }
static inline int mul(int a, int b2) { return T[a * n + b2]; }
unsigned char *hit;
int *candunc, candn, *curunc, curn;   /* uncovered pairs of the candidate / accepted state: code = (side*k+orbit)*k*n + element */
int cost(void) {
    int c = 0, KN = k * n; candn = 0;
    for (int i = 0; i < k; i++) {
        memset(hit, 0, KN);
        for (int w = 0; w < nwA[i]; w++) { int *E = wA[i][w], x;
            if (lenA[i][w] == 2) { if (!penA2[E[0]][E[1]]) continue; x = mul(Inv[volt[E[1]]], volt[E[0]]); if (endA[i][w] == i && x == e_id) continue; }
            else { if (!okA[i][w]) continue; x = mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]]))); }
            hit[endA[i][w] * n + x] = 1; }
        for (int t = 0; t < KN; t++) if (!hit[t]) { c++; candunc[candn++] = i * KN + t; }
    }
    for (int j = 0; j < k; j++) {
        memset(hit, 0, KN);
        for (int w = 0; w < nwB[j]; w++) { int *E = wB[j][w], x;
            if (lenB[j][w] == 2) { if (!penB2[E[0]][E[1]]) continue; x = mul(volt[E[1]], Inv[volt[E[0]]]); if (endB[j][w] == j && x == e_id) continue; }
            else { if (!okB[j][w]) continue; x = mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]]))); }
            hit[endB[j][w] * n + x] = 1; }
        for (int t = 0; t < KN; t++) if (!hit[t]) { c++; candunc[candn++] = (k + j) * KN + t; }
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
/* ---- (b) targeted voltage move ---- */
/* product of walk (side s, orbit i, walk w) under the current voltages, as in cost() */
static inline int walk_prod(int s, int i, int w) {
    if (s == 0) { const int *E = wA[i][w];
        if (lenA[i][w] == 2) return mul(Inv[volt[E[1]]], volt[E[0]]);
        return mul(Inv[volt[E[3]]], mul(volt[E[2]], mul(Inv[volt[E[1]]], volt[E[0]]))); }
    const int *E = wB[i][w];
    if (lenB[i][w] == 2) return mul(volt[E[1]], Inv[volt[E[0]]]);
    return mul(volt[E[3]], mul(Inv[volt[E[2]]], mul(volt[E[1]], Inv[volt[E[0]]])));
}
static int tgt_ei, tgt_old;
/* pick a random uncovered pair; try to find a valid walk to its endpoint with a free edge; set that edge's voltage so the
   walk hits the element (volt[tgt_ei] = new value, tgt_old = old value). Returns 0 if no candidate was found. */
static int tgt_move(void) {
    int KN = k * n;
    int pick = curunc[xr() % curn], t = pick % KN, q = pick / KN, s = q / k, i = q % k, j = t / n, x = t % n;
    int nw = s == 0 ? nwA[i] : nwB[i];
    for (int tries = 0; tries < 200; tries++) {
        int w = xr() % nw;
        int len = s == 0 ? lenA[i][w] : lenB[i][w], en = s == 0 ? endA[i][w] : endB[i][w];
        if (en != j) continue;
        const int *E = s == 0 ? wA[i][w] : wB[i][w];
        if (len == 2) { if (s == 0 ? !penA2[E[0]][E[1]] : !penB2[E[0]][E[1]]) continue; if (en == i && x == e_id) continue; }
        else if (!(s == 0 ? okA[i][w] : okB[i][w])) continue;
        int fp[4], nfp = 0; for (int p = 0; p < len; p++) if (!istree[E[p]]) fp[nfp++] = p;
        if (!nfp) continue;
        int ei = E[fp[xr() % nfp]], old = volt[ei], found = -1;
        for (int v = 0; v < n; v++) { volt[ei] = v; if (walk_prod(s, i, w) == x) { found = v; break; } }
        volt[ei] = old;
        if (found < 0 || found == old) continue;
        volt[ei] = found; tgt_ei = ei; tgt_old = old; return 1;
    }
    return 0;
}
/* ---- self-check (CHECK=1) ---- */
static void verify_state(void) {
    static unsigned char vA[32][700], vB[32][700], vpA[64][64], vpB[64][64];
    memcpy(vA, okA, sizeof okA); memcpy(vB, okB, sizeof okB); memcpy(vpA, penA2, sizeof penA2); memcpy(vpB, penB2, sizeof penB2);
    int c1 = cost();
    if (!eval_chart()) { printf("CHECK: full evaluation failed\n"); exit(4); }
    int c2 = cost(), bad = 0;
    for (int i = 0; i < k; i++) for (int w = 0; w < nwA[i]; w++) if (lenA[i][w] == 4 && okA[i][w] != vA[i][w]) bad++;
    for (int j = 0; j < k; j++) for (int w = 0; w < nwB[j]; w++) if (lenB[j][w] == 4 && okB[j][w] != vB[j][w]) bad++;
    for (int e = 0; e < ne; e++) for (int f = 0; f < ne; f++) if (penA2[e][f] != vpA[e][f] || penB2[e][f] != vpB[e][f]) bad++;
    if (bad || c1 != c2) { printf("CHECK FAILED bad=%d cost_incremental=%d cost_full=%d\n", bad, c1, c2); exit(5); }
}
int main(int argc, char **argv) {
    if (argc < 5) { printf("usage: myanneal BASE TABLE seconds seed [T0] [PV] [out_prefix]\n"); return 1; }
    init_f3();
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
    double T0 = argc > 5 ? atof(argv[5]) : 2.0, PV = argc > 6 ? atof(argv[6]) : 0.8; const char *out = argc > 7 ? argv[7] : NULL;
    if (getenv("TGT")) PT = atof(getenv("TGT"));
    int CHECK = getenv("CHECK") != NULL;
    hit = malloc(k * n + 1);
    candunc = malloc(sizeof(int) * (2 * k * k * n + 8)); curunc = malloc(sizeof(int) * (2 * k * k * n + 8));
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
    build_wl();
    /* initial state */
    if (getenv("INIT_ECHART")) { if (!load_echart(getenv("INIT_ECHART"))) { printf("cannot read echart\n"); return 8; } }
    else if (getenv("INIT_CHART")) { if (!load_colour_chart(getenv("INIT_CHART"))) { printf("cannot read chart\n"); return 8; } }
    else { for (int e = 0; e < ne; e++) { rand_gl(&A[e]); b[e] = rand_vec(); } }
    if (!eval_chart()) { printf("chart not invertible\n"); return 8; }
    if (getenv("INIT_VOLT")) { char *s = getenv("INIT_VOLT"); for (int i = 0; i < ne; i++) { volt[i] = atoi(s) % n; s = strchr(s, ','); if (!s) break; s++; } }
    else do { for (int i = 0; i < ne; i++) volt[i] = istree[i] ? e_id : (int)(xr() % n); } while (!parallel_ok());
    int free_e[64], nf = 0; for (int i = 0; i < ne; i++) if (!istree[i]) free_e[nf++] = i;
    int c = cost(), best = c, bv[64]; mat bA[64]; int bb[64];
    memcpy(bv, volt, sizeof volt); memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b);
    memcpy(curunc, candunc, sizeof(int) * candn); curn = candn;
    printf("start cost %d singular %d pencil_fail %d\n", c, nsing, npen); fflush(stdout);
    clock_t t0 = clock(); long it = 0, nchart = 0, ntgt = 0, ntgt_try = 0;
    while (best > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        it++;
        double fr = (double)(clock() - t0) / CLOCKS_PER_SEC / secs, TT = T0 * pow(0.02, fr);
        int c2;
        if ((double)(xr() % 1000000) / 1e6 < PV) {
            int ei, old, via_t = 0;
            if (curn > 0 && (double)(xr() % 1000000) / 1e6 < PT) { ntgt_try++; if (tgt_move()) { ei = tgt_ei; old = tgt_old; via_t = 1; } }
            if (!via_t) { ei = free_e[xr() % nf]; old = volt[ei]; volt[ei] = xr() % n; }
            if (!parallel_ok()) { volt[ei] = old; continue; }
            c2 = cost();
            if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) { c = c2; memcpy(curunc, candunc, sizeof(int) * candn); curn = candn; ntgt += via_t; }
            else volt[ei] = old;
        } else {
            nchart++;
            int e = xr() % ne; save_state(e);
            int mv_t = xr() % 3;
            if (mv_t == 0) { int cc = xr() % 4, row = xr() % 4; int v = A[e].c[cc], old = coord(v, row), nw = (old + 1 + xr() % 2) % 3; A[e].c[cc] = v + (nw - old) * P3[row]; }
            else if (mv_t == 1) { int row = xr() % 4; int v = b[e], old = coord(v, row), nw = (old + 1 + xr() % 2) % 3; b[e] = v + (nw - old) * P3[row]; }
            else b[e] = rand_vec();
            if (!inc_edge(e)) { restore_state(e); continue; }
            c2 = cost();
            if (c2 <= c || exp((c - c2) / TT) > (double)(xr() % 1000000) / 1e6) { c = c2; memcpy(curunc, candunc, sizeof(int) * candn); curn = candn; }
            else restore_state(e);
        }
        if (c < best) { best = c; memcpy(bv, volt, sizeof volt); memcpy(bA, A, sizeof A); memcpy(bb, b, sizeof b); }
        if (it % 200000 == 0 && c > best + 20) {
            memcpy(volt, bv, sizeof volt); memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b);
            eval_chart(); c = cost(); memcpy(curunc, candunc, sizeof(int) * candn); curn = candn; }
        if (CHECK && it % 20000 == 0) verify_state();
    }
    memcpy(A, bA, sizeof A); memcpy(b, bb, sizeof b); eval_chart(); memcpy(volt, bv, sizeof volt);
    printf("k=%d n=%d m=%d best_cost=%d (recheck %d) chart_singular=%d chart_pencil_viol=%d iters=%ld chart_moves=%ld volt=",
           k, n, k * n, best, cost(), nsing, npen, it, nchart);
    for (int i = 0; i < ne; i++) printf("%d%c", bv[i], i + 1 < ne ? ',' : '\n');
    printf("stats targeted_tried=%ld targeted_accepted=%ld\n", ntgt_try, ntgt);
    if (out && (best == 0 || getenv("WRITEBEST"))) {
        char fn[1024]; snprintf(fn, sizeof fn, "%s.edges", out); FILE *g = fopen(fn, "w");
        for (int i = 0; i < ne; i++) for (int x = 0; x < n; x++) fprintf(g, "%d %d %d\n", EA[i] * n + x, EB[i] * n + mul(bv[i], x), i);
        fclose(g); snprintf(fn, sizeof fn, "%s.echart", out); write_echart(fn, bA, bb); }
    return 0;
}
