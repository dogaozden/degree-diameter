/* localdes.c: local search for "full-coverage" compound designs on a generalized polygon (any polygon given as a
   line list), zero flag voltages, two matchings M_1, M_2 (points -> lines) with hop voltages a_1, a_2 : points -> Z_m.

   For a point x the sheets of its cost <= 2 "full images" are
     C(x) = {0} u {a_i(x)} u {-a_i(M_i^-1(L)) : L on x} u {a_i(x) - a_j(M_j^-1(M_i(x))) : i != j},
   for a line y
     C(y) = {0} u {-a_i(z_i)} u {a_i(P) : P on y} u {a_j(z_i) - a_i(z_i) : j != i},   z_i = M_i^-1(y).
   With zero flag voltages every such image covers its whole copy, so C(v) = Z_m for every vertex v implies that the
   Z_m-lift of I + M_1 + M_2 has diameter <= n + 2 (n = polygon diameter). Cost = sum over v of |Z_m \ C(v)|.
   |C(v)| <= 2q + 7, so m <= 2q + 7.

   Input polygon file: int32 q, N, L, then L*(q+1) int32 point ids (hexgen format; gq.py can write the same).
   Usage: localdes POLY m secs seed OUT.base     (writes a baselift base file: flags voltage 0, matchings with a_i)
   env: T0, T1 (temperatures), SWAP (fraction of matching-swap moves, default 0.3) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int q, q1, N, m;
static int *lp, *pl;           /* line -> points, point -> lines */
static int *M[2], *Mi[2], *a[2];
static int *miss;              /* per vertex: missing count (points 0..N-1, lines N..2N-1) */
static long cost;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }
static inline int md(int x) { x %= m; return x < 0 ? x + m : x; }

static int vmiss(int v) {
    static unsigned char seen[64]; memset(seen, 0, m); int cnt = 0;
#define ADD(x) do { int _c = md(x); if (!seen[_c]) { seen[_c] = 1; cnt++; } } while (0)
    ADD(0);
    if (v < N) {
        int x = v;
        for (int i = 0; i < 2; i++) ADD(a[i][x]);
        for (int j = 0; j < q1; j++) { int L = pl[x * q1 + j]; for (int i = 0; i < 2; i++) ADD(-a[i][Mi[i][L]]); }
        for (int i = 0; i < 2; i++) { int j = 1 - i; int z = Mi[j][M[i][x]]; ADD(a[i][x] - a[j][z]); }
    } else {
        int y = v - N;
        for (int i = 0; i < 2; i++) { int z = Mi[i][y]; ADD(-a[i][z]); ADD(a[1 - i][z] - a[i][z]); }
        for (int j = 0; j < q1; j++) { int P = lp[y * q1 + j]; for (int i = 0; i < 2; i++) ADD(a[i][P]); }
    }
    return m - cnt;
}
/* vertices whose C() depends on a_i(P) or M_i(P): collect into list */
static int affected(int P, int *out) {
    int n = 0;
    out[n++] = P;
    for (int i = 0; i < 2; i++) {
        int L = M[i][P];
        out[n++] = N + L;
        for (int j = 0; j < q1; j++) out[n++] = lp[L * q1 + j];          /* points on M_i(P) */
        int j2 = 1 - i; out[n++] = Mi[j2][L];                            /* x with M_j(x) = L (hop-hop) */
    }
    for (int j = 0; j < q1; j++) out[n++] = N + pl[P * q1 + j];          /* lines through P */
    return n;
}
static int mark[1 << 0];
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: localdes POLY m secs seed OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) return 1;
    q = h[0]; N = h[1]; q1 = q + 1;
    lp = malloc(sizeof(int) * (size_t)N * q1); pl = malloc(sizeof(int) * (size_t)N * q1);
    int32_t *tmp = malloc(4 * (size_t)N * q1); if (fread(tmp, 4, (size_t)N * q1, f) != (size_t)N * q1) return 1; fclose(f);
    int *cnt = calloc(N, sizeof(int));
    for (size_t i = 0; i < (size_t)N * q1; i++) lp[i] = tmp[i];
    for (int l = 0; l < N; l++) for (int j = 0; j < q1; j++) { int p = lp[l * q1 + j]; pl[p * q1 + cnt[p]++] = l; }
    m = atoi(argv[2]); double secs = atof(argv[3]);
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    if (m > 64) { fprintf(stderr, "m <= 64\n"); return 1; }
    double T0 = getenv("T0") ? atof(getenv("T0")) : 1.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    double swapf = getenv("SWAP") ? atof(getenv("SWAP")) : 0.3;
    for (int i = 0; i < 2; i++) {
        M[i] = malloc(sizeof(int) * N); Mi[i] = malloc(sizeof(int) * N); a[i] = malloc(sizeof(int) * N);
        for (int p = 0; p < N; p++) M[i][p] = p;
        for (int p = N - 1; p > 0; p--) { int r = rndi(p + 1), t = M[i][p]; M[i][p] = M[i][r]; M[i][r] = t; }
        for (int p = 0; p < N; p++) { Mi[i][M[i][p]] = p; a[i][p] = rndi(m); }
    }
    miss = malloc(sizeof(int) * 2 * N); cost = 0;
    for (int v = 0; v < 2 * N; v++) { miss[v] = vmiss(v); cost += miss[v]; }
    long best = cost; double t0 = now(), last = t0; long it = 0;
    int *aff = malloc(sizeof(int) * 8 * (q1 + 4)), *aff2 = aff + 4 * (q1 + 4);
    int *stamp = calloc(2 * N, sizeof(int)); int st = 0;
    fprintf(stderr, "q=%d N=%d m=%d start cost %ld\n", q, N, m, cost);
    while (cost > 0 && now() - t0 < secs) {
        double fr = (now() - t0) / secs, T = T0 * pow(T1 / T0, fr);
        int i = rndi(2), P = rndi(N), P2 = -1, old = 0, na, nb2 = 0;
        int sw = (rnd() % 1000) < swapf * 1000;
        if (sw) { P2 = rndi(N); if (P2 == P) continue; }
        na = affected(P, aff); if (sw) nb2 = affected(P2, aff2);
        /* old local cost over the union (dedupe with stamps) */
        st++; long oldc = 0;
        for (int k = 0; k < na; k++) { int v = aff[k]; if (stamp[v] != st) { stamp[v] = st; oldc += miss[v]; } }
        for (int k = 0; k < nb2; k++) { int v = aff2[k]; if (stamp[v] != st) { stamp[v] = st; oldc += miss[v]; } }
        if (sw) { int L1 = M[i][P], L2 = M[i][P2]; M[i][P] = L2; M[i][P2] = L1; Mi[i][L2] = P; Mi[i][L1] = P2; }
        else { old = a[i][P]; int nv = rndi(m); if (nv == old) continue; a[i][P] = nv; }
        /* new affected sets (after a swap they change) */
        int na2 = affected(P, aff + 0), nb3 = sw ? affected(P2, aff2) : 0;
        /* union of old and new sets: recompute all vertices in both old and new (old already stamped) */
        st++; long newc = 0; static int buf[4096]; int nbuf = 0;
        /* collect new sets */
        for (int k = 0; k < na2; k++) { int v = aff[k]; if (stamp[v] != st) { stamp[v] = st; buf[nbuf++] = v; } }
        for (int k = 0; k < nb3; k++) { int v = aff2[k]; if (stamp[v] != st) { stamp[v] = st; buf[nbuf++] = v; } }
        (void)na; (void)nb2;
        /* NOTE: for swaps the old and new affected sets can differ; recompute the old-set vertices too */
        static int ob[4096]; int nob = 0;
        if (sw) {
            /* old sets were computed before the swap into aff/aff2 but are overwritten; recompute them from scratch:
               undo, collect, redo */
            int L1 = M[i][P], L2 = M[i][P2]; M[i][P] = L2; M[i][P2] = L1; Mi[i][L2] = P; Mi[i][L1] = P2;
            static int t1[1024], t2[1024]; int n1 = affected(P, t1), n2 = affected(P2, t2);
            for (int k = 0; k < n1; k++) { int v = t1[k]; if (stamp[v] != st) { stamp[v] = st; ob[nob++] = v; } }
            for (int k = 0; k < n2; k++) { int v = t2[k]; if (stamp[v] != st) { stamp[v] = st; ob[nob++] = v; } }
            L1 = M[i][P]; L2 = M[i][P2]; M[i][P] = L2; M[i][P2] = L1; Mi[i][L2] = P; Mi[i][L1] = P2;
        }
        /* full set = buf u ob; old cost of the full set */
        long oc = 0;
        for (int k = 0; k < nbuf; k++) oc += miss[buf[k]];
        for (int k = 0; k < nob; k++) oc += miss[ob[k]];
        static int nm_[8192];
        for (int k = 0; k < nbuf; k++) { nm_[k] = vmiss(buf[k]); newc += nm_[k]; }
        for (int k = 0; k < nob; k++) { nm_[nbuf + k] = vmiss(ob[k]); newc += nm_[nbuf + k]; }
        (void)oldc;
        long d = newc - oc;
        it++;
        if (d <= 0 || (rnd() >> 11) * (1.0 / 9007199254740992.0) < exp(-d / T)) {
            for (int k = 0; k < nbuf; k++) miss[buf[k]] = nm_[k];
            for (int k = 0; k < nob; k++) miss[ob[k]] = nm_[nbuf + k];
            cost += d; if (cost < best) best = cost;
        } else {
            if (sw) { int L1 = M[i][P], L2 = M[i][P2]; M[i][P] = L2; M[i][P2] = L1; Mi[i][L2] = P; Mi[i][L1] = P2; }
            else a[i][P] = old;
        }
        if (now() - last > 10) { last = now(); fprintf(stderr, "t=%.0f it=%ld T=%.3f cost=%ld best=%ld\n", now() - t0, it, T, cost, best); }
    }
    /* sanity: recompute */
    long chk = 0; for (int v = 0; v < 2 * N; v++) chk += vmiss(v);
    fprintf(stderr, "end cost %ld (recomputed %ld) it=%ld\n", cost, chk, it);
    FILE *o = fopen(argv[5], "w");
    fprintf(o, "%d %d %d\n", 2 * N, m, N * q1 + 2 * N);
    for (int l = 0; l < N; l++) for (int j = 0; j < q1; j++) fprintf(o, "%d %d 0 0\n", lp[l * q1 + j], N + l);
    for (int i = 0; i < 2; i++) for (int p = 0; p < N; p++) fprintf(o, "%d %d %d %d\n", p, N + M[i][p], a[i][p], 100 + i);
    fclose(o);
    printf("RESULT q=%d m=%d localcost=%ld\n", q, m, chk);
    return 0;
}
