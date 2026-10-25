/* clhaarP.c: clhaar.c for any finite group given by generators as permutations (left multiplication), and it writes
   the hub layout itself.
   PGRP file (text): "N r e h nsub", then r lines of N ints (generator k as the permutation y -> g_k y), then nsub
   lines "c a_1 ... a_h" (a subgroup of order h as element indices, c a designated involution in it, or c = e for
   clusters without co-owner pairs, i.e. h <= 10 hubs on a line with one hub per point).
   Elements are reached from e by a BFS over the generators; x = g_k * parent(x), so x*y = g_k*(parent(x)*y).
   Search (as clhaar): Haar graph (g,A) ~ (s g, B), s in S, s_0 = e; at each of L levels the right cosets of a
   subgroup H_i (side A) and K_i (side B) are clusters (pairwise distance 4; co-owners {y, c y} distance 2). Cost =
   #{x : dA(x) > 6} + #{x : dB(x) > 6}, dA/dB the weighted distances from (e,A)/(e,B). Anneals over S and the H_i, K_i.
   At cost 0 it writes OUT (S, subgroup ids) and OUT.hubs3 (x5gen3 format; the cosets of level i go to spread lines
   0, 1, 2, ... in order of first appearance and the co-owner pairs to points 0..9 of the line: freed index 10*r + t).
   NLINES (env, default 730) caps the number of cosets.
   Usage: clhaarP PGRP d L seconds seed OUT */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
static int N, R, E0, hsz, nsub, d, L; static int **gp, **gpi; static int *par, *pgen;
static int *subc, *sube;
static int mulx(int x, int y) {   /* x = g_k1 g_k2 ... g_km (k1 = pgen[x]); x*y = g_k1(g_k2(...g_km(y))) */
    int stack[4096], ns = 0; while (x != E0) { stack[ns++] = pgen[x]; x = par[x]; }
    for (int k = ns - 1; k >= 0; k--) y = gp[stack[k]][y]; return y; }
static int invx(int x) {   /* x^-1 = g_km^-1 ... g_k1^-1: apply g_k1^-1 first */
    int y = E0; while (x != E0) { y = gpi[pgen[x]][y]; x = par[x]; } return y; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int S[64], SI[64], HA[8], HB[8]; static int *ltS, *ltSI; static unsigned char *dist; static int *bk[7], bn[7];
static void build_one(int j) { SI[j] = invx(S[j]); for (int y = 0; y < N; y++) { ltS[(long)j * N + y] = mulx(S[j], y); ltSI[(long)j * N + y] = mulx(SI[j], y); } }
static int run(int side0) {
    memset(dist, 255, 2 * N); for (int k = 0; k < 7; k++) bn[k] = 0;
    int s0 = side0 * N + E0; dist[s0] = 0; bk[0][bn[0]++] = s0;
    for (int dd = 0; dd <= 6; dd++) for (int t = 0; t < bn[dd]; t++) {
        int v = bk[dd][t]; if (dist[v] != dd) continue; int side = v >= N, y = v - side * N;
        if (dd < 6) for (int j = 0; j < d; j++) { int w = side ? ltSI[(long)j * N + y] : N + ltS[(long)j * N + y]; if (dist[w] > dd + 1) { dist[w] = dd + 1; bk[dd + 1][bn[dd + 1]++] = w; } }
        if (dd + 2 <= 6) for (int i = 0; i < L; i++) { int sg = side ? HB[i] : HA[i], c = subc[sg];
            if (dd + 4 <= 6) { for (int k = 0; k < hsz; k++) { int a = sube[sg * hsz + k]; if (a == E0) continue; int w = side * N + mulx(a, y); int nd = dd + (a == c ? 2 : 4); if (dist[w] > nd) { dist[w] = nd; bk[nd][bn[nd]++] = w; } } }
            else if (c != E0) { int w = side * N + mulx(c, y); if (dist[w] > dd + 2) { dist[w] = dd + 2; bk[dd + 2][bn[dd + 2]++] = w; } } }
    }
    int miss = 0; for (int y = 0; y < N; y++) if (dist[side0 * N + y] > 6) miss++; return miss;
}
static void layout(int sg, int *own, int nlines) {
    for (int y = 0; y < N; y++) own[y] = -1; int ncos = 0, c = subc[sg];
    for (int y = 0; y < N; y++) { if (own[y] >= 0) continue; if (ncos >= nlines) { fprintf(stderr, "too many cosets\n"); exit(1); }
        int t = 0; for (int k = 0; k < hsz; k++) { int x = mulx(sube[sg * hsz + k], y); if (own[x] >= 0) continue; own[x] = 10 * ncos + t; if (c != E0) { int x2 = mulx(c, x); own[x2] = 10 * ncos + t; } t++; }
        if (t > 10) { fprintf(stderr, "cluster needs %d points (> 10)\n", t); exit(1); } ncos++; }
}
int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: clhaarP PGRP d L seconds seed OUT\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); d = atoi(argv[2]); L = atoi(argv[3]); double secs = atof(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    if (!f || fscanf(f, "%d %d %d %d %d", &N, &R, &E0, &hsz, &nsub) != 5) return 1;
    gp = malloc(sizeof(int *) * R); gpi = malloc(sizeof(int *) * R);
    for (int k = 0; k < R; k++) { gp[k] = malloc(sizeof(int) * N); gpi[k] = malloc(sizeof(int) * N); for (int y = 0; y < N; y++) if (fscanf(f, "%d", &gp[k][y]) != 1) return 1; for (int y = 0; y < N; y++) gpi[k][gp[k][y]] = y; }
    subc = malloc(sizeof(int) * nsub); sube = malloc(sizeof(int) * nsub * hsz);
    for (int s = 0; s < nsub; s++) { if (fscanf(f, "%d", &subc[s]) != 1) return 1; for (int k = 0; k < hsz; k++) if (fscanf(f, "%d", &sube[s * hsz + k]) != 1) return 1; }
    fclose(f);
    par = malloc(sizeof(int) * N); pgen = malloc(sizeof(int) * N); for (int y = 0; y < N; y++) par[y] = -1;
    int *qu = malloc(sizeof(int) * N), qh = 0, qt = 0; par[E0] = E0; qu[qt++] = E0;
    while (qh < qt) { int x = qu[qh++]; for (int k = 0; k < R; k++) { int y = gp[k][x]; if (par[y] < 0) { par[y] = x; pgen[y] = k; qu[qt++] = y; } } }
    if (qt != N) { fprintf(stderr, "generators reach %d of %d elements\n", qt, N); return 1; }
    for (int s = 0; s < nsub; s++) { for (int k = 0; k < hsz; k++) for (int l = 0; l < hsz; l++) { int z = mulx(sube[s * hsz + k], sube[s * hsz + l]), ok = 0; for (int m = 0; m < hsz; m++) if (sube[s * hsz + m] == z) ok = 1; if (!ok) { fprintf(stderr, "subgroup %d not closed\n", s); return 1; } }
        if (subc[s] != E0 && mulx(subc[s], subc[s]) != E0) { fprintf(stderr, "subgroup %d: c is not an involution\n", s); return 1; } }
    fprintf(stderr, "N=%d generators=%d h=%d subgroups=%d (closed, involutions ok)\n", N, R, hsz, nsub);
    ltS = malloc(sizeof(int) * (long)d * N); ltSI = malloc(sizeof(int) * (long)d * N); dist = malloc(2 * N); for (int k = 0; k < 7; k++) bk[k] = malloc(sizeof(int) * 8 * N);
    S[0] = E0; for (int j = 1; j < d; j++) S[j] = rnd() % N; for (int j = 0; j < d; j++) build_one(j);
    for (int i = 0; i < L; i++) { HA[i] = rnd() % nsub; HB[i] = rnd() % nsub; }
    int c = run(0) + run(1), best = c; double Tm = 2.0; time_t t0 = time(NULL); long evals = 0;
    fprintf(stderr, "start cost=%d\n", c);
    while (c > 0 && difftime(time(NULL), t0) < secs) {
        int kind = rnd() % 10, j = 0, old = 0, oi = 0, side = 0;
        if (kind < 8) { j = 1 + rnd() % (d - 1); old = S[j]; S[j] = rnd() % N; build_one(j); }
        else { side = rnd() & 1; oi = rnd() % L; old = side ? HB[oi] : HA[oi]; if (side) HB[oi] = rnd() % nsub; else HA[oi] = rnd() % nsub; }
        int nc = run(0) + run(1); evals++;
        if (nc <= c || exp((c - nc) / Tm) > (rnd() % 1000000) / 1e6) { c = nc; if (c < best) { best = c; fprintf(stderr, "t=%.0f evals=%ld cost=%d\n", difftime(time(NULL), t0), evals, c); } }
        else { if (kind < 8) { S[j] = old; build_one(j); } else { if (side) HB[oi] = old; else HA[oi] = old; } }
        Tm *= 0.99995; if (Tm < 0.3) Tm = 2.0;
    }
    printf("RESULT N=%d best=%d final=%d evals=%ld time=%.0f\n", N, best, c, evals, difftime(time(NULL), t0));
    if (c != 0) return 0;
    FILE *o = fopen(argv[6], "w"); fprintf(o, "%d 0 %d %d\n", N, d, L); for (int j = 0; j < d; j++) fprintf(o, "%d ", S[j]); fprintf(o, "\n");
    for (int i = 0; i < L; i++) fprintf(o, "%d %d\n", HA[i], HB[i]); fclose(o);
    char fn[1024]; snprintf(fn, sizeof fn, "%s.hubs3", argv[6]); o = fopen(fn, "w");
    const char *nl = getenv("NLINES"); int nlines = nl ? atoi(nl) : 730;
    int *own = malloc(sizeof(int) * N * L * 2);
    for (int i = 0; i < L; i++) { layout(HA[i], own + (long)i * N, nlines); layout(HB[i], own + (long)(L + i) * N, nlines); }
    fprintf(o, "%d %d %ld\n", N, N, (long)N * d);
    for (int side = 0; side < 2; side++) for (int y = 0; y < N; y++) { for (int i = 0; i < L; i++) fprintf(o, "%d%c", own[(long)(side * L + i) * N + y], i + 1 < L ? ' ' : '\n'); }
    for (int y = 0; y < N; y++) for (int j = 0; j < d; j++) fprintf(o, "%d %d\n", y, ltS[(long)j * N + y]);
    fclose(o); printf("wrote %s and %s\n", argv[6], fn);
    return 0;
}
