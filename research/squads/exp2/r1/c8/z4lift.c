/* z4lift.c: exp2-squad round 1, card c8. Feasibility test for FOUR copies of H(q) at Delta = q+2, D = 7.
   Graph: vertices (v,i), v a point or line of H(q), i in Z_4; NV = 8N (q = 5: N = 3906, NV = 31,248).
     hexagon edges : (p,i) ~ (l, i + b[p,l])     for every incidence p on l, b in Z_4 (one voltage per incidence)
     matching edges: (p,i) ~ (M(p), i + a(p))    M: points -> lines bijection, a(p) in {1,2,3}
   Degree 7 = 6 + 1. The level shift (v,i) -> (v,i+c) is an automorphism, so BFS from level 0 suffices.
   Cost = sum over a fixed sample of 20 level-0 sources of #vertices at distance > 7, plus 1000 per double edge.
   Local search: one random move per step (a(p), b(e), or swap of M(p1), M(p2)); accept if cost does not increase.
   Usage: z4lift HEXBIN SEED LS_SECONDS
   Writes z4_final.cfg (M, a, b of the final state) and, only if every level-0 source reaches all vertices within 7
   and there are no double edges, z4_edges.txt (edge list for apsp). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1, NS, NV;        /* NS = 2N vertices per level, NV = 4 NS */
static int32_t *LP, *PL, *PLi;      /* LP[l*Q1+k]: point on line l; PL[p*Q1+j]: line through p;
                                       PLi[p*Q1+j] = l*Q1+k, the incidence id of (p, PL[p*Q1+j]) */
static int *M, *Minv, *A;           /* M: point -> line; Minv: line -> point; A[p] in {1,2,3} */
static uint8_t *Bv;                 /* Bv[l*Q1+k] in Z_4: voltage of the hexagon edge (LP[l*Q1+k], l) */
static int *adj;                    /* adj[7*v + t] */
static uint8_t *dist;
static int *que;
static int nsrc, *srcs;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + 1e-9 * ts.tv_nsec; }

/* vertex ids: point (p,i) = i*NS + p ; line (l,i) = i*NS + N + l */
static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(1); }
    int32_t hdr[3];
    if (fread(hdr, 4, 3, f) != 3) exit(1);
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    if (hdr[2] != N) { fprintf(stderr, "points != lines\n"); exit(1); }
    LP = malloc(4 * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1);
    fclose(f);
    PL = malloc(4 * (size_t)N * Q1); PLi = malloc(4 * (size_t)N * Q1);
    int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) {
        int p = LP[l * Q1 + k];
        PL[p * Q1 + cnt[p]] = l; PLi[p * Q1 + cnt[p]] = l * Q1 + k; cnt[p]++;
    }
    for (int p = 0; p < N; p++) if (cnt[p] != Q1) { fprintf(stderr, "point %d on %d lines\n", p, cnt[p]); exit(1); }
    free(cnt);
    NS = 2 * N; NV = 4 * NS;
}

static void build_adj(void) {
    for (int i = 0; i < 4; i++) for (int p = 0; p < N; p++) {
        int *out = adj + 7 * (size_t)(i * NS + p); int c = 0;
        for (int j = 0; j < Q1; j++) out[c++] = ((i + Bv[PLi[p * Q1 + j]]) & 3) * NS + N + PL[p * Q1 + j];
        out[c++] = ((i + A[p]) & 3) * NS + N + M[p];
    }
    for (int i = 0; i < 4; i++) for (int l = 0; l < N; l++) {
        int *out = adj + 7 * (size_t)(i * NS + N + l); int c = 0;
        for (int k = 0; k < Q1; k++) out[c++] = ((i + 4 - Bv[l * Q1 + k]) & 3) * NS + LP[l * Q1 + k];
        int p = Minv[l];
        out[c++] = ((i + 4 - A[p]) & 3) * NS + p;
    }
}

static int check_symmetric(void) {
    for (int v = 0; v < NV; v++) for (int k = 0; k < 7; k++) {
        int w = adj[7 * (size_t)v + k], found = 0;
        for (int t = 0; t < 7; t++) if (adj[7 * (size_t)w + t] == v) found = 1;
        if (!found) return 0;
    }
    return 1;
}

/* BFS from s, stops expanding at depth lim; returns the number of vertices NOT within distance 7 (dist > 7). */
static int bfs_lim(int s, int lim, int *ecc) {
    memset(dist, 255, NV);
    int h = 0, t = 0, e = 0;
    dist[s] = 0; que[t++] = s;
    while (h < t) {
        int v = que[h++]; int d = dist[v];
        if (d > e) e = d;
        if (d >= lim) continue;
        const int *out = adj + 7 * (size_t)v;
        for (int k = 0; k < 7; k++) { int w = out[k]; if (dist[w] == 255) { dist[w] = (uint8_t)(d + 1); que[t++] = w; } }
    }
    if (ecc) *ecc = (t == NV) ? e : 255;
    return NV - t;
}

static long multi_count(void) {
    long m = 0;
    for (int p = 0; p < N; p++) for (int j = 0; j < Q1; j++)
        if (PL[p * Q1 + j] == M[p]) { if (Bv[PLi[p * Q1 + j]] == A[p]) m++; break; }
    return m;
}

/* raw uncovered count over the sample; optional breakdown bd[level][0 = point, 1 = line] */
static long uncovered_sample(long (*bd)[2]) {
    long c = 0;
    if (bd) memset(bd, 0, sizeof(long) * 8);
    for (int s = 0; s < nsrc; s++) {
        c += bfs_lim(srcs[s], 7, NULL);
        if (bd) for (int v = 0; v < NV; v++) if (dist[v] > 7) bd[v / NS][(v % NS) >= N]++;
    }
    return c;
}

/* cost = raw + 1000 * double edges, early exit once it exceeds limit (the returned value is then > limit) */
static long cost_bounded(long limit) {
    long c = 1000L * multi_count();
    if (c > limit) return c;
    for (int s = 0; s < nsrc; s++) { c += bfs_lim(srcs[s], 7, NULL); if (c > limit) return c; }
    return c;
}

/* all level-0 sources; returns the total number of (source, target) pairs at distance > 7 */
static long full_check(int *maxecc, long *nbad, long (*bdf)[2]) {
    long sum = 0; int me = 0; *nbad = 0;
    memset(bdf, 0, sizeof(long) * 8);
    for (int s = 0; s < NS; s++) {
        int e; bfs_lim(s, 255, &e);
        long u = 0;
        for (int v = 0; v < NV; v++) if (dist[v] > 7) { u++; bdf[v / NS][(v % NS) >= N]++; }
        sum += u; if (u) (*nbad)++;
        if (e > me) me = e;
    }
    *maxecc = me; return sum;
}

static void init_config(int type) {   /* 1: b=0,a=1   2: b=0,a random   3: b random,a random ; M random */
    for (int p = 0; p < N; p++) M[p] = p;
    for (int p = N - 1; p > 0; p--) { int r = rndi(p + 1); int t = M[p]; M[p] = M[r]; M[r] = t; }
    for (int p = 0; p < N; p++) Minv[M[p]] = p;
    for (int p = 0; p < N; p++) A[p] = (type == 1) ? 1 : 1 + rndi(3);
    for (int id = 0; id < N * Q1; id++) Bv[id] = (type == 3) ? (uint8_t)rndi(4) : 0;
}

static void swapM(int p1, int p2) { int a = M[p1], b = M[p2]; M[p1] = b; M[p2] = a; Minv[b] = p1; Minv[a] = p2; }

static void local_search(double secs) {
    double t0 = now(); long it = 0, acc = 0;
    build_adj();
    long cur = cost_bounded(1L << 60);
    printf("LS start: cost %ld (raw sample uncovered + 1000*double edges)\n", cur); fflush(stdout);
    while (cur > 0 && now() - t0 < secs) {
        it++;
        int mv = rndi(3);
        if (mv == 0) {                                   /* a(p) in {1,2,3} */
            int p = rndi(N), old = A[p], nw;
            do { nw = 1 + rndi(3); } while (nw == old);
            A[p] = nw; build_adj();
            long c = cost_bounded(cur);
            if (c <= cur) { cur = c; acc++; } else { A[p] = old; build_adj(); }
        } else if (mv == 1) {                            /* b(e) in Z_4 */
            int id = rndi(N * Q1), old = Bv[id], nw;
            do { nw = rndi(4); } while (nw == old);
            Bv[id] = (uint8_t)nw; build_adj();
            long c = cost_bounded(cur);
            if (c <= cur) { cur = c; acc++; } else { Bv[id] = (uint8_t)old; build_adj(); }
        } else {                                         /* swap the matching images of two points */
            int p1 = rndi(N), p2 = rndi(N);
            if (p1 == p2) continue;
            swapM(p1, p2); build_adj();
            long c = cost_bounded(cur);
            if (c <= cur) { cur = c; acc++; } else { swapM(p1, p2); build_adj(); }
        }
        if (it % 2000 == 0) { printf("it %ld acc %ld cost %ld (%.0fs)\n", it, acc, cur, now() - t0); fflush(stdout); }
    }
    printf("LS done: it %ld acc %ld final cost %ld (%.1fs)\n", it, acc, cur, now() - t0); fflush(stdout);
}

static void save_cfg(const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "z4cfg %d %d\n", q, N);
    for (int p = 0; p < N; p++) fprintf(f, "%d%c", M[p], (p % 30 == 29 || p == N - 1) ? '\n' : ' ');
    for (int p = 0; p < N; p++) fprintf(f, "%d%c", A[p], (p % 30 == 29 || p == N - 1) ? '\n' : ' ');
    for (int id = 0; id < N * Q1; id++) fprintf(f, "%d%c", Bv[id], (id % 60 == 59 || id == N * Q1 - 1) ? '\n' : ' ');
    fclose(f);
}

static void write_edges(const char *fn) {
    FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", NV);
    long m = 0;
    for (int v = 0; v < NV; v++) {
        const int *out = adj + 7 * (size_t)v;
        for (int k = 0; k < 7; k++) if (out[k] > v) { fprintf(f, "%d %d\n", v, out[k]); m++; }
    }
    fclose(f); printf("wrote %s: n=%d edges=%ld\n", fn, NV, m);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: z4lift HEXBIN SEED LS_SECONDS\n"); return 1; }
    load(argv[1]);
    rs ^= (uint64_t)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    double LS = atof(argv[3]);
    adj = malloc(sizeof(int) * 7 * (size_t)NV); dist = malloc(NV); que = malloc(sizeof(int) * NV);
    M = malloc(sizeof(int) * N); Minv = malloc(sizeof(int) * N); A = malloc(sizeof(int) * N);
    Bv = malloc(N * Q1);
    nsrc = 20; srcs = malloc(sizeof(int) * nsrc);
    for (int k = 0; k < nsrc; k++) srcs[k] = rndi(NS);     /* level-0 sources: point p -> p, line l -> N + l */
    printf("q=%d N=%d NV=%d degree 7; sample = %d random level-0 sources\n", q, N, NV, nsrc);
    fflush(stdout);

    static const char *tname[4] = {"", "(a) b=0 a=1      ", "(b) b=0 a random ", "(c) b rnd a random "};
    for (int type = 1; type <= 3; type++) for (int rep = 0; rep < 3; rep++) {
        init_config(type); build_adj();
        if (type == 1 && rep == 0 && !check_symmetric()) { fprintf(stderr, "adjacency not symmetric\n"); return 2; }
        long bd[4][2];
        long raw = uncovered_sample(bd);
        printf("%s rep %d: sample uncovered %ld (per source %.1f), double edges %ld\n", tname[type], rep, raw,
               raw / (double)nsrc, multi_count());
        printf("     sample by level (points,lines): L0 %ld,%ld  L1 %ld,%ld  L2 %ld,%ld  L3 %ld,%ld\n",
               bd[0][0], bd[0][1], bd[1][0], bd[1][1], bd[2][0], bd[2][1], bd[3][0], bd[3][1]);
        fflush(stdout);
        if (rep == 0) {
            int me; long nb; long bdf[4][2];
            long fs = full_check(&me, &nb, bdf);
            printf("     FULL over all %d level-0 sources: avg uncovered per source %.1f, sources with uncovered>0 %ld, max ecc %d\n",
                   NS, fs / (double)NS, nb, me);
            printf("     FULL per source by level (points,lines): L0 %.1f,%.1f  L1 %.1f,%.1f  L2 %.1f,%.1f  L3 %.1f,%.1f\n",
                   bdf[0][0] / (double)NS, bdf[0][1] / (double)NS, bdf[1][0] / (double)NS, bdf[1][1] / (double)NS,
                   bdf[2][0] / (double)NS, bdf[2][1] / (double)NS, bdf[3][0] / (double)NS, bdf[3][1] / (double)NS);
            fflush(stdout);
        }
    }

    printf("--- local search from config (c) for %.0f s ---\n", LS); fflush(stdout);
    init_config(3);
    local_search(LS);
    build_adj();
    long raw = uncovered_sample(NULL);
    printf("LS final: sample uncovered %ld (per source %.2f), double edges %ld\n", raw, raw / (double)nsrc, multi_count());
    int me; long nb; long bdf[4][2];
    long fs = full_check(&me, &nb, bdf);
    printf("LS final FULL over all %d level-0 sources: avg uncovered per source %.2f, sources with uncovered>0 %ld, max ecc %d, total pairs %ld\n",
           NS, fs / (double)NS, nb, me, fs);
    printf("LS final FULL per source by level (points,lines): L0 %.2f,%.2f  L1 %.2f,%.2f  L2 %.2f,%.2f  L3 %.2f,%.2f\n",
           bdf[0][0] / (double)NS, bdf[0][1] / (double)NS, bdf[1][0] / (double)NS, bdf[1][1] / (double)NS,
           bdf[2][0] / (double)NS, bdf[2][1] / (double)NS, bdf[3][0] / (double)NS, bdf[3][1] / (double)NS);
    save_cfg("z4_final.cfg");
    if (fs == 0 && multi_count() == 0) { write_edges("z4_edges.txt"); printf("FOUND: diameter <= 7 for all sources\n"); }
    fflush(stdout);
    return 0;
}
