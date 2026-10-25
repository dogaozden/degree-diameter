/* twocopy.c: two copies of the incidence graph of H(q) (girth 12, diameter 6, degree K = q+1), each copy minus a
   perfect matching sig[c] (point -> incident line), joined by cross perfect matchings tau1 (points of copy 0 to
   lines of copy 1) and tau2 (points of copy 1 to lines of copy 0). Result: degree K everywhere, bipartite,
   n = 4P. Simulated annealing on cost = number of ordered vertex pairs at distance > D.
   Usage: twocopy BASE D SEED ITERS T0 T1 OUT     (BASE in polygons.py format: P, then P lines with K point ids) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static uint64_t rs;
static uint64_t rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n){ return (int)(rnd() % (uint64_t)n); }
static double runif(void){ return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int P, K, N, D;
static int *lp, *pl;            /* lp[p*K+k]: k-th line through point p; pl[l*K+k]: k-th point on line l */
static unsigned char *inc;      /* inc[p*P+l] = 1 if point p on line l */
static int *sig[2], *sigInv[2]; /* removed matching per copy: point -> line and line -> point */
static int *tau1, *tau2, *tau1inv, *tau2inv;
static int *adj, *dist, *qu;

static void build(void) {
    for (int c = 0; c < 2; c++) for (int p = 0; p < P; p++) {
        int v = c * 2 * P + p, cnt = 0;
        for (int k = 0; k < K; k++) { int l = lp[p * K + k]; if (l != sig[c][p]) adj[v * K + cnt++] = c * 2 * P + P + l; }
        if (c == 0) adj[v * K + cnt++] = 1 * 2 * P + P + tau1[p];
        else        adj[v * K + cnt++] = 0 * 2 * P + P + tau2[p];
    }
    for (int c = 0; c < 2; c++) for (int l = 0; l < P; l++) {
        int v = c * 2 * P + P + l, cnt = 0;
        for (int k = 0; k < K; k++) { int p = pl[l * K + k]; if (sig[c][p] != l) adj[v * K + cnt++] = c * 2 * P + p; }
        if (c == 0) adj[v * K + cnt++] = 1 * 2 * P + tau2inv[l];
        else        adj[v * K + cnt++] = 0 * 2 * P + tau1inv[l];
    }
}

/* number of ordered pairs (s,t) with dist(s,t) > D (unreachable counts) */
static int NS; static int *srcs;
static long cost(void) {
    build();
    long bad = 0;
    for (int si = 0; si < NS; si++) { int s = srcs[si];
        int h = 0, t = 0; dist[s] = 0; qu[t++] = s;
        while (h < t) {
            int x = qu[h++]; if (dist[x] >= D) continue;
            for (int k = 0; k < K; k++) { int y = adj[x * K + k]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } }
        }
        bad += N - t;
        for (int i = 0; i < t; i++) dist[qu[i]] = -1;
    }
    return bad;
}

static int *vis, *matchL, *matchP;
static int try_kuhn(int p) {
    int k0 = rint_(K);
    for (int j = 0; j < K; j++) {
        int l = lp[p * K + (k0 + j) % K];
        if (vis[l]) continue; vis[l] = 1;
        if (matchL[l] < 0 || try_kuhn(matchL[l])) { matchL[l] = p; matchP[p] = l; return 1; }
    }
    return 0;
}

static void random_perm(int *a, int n) {
    for (int i = 0; i < n; i++) a[i] = i;
    for (int i = n - 1; i > 0; i--) { int j = rint_(i + 1); int t = a[i]; a[i] = a[j]; a[j] = t; }
}

int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: twocopy BASE D SEED ITERS T0 T1 OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "r");
    D = atoi(argv[2]); rs = 0x9E3779B97F4A7C15ULL ^ (strtoull(argv[3], 0, 10) * 2654435761ULL + 1);
    long iters = atol(argv[4]); double T0 = atof(argv[5]), T1 = atof(argv[6]); char *outf = argv[7];
    if (fscanf(f, "%d", &P) != 1) return 2;
    int cap = P * 16, cnt = 0, *pts = malloc(cap * sizeof(int)); int x;
    while (fscanf(f, "%d", &x) == 1) { if (cnt == cap) { cap *= 2; pts = realloc(pts, cap * sizeof(int)); } pts[cnt++] = x; }
    K = cnt / P; if (K * P != cnt) { fprintf(stderr, "bad base\n"); return 2; }
    N = 4 * P;
    int S = argc > 8 ? atoi(argv[8]) : 0;
    if (S <= 0 || S >= N) { NS = N; srcs = malloc(N * sizeof(int)); for (int i = 0; i < N; i++) srcs[i] = i; }
    else { NS = S; srcs = malloc(S * sizeof(int)); for (int i = 0; i < S; i++) srcs[i] = rint_(N); }
    lp = malloc(P * K * sizeof(int)); pl = malloc(P * K * sizeof(int));
    int *cntp = calloc(P, sizeof(int));
    for (int l = 0; l < P; l++) for (int k = 0; k < K; k++) {
        int p = pts[l * K + k]; pl[l * K + k] = p; lp[p * K + cntp[p]++] = l; }
    for (int p = 0; p < P; p++) if (cntp[p] != K) { fprintf(stderr, "point %d on %d lines\n", p, cntp[p]); return 2; }
    inc = calloc((size_t)P * P, 1);
    for (int p = 0; p < P; p++) for (int k = 0; k < K; k++) inc[p * P + lp[p * K + k]] = 1;
    vis = malloc(P * sizeof(int)); matchL = malloc(P * sizeof(int)); matchP = malloc(P * sizeof(int));
    for (int c = 0; c < 2; c++) {
        sig[c] = malloc(P * sizeof(int)); sigInv[c] = malloc(P * sizeof(int));
        for (int i = 0; i < P; i++) { matchL[i] = -1; matchP[i] = -1; }
        int *ord = malloc(P * sizeof(int)); random_perm(ord, P);
        for (int i = 0; i < P; i++) { memset(vis, 0, P * sizeof(int)); if (!try_kuhn(ord[i])) { fprintf(stderr, "no perfect matching\n"); return 2; } }
        for (int i = 0; i < P; i++) { sig[c][i] = matchP[i]; sigInv[c][i] = matchL[i]; }
        free(ord);
    }
    tau1 = malloc(P * sizeof(int)); tau2 = malloc(P * sizeof(int)); tau1inv = malloc(P * sizeof(int)); tau2inv = malloc(P * sizeof(int));
    random_perm(tau1, P); random_perm(tau2, P);
    for (int p = 0; p < P; p++) { tau1inv[tau1[p]] = p; tau2inv[tau2[p]] = p; }
    adj = malloc((size_t)N * K * sizeof(int)); dist = malloc(N * sizeof(int)); qu = malloc(N * sizeof(int));
    for (int i = 0; i < N; i++) dist[i] = -1;
    long cur = cost(), best = cur;
    int *b_t1 = malloc(P * sizeof(int)), *b_t2 = malloc(P * sizeof(int));
    int *b_s0 = malloc(P * sizeof(int)), *b_s1 = malloc(P * sizeof(int));
    memcpy(b_t1, tau1, P * sizeof(int)); memcpy(b_t2, tau2, P * sizeof(int));
    memcpy(b_s0, sig[0], P * sizeof(int)); memcpy(b_s1, sig[1], P * sizeof(int));
    fprintf(stderr, "init cost %ld\n", cur);
    for (long it = 0; it < iters && cur > 0; it++) {
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int mv = rint_(3);
        if (mv < 2) {
            int *tp = mv == 0 ? tau1 : tau2, *ti = mv == 0 ? tau1inv : tau2inv;
            int i = rint_(P), j = rint_(P); if (i == j) continue;
            int a = tp[i], b = tp[j]; tp[i] = b; tp[j] = a; ti[a] = j; ti[b] = i;
            long nw = cost();
            if (nw <= cur || runif() < exp((double)(cur - nw) / T)) cur = nw;
            else { tp[i] = a; tp[j] = b; ti[a] = i; ti[b] = j; }
        } else {
            int c = rint_(2), p = rint_(P), k = rint_(K);
            int l = sig[c][p], l2 = lp[p * K + k]; if (l2 == l) continue;
            int p2 = sigInv[c][l2]; if (!inc[p2 * P + l]) continue;
            sig[c][p] = l2; sig[c][p2] = l; sigInv[c][l2] = p; sigInv[c][l] = p2;
            long nw = cost();
            if (nw <= cur || runif() < exp((double)(cur - nw) / T)) cur = nw;
            else { sig[c][p] = l; sig[c][p2] = l2; sigInv[c][l] = p; sigInv[c][l2] = p2; }
        }
        if (cur < best) { best = cur; memcpy(b_t1, tau1, P * sizeof(int)); memcpy(b_t2, tau2, P * sizeof(int));
            memcpy(b_s0, sig[0], P * sizeof(int)); memcpy(b_s1, sig[1], P * sizeof(int)); }
        if (it % 500 == 0) fprintf(stderr, "it %ld T %.3f cur %ld best %ld\n", it, T, cur, best);
    }
    /* restore best state and write its graph */
    memcpy(tau1, b_t1, P * sizeof(int)); memcpy(tau2, b_t2, P * sizeof(int));
    memcpy(sig[0], b_s0, P * sizeof(int)); memcpy(sig[1], b_s1, P * sizeof(int));
    for (int p = 0; p < P; p++) { tau1inv[tau1[p]] = p; tau2inv[tau2[p]] = p; }
    for (int c = 0; c < 2; c++) for (int p = 0; p < P; p++) sigInv[c][sig[c][p]] = p;
    long fin = cost();
    printf("RESULT P=%d K=%d D=%d n=%d best=%ld check=%ld\n", P, K, D, N, best, fin);
    if (fin == 0) {
        build();
        FILE *o = fopen(outf, "w"); fprintf(o, "%d\n", N);
        for (int v = 0; v < N; v++) for (int k = 0; k < K; k++) { int w = adj[v * K + k]; if (v < w) fprintf(o, "%d %d\n", v, w); }
        fclose(o); printf("WROTE %s\n", outf);
    }
    return 0;
}
