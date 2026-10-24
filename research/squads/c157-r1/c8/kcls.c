/* kcls.c: class-based version of research/d15D7/kcopy_hub.c (squad c157-r1, card c8 WILDCARD).

   Graph: r = 7 copies (c in Z_7) of the incidence graph of H(q), q = 11, N = 177156 points and lines.
   Cross edges (p,c) ~ (M(p), c+j) for j = 1,2,3 and all p, EXCEPT freed classes.
   A freed class t = (p_t, j_t) deletes the cross edges (p_t,c) ~ (M(p_t), c+j_t) for all c, and adds
     Z_t ~ (p_t, c)        for all c   (line-side hub, degree 7 + hub-graph degree)
     W_t ~ (M(p_t), c)     for all c   (point-side hub)
   so every freed vertex keeps degree 15. A point may carry several classes (different j).
   Hub graph: listed pairs Z_t ~ W_s (hub-graph degree <= 8).
   Vertices: 14N + 2T with T classes (N = 177156, 2N per copy).

   Why only freed sources and hubs need BFS (copy-invariant graph, hubs fixed):
   Let S = {points p with a freed class} u {M(p) : p with a freed class} u hubs. Take two vertices outside S.
   Point-point (u,c),(v,c+d): if d in {1,2,3}, (u,c) -> (M(u),c+d) -> hexagon path (<= 5) has length <= 6, using the
   class (u,d), which is intact because u is outside S. If d in {4,5,6}, the same argument from v with class (v,7-d).
   Point-line (u,c),(L,c+d): if d in {1,2,3}, (u,c) -> (M(u),c+d) -> hexagon path of length <= 6 (line to line), total 7.
   If d in {4,5,6}, (L,c+d) -> (q,c+d-j) with q = M^-1(L) and j in {1,2,3} such that class (q,j) is intact (q outside S),
   then point-point path <= 6, total 7.   Line-line pairs are symmetric.
   Hence every pair outside S is within 7, and a pair with one endpoint in S is covered by a BFS from that endpoint.
   Copy invariance gives the BFS from (p,c) = BFS from (p,0). So BFS from (p_t,0), (M(p_t),0) and all hubs is exact.

   Usage:
     kcls check HEXBIN CLS.sol        basic symmetry/degree test, then eccentricity of every source above
   CLS.sol format: line "d7cls q N T nv"; T lines "p j" (class t = line index, j in 1..3);
     line "hubedges m"; m lines "t s" (Z_t ~ W_s); then N integers M[0..N-1] (points -> lines).  */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define R 7
static int q, N, Q1, T, HB, NV;
static int32_t *LP, *PL;
static int *M, *Minv, *cp, *cj, *cls_of, *HZn, **HZ, *HWn, **HW;

static void load_hex(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(1); }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) exit(1);
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1);
    fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; PL[p * Q1 + cnt[p]++] = l; }
    for (int p = 0; p < N; p++) if (cnt[p] != Q1) { fprintf(stderr, "bad hexagon table\n"); exit(1); }
    free(cnt);
}

static void read_cls(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int qq, nn, nv; char w[16];
    if (fscanf(f, "d7cls %d %d %d %d", &qq, &nn, &T, &nv) != 4 || qq != q || nn != N) { fprintf(stderr, "bad header\n"); exit(1); }
    (void)w;
    cp = malloc(sizeof(int) * (T + 1)); cj = malloc(sizeof(int) * (T + 1));
    cls_of = malloc(sizeof(int) * 3 * (size_t)N); for (size_t i = 0; i < 3 * (size_t)N; i++) cls_of[i] = -1;
    for (int t = 0; t < T; t++) {
        if (fscanf(f, "%d %d", &cp[t], &cj[t]) != 2 || cp[t] < 0 || cp[t] >= N || cj[t] < 1 || cj[t] > 3) { fprintf(stderr, "bad class %d\n", t); exit(1); }
        if (cls_of[3 * cp[t] + cj[t] - 1] >= 0) { fprintf(stderr, "repeated class\n"); exit(1); }
        cls_of[3 * cp[t] + cj[t] - 1] = t;
    }
    char tok[32]; int m = 0;
    if (fscanf(f, "%31s %d", tok, &m) != 2 || strcmp(tok, "hubedges")) { fprintf(stderr, "no hubedges\n"); exit(1); }
    HZn = calloc(T + 1, sizeof(int)); HWn = calloc(T + 1, sizeof(int));
    HZ = malloc(sizeof(int *) * (T + 1)); HW = malloc(sizeof(int *) * (T + 1));
    for (int t = 0; t < T; t++) { HZ[t] = malloc(sizeof(int) * 16); HW[t] = malloc(sizeof(int) * 16); }
    for (int e = 0; e < m; e++) {
        int t, s; if (fscanf(f, "%d %d", &t, &s) != 2 || t < 0 || t >= T || s < 0 || s >= T) { fprintf(stderr, "bad hub edge\n"); exit(1); }
        if (HZn[t] >= 16 || HWn[s] >= 16) { fprintf(stderr, "hub-graph degree > 16\n"); exit(1); }
        HZ[t][HZn[t]++] = s; HW[s][HWn[s]++] = t;
    }
    M = malloc(sizeof(int) * N); Minv = malloc(sizeof(int) * N); for (int l = 0; l < N; l++) Minv[l] = -1;
    for (int p = 0; p < N; p++) {
        if (fscanf(f, "%d", &M[p]) != 1 || M[p] < 0 || M[p] >= N || Minv[M[p]] >= 0) { fprintf(stderr, "bad M at %d\n", p); exit(1); }
        Minv[M[p]] = p;
    }
    fclose(f);
    HB = R * 2 * N; NV = HB + 2 * T;
    if (nv != NV) { fprintf(stderr, "warning: header nv %d, computed %d\n", nv, NV); }
}

static inline int VP(int p, int c) { return c * 2 * N + p; }
static inline int VL(int l, int c) { return c * 2 * N + N + l; }

/* hub ids: Z_t = HB + t, W_t = HB + T + t */
static int nbrs(int v, int *out) {
    int n = 0;
    if (v >= HB) {
        int h = v - HB;
        if (h < T) {
            int p = cp[h]; for (int c = 0; c < R; c++) out[n++] = VP(p, c);
            for (int i = 0; i < HZn[h]; i++) out[n++] = HB + T + HZ[h][i];
        } else {
            h -= T; int l = M[cp[h]]; for (int c = 0; c < R; c++) out[n++] = VL(l, c);
            for (int i = 0; i < HWn[h]; i++) out[n++] = HB + HW[h][i];
        }
        return n;
    }
    int c = v / (2 * N), x = v % (2 * N);
    if (x < N) {
        int p = x;
        for (int t = 0; t < Q1; t++) out[n++] = VL(PL[p * Q1 + t], c);
        for (int j = 1; j <= 3; j++) {
            int t = cls_of[3 * p + j - 1];
            if (t < 0) out[n++] = VL(M[p], (c + j) % R);
            else out[n++] = HB + t;
        }
    } else {
        int l = x - N;
        for (int t = 0; t < Q1; t++) out[n++] = VP(LP[l * Q1 + t], c);
        int p = Minv[l];
        for (int j = 1; j <= 3; j++) {
            int t = cls_of[3 * p + j - 1];
            if (t < 0) out[n++] = VP(p, (c - j + R) % R);
            else out[n++] = HB + T + t;
        }
    }
    return n;
}

static int bfs_ecc(int s, uint8_t *dist, int *que, long *bad) {
    memset(dist, 255, NV);
    int h = 0, t = 0, nb[128], e = 0; dist[s] = 0; que[t++] = s;
    while (h < t) {
        int v = que[h++]; int d = dist[v]; if (d > e) e = d;
        int c = nbrs(v, nb);
        for (int i = 0; i < c; i++) { int w = nb[i]; if (dist[w] == 255) { dist[w] = d + 1; que[t++] = w; } }
    }
    long b = NV - t; for (int i = 0; i < t; i++) if (dist[que[i]] > 7) b++;
    *bad = b;
    return t < NV ? 255 : e;
}

static int basic_stats(int *maxdeg, long *nedges) {
    int nb[128], md = 0; long m = 0;
    for (int v = 0; v < NV; v++) {
        int c = nbrs(v, nb); if (c > md) md = c; m += c;
        for (int i = 0; i < c; i++) {
            int w = nb[i], nb2[128], c2 = nbrs(w, nb2), f = 0;
            for (int t = 0; t < c2; t++) if (nb2[t] == v) f++;
            if (f != 1) { fprintf(stderr, "adjacency not symmetric/simple at %d-%d\n", v, w); return 0; }
            for (int t = i + 1; t < c; t++) if (nb[t] == w) { fprintf(stderr, "repeated edge at %d\n", v); return 0; }
        }
    }
    *maxdeg = md; *nedges = m / 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 4 || strcmp(argv[1], "check")) { fprintf(stderr, "usage: kcls check HEXBIN CLS.sol\n"); return 1; }
    load_hex(argv[2]); read_cls(argv[3]);
    int md; long m;
    int sym = basic_stats(&md, &m);
    printf("classes=%d hubs=%d n=%d (base %d, added %d) edges=%ld maxdeg=%d symmetric=%d\n",
           T, 2 * T, NV, R * 2 * N, NV - R * 2 * N, m, md, sym);
    if (!sym) { printf("-> FAIL (structure)\n"); return 0; }
    uint8_t *dist = malloc(NV); int *que = malloc(sizeof(int) * NV);
    int worst = 0, badsrc = 0, nsrc = 0; long badpairs = 0;
    for (int t = 0; t < T; t++) {
        int srcs[2] = { VP(cp[t], 0), VL(M[cp[t]], 0) };
        for (int s = 0; s < 2; s++) {
            long b; int e = bfs_ecc(srcs[s], dist, que, &b);
            if (e > worst) worst = e;
            if (b) { badsrc++; badpairs += b; if (getenv("KCLS_VERBOSE")) printf("bad class %d (%s) ecc %d far %ld\n", t, s ? "line" : "point", e, b); }
            nsrc++;
        }
    }
    for (int v = HB; v < NV; v++) {
        long b; int e = bfs_ecc(v, dist, que, &b);
        if (e > worst) worst = e;
        if (b) { badsrc++; badpairs += b; if (getenv("KCLS_VERBOSE")) printf("bad hub %d (%s) ecc %d far %ld\n", v - HB, v - HB < T ? "Z" : "W", e, b); }
        nsrc++;
    }
    /* optional independent sample: KCLS_SAMPLE=n random non-hub sources (should all pass if the argument holds) */
    int ns = getenv("KCLS_SAMPLE") ? atoi(getenv("KCLS_SAMPLE")) : 0;
    srand(12345);
    for (int i = 0; i < ns; i++) {
        int v = (int)(((long)rand() * 65536L + rand()) % HB);
        long b; int e = bfs_ecc(v, dist, que, &b);
        if (e > worst) worst = e;
        if (b) { badsrc++; badpairs += b; }
        nsrc++;
    }
    printf("sources %d (freed points/lines and hubs), max eccentricity %d, bad sources %d, far pairs %ld\n",
           nsrc, worst, badsrc, badpairs);
    printf("-> %s\n", (badsrc == 0 && md <= 15 && sym) ? "OK" : "FAIL");
    return 0;
}
