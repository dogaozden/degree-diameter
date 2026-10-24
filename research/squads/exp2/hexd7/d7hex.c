/* d7hex.c: bipartite (q+2, 7) graphs from the generalized hexagon H(q), exp2-squad, 2026-10-24.

   Base construction (reproduces the table value 3|H(q)| = 6(q^6-1)/(q-1) at Delta = q+2, D = 7):
     vertices (v, i), v a point or line of H(q), i in Z3;
     (p, i) ~ (l, i) for p on l                      (hexagon edges, all levels)
     (p, i) ~ (M(p), i+1)                             (one extra edge per vertex; M: points -> lines any bijection)
   Diameter <= 7 for EVERY bijection M (see README.md in this folder): up-routes (p,0)->(M(p),1)->hexagon paths,
   and down-routes (p,0) ~> (M(x),0) -> (x,-1).

   Hubs (+2 vertices per freed pair): for a freed point p, delete the three extra edges (p,i)-(M(p),i+1) and add a
   line-side hub z_p ~ (p,0),(p,1),(p,2) and a point-side hub z'_p ~ (M(p),0),(M(p),1),(M(p),2). Degrees stay <= q+2.
   The graph keeps diameter 7 iff each freed point (p,0) and each freed line (M(p),0) still has eccentricity <= 7
   (all other routes of the base proof survive; hubs reach everything in 7). M near the freed pairs is chosen by a
   targeted local search so that this holds.

   Usage:
     d7hex search HEXBIN K seed maxsec [out.sol]   free K random pairwise-far points, search M, full check, write sol
     d7hex check  HEXBIN SOL                        full eccentricity check of a solution (BFS from level 0 + hubs)
     d7hex edges  HEXBIN SOL out.txt                write "n" then edges "u v" (for research/lifts/coordinator_check/apsp.c)
   Solution file: line "d7hex q N K n", line "freed p1 .. pK", then N line ids M[0..N-1]. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1;            /* N points = N lines */
static int32_t *LP;            /* LP[l*Q1+k]: points on line l */
static int32_t *PL;            /* PL[p*Q1+k]: lines through point p */
static int *M, *Minv;          /* point -> line, line -> point */
static int K, *F, *isF;        /* freed points; isF[p] = index+1 or 0 */
static int NV;                 /* 6N + 2K */
static uint8_t *dist;
static int *que;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

/* vertex ids: point (p,i) = i*2N + p; line (l,i) = i*2N + N + l; hub z_j = 6N + j; hub z'_j = 6N + K + j */
static inline int VP(int p, int i) { return i * 2 * N + p; }
static inline int VL(int l, int i) { return i * 2 * N + N + l; }

static int nbrs(int v, int *out) {
    int c = 0;
    if (v >= 6 * N) {
        int j = v - 6 * N;
        if (j < K) { int p = F[j]; for (int i = 0; i < 3; i++) out[c++] = VP(p, i); }
        else { int l = M[F[j - K]]; for (int i = 0; i < 3; i++) out[c++] = VL(l, i); }
        return c;
    }
    int i = v / (2 * N), r = v % (2 * N);
    if (r < N) {
        int p = r;
        for (int k = 0; k < Q1; k++) out[c++] = VL(PL[p * Q1 + k], i);
        if (isF[p]) out[c++] = 6 * N + isF[p] - 1; else out[c++] = VL(M[p], (i + 1) % 3);
    } else {
        int l = r - N;
        for (int k = 0; k < Q1; k++) out[c++] = VP(LP[l * Q1 + k], i);
        int p = Minv[l];
        if (isF[p]) out[c++] = 6 * N + K + isF[p] - 1; else out[c++] = VP(p, (i + 2) % 3);
    }
    return c;
}

/* BFS from s; returns number of vertices at distance > lim (unreached counts); fills dist */
static int bfs(int s, int lim, int *ecc) {
    memset(dist, 255, NV);
    int h = 0, t = 0, nb[64]; dist[s] = 0; que[t++] = s; int e = 0;
    while (h < t) {
        int v = que[h++]; int d = dist[v]; if (d > e) e = d;
        int c = nbrs(v, nb);
        for (int k = 0; k < c; k++) { int w = nb[k]; if (dist[w] == 255) { dist[w] = d + 1; que[t++] = w; } }
    }
    int bad = NV - t;
    for (int k = 0; k < t; k++) if (dist[que[k]] > lim) bad++;
    if (ecc) *ecc = (t < NV) ? 255 : e;
    return bad;
}

/* hexagon distances from a point (isline=0) or line (isline=1): hd[0..N) points, hd[N..2N) lines */
static void hbfs(int x, int isline, uint8_t *hd) {
    memset(hd, 255, 2 * N);
    int *qq = malloc(sizeof(int) * 2 * N), h = 0, t = 0;
    int s = isline ? N + x : x; hd[s] = 0; qq[t++] = s;
    while (h < t) {
        int v = qq[h++];
        if (v < N) { for (int k = 0; k < Q1; k++) { int w = N + PL[v * Q1 + k]; if (hd[w] == 255) { hd[w] = hd[v] + 1; qq[t++] = w; } } }
        else { int l = v - N; for (int k = 0; k < Q1; k++) { int w = LP[l * Q1 + k]; if (hd[w] == 255) { hd[w] = hd[v] + 1; qq[t++] = w; } } }
    }
    free(qq);
}

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(1); }
    int32_t hdr[3]; if (fread(hdr, 4, 3, f) != 3) exit(1);
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    if (hdr[2] != N) { fprintf(stderr, "points != lines\n"); exit(1); }
    LP = malloc(sizeof(int32_t) * (size_t)N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1);
    fclose(f);
    PL = malloc(sizeof(int32_t) * (size_t)N * Q1); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + cnt[p]++] = l; }
    free(cnt);
}

static void alloc_graph(void) {
    NV = 6 * N + 2 * K;
    dist = malloc(NV); que = malloc(sizeof(int) * NV);
}

/* per freed pair: hexagon distances from p and from M(p) */
static uint8_t **hdp, **hdl;
static int cost_of(int j, int *bA, int *bB) {
    int p = F[j];
    *bA = bfs(VP(p, 0), 7, NULL);
    *bB = bfs(VL(M[p], 0), 7, NULL);
    return *bA + *bB;
}

static int total_cost(int *per) {
    int c = 0;
    for (int j = 0; j < K; j++) { int a, b; per[j] = cost_of(j, &a, &b); c += per[j]; }
    return c;
}

/* full check: BFS from every level-0 vertex and every hub (the construction is invariant under (v,i)->(v,i+1)) */
static int full_check(int *diam) {
    int worst = 0, badsrc = 0;
    for (int v = 0; v < 2 * N; v++) { int e; bfs(v, 7, &e); if (e > worst) worst = e; if (e > 7) badsrc++; }
    for (int v = 6 * N; v < NV; v++) { int e; bfs(v, 7, &e); if (e > worst) worst = e; if (e > 7) badsrc++; }
    *diam = worst; return badsrc;
}

static void write_sol(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "d7hex %d %d %d %d\nfreed", q, N, K, NV);
    for (int j = 0; j < K; j++) fprintf(f, " %d", F[j]);
    fprintf(f, "\n");
    for (int p = 0; p < N; p++) fprintf(f, "%d%c", M[p], (p % 20 == 19 || p == N - 1) ? '\n' : ' ');
    fclose(f);
}

static void read_sol(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int qq, nn, kk, nv; char w[16];
    if (fscanf(f, "d7hex %d %d %d %d %15s", &qq, &nn, &kk, &nv, w) != 5 || qq != q || nn != N) { fprintf(stderr, "bad sol header\n"); exit(1); }
    K = kk; F = malloc(sizeof(int) * (K + 1)); isF = calloc(N, sizeof(int));
    for (int j = 0; j < K; j++) { if (fscanf(f, "%d", &F[j]) != 1) exit(1); isF[F[j]] = j + 1; }
    M = malloc(sizeof(int) * N); Minv = malloc(sizeof(int) * N); for (int l = 0; l < N; l++) Minv[l] = -1;
    for (int p = 0; p < N; p++) { if (fscanf(f, "%d", &M[p]) != 1) exit(1); if (Minv[M[p]] >= 0) { fprintf(stderr, "M not a bijection\n"); exit(1); } Minv[M[p]] = p; }
    fclose(f);
    alloc_graph();
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see header\n"); return 1; }
    load(argv[2]);
    if (!strcmp(argv[1], "check")) {
        read_sol(argv[3]);
        int maxdeg = 0, nb[64];
        for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); if (c > maxdeg) maxdeg = c; }
        int diam, bad = full_check(&diam);
        printf("q=%d n=%d K=%d maxdeg=%d diameter=%d badsources=%d -> %s\n", q, NV, K, maxdeg, diam, bad,
               (bad == 0 && diam <= 7 && maxdeg <= q + 2) ? "VALID" : "INVALID");
        return 0;
    }
    if (!strcmp(argv[1], "edges")) {
        read_sol(argv[3]);
        FILE *f = fopen(argv[4], "w"); fprintf(f, "%d\n", NV); int nb[64]; long m = 0;
        for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); for (int k = 0; k < c; k++) if (nb[k] > v) { fprintf(f, "%d %d\n", v, nb[k]); m++; } }
        fclose(f); fprintf(stderr, "wrote %s: n=%d edges=%ld\n", argv[4], NV, m);
        return 0;
    }
    if (strcmp(argv[1], "search")) return 1;
    K = atoi(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    double maxsec = atof(argv[5]);
    const char *out = argc > 6 ? argv[6] : NULL;
    /* random bijection M */
    M = malloc(sizeof(int) * N); Minv = malloc(sizeof(int) * N);
    for (int p = 0; p < N; p++) M[p] = p;
    for (int p = N - 1; p > 0; p--) { int r = rndi(p + 1); int t = M[p]; M[p] = M[r]; M[r] = t; }
    for (int p = 0; p < N; p++) Minv[M[p]] = p;
    /* freed points: greedy pairwise opposite (hexagon distance 6) random choice; lines M(p) also far apart */
    F = malloc(sizeof(int) * (K + 1)); isF = calloc(N, sizeof(int));
    uint8_t *tmp = malloc(2 * N); uint8_t *ok = malloc(N); memset(ok, 1, N);
    for (int j = 0; j < K; j++) {
        int p = -1;
        for (int tries = 0; tries < 100000; tries++) { int c = rndi(N); if (ok[c]) { p = c; break; } }
        if (p < 0) { fprintf(stderr, "could only place %d freed points\n", j); K = j; break; }
        F[j] = p; isF[p] = j + 1;
        hbfs(p, 0, tmp); for (int x = 0; x < N; x++) if (tmp[x] < 6) ok[x] = 0;
    }
    alloc_graph();
    hdp = malloc(sizeof(uint8_t *) * K); hdl = malloc(sizeof(uint8_t *) * K);
    for (int j = 0; j < K; j++) { hdp[j] = malloc(2 * N); hbfs(F[j], 0, hdp[j]); hdl[j] = malloc(2 * N); hbfs(M[F[j]], 1, hdl[j]); }
    int *per = malloc(sizeof(int) * K), *per2 = malloc(sizeof(int) * K);
    int cost = total_cost(per);
    fprintf(stderr, "q=%d N=%d K=%d n=%d initial cost %d\n", q, N, K, NV, cost);
    clock_t t0 = clock(); long it = 0, acc = 0;
    int *badlist = malloc(sizeof(int) * NV);
    while (cost > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < maxsec) {
        it++;
        /* pick a freed pair with positive cost, a side, and an uncovered target */
        int j; do { j = rndi(K); } while (per[j] == 0);
        int p = F[j], lp = M[p];
        int side = rndi(2);
        int src = side == 0 ? VP(p, 0) : VL(lp, 0);
        int nbad = bfs(src, 7, NULL);
        if (nbad == 0) { side ^= 1; src = side == 0 ? VP(p, 0) : VL(lp, 0); nbad = bfs(src, 7, NULL); }
        if (nbad == 0) continue;
        int nb2 = 0; for (int v = 0; v < NV; v++) if (dist[v] > 7) badlist[nb2++] = v;
        int t = badlist[rndi(nb2)];
        if (t >= 6 * N) continue;
        int ti = t / (2 * N), tr = t % (2 * N);
        int u = -1, w = -1, newl = -1;   /* move: M[u] := newl, previous owner w of newl gets old M[u] */
        if (side == 0) {
            if (tr >= N) continue;                       /* expect a point target */
            int x = tr; (void)ti;
            int kind = rndi(4);
            if (kind < 3) {  /* (a=4): u at distance 4 from p, newl through x at distance 5 from p */
                int cand[64], nc = 0;
                for (int k = 0; k < Q1; k++) { int l = PL[x * Q1 + k]; if (hdp[j][N + l] == 5) cand[nc++] = l; }
                if (!nc) continue; newl = cand[rndi(nc)];
                for (int tries = 0; tries < 200; tries++) { int c = rndi(N); if (hdp[j][c] == 4) { u = c; break; } }
            } else {         /* (a=2): u at distance 2 from p, newl within distance 3 of x */
                int l1 = PL[x * Q1 + rndi(Q1)]; int y = LP[l1 * Q1 + rndi(Q1)]; newl = PL[y * Q1 + rndi(Q1)];
                for (int tries = 0; tries < 200; tries++) { int c = rndi(N); if (hdp[j][c] == 2) { u = c; break; } }
            }
        } else {
            if (tr < N) continue;                        /* expect a line target */
            int lt = tr - N;
            int kind = rndi(4);
            int y = -1, l2 = -1;
            if (kind < 3) {  /* line l2 at distance 4 from lp gets preimage y on lt, y at distance 5 from lp */
                int cand[64], nc = 0;
                for (int k = 0; k < Q1; k++) { int c = LP[lt * Q1 + k]; if (hdl[j][c] == 5) cand[nc++] = c; }
                if (!nc) continue; y = cand[rndi(nc)];
                for (int tries = 0; tries < 200; tries++) { int c = rndi(N); if (hdl[j][N + c] == 4) { l2 = c; break; } }
            } else {         /* line l2 at distance 2 from lp gets a preimage within distance 3 of lt */
                int y1 = LP[lt * Q1 + rndi(Q1)]; int l1 = PL[y1 * Q1 + rndi(Q1)]; y = LP[l1 * Q1 + rndi(Q1)];
                for (int tries = 0; tries < 200; tries++) { int c = rndi(N); if (hdl[j][N + c] == 2) { l2 = c; break; } }
            }
            if (l2 < 0) continue;
            u = y; newl = l2;
        }
        if (u < 0 || newl < 0) continue;
        w = Minv[newl];
        if (w == u || isF[u] || isF[w]) continue;
        /* apply */
        int oldl = M[u];
        M[u] = newl; Minv[newl] = u; M[w] = oldl; Minv[oldl] = w;
        int c2 = total_cost(per2);
        if (c2 <= cost) { cost = c2; memcpy(per, per2, sizeof(int) * K); acc++; }
        else { M[u] = oldl; Minv[oldl] = u; M[w] = newl; Minv[newl] = w; }
        if (it % 500 == 0) fprintf(stderr, "it %ld acc %ld cost %d  (%.1fs)\n", it, acc, cost, (double)(clock() - t0) / CLOCKS_PER_SEC);
    }
    fprintf(stderr, "search done: it %ld cost %d (%.1fs)\n", it, cost, (double)(clock() - t0) / CLOCKS_PER_SEC);
    if (cost == 0) {
        int diam, bad = full_check(&diam);
        int maxdeg = 0, nb[64]; for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); if (c > maxdeg) maxdeg = c; }
        printf("RESULT q=%d K=%d n=%d maxdeg=%d diameter=%d badsources=%d %s\n", q, K, NV, maxdeg, diam, bad,
               (bad == 0 && diam <= 7 && maxdeg <= q + 2) ? "VALID" : "INVALID");
        if (out && bad == 0 && diam <= 7) write_sol(out);
    } else printf("RESULT q=%d K=%d unsolved cost %d\n", q, K, cost);
    return 0;
}
