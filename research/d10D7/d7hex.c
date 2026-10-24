/* d7hex.c (copy of research/squads/exp2/hexd7/d7hex.c on master, exp2-squad): bipartite (q+2, 7) graphs from the generalized hexagon H(q), exp2-squad, 2026-10-24.

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
     d7hex search HEXBIN K seed maxsec out.sol [mode [alg [mind [HGFILE]]]]
         mode 0: K points pairwise opposite, no hub links (valid only for K = 1)
         mode 1: star (K <= q+1 points on distinct lines through a centre; hubs close without links)
         mode 2: hub graph = incidence graph of PG(2,q-2), K = (q-2)^2+(q-2)+1, freed points pairwise >= mind apart
         mode 3: hub graph read from HGFILE ("K m" then m lines "j k"; hub degrees <= q-1); K is taken from the file
         alg=1 installs the algebraic cover for every pair, then targeted local search, then the full check
         alg=2 additionally runs the fast proxy search (incremental route counts) before the BFS-based search
         alg=3 also runs a type-2 greedy pre-pass before the algebraic covers
         alg=4 joint algebraic cover: M maps each point to a line with the same membership vector (bits k: point in
               S'(p_k), line in S(l_k)), leftovers paired by popcount; then the fast proxy search (use with OPPFLAGS)
         env: BESTK=k best-of-k moves; SKIPFULL=1 skip the internal full check (verify with apsp);
              DROPSEC=s, DROPSTART=t: after t s, whenever the proxy has not fallen 2% in s seconds, drop the worst pair;
              DROP=1: after the search, drop the worst pairs until every freed source is fine
              OPPFLAGS=1: choose the freed flags (p, M(p)) pairwise opposite (fewer cover conflicts)
              GREEDYFLAGS=c: with OPPFLAGS, each new flag is the best of c candidates for the vector mismatch (alg 4)
              PEXH=p: with probability p (when < 4000 targets remain) try all type-4 candidates for a target
              GROW=Kmax: once solved, add freed pairs one at a time (best of NCAND flags by uncovered targets, opposite
                to all if OPPGROW=1), hub edges HGDEG each, repair for STEPSEC s; keep if solved, else revert (MAXFAIL)
     d7hex check  HEXBIN SOL                        full eccentricity check of a solution (BFS from level 0 + hubs)
     d7hex edges  HEXBIN SOL out.txt                write "n" then edges "u v" (for research/lifts/coordinator_check/apsp.c)
     d7hex super  HEXBIN SOL out.txt seed tries     add super-hubs (new vertices on hubs with spare degree whose freed
                                                    elements' 4-balls cover a whole side), keep those with ecc <= 7, write edges
   Solution file: line "d7hex q N K n", line "freed p1 .. pK", then N line ids M[0..N-1]. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>

static int q, N, Q1;            /* N points = N lines */
static int32_t *LP;            /* LP[l*Q1+k]: points on line l */
static int32_t *PL;            /* PL[p*Q1+k]: lines through point p */
static int *M, *Minv;          /* point -> line, line -> point */
static int K, *F, *isF;        /* freed points; isF[p] = index+1 or 0 */
static int NV;                 /* 6N + 2K */
static uint8_t *dist;
static int *que;
/* hub graph: line-side hub j ~ point-side hub k (uses the hubs' q-1 spare slots; keeps hubs pairwise close) */
static int HGm = 0, *HGj, *HGk;          /* edge list */
static int **HGL, **HGP, *HGLn, *HGPn;   /* adjacency */
/* super-hubs (mode "super"): new vertices 6N+2K+s adjacent only to hubs */
static int NSH = 0, *SHn, **SHnb, *HXn, **HX;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

/* membership vectors for the joint algebraic cover (alg 4, GREEDYFLAGS): bit k of a point u is set when u is in
   S'(p_k) (distance 4 from p_k, not via l_k); bit k of a line L when L is in S(l_k) (distance 4 from l_k, not via p_k).
   A bijection M that maps every point to a line with the same vector installs all K algebraic covers at once. */
typedef struct { uint64_t a, b; } v128;
static inline void vset(v128 *v, int k) { if (k < 64) v->a |= 1ULL << k; else v->b |= 1ULL << (k - 64); }
static inline int vcmp(const v128 *u, const v128 *v) { if (u->b != v->b) return u->b < v->b ? -1 : 1; if (u->a != v->a) return u->a < v->a ? -1 : 1; return 0; }
static int cmpv(const void *x, const void *y) { return vcmp((const v128 *)x, (const v128 *)y); }
static long mismatch(const v128 *P, const v128 *L, int n, v128 *tp, v128 *tl) {   /* sum over vectors of |#points - #lines| */
    memcpy(tp, P, sizeof(v128) * n); memcpy(tl, L, sizeof(v128) * n);
    qsort(tp, n, sizeof(v128), cmpv); qsort(tl, n, sizeof(v128), cmpv);
    long mm = 0; int i = 0, j = 0;
    while (i < n || j < n) {
        int c = (i >= n) ? 1 : (j >= n) ? -1 : vcmp(&tp[i], &tl[j]);
        if (c == 0) { v128 v = tp[i]; long a = 0, b = 0; while (i < n && !vcmp(&tp[i], &v)) { i++; a++; } while (j < n && !vcmp(&tl[j], &v)) { j++; b++; } mm += labs(a - b); }
        else if (c < 0) { v128 v = tp[i]; while (i < n && !vcmp(&tp[i], &v)) { i++; mm++; } }
        else { v128 v = tl[j]; while (j < n && !vcmp(&tl[j], &v)) { j++; mm++; } }
    }
    return mm;
}
typedef struct { v128 v; int id; int pc; uint32_t r; } vitem;
static int cmpitem(const void *x, const void *y) {
    const vitem *u = x, *w = y; int c = vcmp(&u->v, &w->v); if (c) return c;
    return u->r < w->r ? -1 : u->r > w->r ? 1 : 0;
}
static int cmpitem_pc(const void *x, const void *y) {
    const vitem *u = x, *w = y; if (u->pc != w->pc) return u->pc - w->pc; return cmpitem(x, y);
}

/* vertex ids: point (p,i) = i*2N + p; line (l,i) = i*2N + N + l; hub z_j = 6N + j; hub z'_j = 6N + K + j */
static inline int VP(int p, int i) { return i * 2 * N + p; }
static inline int VL(int l, int i) { return i * 2 * N + N + l; }

static int nbrs(int v, int *out) {
    int c = 0;
    if (v >= 6 * N + 2 * K) { int s = v - 6 * N - 2 * K; for (int t = 0; t < SHn[s]; t++) out[c++] = SHnb[s][t]; return c; }
    if (v >= 6 * N) {
        int j = v - 6 * N;
        if (NSH) { int h = j; for (int t = 0; t < HXn[h]; t++) out[c++] = HX[h][t]; }
        if (j < K) { int p = F[j]; for (int i = 0; i < 3; i++) out[c++] = VP(p, i);
                     if (HGm) for (int t = 0; t < HGLn[j]; t++) out[c++] = 6 * N + K + HGL[j][t]; }
        else { int l = M[F[j - K]]; for (int i = 0; i < 3; i++) out[c++] = VL(l, i);
               if (HGm) for (int t = 0; t < HGPn[j - K]; t++) out[c++] = 6 * N + HGP[j - K][t]; }
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

static void hg_build(void) {
    HGL = malloc(sizeof(int *) * (K + 1)); HGP = malloc(sizeof(int *) * (K + 1));
    HGLn = calloc(K + 1, sizeof(int)); HGPn = calloc(K + 1, sizeof(int));
    for (int j = 0; j < K; j++) { HGL[j] = malloc(sizeof(int) * 16); HGP[j] = malloc(sizeof(int) * 16); }
    for (int e = 0; e < HGm; e++) {
        int j = HGj[e], k = HGk[e];
        if (HGLn[j] >= 16 || HGPn[k] >= 16) { fprintf(stderr, "hub graph degree too large\n"); exit(1); }
        HGL[j][HGLn[j]++] = k; HGP[k][HGPn[k]++] = j;
    }
}

/* incidence graph of PG(2,r), r prime: returns number of points (= lines) and fills HGj/HGk */
static int hg_pg2(int r) {
    int pts[512][3], n = 0;
    for (int a = 0; a < r; a++) for (int b = 0; b < r; b++) for (int c = 0; c < r; c++) {
        int v[3] = {a, b, c}, f = -1; for (int i = 0; i < 3; i++) if (v[i]) { f = v[i]; break; }
        if (f == 1) { pts[n][0] = a; pts[n][1] = b; pts[n][2] = c; n++; }
    }
    HGj = malloc(sizeof(int) * n * (r + 1)); HGk = malloc(sizeof(int) * n * (r + 1)); HGm = 0;
    for (int j = 0; j < n; j++) for (int k = 0; k < n; k++)
        if ((pts[j][0] * pts[k][0] + pts[j][1] * pts[k][1] + pts[j][2] * pts[k][2]) % r == 0) { HGj[HGm] = j; HGk[HGm] = k; HGm++; }
    return n;
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
    fprintf(f, "\nhubedges %d", HGm);
    for (int e = 0; e < HGm; e++) fprintf(f, " %d %d", HGj[e], HGk[e]);
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
    long pos = ftell(f); char tok[32];
    if (fscanf(f, "%31s", tok) == 1 && !strcmp(tok, "hubedges")) {
        if (fscanf(f, "%d", &HGm) != 1) exit(1);
        HGj = malloc(sizeof(int) * (HGm + 1)); HGk = malloc(sizeof(int) * (HGm + 1));
        for (int e = 0; e < HGm; e++) if (fscanf(f, "%d %d", &HGj[e], &HGk[e]) != 2) exit(1);
        if (HGm) hg_build();
    } else fseek(f, pos, SEEK_SET);
    M = malloc(sizeof(int) * N); Minv = malloc(sizeof(int) * N); for (int l = 0; l < N; l++) Minv[l] = -1;
    for (int p = 0; p < N; p++) { if (fscanf(f, "%d", &M[p]) != 1) exit(1); if (Minv[M[p]] >= 0) { fprintf(stderr, "M not a bijection\n"); exit(1); } Minv[M[p]] = p; }
    fclose(f);
    alloc_graph();
}



/* ---------- type-2 greedy pre-pass (alg >= 3) ----------
   Side A of pair k: the q(q+1) points u collinear with p_k get lines L whose 3-balls cover many points opposite p_k.
   Side B: the q(q+1) lines meeting l_k get preimages y whose 3-balls (in lines) cover many lines opposite l_k.
   These use few elements per pair, so different pairs rarely compete; type-4 covers then fill the rest. */
static int ball3_lines_of_point(int x, int *out) {   /* lines within distance 3 of point x */
    int c = 0;
    for (int a = 0; a < Q1; a++) { int L = PL[x * Q1 + a]; out[c++] = L;
        for (int b = 0; b < Q1; b++) { int y = LP[L * Q1 + b]; if (y == x) continue;
            for (int d = 0; d < Q1; d++) { int L2 = PL[y * Q1 + d]; if (L2 != L) out[c++] = L2; } } }
    return c;
}
static int ball3_points_of_line(int L, int *out) {   /* points within distance 3 of line L */
    int c = 0;
    for (int a = 0; a < Q1; a++) { int y = LP[L * Q1 + a]; out[c++] = y;
        for (int b = 0; b < Q1; b++) { int L2 = PL[y * Q1 + b]; if (L2 == L) continue;
            for (int d = 0; d < Q1; d++) { int x = LP[L2 * Q1 + d]; if (x != y) out[c++] = x; } } }
    return c;
}
static void type2_prepass(uint8_t *lockp, uint8_t *lockl) {
    int cap = 4 * Q1 * Q1 * Q1, *buf = malloc(sizeof(int) * cap), *buf2 = malloc(sizeof(int) * cap);
    uint8_t *resP = calloc(N, 1), *resL = calloc(N, 1), *unc = malloc(N);
    for (int k = 0; k < K; k++) for (int v = 0; v < N; v++) { if (hdp[k][v] == 2) resP[v] = 1; if (hdl[k][N + v] == 2) resL[v] = 1; }
    long covA = 0, covB = 0, totA = 0, totB = 0;
    for (int k = 0; k < K; k++) {
        /* side A */
        int nU = 0; for (int x = 0; x < N; x++) { unc[x] = (hdp[k][x] == 6); nU += unc[x]; }
        totA += nU;
        for (int v = 0; v < N; v++) {
            if (hdp[k][v] != 2 || isF[v] || lockp[v]) continue;
            int u = v, bestL = -1, bestg = 0;
            for (int s = 0; s < 3 && nU > 0; s++) {
                int x; do { x = rndi(N); } while (!unc[x]);
                int nc = ball3_lines_of_point(x, buf);
                for (int c = 0; c < 64; c++) {
                    int L = buf[rndi(nc)];
                    if (lockl[L] || resL[L] || isF[Minv[L]] || lockp[Minv[L]] || hdp[k][N + L] != 5) continue;
                    int np = ball3_points_of_line(L, buf2), g = 0;
                    for (int t = 0; t < np; t++) g += unc[buf2[t]];
                    if (g > bestg) { bestg = g; bestL = L; }
                }
            }
            if (bestL < 0) continue;
            int w = Minv[bestL], o = M[u]; M[u] = bestL; Minv[bestL] = u; M[w] = o; Minv[o] = w;
            lockp[u] = 1; lockl[bestL] = 1;
            int np = ball3_points_of_line(bestL, buf2);
            for (int t = 0; t < np; t++) if (unc[buf2[t]]) { unc[buf2[t]] = 0; nU--; covA++; }
        }
        /* side B */
        nU = 0; for (int t = 0; t < N; t++) { unc[t] = (hdl[k][N + t] == 6); nU += unc[t]; }
        totB += nU;
        for (int L = 0; L < N; L++) {
            if (hdl[k][N + L] != 2 || lockl[L] || isF[Minv[L]] || lockp[Minv[L]]) continue;
            int besty = -1, bestg = 0;
            for (int s = 0; s < 3 && nU > 0; s++) {
                int t; do { t = rndi(N); } while (!unc[t]);
                int nc = ball3_points_of_line(t, buf);
                for (int c = 0; c < 64; c++) {
                    int y = buf[rndi(nc)];
                    if (lockp[y] || resP[y] || isF[y] || lockl[M[y]] || hdl[k][y] != 5) continue;
                    int nl = ball3_lines_of_point(y, buf2), g = 0;
                    for (int a = 0; a < nl; a++) g += unc[buf2[a]];
                    if (g > bestg) { bestg = g; besty = y; }
                }
            }
            if (besty < 0) continue;
            int y = besty, w = Minv[L], o = M[y]; M[y] = L; Minv[L] = y; M[w] = o; Minv[o] = w;
            lockp[y] = 1; lockl[L] = 1;
            int nl = ball3_lines_of_point(y, buf2);
            for (int a = 0; a < nl; a++) if (unc[buf2[a]]) { unc[buf2[a]] = 0; nU--; covB++; }
        }
    }
    fprintf(stderr, "type-2 pre-pass: side A covered %ld of %ld, side B %ld of %ld\n", covA, totA, covB, totB);
    free(buf); free(buf2); free(resP); free(resL); free(unc);
}

/* ---------- fast proxy search ----------
   For pair k (freed point p = F[k], freed line l = M(p), p on l), count routes of two kinds:
   side A (targets x opposite p, level 1):  u at distance 4 from p, M(u) at distance 5 from p, x on M(u)       [type 4]
                                             u at distance 2 from p, x within distance 3 of M(u)                 [type 2]
   side B (targets t opposite l, level -1): line L at distance 4 from l, y = M^-1(L) at distance 5 from l, t through y [type 4]
                                             line L at distance 2 from l, t within distance 3 of y = M^-1(L)       [type 2]
   Each is a real route of length <= 6 in X, so proxy cost 0 implies every freed source has eccentricity <= 7. */
static uint16_t **cA, **cB; static long zeros = 0;
static int **oppA, **oppB, *noppA, *noppB, **n4p, **n2p, **n4l, **n2l, *nn4p, *nn2p, *nn4l, *nn2l;
static int **memP, *nmemP, **memL, *nmemL;   /* memP[u]: entries (k*2 + (type==2)) for pairs with d(p_k,u) in {2,4} */
static inline void updA(int k, int x, int s) { if (s > 0) { if (cA[k][x]++ == 0) zeros--; } else { if (--cA[k][x] == 0) zeros++; } }
static inline void updB(int k, int t, int s) { if (s > 0) { if (cB[k][t]++ == 0) zeros--; } else { if (--cB[k][t] == 0) zeros++; } }
static void contribA(int k, int ty, int L, int s) {
    uint8_t *h = hdp[k];
    if (ty == 4) { if (h[N + L] != 5) return; for (int a = 0; a < Q1; a++) { int x = LP[L * Q1 + a]; if (h[x] == 6) updA(k, x, s); } return; }
    for (int a = 0; a < Q1; a++) { int y = LP[L * Q1 + a]; if (h[y] == 6) updA(k, y, s);
        for (int b = 0; b < Q1; b++) { int L2 = PL[y * Q1 + b]; if (L2 == L) continue;
            for (int c = 0; c < Q1; c++) { int x = LP[L2 * Q1 + c]; if (x != y && h[x] == 6) updA(k, x, s); } } }
}
static void contribB(int k, int ty, int y, int s) {
    uint8_t *h = hdl[k];
    if (ty == 4) { if (h[y] != 5) return; for (int a = 0; a < Q1; a++) { int t = PL[y * Q1 + a]; if (h[N + t] == 6) updB(k, t, s); } return; }
    for (int a = 0; a < Q1; a++) { int t = PL[y * Q1 + a]; if (h[N + t] == 6) updB(k, t, s);
        for (int b = 0; b < Q1; b++) { int x = LP[t * Q1 + b]; if (x == y) continue;
            for (int c = 0; c < Q1; c++) { int t2 = PL[x * Q1 + c]; if (t2 != t && h[N + t2] == 6) updB(k, t2, s); } } }
}
/* contribution of point u with line M[u] (side A) and of line L with preimage Minv[L] (side B) */
static void pointA(int u, int s) { if (isF[u]) return; for (int e = 0; e < nmemP[u]; e++) { int k = memP[u][e] >> 1, ty = (memP[u][e] & 1) ? 2 : 4; contribA(k, ty, M[u], s); } }
static void lineB(int L, int s) { int y = Minv[L]; if (isF[y]) return; for (int e = 0; e < nmemL[L]; e++) { int k = memL[L][e] >> 1, ty = (memL[L][e] & 1) ? 2 : 4; contribB(k, ty, y, s); } }
static void swapM(int u, int w) {   /* exchange the lines of points u and w, keeping the proxy counts current */
    int a = M[u], b = M[w];
    pointA(u, -1); pointA(w, -1); lineB(a, -1); lineB(b, -1);
    M[u] = b; M[w] = a; Minv[b] = u; Minv[a] = w;
    pointA(u, +1); pointA(w, +1); lineB(a, +1); lineB(b, +1);
}
static int BESTK = 1, nodrop = 0;
static double repairsec = 30;
static uint8_t *activeP;   /* adaptive dropping: inactive pairs no longer count and their extra edges are back */
static long pair_zeros(int k) {
    long z = 0;
    for (int a = 0; a < noppA[k]; a++) z += cA[k][oppA[k][a]] == 0;
    for (int a = 0; a < noppB[k]; a++) z += cB[k][oppB[k][a]] == 0;
    return z;
}
static void hubgraph_static(int k_src, int s);
static void deactivate(int k) {   /* drop pair k inside the fast search */
    zeros -= pair_zeros(k);
    for (int a = 0; a < noppA[k]; a++) cA[k][oppA[k][a]] = 1000;   /* never zero again */
    for (int a = 0; a < noppB[k]; a++) cB[k][oppB[k][a]] = 1000;
    if (!getenv("NOHGSTATIC")) hubgraph_static(k, -1);   /* its hubs disappear */
    activeP[k] = 0;
    int p = F[k]; isF[p] = 0;               /* p and its line M(p) contribute routes again */
    pointA(p, +1); lineB(M[p], +1);
}

/* static coverage through the hub graph (independent of M):
   side A of pair j: (p_j,0) -> z_j -> z'_k -> (l_k,i) then 3 more steps: points within distance 3 of l_k, at every level;
   side B of pair k: (l_k,0) -> z'_k -> z_j -> (p_j,i) then 3 more steps: lines within distance 3 of p_j. */
static void hubgraph_static(int k_src, int s) {   /* add (s=+1) or remove (s=-1) the coverage that pair k_src's hubs give */
    if (!HGm) return;
    int *buf = malloc(sizeof(int) * 4 * Q1 * Q1 * Q1);
    /* pair k_src's point-side hub z'_ksrc helps side A of every line-side neighbour j */
    for (int t = 0; t < HGPn[k_src]; t++) {
        int j = HGP[k_src][t]; if (!activeP[j] || j == k_src) continue;
        int np = ball3_points_of_line(M[F[k_src]], buf);
        for (int a = 0; a < np; a++) { int x = buf[a]; if (hdp[j][x] == 6) updA(j, x, s); }
    }
    /* pair k_src's line-side hub z_ksrc helps side B of every point-side neighbour k */
    for (int t = 0; t < HGLn[k_src]; t++) {
        int k = HGL[k_src][t]; if (!activeP[k] || k == k_src) continue;
        int nl = ball3_lines_of_point(F[k_src], buf);
        for (int a = 0; a < nl; a++) { int x = buf[a]; if (hdl[k][N + x] == 6) updB(k, x, s); }
    }
    free(buf);
}
static int fsK = -1;
static void fs_free(void) {   /* release the proxy structures of the previous fast_search call */
    if (fsK < 0) return;
    for (int k = 0; k < fsK; k++) { free(cA[k]); free(cB[k]); free(oppA[k]); free(oppB[k]); free(n4p[k]); free(n2p[k]); free(n4l[k]); free(n2l[k]); }
    free(cA); free(cB); free(oppA); free(oppB); free(noppA); free(noppB); free(n4p); free(n2p); free(n4l); free(n2l);
    free(nn4p); free(nn2p); free(nn4l); free(nn2l);
    for (int v = 0; v < N; v++) { free(memP[v]); free(memL[v]); }
    free(memP); free(memL); free(nmemP); free(nmemL); free(activeP);
    fsK = -1;
}
static long fast_search(double maxsec) {
    if (getenv("BESTK")) BESTK = atoi(getenv("BESTK"));
    fs_free(); fsK = K;
    activeP = malloc(K + 1); memset(activeP, 1, K + 1);
    cA = malloc(sizeof(uint16_t *) * K); cB = malloc(sizeof(uint16_t *) * K);
    oppA = malloc(sizeof(int *) * K); oppB = malloc(sizeof(int *) * K); noppA = calloc(K, sizeof(int)); noppB = calloc(K, sizeof(int));
    n4p = malloc(sizeof(int *) * K); n2p = malloc(sizeof(int *) * K); n4l = malloc(sizeof(int *) * K); n2l = malloc(sizeof(int *) * K);
    nn4p = calloc(K, sizeof(int)); nn2p = calloc(K, sizeof(int)); nn4l = calloc(K, sizeof(int)); nn2l = calloc(K, sizeof(int));
    nmemP = calloc(N, sizeof(int)); nmemL = calloc(N, sizeof(int));
    for (int k = 0; k < K; k++) for (int v = 0; v < N; v++) {
        if (hdp[k][v] == 2 || hdp[k][v] == 4) nmemP[v]++;
        if (hdl[k][N + v] == 2 || hdl[k][N + v] == 4) nmemL[v]++;
    }
    memP = malloc(sizeof(int *) * N); memL = malloc(sizeof(int *) * N);
    for (int v = 0; v < N; v++) { memP[v] = malloc(sizeof(int) * (nmemP[v] + 1)); memL[v] = malloc(sizeof(int) * (nmemL[v] + 1)); nmemP[v] = nmemL[v] = 0; }
    zeros = 0;
    for (int k = 0; k < K; k++) {
        cA[k] = calloc(N, sizeof(uint16_t)); cB[k] = calloc(N, sizeof(uint16_t));
        oppA[k] = malloc(sizeof(int) * N); oppB[k] = malloc(sizeof(int) * N);
        n4p[k] = malloc(sizeof(int) * N); n2p[k] = malloc(sizeof(int) * N); n4l[k] = malloc(sizeof(int) * N); n2l[k] = malloc(sizeof(int) * N);
        for (int v = 0; v < N; v++) {
            int dp = hdp[k][v], dl = hdl[k][N + v];
            if (dp == 6) { oppA[k][noppA[k]++] = v; zeros++; }
            if (hdl[k][N + v] == 6) { oppB[k][noppB[k]++] = v; zeros++; }
            if (dp == 4 && !isF[v]) n4p[k][nn4p[k]++] = v;
            if (dp == 2 && !isF[v]) n2p[k][nn2p[k]++] = v;
            if (dl == 4) n4l[k][nn4l[k]++] = v;
            if (dl == 2) n2l[k][nn2l[k]++] = v;
            if (dp == 2 || dp == 4) memP[v][nmemP[v]++] = k * 2 + (dp == 2);
            if (dl == 2 || dl == 4) memL[v][nmemL[v]++] = k * 2 + (dl == 2);
        }
    }
    for (int u = 0; u < N; u++) pointA(u, +1);
    for (int L = 0; L < N; L++) lineB(L, +1);
    if (!getenv("NOHGSTATIC")) for (int k = 0; k < K; k++) hubgraph_static(k, +1);
    fprintf(stderr, "fast search: proxy cost %ld\n", zeros);
    clock_t t0 = clock(); long it = 0, best = zeros; double T0 = 0.6;
    int zcap = 4000; long *zl = malloc(sizeof(long) * zcap); int nz = 0; long lastchk = 1L << 60;
    double pexh = getenv("PEXH") ? atof(getenv("PEXH")) : 0;   /* probability of an exhaustive endgame move */
    double dropsec = (getenv("DROPSEC") && !nodrop) ? atof(getenv("DROPSEC")) : 0, lastimp = 0; int nactive = K;
    long impref = zeros;
    double dropstart = getenv("DROPSTART") ? atof(getenv("DROPSTART")) : 0;   /* no dropping before this many seconds */
    while (zeros > 0) {
        it++;
        if ((it & 1023) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > maxsec) break;
            if (dropsec > 0 && el > dropstart && el - lastimp > dropsec) {   /* stalled: drop the active pair with most uncovered targets */
                int w = -1; long wz = 0;
                for (int kk = 0; kk < K; kk++) if (activeP[kk]) { long z = pair_zeros(kk); if (z > wz) { wz = z; w = kk; } }
                if (w >= 0) { deactivate(w); nactive--; fprintf(stderr, "drop pair %d (%ld uncovered): %d active, proxy %ld (%.0fs)\n", w, wz, nactive, zeros, el); }
                lastimp = el; best = zeros; impref = zeros; nz = 0;
            }
            if ((it & ((1 << 20) - 1)) == 0) fprintf(stderr, "it %ld proxy %ld best %ld (%.0fs)\n", it, zeros, best, el);
        }
        double T = T0 * (1.0 - (double)(clock() - t0) / CLOCKS_PER_SEC / maxsec); if (T < 0.05) T = 0.05;
        int k, side, tgt = -1;
        if (zeros <= zcap) {   /* few targets left: keep an explicit list, refreshed when stale; check the true cost now and then */
            if (nz == 0 || (it & 4095) == 0) {
                nz = 0;
                for (int kk = 0; kk < K; kk++) {
                    for (int a = 0; a < noppA[kk]; a++) if (cA[kk][oppA[kk][a]] == 0 && nz < zcap) zl[nz++] = (long)kk * 2 * N + oppA[kk][a];
                    for (int a = 0; a < noppB[kk]; a++) if (cB[kk][oppB[kk][a]] == 0 && nz < zcap) zl[nz++] = (long)kk * 2 * N + N + oppB[kk][a];
                }
                if (zeros < lastchk && (zeros < 64 || zeros * 5 < lastchk * 4)) {   /* exact BFS check of all freed sources (only after real progress) */
                    lastchk = zeros; long tc = 0; for (int kk = 0; kk < K; kk++) { int a, b; tc += cost_of(kk, &a, &b); }
                    if (tc == 0) { fprintf(stderr, "true cost 0 at proxy %ld\n", zeros); break; }
                }
                if (nz == 0) continue;
            }
            long e = zl[rndi(nz)]; k = (int)(e / (2 * N)); int r = (int)(e % (2 * N));
            side = r >= N; tgt = side ? r - N : r;
            if ((side == 0 ? cA[k][tgt] : cB[k][tgt]) != 0) continue;
        } else {
            k = rndi(K); if (!activeP[k]) continue; side = rndi(2);
            int n = side == 0 ? noppA[k] : noppB[k]; int *lst = side == 0 ? oppA[k] : oppB[k]; uint16_t *cc = side == 0 ? cA[k] : cB[k];
            for (int tr = 0; tr < 64; tr++) { int v = lst[rndi(n)]; if (cc[v] == 0) { tgt = v; break; } }
            if (tgt < 0) continue;
        }
        int nbest = BESTK, bu = -1, bw = -1; long bd = 1L << 60;
        if (zeros <= zcap && pexh > 0 && (double)(rnd() % 1000000) / 1e6 < pexh) {
            /* endgame: try every type-4 candidate for this target and keep the best */
            if (side == 0) {
                for (int a = 0; a < nn4p[k]; a++) { int u = n4p[k][a];
                    for (int b2 = 0; b2 < Q1; b2++) { int bl = PL[tgt * Q1 + b2], w = Minv[bl];
                        if (u == w || isF[u] || isF[w]) continue;
                        long before = zeros; swapM(u, w); long d = zeros - before; swapM(u, w);
                        if (d < bd) { bd = d; bu = u; bw = w; } } }
            } else {
                for (int a = 0; a < nn4l[k]; a++) { int L = n4l[k][a], w = Minv[L];
                    for (int b2 = 0; b2 < Q1; b2++) { int y = LP[tgt * Q1 + b2];
                        if (y == w || isF[y] || isF[w]) continue;
                        long before = zeros; swapM(y, w); long d = zeros - before; swapM(y, w);
                        if (d < bd) { bd = d; bu = y; bw = w; } } }
            }
            nbest = 0;   /* skip the random candidates */
        }
        for (int cand = 0; cand < nbest; cand++) {
        int u, w, ty4 = rndi(8) != 0;
        if (side == 0) {      /* make some line through (or near) x the image of a point near p */
            int x = tgt, b;
            if (ty4) { if (!nn4p[k]) continue; u = n4p[k][rndi(nn4p[k])]; b = PL[x * Q1 + rndi(Q1)]; }
            else { if (!nn2p[k]) continue; u = n2p[k][rndi(nn2p[k])]; int L1 = PL[x * Q1 + rndi(Q1)]; int y = LP[L1 * Q1 + rndi(Q1)]; b = PL[y * Q1 + rndi(Q1)]; }
            w = Minv[b];
        } else {              /* make a point on (or near) t the preimage of a line near l */
            int t = tgt, L, y;
            if (ty4) { if (!nn4l[k]) continue; L = n4l[k][rndi(nn4l[k])]; y = LP[t * Q1 + rndi(Q1)]; }
            else { if (!nn2l[k]) continue; L = n2l[k][rndi(nn2l[k])]; int x1 = LP[t * Q1 + rndi(Q1)]; int t1 = PL[x1 * Q1 + rndi(Q1)]; y = LP[t1 * Q1 + rndi(Q1)]; }
            u = y; w = Minv[L];
        }
        if (u == w || isF[u] || isF[w]) continue;
        long before = zeros;
        swapM(u, w);
        long d = zeros - before;
        swapM(u, w);
        if (d < bd) { bd = d; bu = u; bw = w; }
        }
        if (bu < 0) continue;
        if (bd <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-bd / T)) swapM(bu, bw);
        if (zeros < best) { best = zeros; if (best < impref - impref / 50 - 1) { impref = best; lastimp = (double)(clock() - t0) / CLOCKS_PER_SEC; } }
    }
    fprintf(stderr, "fast search done: it %ld proxy %ld (%.1fs)\n", it, zeros, (double)(clock() - t0) / CLOCKS_PER_SEC);
    return zeros;
}


/* BFS-based targeted local search on the freed sources (exact costs); returns the final cost */
static int bfs_phase(double bfsec, int *per, int *per2, int *badlist, int cost) {
    clock_t t0 = clock(); long it = 0, acc = 0;
    while (cost > 0 && (double)(clock() - t0) / CLOCKS_PER_SEC < bfsec) {
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
        /* evaluate the targeted pair first; reject cheaply if it got worse, otherwise re-evaluate all pairs */
        int a0, b0, cj = cost_of(j, &a0, &b0), c2 = -1;
        if (cj <= per[j]) c2 = total_cost(per2);
        if (c2 >= 0 && c2 <= cost) { cost = c2; memcpy(per, per2, sizeof(int) * K); acc++; }
        else { M[u] = oldl; Minv[oldl] = u; M[w] = newl; Minv[newl] = w; }
        if (it % 500 == 0) fprintf(stderr, "it %ld acc %ld cost %d  (%.1fs)\n", it, acc, cost, (double)(clock() - t0) / CLOCKS_PER_SEC);
    }
    fprintf(stderr, "search done: it %ld cost %d (%.1fs)\n", it, cost, (double)(clock() - t0) / CLOCKS_PER_SEC);
    return cost;
}


/* ---------- growth mode (GROW=Kmax): add freed pairs one at a time to a solved configuration ---------- */
/* opposite targets of a candidate pair (p, l) left uncovered by the type-4 / type-2 routes of the current M */
static long cand_uncovered(int p, int l, uint8_t *dp, uint8_t *dl, uint8_t *mark, int *buf) {
    hbfs(p, 0, dp); hbfs(l, 1, dl);
    memset(mark, 0, 2 * N);
    for (int u = 0; u < N; u++) {
        if (isF[u] || u == p) continue;
        int L = M[u];
        if (dp[u] == 4 && dp[N + L] == 5) for (int a = 0; a < Q1; a++) { int x = LP[L * Q1 + a]; if (dp[x] == 6) mark[x] = 1; }
        else if (dp[u] == 2) { int np = ball3_points_of_line(L, buf); for (int a = 0; a < np; a++) if (dp[buf[a]] == 6) mark[buf[a]] = 1; }
    }
    for (int L = 0; L < N; L++) {
        int y = Minv[L]; if (isF[y] || L == l) continue;
        if (dl[N + L] == 4 && dl[y] == 5) for (int a = 0; a < Q1; a++) { int t = PL[y * Q1 + a]; if (dl[N + t] == 6) mark[N + t] = 1; }
        else if (dl[N + L] == 2) { int nl = ball3_lines_of_point(y, buf); for (int a = 0; a < nl; a++) if (dl[N + buf[a]] == 6) mark[N + buf[a]] = 1; }
    }
    long unc = 0;
    for (int x = 0; x < N; x++) { if (dp[x] == 6 && !mark[x]) unc++; if (dl[N + x] == 6 && !mark[N + x]) unc++; }
    return unc;
}
static int HGcap = 0;
static void hg_rebuild_cap(int cap) {   /* adjacency of the hub graph for hubs 0..cap-1 (edge list HGj/HGk) */
    if (HGcap < cap) {
        HGL = realloc(HGL, sizeof(int *) * cap); HGP = realloc(HGP, sizeof(int *) * cap);
        HGLn = realloc(HGLn, sizeof(int) * cap); HGPn = realloc(HGPn, sizeof(int) * cap);
        for (int j = HGcap; j < cap; j++) { HGL[j] = malloc(sizeof(int) * 16); HGP[j] = malloc(sizeof(int) * 16); }
        HGcap = cap;
    }
    for (int j = 0; j < HGcap; j++) HGLn[j] = HGPn[j] = 0;
    for (int e = 0; e < HGm; e++) { HGL[HGj[e]][HGLn[HGj[e]]++] = HGk[e]; HGP[HGk[e]][HGPn[HGk[e]]++] = HGj[e]; }
}
static int hg_has(int j, int k) { for (int t = 0; t < HGLn[j]; t++) if (HGL[j][t] == k) return 1; return 0; }
/* same-side hubs must be within 6: hub-graph distance <= 4, or freed points (lines) within hexagon distance 4.
   Returns the number of same-side pairs involving hub k that violate this. side 0: line-side hubs z, 1: point-side z'. */
static int hub_violations(int k, int side) {
    int n2 = 2 * K, *d = malloc(sizeof(int) * n2), *qq = malloc(sizeof(int) * n2), h = 0, t = 0, bad = 0;
    for (int v = 0; v < n2; v++) d[v] = -1;
    int s = side == 0 ? k : K + k; d[s] = 0; qq[t++] = s;   /* ids: line-side hub j = j, point-side hub j = K + j */
    while (h < t) { int v = qq[h++]; if (d[v] >= 4) continue;
        if (v < K) { for (int a = 0; a < HGLn[v]; a++) { int w = K + HGL[v][a]; if (d[w] < 0) { d[w] = d[v] + 1; qq[t++] = w; } } }
        else { int j = v - K; for (int a = 0; a < HGPn[j]; a++) { int w = HGP[j][a]; if (d[w] < 0) { d[w] = d[v] + 1; qq[t++] = w; } } } }
    for (int j = 0; j < K; j++) {
        if (j == k) continue;
        int dv = side == 0 ? d[j] : d[K + j];
        if (dv >= 0 && dv <= 4) continue;
        int hex = side == 0 ? hdp[k][F[j]] : hdl[k][N + M[F[j]]];
        if (hex <= 4) continue;
        bad++;
    }
    free(d); free(qq); return bad;
}
/* add hub-graph edges for the new pair k: z_k to point-side hubs, z'_k to line-side hubs (spare degree q-1) */
static void hg_add_new(int k, int deg) {
    int maxdeg = q - 1;
    for (int side = 0; side < 2; side++) {
        int added = 0;
        for (int att = 0; att < 200 && added < deg && k > 0; att++) {
            int bj = -1, bd = 99;
            for (int s = 0; s < 6; s++) { int j = rndi(k); int dj = side == 0 ? HGPn[j] : HGLn[j];
                if (dj >= maxdeg) continue; if (side == 0 ? hg_has(k, j) : hg_has(j, k)) continue;
                if (dj < bd) { bd = dj; bj = j; } }
            if (bj < 0) continue;
            if (side == 0) { HGj[HGm] = k; HGk[HGm] = bj; } else { HGj[HGm] = bj; HGk[HGm] = k; }
            HGm++; added++;
            hg_rebuild_cap(HGcap);
        }
    }
}

/* drop freed pair j: restore its extra edges, delete its two hubs, re-index (the last pair takes index j) */
static void drop_pair(int j) {
    int last = K - 1;
    isF[F[j]] = 0;
    if (j != last) { F[j] = F[last]; isF[F[j]] = j + 1; uint8_t *t = hdp[j]; hdp[j] = hdp[last]; hdp[last] = t; t = hdl[j]; hdl[j] = hdl[last]; hdl[last] = t; }
    int m2 = 0;
    for (int e = 0; e < HGm; e++) {
        int a = HGj[e], b = HGk[e];
        if (a == j || b == j) continue;
        if (a == last) a = j; if (b == last) b = j;
        HGj[m2] = a; HGk[m2] = b; m2++;
    }
    HGm = m2; K = last; NV = 6 * N + 2 * K;
    for (int t = 0; t <= K; t++) { HGLn[t] = HGPn[t] = 0; }
    for (int e = 0; e < HGm; e++) { HGL[HGj[e]][HGLn[HGj[e]]++] = HGk[e]; HGP[HGk[e]][HGPn[HGk[e]]++] = HGj[e]; }
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
    if (!strcmp(argv[1], "super")) {   /* d7hex super HEXBIN SOL OUTEDGES seed tries: add super-hubs, keep those with ecc <= 7 */
        read_sol(argv[3]);
        rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
        int tries = atoi(argv[6]), cap = 4 * K + 64;
        free(dist); free(que); dist = malloc(6 * N + 2 * K + cap); que = malloc(sizeof(int) * (6 * N + 2 * K + cap));
        SHn = calloc(cap, sizeof(int)); SHnb = malloc(sizeof(int *) * cap); for (int s = 0; s < cap; s++) SHnb[s] = malloc(sizeof(int) * 16);
        HXn = calloc(2 * K, sizeof(int)); HX = malloc(sizeof(int *) * 2 * K); for (int h = 0; h < 2 * K; h++) HX[h] = malloc(sizeof(int) * 16);
        int base = 6 * N + 2 * K, nb[64];
        int *spare = malloc(sizeof(int) * 2 * K);
        for (int h = 0; h < 2 * K; h++) spare[h] = q + 2 - nbrs(6 * N + h, nb);
        /* 4-balls: for line-side hubs, points within distance 4 of the freed point; for point-side hubs, lines within 4 of the freed line */
        uint8_t **ball = malloc(sizeof(uint8_t *) * 2 * K), *tmp = malloc(2 * N);
        for (int j = 0; j < K; j++) {
            ball[j] = malloc(N); hbfs(F[j], 0, tmp); for (int x = 0; x < N; x++) ball[j][x] = tmp[x] <= 4;
            ball[K + j] = malloc(N); hbfs(M[F[j]], 1, tmp); for (int x = 0; x < N; x++) ball[K + j][x] = tmp[N + x] <= 4;
        }
        uint8_t *cov = malloc(N); int added[2] = {0, 0};
        for (int side = 0; side < 2; side++) {   /* side 0: point-side super-hubs on line-side hubs 0..K-1; side 1: the reverse */
            int fails = 0;
            while (fails < tries) {
                memset(cov, 0, N); int ncov = 0, set[16], ns = 0;
                while (ns < q + 2 && ncov < N) {
                    int bh = -1, bg = -1;
                    for (int h0 = 0; h0 < K; h0++) {
                        int h = side * K + h0; if (spare[h] <= 0) continue;
                        int dup = 0; for (int t = 0; t < ns; t++) if (set[t] == h) dup = 1; if (dup) continue;
                        int g = 0; for (int x = 0; x < N; x++) g += ball[h][x] && !cov[x];
                        g = g * 16 + (int)(rnd() % 16);
                        if (g > bg) { bg = g; bh = h; }
                    }
                    if (bh < 0 || bg < 16) break;
                    set[ns++] = bh; for (int x = 0; x < N; x++) if (ball[bh][x] && !cov[x]) { cov[x] = 1; ncov++; }
                }
                if (ncov < N) { fails++; continue; }
                /* tentatively add */
                int s = NSH, v = base + s; SHn[s] = ns;
                for (int t = 0; t < ns; t++) { SHnb[s][t] = 6 * N + set[t]; HX[set[t]][HXn[set[t]]++] = v; }
                NSH++; NV = base + NSH;
                int e; bfs(v, 7, &e);
                if (e <= 7) { for (int t = 0; t < ns; t++) spare[set[t]]--; added[side]++; fails = 0;
                              fprintf(stderr, "super-hub %d (side %d, %d hubs): ecc %d\n", s, side, ns, e); }
                else { for (int t = 0; t < ns; t++) HXn[set[t]]--; NSH--; NV = base + NSH; fails++; }
            }
        }
        /* eccentricities of all hubs and super-hubs (other vertices can only get closer) */
        int worst = 0, badh = 0;
        for (int v = 6 * N; v < NV; v++) { int e; bfs(v, 7, &e); if (e > worst) worst = e; if (e > 7) badh++; }
        fprintf(stderr, "added %d + %d super-hubs; n = %d; hubs/super-hubs with ecc > 7: %d (worst %d)\n", added[0], added[1], NV, badh, worst);
        FILE *f = fopen(argv[4], "w"); fprintf(f, "%d\n", NV); long m = 0;
        for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); for (int k2 = 0; k2 < c; k2++) if (nb[k2] > v) { fprintf(f, "%d %d\n", v, nb[k2]); m++; } }
        fclose(f); fprintf(stderr, "wrote %s: n=%d edges=%ld\n", argv[4], NV, m);
        /* record the super-hubs */
        char fn2[512]; snprintf(fn2, sizeof fn2, "%s.super", argv[4]); f = fopen(fn2, "w");
        fprintf(f, "superhubs %d\n", NSH); for (int s = 0; s < NSH; s++) { fprintf(f, "%d", SHn[s]); for (int t = 0; t < SHn[s]; t++) fprintf(f, " %d", SHnb[s][t] - 6 * N); fprintf(f, "\n"); }
        fclose(f);
        return 0;
    }
    if (strcmp(argv[1], "search")) return 1;
    K = atoi(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    double maxsec = atof(argv[5]);
    const char *out = argc > 6 ? argv[6] : NULL;
    int mode = argc > 7 ? atoi(argv[7]) : 0, alg = argc > 8 ? atoi(argv[8]) : 1;
    /* random bijection M */
    M = malloc(sizeof(int) * N); Minv = malloc(sizeof(int) * N);
    for (int p = 0; p < N; p++) M[p] = p;
    for (int p = N - 1; p > 0; p--) { int r = rndi(p + 1); int t = M[p]; M[p] = M[r]; M[r] = t; }
    for (int p = 0; p < N; p++) Minv[M[p]] = p;
    /* freed points.
       mode 0: greedy pairwise opposite, M(p) random (hubs of one side are then 8 apart when K > 1: invalid for K > 1)
       mode 1: star: a centre point c, freed p_j on distinct lines l_j through c (p_j != c), M(p_j) = l_j (K <= q+1);
               freed points pairwise at distance 4, freed lines pairwise at distance 2, so all hubs are within 7.
       In both modes the algebraic cover is installed for each pair (p, l = M(p) with p on l):
         S'(p) = points u with d(p,u) = 4, d(l,u) = 5;  S(l) = lines N with d(l,N) = 4, d(p,N) = 5;  M maps S'(p) onto S(l).
       Then every point opposite p lies on exactly one line of S and every line opposite l contains exactly one point
       of S', so (p,0) ~> (u,0) -> (M(u),1) -> (x,1) and (l,0) ~> (M(y),0) -> (y,-1) -> (t,-1) cover what the hubs miss. */
    F = malloc(sizeof(int) * (K + 1)); isF = calloc(N, sizeof(int));
    uint8_t *tmp = malloc(2 * N); uint8_t *ok = malloc(N); memset(ok, 1, N);
    int *fl = malloc(sizeof(int) * (K + 1));
    if (mode == 1) {
        int c = rndi(N); if (K > Q1) K = Q1;
        int perm[64]; for (int k = 0; k < Q1; k++) perm[k] = k;
        for (int k = Q1 - 1; k > 0; k--) { int r = rndi(k + 1); int t = perm[k]; perm[k] = perm[r]; perm[r] = t; }
        for (int j = 0; j < K; j++) {
            int l = PL[c * Q1 + perm[j]]; int p;
            do { p = LP[l * Q1 + rndi(Q1)]; } while (p == c);
            F[j] = p; isF[p] = j + 1; fl[j] = l;
        }
    } else {
        int mind = 6;
        if (mode == 3) {   /* hub graph from file HGFILE (argv[10]): "K m" then m lines "j k" (line-side hub j ~ point-side hub k) */
            FILE *hf = fopen(argv[10], "r"); int kk;
            if (!hf || fscanf(hf, "%d %d", &kk, &HGm) != 2) { fprintf(stderr, "bad hub graph file\n"); return 1; }
            K = kk; HGj = malloc(sizeof(int) * (HGm + 1)); HGk = malloc(sizeof(int) * (HGm + 1));
            for (int e = 0; e < HGm; e++) if (fscanf(hf, "%d %d", &HGj[e], &HGk[e]) != 2) return 1;
            fclose(hf);
            F = realloc(F, sizeof(int) * (K + 1)); fl = realloc(fl, sizeof(int) * (K + 1));
            hg_build();
            for (int j = 0; j < K; j++) if (HGLn[j] > q - 1 || HGPn[j] > q - 1) { fprintf(stderr, "hub %d degree > q-1\n", j); return 1; }
            mind = argc > 9 ? atoi(argv[9]) : 4;
        }
        if (mode == 2) {   /* hub graph PG(2,q-2): K = (q-2)^2+(q-2)+1 pairs anywhere; freed points pairwise >= mind apart */
            int r = q - 2, n = hg_pg2(r);
            if (K > n) K = n;
            if (K < n) { int m2 = 0; for (int e = 0; e < HGm; e++) if (HGj[e] < K && HGk[e] < K) { HGj[m2] = HGj[e]; HGk[m2] = HGk[e]; m2++; } HGm = m2; }
            hg_build();
            mind = argc > 9 ? atoi(argv[9]) : 4;
        }
        if (getenv("OPPFLAGS")) {   /* freed flags pairwise opposite: d(p,p') = d(l,l') = 6, d(p,l') = d(p',l) = 5 */
            /* GREEDYFLAGS=c: each new flag is the best of c opposite candidates for the membership-vector mismatch */
            int gc = getenv("GREEDYFLAGS") ? atoi(getenv("GREEDYFLAGS")) : 1; if (gc < 1) gc = 1;
            uint8_t **dp_ = malloc(sizeof(uint8_t *) * K), **dl_ = malloc(sizeof(uint8_t *) * K);
            v128 *mP = calloc(N, sizeof(v128)), *mL = calloc(N, sizeof(v128)), *cP = malloc(sizeof(v128) * N), *cL = malloc(sizeof(v128) * N);
            v128 *tp = malloc(sizeof(v128) * N), *tl = malloc(sizeof(v128) * N);
            uint8_t *cdp = malloc(2 * N), *cdl = malloc(2 * N), *bdp = malloc(2 * N), *bdl = malloc(2 * N);
            int placed = 0; long tries = 0;
            while (placed < K && tries < 400000000L) {
                long bestmm = -1; int bp = -1, bl = -1, found = 0;
                while (found < gc && tries < 400000000L) {
                    tries++;
                    int p = rndi(N), l = PL[p * Q1 + rndi(Q1)], good = 1;
                    for (int i = 0; i < placed && good; i++)
                        if (dp_[i][p] != 6 || dl_[i][N + l] != 6 || dp_[i][N + l] != 5 || dl_[i][p] != 5) good = 0;
                    if (!good) continue;
                    found++;
                    hbfs(p, 0, cdp); hbfs(l, 1, cdl);
                    long mm = 0;
                    if (gc > 1) {
                        memcpy(cP, mP, sizeof(v128) * N); memcpy(cL, mL, sizeof(v128) * N);
                        for (int u = 0; u < N; u++) { if (cdp[u] == 4 && cdl[u] == 5) vset(&cP[u], placed); if (cdl[N + u] == 4 && cdp[N + u] == 5) vset(&cL[u], placed); }
                        mm = mismatch(cP, cL, N, tp, tl);
                    }
                    if (bestmm < 0 || mm < bestmm) { bestmm = mm; bp = p; bl = l; uint8_t *t = cdp; cdp = bdp; bdp = t; t = cdl; cdl = bdl; bdl = t; }
                }
                if (bp < 0) break;
                F[placed] = bp; isF[bp] = placed + 1; fl[placed] = bl;
                dp_[placed] = malloc(2 * N); memcpy(dp_[placed], bdp, 2 * N); dl_[placed] = malloc(2 * N); memcpy(dl_[placed], bdl, 2 * N);
                for (int u = 0; u < N; u++) { if (bdp[u] == 4 && bdl[u] == 5) vset(&mP[u], placed); if (bdl[N + u] == 4 && bdp[N + u] == 5) vset(&mL[u], placed); }
                if (gc > 1) fprintf(stderr, "flag %d: (%d,%d) mismatch %ld (tries %ld)\n", placed, bp, bl, bestmm, tries);
                placed++;
            }
            if (placed < K) { fprintf(stderr, "could only place %d opposite flags\n", placed); K = placed; }
        } else
        for (int j = 0; j < K; j++) {
            int p = -1;
            for (int tries = 0; tries < 100000; tries++) { int c = rndi(N); if (ok[c]) { p = c; break; } }
            if (p < 0) { fprintf(stderr, "could only place %d freed points\n", j); K = j; break; }
            F[j] = p; isF[p] = j + 1; fl[j] = PL[p * Q1 + rndi(Q1)];
            hbfs(p, 0, tmp); for (int x = 0; x < N; x++) if (tmp[x] < mind) ok[x] = 0;
        }
    }
    /* install M(p_j) = l_j */
    for (int j = 0; j < K; j++) { int p = F[j], l = fl[j], w = Minv[l], o = M[p]; M[p] = l; Minv[l] = p; M[w] = o; Minv[o] = w; }
    alloc_graph();
    hdp = malloc(sizeof(uint8_t *) * K); hdl = malloc(sizeof(uint8_t *) * K);
    for (int j = 0; j < K; j++) { hdp[j] = malloc(2 * N); hbfs(F[j], 0, hdp[j]); hdl[j] = malloc(2 * N); hbfs(M[F[j]], 1, hdl[j]); }
    if (alg == 4 && K > 128) { fprintf(stderr, "alg 4 supports K <= 128\n"); return 1; }
    if (alg == 4) {   /* joint algebraic cover: M maps each point to a line with the same membership vector */
        vitem *ip = malloc(sizeof(vitem) * N), *il = malloc(sizeof(vitem) * N); int np = 0, nl = 0;
        uint8_t *usedL = calloc(N, 1); for (int j = 0; j < K; j++) usedL[M[F[j]]] = 1;
        for (int u = 0; u < N; u++) if (!isF[u]) { ip[np].v.a = ip[np].v.b = 0; ip[np].id = u; ip[np].r = (uint32_t)rnd(); np++; }
        for (int L = 0; L < N; L++) if (!usedL[L]) { il[nl].v.a = il[nl].v.b = 0; il[nl].id = L; il[nl].r = (uint32_t)rnd(); nl++; }
        for (int k = 0; k < K; k++) {
            for (int a = 0; a < np; a++) { int u = ip[a].id; if (hdp[k][u] == 4 && hdl[k][u] == 5) vset(&ip[a].v, k); }
            for (int a = 0; a < nl; a++) { int L = il[a].id; if (hdl[k][N + L] == 4 && hdp[k][N + L] == 5) vset(&il[a].v, k); }
        }
        for (int a = 0; a < np; a++) ip[a].pc = __builtin_popcountll(ip[a].v.a) + __builtin_popcountll(ip[a].v.b);
        for (int a = 0; a < nl; a++) il[a].pc = __builtin_popcountll(il[a].v.a) + __builtin_popcountll(il[a].v.b);
        qsort(ip, np, sizeof(vitem), cmpitem); qsort(il, nl, sizeof(vitem), cmpitem);
        vitem *lp = malloc(sizeof(vitem) * N), *ll = malloc(sizeof(vitem) * N); int nlp = 0, nll = 0, matched = 0;
        int i = 0, j = 0;
        while (i < np || j < nl) {
            int c = (i >= np) ? 1 : (j >= nl) ? -1 : vcmp(&ip[i].v, &il[j].v);
            if (c == 0) {
                v128 v = ip[i].v; int i2 = i, j2 = j;
                while (i2 < np && !vcmp(&ip[i2].v, &v)) i2++;
                while (j2 < nl && !vcmp(&il[j2].v, &v)) j2++;
                int m = (i2 - i < j2 - j) ? i2 - i : j2 - j;
                for (int t = 0; t < m; t++) { M[ip[i + t].id] = il[j + t].id; matched++; }
                for (int t = m; t < i2 - i; t++) lp[nlp++] = ip[i + t];
                for (int t = m; t < j2 - j; t++) ll[nll++] = il[j + t];
                i = i2; j = j2;
            } else if (c < 0) lp[nlp++] = ip[i++];
            else ll[nll++] = il[j++];
        }
        qsort(lp, nlp, sizeof(vitem), cmpitem_pc); qsort(ll, nll, sizeof(vitem), cmpitem_pc);
        for (int t = 0; t < nlp; t++) M[lp[t].id] = ll[t].id;
        for (int p = 0; p < N; p++) Minv[M[p]] = p;
        fprintf(stderr, "joint algebraic cover: %d points matched by vector, %d leftovers\n", matched, nlp);
        free(ip); free(il); free(lp); free(ll); free(usedL);
    }
    if (alg && alg != 4) {
        uint8_t *lockp = calloc(N, 1), *lockl = calloc(N, 1);
        for (int j = 0; j < K; j++) { lockp[F[j]] = 1; lockl[M[F[j]]] = 1; }
        if (alg >= 3) type2_prepass(lockp, lockl);
        int *Sp = malloc(sizeof(int) * N), *Sl = malloc(sizeof(int) * N); uint8_t *inS = calloc(N, 1), *used = calloc(N, 1);
        long conflicts = 0;
        for (int j = 0; j < K; j++) {
            int ns = 0, nl = 0;
            memset(inS, 0, N); memset(used, 0, N);
            for (int l = 0; l < N; l++) if (hdl[j][N + l] == 4 && hdp[j][N + l] == 5) { inS[l] = 1; Sl[nl++] = l; }
            for (int u = 0; u < N; u++) if (hdp[j][u] == 4 && hdl[j][u] == 5) Sp[ns++] = u;
            /* locked points already mapped into S(l_j) keep their line */
            int nfree = 0;
            for (int k = 0; k < ns; k++) { int u = Sp[k]; if (lockp[u]) { if (inS[M[u]] && !used[M[u]]) used[M[u]] = 1; else conflicts++; } else Sp[nfree++] = u; }
            int li = 0;
            for (int k = 0; k < nfree; k++) {
                while (li < nl && (used[Sl[li]] || lockl[Sl[li]])) li++;
                if (li >= nl) { conflicts += nfree - k; break; }
                int u = Sp[k], l = Sl[li++]; used[l] = 1;
                int w = Minv[l], o = M[u]; M[u] = l; Minv[l] = u; M[w] = o; Minv[o] = w;
                lockp[u] = 1; lockl[l] = 1;
            }
            if (j == 0 || j == K - 1) fprintf(stderr, "pair %d: |S'| = %d, |S| = %d\n", j, ns, nl);
        }
        fprintf(stderr, "algebraic cover installed, conflicts %ld\n", conflicts);
    }
    if (alg >= 2) {
        fast_search(maxsec * 0.9);
        if (getenv("DROPSEC")) {   /* remove the pairs dropped during the search */
            if (!HGm) { HGL = malloc(sizeof(int *) * (K + 1)); HGP = malloc(sizeof(int *) * (K + 1)); HGLn = calloc(K + 1, sizeof(int)); HGPn = calloc(K + 1, sizeof(int)); HGj = malloc(sizeof(int)); HGk = malloc(sizeof(int)); }
            for (int j = K - 1; j >= 0; j--) if (!activeP[j]) {
                int last = K - 1; isF[F[j]] = j + 1;   /* drop_pair expects it freed */
                drop_pair(j); activeP[j] = activeP[last];
            }
            fprintf(stderr, "after dropping: K=%d n=%d\n", K, 6 * N + 2 * K);
        }
    }
    int *per = malloc(sizeof(int) * K), *per2 = malloc(sizeof(int) * K);
    int cost = total_cost(per);
    fprintf(stderr, "q=%d N=%d K=%d n=%d initial cost %d\n", q, N, K, NV, cost);
    int *badlist = malloc(sizeof(int) * NV);
    double bfsec = alg >= 2 ? 0.1 * maxsec : maxsec;   /* after the fast search only a short BFS-based phase */
    cost = bfs_phase(bfsec, per, per2, badlist, cost);
    if (cost == 0 && getenv("GROW")) {   /* growth: add one freed pair at a time, repair with the fast search, keep it if solved */
        int KMAX = atoi(getenv("GROW")); double stepsec = getenv("STEPSEC") ? atof(getenv("STEPSEC")) : 120;
        int ncand = getenv("NCAND") ? atoi(getenv("NCAND")) : 48, hgdeg = getenv("HGDEG") ? atoi(getenv("HGDEG")) : q - 1;
        int oppgrow = getenv("OPPGROW") ? atoi(getenv("OPPGROW")) : 1, maxfail = getenv("MAXFAIL") ? atoi(getenv("MAXFAIL")) : 6;
        F = realloc(F, sizeof(int) * (KMAX + 1)); fl = realloc(fl, sizeof(int) * (KMAX + 1));
        hdp = realloc(hdp, sizeof(uint8_t *) * (KMAX + 1)); hdl = realloc(hdl, sizeof(uint8_t *) * (KMAX + 1));
        per = realloc(per, sizeof(int) * (KMAX + 1)); per2 = realloc(per2, sizeof(int) * (KMAX + 1));
        int nvmax = 6 * N + 2 * KMAX + 2;
        free(dist); free(que); dist = malloc(nvmax); que = malloc(sizeof(int) * nvmax); badlist = realloc(badlist, sizeof(int) * nvmax);
        HGj = realloc(HGj, sizeof(int) * (KMAX * 8 + 64)); HGk = realloc(HGk, sizeof(int) * (KMAX * 8 + 64));
        HGcap = HGL ? K : 0;   /* hg_build initialised HGL[0..K-1] */
        hg_rebuild_cap(KMAX + 1);
        int *Msave = malloc(sizeof(int) * N), *Minvsave = malloc(sizeof(int) * N), *buf = malloc(sizeof(int) * 4 * Q1 * Q1 * Q1);
        uint8_t *cdp = malloc(2 * N), *cdl = malloc(2 * N), *bdp = malloc(2 * N), *bdl = malloc(2 * N), *mark = malloc(2 * N);
        char fn[600];
        if (out) { snprintf(fn, sizeof fn, "%s.K%d", out, K); write_sol(fn); }
        int fails = 0; clock_t tg = clock();
        while (K < KMAX && fails < maxfail) {
            long best = -1, tries = 0; int bp = -1, bl = -1, found = 0;
            while (found < ncand && tries < 100000000L) {
                tries++;
                int p = rndi(N); if (isF[p]) continue;
                int l = PL[p * Q1 + rndi(Q1)]; if (isF[Minv[l]]) continue;
                int good = 1;
                for (int j = 0; j < K && good; j++) {
                    if (oppgrow) { if (hdp[j][p] != 6 || hdl[j][N + l] != 6 || hdp[j][N + l] != 5 || hdl[j][p] != 5) good = 0; }
                    else if (hdp[j][p] < 4 || hdl[j][N + l] < 4) good = 0;
                }
                if (!good) continue;
                found++;
                long u = cand_uncovered(p, l, cdp, cdl, mark, buf);
                if (best < 0 || u < best) { best = u; bp = p; bl = l; uint8_t *tt = cdp; cdp = bdp; bdp = tt; tt = cdl; cdl = bdl; bdl = tt; }
            }
            if (bp < 0) { fprintf(stderr, "GROW: no candidate flag (tries %ld)\n", tries); break; }
            memcpy(Msave, M, sizeof(int) * N); memcpy(Minvsave, Minv, sizeof(int) * N); int HGmsave = HGm;
            int k = K;
            F[k] = bp; isF[bp] = k + 1; fl[k] = bl;
            { int w = Minv[bl], o = M[bp]; M[bp] = bl; Minv[bl] = bp; M[w] = o; Minv[o] = w; }
            hdp[k] = malloc(2 * N); memcpy(hdp[k], bdp, 2 * N); hdl[k] = malloc(2 * N); memcpy(hdl[k], bdl, 2 * N);
            K++; NV = 6 * N + 2 * K;
            hg_rebuild_cap(KMAX + 1); hg_add_new(k, hgdeg);
            int hv = hub_violations(k, 0) + hub_violations(k, 1);
            int c = -1;
            if (hv == 0) {
                nodrop = 1; fast_search(stepsec); nodrop = 0;
                c = total_cost(per);
                if (c > 0) c = bfs_phase(0.25 * stepsec, per, per2, badlist, c);
            }
            double el = (double)(clock() - tg) / CLOCKS_PER_SEC;
            if (c == 0) {
                fails = 0;
                fprintf(stderr, "GROW: K=%d n=%d solved (candidate uncovered %ld, hub edges %d, %.0fs)\n", K, NV, best, HGm, el);
                if (out) { snprintf(fn, sizeof fn, "%s.K%d", out, K); write_sol(fn); }
            } else {
                fails++;
                fprintf(stderr, "GROW: K=%d failed (cost %d, hub violations %d), reverting (%.0fs)\n", K, c, hv, el);
                K--; NV = 6 * N + 2 * K; isF[bp] = 0; free(hdp[k]); free(hdl[k]);
                memcpy(M, Msave, sizeof(int) * N); memcpy(Minv, Minvsave, sizeof(int) * N); HGm = HGmsave; hg_rebuild_cap(KMAX + 1);
            }
        }
        cost = total_cost(per);
        fprintf(stderr, "GROW done: K=%d n=%d cost %d\n", K, NV, cost);
    }
    if (getenv("REPAIRSEC")) repairsec = atof(getenv("REPAIRSEC"));
    if (cost > 0 && getenv("DROP")) {   /* salvage: drop the worst pairs until every remaining freed source is fine */
        if (!HGm) { HGL = malloc(sizeof(int *) * (K + 1)); HGP = malloc(sizeof(int *) * (K + 1)); HGLn = calloc(K + 1, sizeof(int)); HGPn = calloc(K + 1, sizeof(int)); HGj = malloc(sizeof(int)); HGk = malloc(sizeof(int)); }
        while (cost > 0 && K > 0) {
            int w = 0; for (int j = 1; j < K; j++) if (per[j] > per[w]) w = j;
            drop_pair(w);
            cost = total_cost(per);
            fprintf(stderr, "dropped a pair: K=%d cost %d\n", K, cost);
            for (int rep = 0; cost > 0 && alg >= 2 && rep < 4; rep++) {   /* the dropped pair's hubs may have carried routes of other pairs: repair */
                int before = cost;
                nodrop = 1; fast_search(repairsec); nodrop = 0;
                cost = total_cost(per);
                fprintf(stderr, "  after repair: K=%d cost %d\n", K, cost);
                if (cost > before * 7 / 10) break;   /* repairs stopped paying: drop another pair */
            }
        }
    }
    if (cost == 0 && getenv("SKIPFULL")) {   /* freed sources verified by BFS; the rest is left to apsp */
        printf("RESULT q=%d K=%d n=%d freed sources OK (full check skipped; run apsp)\n", q, K, NV);
        if (out) write_sol(out);
    } else if (cost == 0) {
        int diam, bad = full_check(&diam);
        int maxdeg = 0, nb[64]; for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); if (c > maxdeg) maxdeg = c; }
        printf("RESULT q=%d K=%d n=%d maxdeg=%d diameter=%d badsources=%d %s\n", q, K, NV, maxdeg, diam, bad,
               (bad == 0 && diam <= 7 && maxdeg <= q + 2) ? "VALID" : "INVALID");
        if (out && bad == 0 && diam <= 7) write_sol(out);
    } else printf("RESULT q=%d K=%d unsolved cost %d\n", q, K, cost);
    return 0;
}
