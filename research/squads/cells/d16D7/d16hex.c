/* d16hex.c: bipartite (q+3, 7) graphs from the generalized hexagon H(q) on five levels, cell-16-7 session, 2026-10-24.
   The five-level analogue of research/squads/exp2/hexd7/d7hex.c (three levels, Delta = q+2).

   Base construction (reproduces the table value 5|H(q)| = 10(q^6-1)/(q-1) at Delta = q+3, D = 7; q = 13 gives (16,7)):
     vertices (v, i), v a point or line of H(q), i in Z5;
     (p, i) ~ (l, i) for p on l                         (hexagon edges, all levels)
     (p, i) ~ (M1(p), i+1),  (p, i) ~ (M2(p), i+2)      (M1, M2: points -> lines, any two bijections)
   Diameter <= 7 for EVERY M1, M2 (README.md): from (p,0), level +a by (p,0)->(Ma(p),a)->hexagon path, level -a by
   (p,0) ~> (Ma(x),0) -> (x,-a); from (l,0) the mirror routes; {0, +-1, +-2} = Z5.

   Hubs (+2 vertices per freed pair): a freed pair j = (p, l = M1(p)), p on l, loses its five M1 edges (p,i)-(l,i+1);
   a line-side hub z_j ~ (p,0..4) and a point-side hub z'_j ~ (l,0..4) are added. Degrees stay <= q+3. Every route
   above survives except the freed elements' own M1 routes, so the graph keeps diameter 7 iff every freed (p,0) and
   (l,0) and every hub has eccentricity <= 7 (the construction is invariant under (v,i) -> (v,i+1)). What is left to
   cover: the level-1 points opposite p (from (p,0)) and the level-(-1) lines opposite l (from (l,0)); M1 near the freed
   pairs is chosen to cover them. Hubs of one side must be within 6 of each other: freed points (lines) pairwise not
   opposite, or a hub graph (line-side hub j ~ point-side hub k) in the hubs' q-2 spare slots, here PG(2,r), r+1 <= q-2.

   Search (alg bits): 1 = algebraic cover M1(S'(p)) = S(l) per pair (S'(p) = points at distance 4 from p and 5 from l,
   S(l) = lines at distance 4 from l and 5 from p: every point opposite p is on one line of S, every line opposite l
   has one point of S'); 2 = fast route-count annealing over M1 (counts of real routes of length <= 6 through one M1
   edge, types listed at fast_search, plus routes using no M1 edge found by BFS once); then BFS-targeted polishing.

   Usage:
     d16hex search HEX K seed maxsec out.sol [mode [alg [r [mind]]]]
         mode 1: star (centre c, freed p_j on distinct lines l_j through c; K <= q+1; no hub links needed)
         mode 2: hub graph = incidence graph of PG(2,r), r prime, r+1 <= q-2; K <= r^2+r+1; freed points >= mind apart
     d16hex check HEX SOL            eccentricity of every freed source and hub (with the Lemma this is the full check)
     d16hex sample HEX SOL n seed    plus BFS from n random level-0 sources (sanity check of the Lemma)
     d16hex edges HEX SOL out.txt    write "n" then edges "u v" (for research/lifts/coordinator_check/apsp.c)
   Solution file: "d16hex q N K n" / "freed p1 .. pK" / "hubedges m j1 k1 .." / "bg s1 s2" / "m1 c" + c pairs "p l" /
   "m2 c" + c pairs. M1, M2 are the background permutations bgperm(s1), bgperm(s2) (Fisher-Yates driven by splitmix64,
   see bgperm) with the listed entries overwritten; the reader checks that the result is a bijection.
   Vertex ids: point (p,i) = 2Ni + p, line (l,i) = 2Ni + N + l, hubs z_j = 10N + j, z'_j = 10N + K + j. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <math.h>

#define NLEV 5
static int q, N, Q1;
static int32_t *LP, *PL;              /* LP[l*Q1+k]: points on line l; PL[p*Q1+k]: lines through p */
static int *M1, *M1inv, *M2, *M2inv, *BG1, *BG2;
static uint64_t bgs1, bgs2;
static int K, *F, *isF;               /* freed points; isF[p] = index+1 */
static int *FLn, *isFL;               /* freed lines FLn[j] = M1(F[j]); isFL[l] = index+1 */
static int NV, noM1 = 0;
static uint8_t *dist;
static int *que;
static int HGm = 0, *HGj, *HGk, **HGL, **HGP, *HGLn, *HGPn;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static inline double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static inline int VP(int p, int i) { return i * 2 * N + p; }
static inline int VL(int l, int i) { return i * 2 * N + N + l; }

static int nbrs(int v, int *out) {
    int c = 0;
    if (v >= NLEV * 2 * N) {
        int j = v - NLEV * 2 * N;
        if (j < K) { int p = F[j]; for (int i = 0; i < NLEV; i++) out[c++] = VP(p, i);
                     if (HGm) for (int t = 0; t < HGLn[j]; t++) out[c++] = NLEV * 2 * N + K + HGL[j][t]; }
        else { int l = FLn[j - K]; for (int i = 0; i < NLEV; i++) out[c++] = VL(l, i);
               if (HGm) for (int t = 0; t < HGPn[j - K]; t++) out[c++] = NLEV * 2 * N + HGP[j - K][t]; }
        return c;
    }
    int i = v / (2 * N), r = v - i * 2 * N;
    if (r < N) {
        int p = r; const int32_t *pl = PL + (size_t)p * Q1;
        for (int k = 0; k < Q1; k++) out[c++] = VL(pl[k], i);
        if (isF[p]) out[c++] = NLEV * 2 * N + isF[p] - 1; else if (!noM1) out[c++] = VL(M1[p], (i + 1) % NLEV);
        out[c++] = VL(M2[p], (i + 2) % NLEV);
    } else {
        int l = r - N; const int32_t *lp = LP + (size_t)l * Q1;
        for (int k = 0; k < Q1; k++) out[c++] = VP(lp[k], i);
        if (isFL[l]) out[c++] = NLEV * 2 * N + K + isFL[l] - 1; else if (!noM1) out[c++] = VP(M1inv[l], (i + NLEV - 1) % NLEV);
        out[c++] = VP(M2inv[l], (i + NLEV - 2) % NLEV);
    }
    return c;
}

/* BFS from s; returns the number of vertices at distance > lim (unreached count too); fills dist; ecc if asked */
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
    for (int j = 0; j < K; j++) { HGL[j] = malloc(sizeof(int) * 32); HGP[j] = malloc(sizeof(int) * 32); }
    for (int e = 0; e < HGm; e++) {
        int j = HGj[e], k = HGk[e];
        if (j < 0 || k < 0 || j >= K || k >= K || HGLn[j] >= 32 || HGPn[k] >= 32) { fprintf(stderr, "bad hub graph\n"); exit(1); }
        HGL[j][HGLn[j]++] = k; HGP[k][HGPn[k]++] = j;
    }
}

/* incidence graph of PG(2,r), r prime: returns the number of points (= lines), fills HGj/HGk */
static int hg_pg2(int r) {
    static int pts[4096][3]; int n = 0;
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

static void alloc_graph(void) { NV = NLEV * 2 * N + 2 * K; dist = malloc(NV); que = malloc(sizeof(int) * NV); }

/* background permutation: Fisher-Yates driven by splitmix64(seed) */
static uint64_t sm_state;
static uint64_t splitmix(void) { uint64_t z = (sm_state += 0x9E3779B97F4A7C15ULL); z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL; z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL; return z ^ (z >> 31); }
static void bgperm(uint64_t seed, int *M) {
    sm_state = seed;
    for (int p = 0; p < N; p++) M[p] = p;
    for (int p = N - 1; p > 0; p--) { int r = (int)(splitmix() % (uint64_t)(p + 1)); int t = M[p]; M[p] = M[r]; M[r] = t; }
}

static void set_freed_from_F(void) {
    isF = calloc(N, sizeof(int)); isFL = calloc(N, sizeof(int)); FLn = malloc(sizeof(int) * (K + 1));
    for (int j = 0; j < K; j++) { if (isF[F[j]]) { fprintf(stderr, "freed point repeated\n"); exit(1); } isF[F[j]] = j + 1; FLn[j] = M1[F[j]]; isFL[FLn[j]] = j + 1; }
}

static void write_sol(const char *fn) {
    FILE *f = fopen(fn, "w");
    fprintf(f, "d16hex %d %d %d %d\nfreed", q, N, K, NV);
    for (int j = 0; j < K; j++) fprintf(f, " %d", F[j]);
    fprintf(f, "\nhubedges %d", HGm);
    for (int e = 0; e < HGm; e++) fprintf(f, " %d %d", HGj[e], HGk[e]);
    fprintf(f, "\nbg %llu %llu\n", (unsigned long long)bgs1, (unsigned long long)bgs2);
    int c = 0; for (int p = 0; p < N; p++) if (M1[p] != BG1[p]) c++;
    fprintf(f, "m1 %d\n", c); c = 0;
    for (int p = 0; p < N; p++) if (M1[p] != BG1[p]) { fprintf(f, "%d %d%c", p, M1[p], (++c % 10 == 0) ? '\n' : ' '); }
    if (c % 10) fprintf(f, "\n");
    c = 0; for (int p = 0; p < N; p++) if (M2[p] != BG2[p]) c++;
    fprintf(f, "m2 %d\n", c); c = 0;
    for (int p = 0; p < N; p++) if (M2[p] != BG2[p]) { fprintf(f, "%d %d%c", p, M2[p], (++c % 10 == 0) ? '\n' : ' '); }
    if (c % 10) fprintf(f, "\n");
    fclose(f);
}

static void read_overrides(FILE *f, const char *name, int *M, int *Minv) {
    char tok[32]; int c;
    if (fscanf(f, "%31s %d", tok, &c) != 2 || strcmp(tok, name)) { fprintf(stderr, "expected %s\n", name); exit(1); }
    for (int i = 0; i < c; i++) { int p, l; if (fscanf(f, "%d %d", &p, &l) != 2 || p < 0 || p >= N || l < 0 || l >= N) { fprintf(stderr, "bad %s entry\n", name); exit(1); } M[p] = l; }
    for (int l = 0; l < N; l++) Minv[l] = -1;
    for (int p = 0; p < N; p++) { if (Minv[M[p]] >= 0) { fprintf(stderr, "%s is not a bijection\n", name); exit(1); } Minv[M[p]] = p; }
}

static void alloc_M(void) {
    M1 = malloc(sizeof(int) * N); M1inv = malloc(sizeof(int) * N); M2 = malloc(sizeof(int) * N); M2inv = malloc(sizeof(int) * N);
    BG1 = malloc(sizeof(int) * N); BG2 = malloc(sizeof(int) * N);
}

static void read_sol(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int qq, nn, kk, nv; char w[16];
    if (fscanf(f, "d16hex %d %d %d %d %15s", &qq, &nn, &kk, &nv, w) != 5 || qq != q || nn != N || strcmp(w, "freed")) { fprintf(stderr, "bad sol header\n"); exit(1); }
    K = kk; F = malloc(sizeof(int) * (K + 1));
    for (int j = 0; j < K; j++) if (fscanf(f, "%d", &F[j]) != 1 || F[j] < 0 || F[j] >= N) exit(1);
    char tok[32];
    if (fscanf(f, "%31s", tok) != 1 || strcmp(tok, "hubedges")) { fprintf(stderr, "no hubedges line\n"); exit(1); }
    if (fscanf(f, "%d", &HGm) != 1) exit(1);
    HGj = malloc(sizeof(int) * (HGm + 1)); HGk = malloc(sizeof(int) * (HGm + 1));
    for (int e = 0; e < HGm; e++) if (fscanf(f, "%d %d", &HGj[e], &HGk[e]) != 2) exit(1);
    if (HGm) hg_build();
    unsigned long long s1, s2;
    if (fscanf(f, "%31s %llu %llu", tok, &s1, &s2) != 3 || strcmp(tok, "bg")) { fprintf(stderr, "no bg line\n"); exit(1); }
    alloc_M(); bgs1 = s1; bgs2 = s2;
    bgperm(bgs1, BG1); bgperm(bgs2, BG2); memcpy(M1, BG1, sizeof(int) * N); memcpy(M2, BG2, sizeof(int) * N);
    read_overrides(f, "m1", M1, M1inv); read_overrides(f, "m2", M2, M2inv);
    fclose(f);
    set_freed_from_F();
    alloc_graph();
}

static inline void m1set(int u, int l) {   /* M1[u] := l; the previous owner of l takes u's old line */
    int w = M1inv[l], o = M1[u]; M1[u] = l; M1inv[l] = u; M1[w] = o; M1inv[o] = w;
}

static int cost_of(int j, int *bA, int *bB) {
    *bA = bfs(VP(F[j], 0), 7, NULL);
    *bB = bfs(VL(FLn[j], 0), 7, NULL);
    return *bA + *bB;
}
static int total_cost(int *per) {
    int c = 0;
    for (int j = 0; j < K; j++) { int a, b; per[j] = cost_of(j, &a, &b); c += per[j]; }
    return c;
}

/* eccentricity of every freed source and hub (level-shift invariance + the Lemma make this the full check) */
static int freed_check(int *worst) {
    int bad = 0; *worst = 0;
    for (int j = 0; j < K; j++) {
        int e;
        bfs(VP(F[j], 0), 7, &e); if (e > *worst) *worst = e; if (e > 7) bad++;
        bfs(VL(FLn[j], 0), 7, &e); if (e > *worst) *worst = e; if (e > 7) bad++;
    }
    for (int v = NLEV * 2 * N; v < NV; v++) { int e; bfs(v, 7, &e); if (e > *worst) *worst = e; if (e > 7) bad++; }
    return bad;
}

/* ---------------- fast route-count annealing ----------------
   For pair k (p = F[k], l = FLn[k]) the targets are the points x with d(p,x) = 6 (side A, reached from (p,0) at
   level 1) and the lines t with d(l,t) = 6 (side B, reached from (l,0) at level -1 = 4). Counted routes (length <= 6,
   exactly one M1 edge, its "anchor"); D2A(L) = min over u of d(p,u) + d(M2(u),L), D2B(y) = min over L of
   d(l,L) + d(M2^-1(L),y):
     A1  (p,0) ~> (u,0) -> (M1 u,1) ~> (x,1)                         d(p,u) = 4: x on M1 u;  d(p,u) = 2: d(M1 u,x) <= 3
     A2  (p,0) ~> (u,0) -> (M2 u,2) ~> (L,2) -> (M1^-1 L,1) ~> (x,1)   d(M1^-1 L, x) <= 4 - D2A(L)
     A3  (p,0) ~> (l',0) -> (y = M1^-1 l',-1) ~> (y',-1) -> (M2 y',1) ~> (x,1)
                                 d(p,l') = 1: d(M2 y,x) <= 3 or (d(y,y') = 2, x on M2 y');  d(p,l') = 3: x on M2 y
     B1-B3 the mirror images for (l,0) (lines and points exchanged, M1 and M2 inverted).
   Routes with no M1 edge (hexagon, M2, hubs) are found once by BFS in the graph without M1 edges ("static").
   Every counted route is a real path, so count > 0 for all targets implies eccentricity <= 7. */
enum { KA4, KA2, KB20, KB22, KB24, KB31, KB33 };          /* point-anchored kinds: anchor u, uses M1[u] */
enum { KL20, KL22, KL24, KL31, KL33, KLB4, KLB2 };         /* line-anchored kinds: anchor L, uses M1inv[L] */
static uint8_t **hdp, **hdl, **D2A, **D2B;
static uint16_t **cA, **cB;
static long zeros;
static int32_t **memP, **memL; static int *nmemP, *nmemL;
static int **n4p, **n2p, **n4l, **n2l, **e4A, **e2A, **e4B, **e2B, *nn4p, *nn2p, *nn4l, *nn2l, *ne4A, *ne2A, *ne4B, *ne2B;
static int **oppA, **oppB;   /* target lists (points opposite p_k: q^5; lines opposite l_k) */
static int nopp;

static inline void updA(int k, int x, int s) { if (hdp[k][x] != 6) return; if (s > 0) { if (cA[k][x]++ == 0) zeros--; } else { if (--cA[k][x] == 0) zeros++; } }
static inline void updB(int k, int t, int s) { if (hdl[k][N + t] != 6) return; if (s > 0) { if (cB[k][t]++ == 0) zeros--; } else { if (--cB[k][t] == 0) zeros++; } }

/* ball enumerations in the hexagon (girth 12: non-backtracking walks of length <= 5 reach each element once) */
static void A_ball3_line(int k, int m, int s) {      /* points within 3 of line m */
    for (int a = 0; a < Q1; a++) { int y = LP[m * Q1 + a]; updA(k, y, s);
        for (int b = 0; b < Q1; b++) { int L2 = PL[y * Q1 + b]; if (L2 == m) continue;
            for (int c = 0; c < Q1; c++) { int x = LP[L2 * Q1 + c]; if (x != y) updA(k, x, s); } } }
}
static void A_ball_point(int k, int y, int r, int s) {   /* points within r (0, 2, 4) of point y */
    updA(k, y, s); if (r < 2) return;
    for (int a = 0; a < Q1; a++) { int L1 = PL[y * Q1 + a];
        for (int b = 0; b < Q1; b++) { int y1 = LP[L1 * Q1 + b]; if (y1 == y) continue; updA(k, y1, s);
            if (r < 4) continue;
            for (int c = 0; c < Q1; c++) { int L2 = PL[y1 * Q1 + c]; if (L2 == L1) continue;
                for (int d = 0; d < Q1; d++) { int x = LP[L2 * Q1 + d]; if (x != y1) updA(k, x, s); } } } }
}
static void B_ball3_point(int k, int y, int s) {      /* lines within 3 of point y */
    for (int a = 0; a < Q1; a++) { int t = PL[y * Q1 + a]; updB(k, t, s);
        for (int b = 0; b < Q1; b++) { int x = LP[t * Q1 + b]; if (x == y) continue;
            for (int c = 0; c < Q1; c++) { int t2 = PL[x * Q1 + c]; if (t2 != t) updB(k, t2, s); } } }
}
static void B_ball_line(int k, int m, int r, int s) {    /* lines within r (0, 2, 4) of line m */
    updB(k, m, s); if (r < 2) return;
    for (int a = 0; a < Q1; a++) { int y1 = LP[m * Q1 + a];
        for (int b = 0; b < Q1; b++) { int L1 = PL[y1 * Q1 + b]; if (L1 == m) continue; updB(k, L1, s);
            if (r < 4) continue;
            for (int c = 0; c < Q1; c++) { int y2 = LP[L1 * Q1 + c]; if (y2 == y1) continue;
                for (int d = 0; d < Q1; d++) { int t = PL[y2 * Q1 + d]; if (t != L1) updB(k, t, s); } } } }
}

static void contribP(int k, int kind, int u, int m, int s) {   /* anchor point u with M1[u] = m */
    switch (kind) {
    case KA4: if (hdp[k][N + m] == 5) for (int a = 0; a < Q1; a++) updA(k, LP[m * Q1 + a], s); break;
    case KA2: A_ball3_line(k, m, s); break;
    case KB20: B_ball_line(k, m, 4, s); break;
    case KB22: B_ball_line(k, m, 2, s); break;
    case KB24: updB(k, m, s); break;
    case KB31: { int z = M2inv[m]; B_ball3_point(k, z, s);
        for (int a = 0; a < Q1; a++) { int y = LP[m * Q1 + a];
            for (int b = 0; b < Q1; b++) { int L2 = PL[y * Q1 + b]; if (L2 == m) continue; int z2 = M2inv[L2];
                for (int c = 0; c < Q1; c++) updB(k, PL[z2 * Q1 + c], s); } } } break;
    case KB33: { int z = M2inv[m]; for (int c = 0; c < Q1; c++) updB(k, PL[z * Q1 + c], s); } break;
    }
    (void)u;
}
static void contribL(int k, int kind, int L, int y, int s) {   /* anchor line L with M1inv[L] = y */
    switch (kind) {
    case KL20: A_ball_point(k, y, 4, s); break;
    case KL22: A_ball_point(k, y, 2, s); break;
    case KL24: updA(k, y, s); break;
    case KL31: { int m = M2[y]; A_ball3_line(k, m, s);
        for (int a = 0; a < Q1; a++) { int L1 = PL[y * Q1 + a];
            for (int b = 0; b < Q1; b++) { int y2 = LP[L1 * Q1 + b]; if (y2 == y) continue; int m2 = M2[y2];
                for (int c = 0; c < Q1; c++) updA(k, LP[m2 * Q1 + c], s); } } } break;
    case KL33: { int m = M2[y]; for (int c = 0; c < Q1; c++) updA(k, LP[m * Q1 + c], s); } break;
    case KLB4: if (hdl[k][y] == 5) for (int a = 0; a < Q1; a++) updB(k, PL[y * Q1 + a], s); break;
    case KLB2: B_ball3_point(k, y, s); break;
    }
    (void)L;
}
static inline void pointC(int u, int s) { if (isF[u]) return; for (int e = 0; e < nmemP[u]; e++) contribP(memP[u][e] >> 3, memP[u][e] & 7, u, M1[u], s); }
static inline void lineC(int L, int s) { if (isFL[L]) return; for (int e = 0; e < nmemL[L]; e++) contribL(memL[L][e] >> 3, memL[L][e] & 7, L, M1inv[L], s); }
static void swapM1(int u, int w) {   /* exchange the lines of points u and w, keeping the counts current */
    int a = M1[u], b = M1[w];
    pointC(u, -1); pointC(w, -1); lineC(a, -1); lineC(b, -1);
    M1[u] = b; M1[w] = a; M1inv[b] = u; M1inv[a] = w;
    pointC(u, +1); pointC(w, +1); lineC(a, +1); lineC(b, +1);
}

static void fs_setup(void) {
    D2A = malloc(sizeof(uint8_t *) * K); D2B = malloc(sizeof(uint8_t *) * K);
    cA = malloc(sizeof(uint16_t *) * K); cB = malloc(sizeof(uint16_t *) * K);
    int **lists[] = {0}; (void)lists;
    n4p = malloc(sizeof(int *) * K); n2p = malloc(sizeof(int *) * K); n4l = malloc(sizeof(int *) * K); n2l = malloc(sizeof(int *) * K);
    e4A = malloc(sizeof(int *) * K); e2A = malloc(sizeof(int *) * K); e4B = malloc(sizeof(int *) * K); e2B = malloc(sizeof(int *) * K);
    nn4p = calloc(K, sizeof(int)); nn2p = calloc(K, sizeof(int)); nn4l = calloc(K, sizeof(int)); nn2l = calloc(K, sizeof(int));
    ne4A = calloc(K, sizeof(int)); ne2A = calloc(K, sizeof(int)); ne4B = calloc(K, sizeof(int)); ne2B = calloc(K, sizeof(int));
    oppA = malloc(sizeof(int *) * K); oppB = malloc(sizeof(int *) * K);
    nmemP = calloc(N, sizeof(int)); nmemL = calloc(N, sizeof(int));
    for (int k = 0; k < K; k++) {
        uint8_t *hp = hdp[k], *hl = hdl[k];
        D2A[k] = malloc(N); memset(D2A[k], 255, N); D2B[k] = malloc(N); memset(D2B[k], 255, N);
        /* D2A over lines: u with d(p,u) = 0, 2, 4, then lines within 4 - d(p,u) of M2(u) */
        for (int u = 0; u < N; u++) {
            int b = hp[u]; if (b > 4) continue;
            int m = M2[u];
            if (b <= 4 && D2A[k][m] > b) D2A[k][m] = b;
            if (b <= 2) for (int a = 0; a < Q1; a++) { int y1 = LP[m * Q1 + a];
                for (int c = 0; c < Q1; c++) { int L1 = PL[y1 * Q1 + c]; if (L1 == m) continue; if (D2A[k][L1] > b + 2) D2A[k][L1] = b + 2;
                    if (b == 0) for (int d = 0; d < Q1; d++) { int y2 = LP[L1 * Q1 + d]; if (y2 == y1) continue;
                        for (int e = 0; e < Q1; e++) { int t = PL[y2 * Q1 + e]; if (t != L1 && D2A[k][t] > 4) D2A[k][t] = 4; } } } }
        }
        for (int L = 0; L < N; L++) {
            int b = hl[N + L]; if (b > 4) continue;
            int y = M2inv[L];
            if (D2B[k][y] > b) D2B[k][y] = b;
            if (b <= 2) for (int a = 0; a < Q1; a++) { int L1 = PL[y * Q1 + a];
                for (int c = 0; c < Q1; c++) { int y1 = LP[L1 * Q1 + c]; if (y1 == y) continue; if (D2B[k][y1] > b + 2) D2B[k][y1] = b + 2;
                    if (b == 0) for (int d = 0; d < Q1; d++) { int L2 = PL[y1 * Q1 + d]; if (L2 == L1) continue;
                        for (int e = 0; e < Q1; e++) { int x = LP[L2 * Q1 + e]; if (x != y1 && D2B[k][x] > 4) D2B[k][x] = 4; } } } }
        }
        n4p[k] = malloc(sizeof(int) * N); n2p[k] = malloc(sizeof(int) * 4096); n4l[k] = malloc(sizeof(int) * N); n2l[k] = malloc(sizeof(int) * 4096);
        e4A[k] = malloc(sizeof(int) * N); e2A[k] = malloc(sizeof(int) * N); e4B[k] = malloc(sizeof(int) * N); e2B[k] = malloc(sizeof(int) * N);
        oppA[k] = malloc(sizeof(int) * N); oppB[k] = malloc(sizeof(int) * N);
        int na = 0, nb = 0;
        for (int v = 0; v < N; v++) {
            if (hp[v] == 6) oppA[k][na++] = v;
            if (hl[N + v] == 6) oppB[k][nb++] = v;
            if (!isF[v]) {
                if (hp[v] == 4) n4p[k][nn4p[k]++] = v;
                if (hp[v] == 2) n2p[k][nn2p[k]++] = v;
                if (D2B[k][v] == 4) e4B[k][ne4B[k]++] = v;
                if (D2B[k][v] <= 2) e2B[k][ne2B[k]++] = v;
            }
            if (!isFL[v]) {
                if (hl[N + v] == 4) n4l[k][nn4l[k]++] = v;
                if (hl[N + v] == 2) n2l[k][nn2l[k]++] = v;
                if (D2A[k][v] == 4) e4A[k][ne4A[k]++] = v;
                if (D2A[k][v] <= 2) e2A[k][ne2A[k]++] = v;
            }
        }
        nopp = na;
        if (k == 0) fprintf(stderr, "pair 0: targets %d + %d; anchors A1 %d+%d, A2 %d+%d, B1 %d+%d, B2 %d+%d\n", na, nb,
                            nn4p[0], nn2p[0], ne4A[0], ne2A[0], nn4l[0], nn2l[0], ne4B[0], ne2B[0]);
    }
    /* anchor lists */
    for (int pass = 0; pass < 2; pass++) {
        if (pass == 1) {
            memP = malloc(sizeof(int32_t *) * N); memL = malloc(sizeof(int32_t *) * N);
            for (int v = 0; v < N; v++) { memP[v] = malloc(sizeof(int32_t) * (nmemP[v] + 1)); memL[v] = malloc(sizeof(int32_t) * (nmemL[v] + 1)); nmemP[v] = nmemL[v] = 0; }
        }
        for (int k = 0; k < K; k++) {
            uint8_t *hp = hdp[k], *hl = hdl[k];
            for (int v = 0; v < N; v++) {
                int kp[3], np = 0, kl[3], nl = 0;
                if (hp[v] == 4) kp[np++] = KA4; else if (hp[v] == 2) kp[np++] = KA2;
                if (D2B[k][v] == 0) kp[np++] = KB20; else if (D2B[k][v] == 2) kp[np++] = KB22; else if (D2B[k][v] == 4) kp[np++] = KB24;
                if (hl[v] == 1) kp[np++] = KB31; else if (hl[v] == 3) kp[np++] = KB33;
                if (D2A[k][v] == 0) kl[nl++] = KL20; else if (D2A[k][v] == 2) kl[nl++] = KL22; else if (D2A[k][v] == 4) kl[nl++] = KL24;
                if (hp[N + v] == 1) kl[nl++] = KL31; else if (hp[N + v] == 3) kl[nl++] = KL33;
                if (hl[N + v] == 4) kl[nl++] = KLB4; else if (hl[N + v] == 2) kl[nl++] = KLB2;
                for (int i = 0; i < np; i++) { if (pass) memP[v][nmemP[v]] = k * 8 + kp[i]; nmemP[v]++; }
                for (int i = 0; i < nl; i++) { if (pass) memL[v][nmemL[v]] = k * 8 + kl[i]; nmemL[v]++; }
            }
        }
    }
    long tot = 0; for (int v = 0; v < N; v++) tot += nmemP[v] + nmemL[v];
    fprintf(stderr, "anchor entries %ld (%.1f per element)\n", tot, (double)tot / (2.0 * N));
}

/* static coverage: BFS without M1 edges; then counts start at 1 for statically covered targets */
static void fs_init_counts(void) {
    zeros = 0; long st = 0;
    noM1 = 1;
    for (int k = 0; k < K; k++) {
        cA[k] = calloc(N, sizeof(uint16_t)); cB[k] = calloc(N, sizeof(uint16_t));
        bfs(VP(F[k], 0), 7, NULL);
        for (int x = 0; x < N; x++) if (hdp[k][x] == 6) { if (dist[VP(x, 1)] <= 6) { cA[k][x] = 1; st++; } else zeros++; }
        bfs(VL(FLn[k], 0), 7, NULL);
        for (int t = 0; t < N; t++) if (hdl[k][N + t] == 6) { if (dist[VL(t, NLEV - 1)] <= 6) { cB[k][t] = 1; st++; } else zeros++; }
    }
    noM1 = 0;
    fprintf(stderr, "static coverage: %ld covered, %ld not\n", st, zeros);
    for (int u = 0; u < N; u++) pointC(u, +1);
    for (int L = 0; L < N; L++) lineC(L, +1);
    fprintf(stderr, "proxy cost after counting routes: %ld\n", zeros);
}

static int BESTK = 1;
static long fast_search(double maxsec, double T0) {
    if (getenv("BESTK")) BESTK = atoi(getenv("BESTK"));
    double t0 = now(); long it = 0, best = zeros, acc = 0;
    int zcap = 20000; long *zl = malloc(sizeof(long) * zcap); int nz = 0;
    while (zeros > 0) {
        it++;
        double el = now() - t0;
        if ((it & 1023) == 0) {
            if (el > maxsec) break;
            if ((it & ((1 << 18) - 1)) == 0) fprintf(stderr, "it %ld acc %ld proxy %ld best %ld (%.0fs)\n", it, acc, zeros, best, el);
        }
        double T = T0 * (1.0 - el / maxsec); if (T < 0.05) T = 0.05;
        int k, side, tgt = -1;
        if (zeros <= zcap) {
            if (nz == 0 || (it & 4095) == 0) {
                nz = 0;
                for (int kk = 0; kk < K; kk++) for (int a = 0; a < nopp; a++) {
                    if (cA[kk][oppA[kk][a]] == 0 && nz < zcap) zl[nz++] = (long)kk * 2 * N + oppA[kk][a];
                    if (cB[kk][oppB[kk][a]] == 0 && nz < zcap) zl[nz++] = (long)kk * 2 * N + N + oppB[kk][a];
                }
                if (nz == 0) continue;
            }
            long e = zl[rndi(nz)]; k = (int)(e / (2 * N)); int r = (int)(e % (2 * N));
            side = r >= N; tgt = side ? r - N : r;
            if ((side == 0 ? cA[k][tgt] : cB[k][tgt]) != 0) continue;
        } else {
            k = rndi(K); side = rndi(2);
            int *lst = side == 0 ? oppA[k] : oppB[k]; uint16_t *cc = side == 0 ? cA[k] : cB[k];
            for (int tr = 0; tr < 64; tr++) { int v = lst[rndi(nopp)]; if (cc[v] == 0) { tgt = v; break; } }
            if (tgt < 0) continue;
        }
        int bu = -1, bw = -1; long bd = 1L << 60;
        for (int cand = 0; cand < BESTK; cand++) {
            int u = -1, w = -1, kind = rndi(16);
            if (side == 0) {   /* make some route reach the point tgt */
                int x = tgt;
                if (kind < 10) { if (!nn4p[k]) continue; u = n4p[k][rndi(nn4p[k])]; w = M1inv[PL[x * Q1 + rndi(Q1)]]; }
                else if (kind < 12) { if (!nn2p[k]) continue; u = n2p[k][rndi(nn2p[k])]; int L1 = PL[x * Q1 + rndi(Q1)]; int y = LP[L1 * Q1 + rndi(Q1)]; w = M1inv[PL[y * Q1 + rndi(Q1)]]; }
                else if (kind < 15) { if (!ne4A[k]) continue; u = x; w = M1inv[e4A[k][rndi(ne4A[k])]]; }
                else { if (!ne2A[k]) continue; int L1 = PL[x * Q1 + rndi(Q1)]; u = LP[L1 * Q1 + rndi(Q1)]; w = M1inv[e2A[k][rndi(ne2A[k])]]; }
            } else {           /* make some route reach the line tgt */
                int t = tgt;
                if (kind < 10) { if (!nn4l[k]) continue; u = LP[t * Q1 + rndi(Q1)]; w = M1inv[n4l[k][rndi(nn4l[k])]]; }
                else if (kind < 12) { if (!nn2l[k]) continue; int y1 = LP[t * Q1 + rndi(Q1)]; int L1 = PL[y1 * Q1 + rndi(Q1)]; u = LP[L1 * Q1 + rndi(Q1)]; w = M1inv[n2l[k][rndi(nn2l[k])]]; }
                else if (kind < 15) { if (!ne4B[k]) continue; u = e4B[k][rndi(ne4B[k])]; w = M1inv[t]; }
                else { if (!ne2B[k]) continue; u = e2B[k][rndi(ne2B[k])]; int y1 = LP[t * Q1 + rndi(Q1)]; w = M1inv[PL[y1 * Q1 + rndi(Q1)]]; }
            }
            /* the move gives u the line currently held by w (A1/B2 kinds: u is the anchor point; else w's line is the anchor) */
            if (u < 0 || w < 0 || u == w || isF[u] || isF[w]) continue;
            long before = zeros;
            swapM1(u, w);
            long d = zeros - before;
            swapM1(u, w);
            if (d < bd) { bd = d; bu = u; bw = w; }
        }
        if (bu < 0) continue;
        if (bd <= 0 || (double)(rnd() % 1000000) / 1e6 < exp(-bd / T)) { swapM1(bu, bw); acc++; }
        if (zeros < best) best = zeros;
    }
    fprintf(stderr, "fast search done: it %ld acc %ld proxy %ld (%.1fs)\n", it, acc, zeros, now() - t0);
    return zeros;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see header\n"); return 1; }
    load(argv[2]);
    if (!strcmp(argv[1], "check") || !strcmp(argv[1], "sample")) {
        read_sol(argv[3]);
        int maxdeg = 0, nb[64];
        for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); if (c > maxdeg) maxdeg = c; }
        double t0 = now();
        int worst, bad = freed_check(&worst);
        printf("q=%d n=%d K=%d maxdeg=%d freed+hub sources: worst ecc %d, bad %d (%.1fs)\n", q, NV, K, maxdeg, worst, bad, now() - t0);
        if (!strcmp(argv[1], "sample")) {
            int ns = atoi(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL;
            int sw = 0, sb = 0;
            for (int s = 0; s < ns; s++) { int v = rndi(2 * N), e; bfs(v, 7, &e); if (e > sw) sw = e; if (e > 7) sb++; }
            printf("sample of %d level-0 sources: worst ecc %d, bad %d\n", ns, sw, sb);
            bad += sb;
        }
        printf("RESULT %s n=%d\n", (bad == 0 && worst <= 7 && maxdeg <= q + 3) ? "VALID" : "INVALID", NV);
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
    K = atoi(argv[3]); uint64_t seed = (uint64_t)atoll(argv[4]);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    double maxsec = atof(argv[5]);
    const char *out = argc > 6 ? argv[6] : NULL;
    int mode = argc > 7 ? atoi(argv[7]) : 0, alg = argc > 8 ? atoi(argv[8]) : 1, r = argc > 9 ? atoi(argv[9]) : 0;
    int mind = argc > 10 ? atoi(argv[10]) : 6;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 0.6, fsfrac = getenv("FSFRAC") ? atof(getenv("FSFRAC")) : 0.8;
    alloc_M();
    bgs1 = seed * 2 + 1; bgs2 = seed * 2 + 2;
    bgperm(bgs1, BG1); bgperm(bgs2, BG2);
    memcpy(M1, BG1, sizeof(int) * N); memcpy(M2, BG2, sizeof(int) * N);
    for (int p = 0; p < N; p++) { M1inv[M1[p]] = p; M2inv[M2[p]] = p; }
    F = malloc(sizeof(int) * (K + 1)); int *fl = malloc(sizeof(int) * (K + 1));
    uint8_t *tmp = malloc(2 * N), *ok = malloc(N); memset(ok, 1, N);
    if (mode == 1) {
        int c = rndi(N); if (K > Q1) K = Q1;
        int perm[64]; for (int k = 0; k < Q1; k++) perm[k] = k;
        for (int k = Q1 - 1; k > 0; k--) { int rr = rndi(k + 1); int t = perm[k]; perm[k] = perm[rr]; perm[rr] = t; }
        for (int j = 0; j < K; j++) { int l = PL[c * Q1 + perm[j]], p; do { p = LP[l * Q1 + rndi(Q1)]; } while (p == c); F[j] = p; fl[j] = l; }
    } else {
        if (mode == 2) {
            int n = hg_pg2(r); if (K > n) K = n;
            int m2 = 0; for (int e = 0; e < HGm; e++) if (HGj[e] < K && HGk[e] < K) { HGj[m2] = HGj[e]; HGk[m2] = HGk[e]; m2++; } HGm = m2;
            hg_build();
            for (int j = 0; j < K; j++) if (HGLn[j] > q - 2 || HGPn[j] > q - 2) { fprintf(stderr, "hub degree > q-2\n"); return 1; }
        } else if (K > 1) { fprintf(stderr, "mode 0 is for K = 1\n"); return 1; }
        for (int j = 0; j < K; j++) {
            int p = -1;
            for (int tries = 0; tries < 1000000; tries++) { int c = rndi(N); if (ok[c]) { p = c; break; } }
            if (p < 0) { fprintf(stderr, "could only place %d freed points\n", j); return 1; }
            F[j] = p; fl[j] = PL[p * Q1 + rndi(Q1)];
            hbfs(p, 0, tmp); for (int x = 0; x < N; x++) if (tmp[x] < mind) ok[x] = 0;
        }
    }
    for (int j = 0; j < K; j++) m1set(F[j], fl[j]);
    set_freed_from_F();
    alloc_graph();
    hdp = malloc(sizeof(uint8_t *) * K); hdl = malloc(sizeof(uint8_t *) * K);
    for (int j = 0; j < K; j++) { hdp[j] = malloc(2 * N); hbfs(F[j], 0, hdp[j]); hdl[j] = malloc(2 * N); hbfs(FLn[j], 1, hdl[j]); }
    if (alg & 1) {   /* algebraic cover: M1 maps S'(p) onto S(l) */
        uint8_t *lockp = calloc(N, 1), *lockl = calloc(N, 1), *inS = calloc(N, 1), *used = calloc(N, 1);
        for (int j = 0; j < K; j++) { lockp[F[j]] = 1; lockl[FLn[j]] = 1; }
        int *Sp = malloc(sizeof(int) * N), *Sl = malloc(sizeof(int) * N); long conflicts = 0;
        for (int j = 0; j < K; j++) {
            int ns = 0, nl = 0; memset(inS, 0, N); memset(used, 0, N);
            for (int l = 0; l < N; l++) if (hdl[j][N + l] == 4 && hdp[j][N + l] == 5) { inS[l] = 1; Sl[nl++] = l; }
            for (int u = 0; u < N; u++) if (hdp[j][u] == 4 && hdl[j][u] == 5) Sp[ns++] = u;
            int nfree = 0;
            for (int k = 0; k < ns; k++) { int u = Sp[k]; if (lockp[u]) { if (inS[M1[u]] && !used[M1[u]]) used[M1[u]] = 1; else conflicts++; } else Sp[nfree++] = u; }
            int li = 0;
            for (int k = 0; k < nfree; k++) {
                while (li < nl && (used[Sl[li]] || lockl[Sl[li]])) li++;
                if (li >= nl) { conflicts += nfree - k; break; }
                int u = Sp[k], l = Sl[li++]; used[l] = 1; m1set(u, l); lockp[u] = 1; lockl[l] = 1;
            }
        }
        fprintf(stderr, "algebraic cover installed, conflicts %ld\n", conflicts);
    }
    double tstart = now();
    if (alg & 2) {
        fs_setup();
        fs_init_counts();
        fast_search(maxsec * fsfrac, T0);
    }
    int *per = malloc(sizeof(int) * K), *per2 = malloc(sizeof(int) * K);
    int cost = total_cost(per);
    fprintf(stderr, "q=%d N=%d K=%d n=%d BFS cost %d (%.1fs)\n", q, N, K, NV, cost, now() - tstart);
    long it = 0, acc = 0;
    int *badlist = malloc(sizeof(int) * NV);
    while (cost > 0 && now() - tstart < maxsec) {   /* BFS-targeted polishing (slow; for the last few targets) */
        it++;
        int j; do { j = rndi(K); } while (per[j] == 0);
        int side = rndi(2);
        int src = side == 0 ? VP(F[j], 0) : VL(FLn[j], 0), nbad = bfs(src, 7, NULL);
        if (nbad == 0) { side ^= 1; src = side == 0 ? VP(F[j], 0) : VL(FLn[j], 0); nbad = bfs(src, 7, NULL); }
        if (nbad == 0) continue;
        int nb2 = 0; for (int v = 0; v < NV; v++) if (dist[v] > 7) badlist[nb2++] = v;
        int t = badlist[rndi(nb2)];
        if (t >= NLEV * 2 * N) continue;
        int tr = t % (2 * N), u = -1, w = -1;
        if (side == 0) { if (tr >= N) continue; int x = tr;
            for (int tries = 0; tries < 200; tries++) { int c = rndi(N); if (hdp[j][c] == 4) { u = c; break; } }
            w = M1inv[PL[x * Q1 + rndi(Q1)]];
        } else { if (tr < N) continue; int lt = tr - N;
            u = LP[lt * Q1 + rndi(Q1)];
            for (int tries = 0; tries < 200; tries++) { int c = rndi(N); if (hdl[j][N + c] == 4) { w = M1inv[c]; break; } }
        }
        if (u < 0 || w < 0 || u == w || isF[u] || isF[w]) continue;
        int a = M1[u], b = M1[w];
        M1[u] = b; M1[w] = a; M1inv[b] = u; M1inv[a] = w;
        int a0, b0, cj = cost_of(j, &a0, &b0), c2 = -1;
        if (cj <= per[j]) c2 = total_cost(per2);
        if (c2 >= 0 && c2 <= cost) { cost = c2; memcpy(per, per2, sizeof(int) * K); acc++; }
        else { M1[u] = a; M1[w] = b; M1inv[a] = u; M1inv[b] = w; }
        if (it % 20 == 0) fprintf(stderr, "polish it %ld acc %ld cost %d (%.0fs)\n", it, acc, cost, now() - tstart);
    }
    if (cost == 0) {
        int worst, bad = freed_check(&worst);
        int maxdeg = 0, nb[64]; for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); if (c > maxdeg) maxdeg = c; }
        printf("RESULT q=%d K=%d n=%d maxdeg=%d freed+hub worst ecc %d bad %d %s\n", q, K, NV, maxdeg, worst, bad,
               (bad == 0 && worst <= 7 && maxdeg <= q + 3) ? "VALID" : "INVALID");
        if (out && bad == 0 && worst <= 7) write_sol(out);
    } else printf("RESULT q=%d K=%d unsolved cost %d\n", q, K, cost);
    return 0;
}
