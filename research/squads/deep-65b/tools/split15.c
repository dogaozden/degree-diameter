/* split15.c (deep-65b): exact search of all voltage lifts of the 2+2 base [[1,5],[5,1]] by a group of order m <= 256,
 * maximum degree 6, diameter 5 (n = 4m).
 *
 * Normal form. Base A0, A1 | B0, B1 with A0-B0 and A1-B1 single edges, A0-B1 and A1-B0 five edges each. Put voltage 1
 * on both single edges (a spanning-tree normalisation), then the lift is
 *     A0_h ~ B0_h,  A1_h ~ B1_h,  A0_h ~ B1_{h e} (e in E1),  B0_h ~ A1_{h e} (e in E2),
 * i.e. the degree-10 Haar graph H(G, E1 u E2) with every vertex split into an edge (A0_h-B0_h on one side,
 * A1_h-B1_h on the other). With E = E1 u E2, reading off the walks of length <= 4 gives: diameter <= 5 iff
 *   C1 (A0-A0)  E E^-1 u (E1 E1^-1)^2 = G           C2 (B0-B0)  E E^-1 u (E2 E2^-1)^2 = G
 *   C3 (A1-A1)  E^-1 E u (E2^-1 E2)^2 = G           C4 (B1-B1)  E^-1 E u (E1^-1 E1)^2 = G
 *   C5 (A0-A1)  E u E1E1^-1E1 u E1E1^-1E2 u E1E2^-1E2 u E2E2^-1E2 = G
 *   C6 (B0-B1)  E u E1E1^-1E1 u E2E1^-1E1 u E2E2^-1E1 u E2E2^-1E2 = G
 * (mode rand checks these against BFS on the actual graph). Symmetries: (E1,E2) -> (t phi(E1) h, t phi(E2) h) for
 * t, h in G and phi in Aut(G); (E1,E2) -> (E2,E1); (E1,E2) -> (E1^-1,E2^-1).
 *
 * Exact search (mode ex). E1 runs over orbit representatives of 5-sets containing 1 under translations, Aut(G) and
 * inversion (union-find over all 4-subsets of G\{1}). For fixed E1 the sets UA = G \ (E1E1^-1)^2 and
 * UB = G \ (E1^-1E1)^2 must be covered by E1E2^-1 u E2E1^-1 u E2E2^-1 (C1) and E1^-1E2 u E2^-1E1 u E2^-1E2 (C4).
 * E2 is built by branching on the first uncovered element x: x is covered linearly by a new element (10 choices),
 * quadratically with an element already chosen (2k choices), or by a new pair (m choices, two slots). Every E2 with
 * C1 and C4 is reached (mode bf compares with brute force over all E2). Leaves are deduplicated, the swap symmetry
 * keeps class(E2) >= class(E1), and C5, C6, C2, C3 are tested.
 *
 * usage: split15 TAB rand N SEED      validation against BFS
 *        split15 TAB ex [NPROC PROC]   exact search; prints SOL lines, best near-miss cost (sum of misses of C2,C3,C5,C6)
 *        split15 TAB bf K              brute force over all E2 for the K-th E1 representative, compared with the DFS
 * TAB: m, the m x m table (identity 0), then "ngen k" and k automorphism generators (images of 0..m-1).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef struct { uint64_t w[4]; } bs;
static int m, NW;
static uint8_t T[256][256], inv_[256];
static int ngen, gen[64][256];
static bs FULL;
static inline void bset(bs *b, int x) { b->w[x >> 6] |= 1ULL << (x & 63); }
static inline int btest(const bs *b, int x) { return (b->w[x >> 6] >> (x & 63)) & 1; }
static inline int bcount(const bs *b) { int c = 0; for (int i = 0; i < NW; i++) c += __builtin_popcountll(b->w[i]); return c; }
static inline int bmissing(const bs *b) { int c = 0; for (int i = 0; i < NW; i++) c += __builtin_popcountll(FULL.w[i] & ~b->w[i]); return c; }
static inline int bempty(const bs *b) { for (int i = 0; i < NW; i++) if (b->w[i]) return 0; return 1; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void readtab(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f || fscanf(f, "%d", &m) != 1 || m > 256) { fprintf(stderr, "bad table\n"); exit(2); }
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) { int x; if (fscanf(f, "%d", &x) != 1) exit(2); T[i][j] = x; }
    char w[16]; ngen = 0;
    if (fscanf(f, "%15s %d", w, &ngen) == 2 && !strcmp(w, "ngen")) {
        for (int a = 0; a < ngen; a++) for (int x = 0; x < m; x++) if (fscanf(f, "%d", &gen[a][x]) != 1) exit(2);
    } else ngen = 0;
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (T[i][j] == 0) inv_[i] = j;
    NW = (m + 63) / 64; memset(&FULL, 0, sizeof FULL); for (int x = 0; x < m; x++) bset(&FULL, x);
}

/* ---------- the six conditions (generic) ---------- */
static int dedup(int *a, int n) { static char c[256]; memset(c, 0, m); int o = 0; for (int i = 0; i < n; i++) if (!c[a[i]]) { c[a[i]] = 1; a[o++] = a[i]; } return o; }
static int prodl(const int *A, int na, const int *B, int nb, int *out) { int n = 0; for (int i = 0; i < na; i++) for (int j = 0; j < nb; j++) out[n++] = T[A[i]][B[j]]; return dedup(out, n); }
static void conds(const int *E1, const int *E2, int *miss) {
    int I1[5], I2[5]; for (int i = 0; i < 5; i++) { I1[i] = inv_[E1[i]]; I2[i] = inv_[E2[i]]; }
    int E[10], EI[10]; for (int i = 0; i < 5; i++) { E[i] = E1[i]; E[5 + i] = E2[i]; EI[i] = I1[i]; EI[5 + i] = I2[i]; }
    int Q1[25], Q2[25], P1[25], P2[25], EEi[100], EiE[100];
    int nQ1 = prodl(E1, 5, I1, 5, Q1), nQ2 = prodl(E2, 5, I2, 5, Q2), nP1 = prodl(I1, 5, E1, 5, P1), nP2 = prodl(I2, 5, E2, 5, P2);
    int nEEi = prodl(E, 10, EI, 10, EEi), nEiE = prodl(EI, 10, E, 10, EiE);
    int tmp[2000], n; bs c;
    /* C1 */ memset(&c, 0, sizeof c); for (int i = 0; i < nEEi; i++) bset(&c, EEi[i]); n = prodl(Q1, nQ1, Q1, nQ1, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]); miss[0] = bmissing(&c);
    /* C2 */ memset(&c, 0, sizeof c); for (int i = 0; i < nEEi; i++) bset(&c, EEi[i]); n = prodl(Q2, nQ2, Q2, nQ2, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]); miss[1] = bmissing(&c);
    /* C3 */ memset(&c, 0, sizeof c); for (int i = 0; i < nEiE; i++) bset(&c, EiE[i]); n = prodl(P2, nP2, P2, nP2, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]); miss[2] = bmissing(&c);
    /* C4 */ memset(&c, 0, sizeof c); for (int i = 0; i < nEiE; i++) bset(&c, EiE[i]); n = prodl(P1, nP1, P1, nP1, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]); miss[3] = bmissing(&c);
    /* C5 */ memset(&c, 0, sizeof c); for (int i = 0; i < 10; i++) bset(&c, E[i]);
    n = prodl(Q1, nQ1, E1, 5, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]);
    n = prodl(Q1, nQ1, E2, 5, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]);
    n = prodl(E1, 5, P2, nP2, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]);
    n = prodl(Q2, nQ2, E2, 5, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]);
    miss[4] = bmissing(&c);
    /* C6 */ memset(&c, 0, sizeof c); for (int i = 0; i < 10; i++) bset(&c, E[i]);
    n = prodl(Q1, nQ1, E1, 5, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]);
    n = prodl(E2, 5, P1, nP1, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]);
    n = prodl(Q2, nQ2, E1, 5, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]);
    n = prodl(Q2, nQ2, E2, 5, tmp); for (int i = 0; i < n; i++) bset(&c, tmp[i]);
    miss[5] = bmissing(&c);
}

/* ---------- graph + BFS (validation) ---------- */
static int nv, adj[1024][6], dg[1024];
static void addedge(int u, int v) { adj[u][dg[u]++] = v; adj[v][dg[v]++] = u; }
static int build(const int *E1, const int *E2) {   /* A0 = 0..m-1, A1 = m.., B0 = 2m.., B1 = 3m.. */
    nv = 4 * m; memset(dg, 0, sizeof(int) * nv);
    for (int h = 0; h < m; h++) {
        addedge(h, 2 * m + h); addedge(m + h, 3 * m + h);
        for (int i = 0; i < 5; i++) { addedge(h, 3 * m + T[h][E1[i]]); addedge(2 * m + h, m + T[h][E2[i]]); }
    }
    for (int v = 0; v < nv; v++) if (dg[v] != 6) return 0;
    for (int v = 0; v < nv; v++) for (int i = 0; i < 6; i++) for (int j = i + 1; j < 6; j++) if (adj[v][i] == adj[v][j]) return 0;
    return 1;
}
static void bfs(int s, int *dist) {
    static int q[1024]; for (int i = 0; i < nv; i++) dist[i] = -1;
    int h = 0, t = 0; dist[s] = 0; q[t++] = s;
    while (h < t) { int x = q[h++]; for (int i = 0; i < 6; i++) { int y = adj[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
}
static int farcount(const int *dist, int lo, int hi, int lim) { int c = 0; for (int v = lo; v < hi; v++) if (dist[v] < 0 || dist[v] > lim) c++; return c; }

static void rand_set(int *E, int with1) {
    int n = 0; if (with1) E[n++] = 0;
    while (n < 5) { int x = rnd() % m, ok = 1; for (int i = 0; i < n; i++) if (E[i] == x) ok = 0; if (ok) E[n++] = x; }
}

/* ---------- 4-subset ranking and union-find ---------- */
static uint64_t binom[300][6];
static uint64_t N4;
static int32_t *par;
static int16_t *qv;   /* q = |UA|+|UB| of the class, stored at class roots */
static inline uint64_t rank4(int *s) {   /* s: 4 distinct elements of 1..m-1 */
    int a[4] = {s[0] - 1, s[1] - 1, s[2] - 1, s[3] - 1};
    for (int i = 1; i < 4; i++) for (int j = i; j > 0 && a[j] < a[j - 1]; j--) { int t = a[j]; a[j] = a[j - 1]; a[j - 1] = t; }
    return binom[a[0]][1] + binom[a[1]][2] + binom[a[2]][3] + binom[a[3]][4];
}
static void unrank4(uint64_t r, int *s) {
    for (int k = 4; k >= 1; k--) { int x = k - 1; while (binom[x + 1][k] <= r) x++; s[k - 1] = x + 1; r -= binom[x][k]; }
}
static int32_t findr(int32_t x) { while (par[x] != x) { par[x] = par[par[x]]; x = par[x]; } return x; }
static void unite(int32_t a, int32_t b) { a = findr(a); b = findr(b); if (a == b) return; if (a < b) par[b] = a; else par[a] = b; }
/* class of an arbitrary 5-set (any elements): translate so that its first element becomes 1 */
static int32_t class5(const int *E) {
    int s[4], n = 0, e0 = inv_[E[0]];
    for (int i = 1; i < 5; i++) s[n++] = T[e0][E[i]];
    return findr((int32_t)rank4(s));
}
static void build_classes(void) {
    for (int i = 0; i < 300; i++) { binom[i][0] = 1; for (int k = 1; k < 6; k++) binom[i][k] = i == 0 ? 0 : binom[i - 1][k - 1] + binom[i - 1][k]; }
    N4 = binom[m - 1][4];
    par = malloc(sizeof(int32_t) * N4); if (!par) { fprintf(stderr, "no memory\n"); exit(2); }
    for (uint64_t r = 0; r < N4; r++) par[r] = (int32_t)r;
    int s[4], t[4];
    for (uint64_t r = 0; r < N4; r++) {
        unrank4(r, s);
        for (int g = 0; g < ngen; g++) { for (int i = 0; i < 4; i++) t[i] = gen[g][s[i]]; unite(r, rank4(t)); }
        for (int i = 0; i < 4; i++) { int si = inv_[s[i]], n = 0; t[n++] = si; for (int j = 0; j < 4; j++) if (j != i) t[n++] = T[si][s[j]]; unite(r, rank4(t)); }
        for (int i = 0; i < 4; i++) t[i] = inv_[s[i]];
        unite(r, rank4(t));
    }
    for (uint64_t r = 0; r < N4; r++) par[r] = findr(r);
}

/* ---------- DFS over E2 for a fixed E1 ---------- */
static int E1[5], I1[5], Q1[25], nQ1, P1[25], nP1;
static bs linA[256], linB[256], F5, F6;   /* F5 = F6 = E1 u E1E1^-1E1 */
static int32_t cls1; static int q1cur;
static long long nleaf, ndup, nswap, ncheck, nsol;
static int bestcost = 1 << 30; static int bestE1[5], bestE2[5];
static int quiet = 0;
static int noswap = 0;
/* dedup hash */
#define HB 22
static uint64_t *hkey; static uint32_t *hgen, curgen = 1;
static long long hcount;
static int hash_insert(uint64_t key) {
    if (hcount >= (3LL << (HB - 2))) return 1;   /* table full: stop deduplicating (only costs time) */
    uint64_t h = (key * 0x9E3779B97F4A7C15ULL) >> (64 - HB);
    while (1) { if (hgen[h] != curgen) { hgen[h] = curgen; hkey[h] = key; return 1; } if (hkey[h] == key) return 0; h = (h + 1) & ((1ULL << HB) - 1); }
}

static void setup_E1(const int *e1) {
    for (int i = 0; i < 5; i++) { E1[i] = e1[i]; I1[i] = inv_[e1[i]]; }
    nQ1 = prodl(E1, 5, I1, 5, Q1); nP1 = prodl(I1, 5, E1, 5, P1);
    for (int y = 0; y < m; y++) {
        memset(&linA[y], 0, sizeof(bs)); memset(&linB[y], 0, sizeof(bs));
        int yi = inv_[y];
        for (int i = 0; i < 5; i++) { bset(&linA[y], T[E1[i]][yi]); bset(&linA[y], T[y][I1[i]]); bset(&linB[y], T[I1[i]][y]); bset(&linB[y], T[yi][E1[i]]); }
    }
    memset(&F5, 0, sizeof F5);
    for (int i = 0; i < 5; i++) bset(&F5, E1[i]);
    for (int a = 0; a < nQ1; a++) for (int i = 0; i < 5; i++) bset(&F5, T[Q1[a]][E1[i]]);
    F6 = F5;
}
static void initial_U(bs *UA, bs *UB) {
    bs ca, cb; memset(&ca, 0, sizeof ca); memset(&cb, 0, sizeof cb);
    for (int a = 0; a < nQ1; a++) for (int b = 0; b < nQ1; b++) bset(&ca, T[Q1[a]][Q1[b]]);
    for (int a = 0; a < nP1; a++) for (int b = 0; b < nP1; b++) bset(&cb, T[P1[a]][P1[b]]);
    for (int i = 0; i < 4; i++) { UA->w[i] = FULL.w[i] & ~ca.w[i]; UB->w[i] = FULL.w[i] & ~cb.w[i]; }
}

static void leaf(const int *Y) {
    nleaf++;
    int E2[5]; for (int i = 0; i < 5; i++) E2[i] = Y[i];
    for (int i = 1; i < 5; i++) for (int j = i; j > 0 && E2[j] < E2[j - 1]; j--) { int t = E2[j]; E2[j] = E2[j - 1]; E2[j - 1] = t; }
    uint64_t key = 0; for (int i = 0; i < 5; i++) key = key << 8 | E2[i];
    if (!hash_insert(key)) { ndup++; return; }
    hcount++;
    if (!noswap) { int32_t c2 = class5(E2); int q2 = qv[c2];
        if (q2 > q1cur || (q2 == q1cur && c2 > cls1)) { nswap++; return; } }
    ncheck++;
    /* C5 then C6, C2, C3 with a running miss count (early exit above the best near miss) */
    int I2[5]; for (int i = 0; i < 5; i++) I2[i] = inv_[E2[i]];
    int Q2[25], P2[25]; int nQ2 = prodl(E2, 5, I2, 5, Q2), nP2 = prodl(I2, 5, E2, 5, P2);
    int cost = 0; bs c;
    c = F5; for (int i = 0; i < 5; i++) bset(&c, E2[i]);
    for (int a = 0; a < nQ1; a++) for (int i = 0; i < 5; i++) bset(&c, T[Q1[a]][E2[i]]);
    for (int i = 0; i < 5; i++) for (int a = 0; a < nP2; a++) bset(&c, T[E1[i]][P2[a]]);
    for (int a = 0; a < nQ2; a++) for (int i = 0; i < 5; i++) bset(&c, T[Q2[a]][E2[i]]);
    cost += bmissing(&c); if (cost > bestcost) return;
    c = F6; for (int i = 0; i < 5; i++) bset(&c, E2[i]);
    for (int i = 0; i < 5; i++) for (int a = 0; a < nP1; a++) bset(&c, T[E2[i]][P1[a]]);
    for (int a = 0; a < nQ2; a++) for (int i = 0; i < 5; i++) { bset(&c, T[Q2[a]][E1[i]]); bset(&c, T[Q2[a]][E2[i]]); }
    cost += bmissing(&c); if (cost > bestcost) return;
    memset(&c, 0, sizeof c);
    for (int a = 0; a < nQ1; a++) bset(&c, Q1[a]);
    for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) { bset(&c, T[E1[i]][I2[j]]); bset(&c, T[E2[i]][I1[j]]); }
    for (int a = 0; a < nQ2; a++) for (int b = 0; b < nQ2; b++) bset(&c, T[Q2[a]][Q2[b]]);
    cost += bmissing(&c); if (cost > bestcost) return;
    memset(&c, 0, sizeof c);
    for (int a = 0; a < nP1; a++) bset(&c, P1[a]);
    for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) { bset(&c, T[I1[i]][E2[j]]); bset(&c, T[I2[i]][E1[j]]); }
    for (int a = 0; a < nP2; a++) for (int b = 0; b < nP2; b++) bset(&c, T[P2[a]][P2[b]]);
    cost += bmissing(&c); if (cost > bestcost) return;
    if (cost < bestcost) { bestcost = cost; memcpy(bestE1, E1, sizeof E1); memcpy(bestE2, E2, sizeof E2);
        if (!quiet) { printf("BEST %d E1 %d %d %d %d %d E2 %d %d %d %d %d\n", cost, E1[0], E1[1], E1[2], E1[3], E1[4], E2[0], E2[1], E2[2], E2[3], E2[4]); fflush(stdout); } }
    if (cost == 0) { nsol++; printf("SOL E1 %d %d %d %d %d E2 %d %d %d %d %d\n", E1[0], E1[1], E1[2], E1[3], E1[4], E2[0], E2[1], E2[2], E2[3], E2[4]); fflush(stdout); }
}

static int inY(const int *Y, int k, int y) { for (int i = 0; i < k; i++) if (Y[i] == y) return 1; return 0; }
static void dfs(int *Y, int k, bs UA, bs UB);
static void dfs_free(int *Y, int k, int start) {
    for (int y = start; y < m; y++) if (!inY(Y, k, y)) { Y[k] = y; if (k + 1 == 5) leaf(Y); else dfs_free(Y, k + 1, y + 1); }
}
static void add_and_recurse(int *Y, int k, bs UA, bs UB, int y) {
    if (inY(Y, k, y)) return;
    int yi = inv_[y];
    for (int i = 0; i < NW; i++) { UA.w[i] &= ~linA[y].w[i]; UB.w[i] &= ~linB[y].w[i]; }
    for (int i = 0; i < k; i++) {
        int z = Y[i], zi = inv_[z];
        int a1 = T[y][zi], a2 = T[z][yi], b1 = T[zi][y], b2 = T[yi][z];
        UA.w[a1 >> 6] &= ~(1ULL << (a1 & 63)); UA.w[a2 >> 6] &= ~(1ULL << (a2 & 63));
        UB.w[b1 >> 6] &= ~(1ULL << (b1 & 63)); UB.w[b2 >> 6] &= ~(1ULL << (b2 & 63));
    }
    Y[k] = y; dfs(Y, k + 1, UA, UB);
}
static void dfs(int *Y, int k, bs UA, bs UB) {
    int ea = bempty(&UA), eb = bempty(&UB);
    if (k == 5) { if (ea && eb) leaf(Y); return; }
    if (ea && eb) { dfs_free(Y, k, 0); return; }   /* everything covered: the remaining elements are free */
    int x, sideA = !ea;
    { const bs *U = sideA ? &UA : &UB; int i = 0; while (!U->w[i]) i++; x = i * 64 + __builtin_ctzll(U->w[i]); }
    int xi = inv_[x];
    if (sideA) {
        for (int i = 0; i < 5; i++) { add_and_recurse(Y, k, UA, UB, T[xi][E1[i]]); add_and_recurse(Y, k, UA, UB, T[x][E1[i]]); }
        for (int i = 0; i < k; i++) { add_and_recurse(Y, k, UA, UB, T[x][Y[i]]); add_and_recurse(Y, k, UA, UB, T[xi][Y[i]]); }
        if (k <= 3) for (int a = 0; a < m; a++) {
            int b = T[x][a]; if (inY(Y, k, a) || inY(Y, k, b)) continue;
            bs ua = UA, ub = UB; int ya = a;
            /* add a then b */
            int Y2[5]; memcpy(Y2, Y, sizeof(int) * k);
            int yi_ = inv_[ya];
            for (int i = 0; i < NW; i++) { ua.w[i] &= ~linA[ya].w[i]; ub.w[i] &= ~linB[ya].w[i]; }
            for (int i = 0; i < k; i++) { int z = Y[i], zi = inv_[z]; int a1 = T[ya][zi], a2 = T[z][yi_], b1 = T[zi][ya], b2 = T[yi_][z];
                ua.w[a1 >> 6] &= ~(1ULL << (a1 & 63)); ua.w[a2 >> 6] &= ~(1ULL << (a2 & 63)); ub.w[b1 >> 6] &= ~(1ULL << (b1 & 63)); ub.w[b2 >> 6] &= ~(1ULL << (b2 & 63)); }
            Y2[k] = ya;
            add_and_recurse(Y2, k + 1, ua, ub, b);
        }
    } else {
        for (int i = 0; i < 5; i++) { add_and_recurse(Y, k, UA, UB, T[E1[i]][x]); add_and_recurse(Y, k, UA, UB, T[E1[i]][xi]); }
        for (int i = 0; i < k; i++) { add_and_recurse(Y, k, UA, UB, T[Y[i]][x]); add_and_recurse(Y, k, UA, UB, T[Y[i]][xi]); }
        if (k <= 3) for (int a = 0; a < m; a++) {
            int b = T[a][x]; if (inY(Y, k, a) || inY(Y, k, b)) continue;
            bs ua = UA, ub = UB; int ya = a; int Y2[5]; memcpy(Y2, Y, sizeof(int) * k);
            int yi_ = inv_[ya];
            for (int i = 0; i < NW; i++) { ua.w[i] &= ~linA[ya].w[i]; ub.w[i] &= ~linB[ya].w[i]; }
            for (int i = 0; i < k; i++) { int z = Y[i], zi = inv_[z]; int a1 = T[ya][zi], a2 = T[z][yi_], b1 = T[zi][ya], b2 = T[yi_][z];
                ua.w[a1 >> 6] &= ~(1ULL << (a1 & 63)); ua.w[a2 >> 6] &= ~(1ULL << (a2 & 63)); ub.w[b1 >> 6] &= ~(1ULL << (b1 & 63)); ub.w[b2 >> 6] &= ~(1ULL << (b2 & 63)); }
            Y2[k] = ya;
            add_and_recurse(Y2, k + 1, ua, ub, b);
        }
    }
}

static void run_E1(const int *e1) {
    setup_E1(e1); cls1 = class5(e1);
    bs UA, UB; initial_U(&UA, &UB); q1cur = bcount(&UA) + bcount(&UB);
    curgen++; if (curgen == 0) { memset(hgen, 0, sizeof(uint32_t) << HB); curgen = 1; }
    hcount = 0;
    int Y[5]; dfs(Y, 0, UA, UB);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: split15 TAB rand|ex|bf ...\n"); return 2; }
    readtab(argv[1]);
    if (!strcmp(argv[2], "rand")) {
        int N = argc > 3 ? atoi(argv[3]) : 100; rs += argc > 4 ? atoll(argv[4]) : 1;
        int bad = 0, nvalid = 0;
        for (int it = 0; it < N; it++) {
            int e1[5], e2[5]; rand_set(e1, 0); rand_set(e2, 0);
            if (!build(e1, e2)) { it--; continue; }
            int miss[6]; conds(e1, e2, miss);
            int dist[1024], f[6];
            bfs(0, dist); f[0] = farcount(dist, 0, m, 4); f[4] = farcount(dist, m, 2 * m, 4);
            int d5 = farcount(dist, 0, 4 * m, 5);
            bfs(2 * m, dist); f[1] = farcount(dist, 2 * m, 3 * m, 4); f[5] = farcount(dist, 3 * m, 4 * m, 4); d5 += farcount(dist, 0, 4 * m, 5);
            bfs(m, dist); f[2] = farcount(dist, m, 2 * m, 4); d5 += farcount(dist, 0, 4 * m, 5);
            bfs(3 * m, dist); f[3] = farcount(dist, 3 * m, 4 * m, 4); d5 += farcount(dist, 0, 4 * m, 5);
            int ok = 1; for (int i = 0; i < 6; i++) if (f[i] != miss[i]) ok = 0;
            int allc = 1; for (int i = 0; i < 6; i++) if (miss[i]) allc = 0;
            if ((d5 == 0) != allc) ok = 0;
            if (allc) nvalid++;
            if (!ok) { bad++; printf("MISMATCH it %d conds %d %d %d %d %d %d bfs %d %d %d %d %d %d d5 %d\n", it, miss[0], miss[1], miss[2], miss[3], miss[4], miss[5], f[0], f[1], f[2], f[3], f[4], f[5], d5); }
            if (it < 3) printf("it %d conds %d %d %d %d %d %d bfs %d %d %d %d %d %d d5far %d\n", it, miss[0], miss[1], miss[2], miss[3], miss[4], miss[5], f[0], f[1], f[2], f[3], f[4], f[5], d5);
        }
        printf("rand: %d tests, %d mismatches, %d valid\n", N, bad, nvalid);
        return bad != 0;
    }
    hkey = malloc(sizeof(uint64_t) << HB); hgen = calloc(1ULL << HB, sizeof(uint32_t));
    double t0 = now();
    build_classes();
    long long nclass = 0; for (uint64_t r = 0; r < N4; r++) if (par[r] == (int32_t)r) nclass++;
    qv = malloc(sizeof(int16_t) * N4);
    for (uint64_t r = 0; r < N4; r++) if (par[r] == (int32_t)r) {
        int s[4]; unrank4(r, s); int e1[5] = {0, s[0], s[1], s[2], s[3]}; setup_E1(e1);
        bs UA, UB; initial_U(&UA, &UB); qv[r] = bcount(&UA) + bcount(&UB);
    }
    fprintf(stderr, "m %d ngen %d 4-subsets %llu E1 classes %lld (%.1f s)\n", m, ngen, (unsigned long long)N4, nclass, now() - t0);
    if (!strcmp(argv[2], "stats")) {   /* |UA|+|UB| per E1 class: histogram and the best classes */
        static long long hist[600]; long long c = 0; int top = argc > 3 ? atoi(argv[3]) : 5;
        int bestv[64]; long long bestk[64]; for (int i = 0; i < 64; i++) bestv[i] = 1 << 30;
        for (uint64_t r = 0; r < N4; r++) if (par[r] == (int32_t)r) {
            int s[4]; unrank4(r, s); int e1[5] = {0, s[0], s[1], s[2], s[3]}; setup_E1(e1);
            bs UA, UB; initial_U(&UA, &UB); int v = bcount(&UA) + bcount(&UB); hist[v]++;
            for (int i = 0; i < top; i++) if (v < bestv[i]) { for (int j = top - 1; j > i; j--) { bestv[j] = bestv[j - 1]; bestk[j] = bestk[j - 1]; } bestv[i] = v; bestk[i] = c; break; }
            c++;
        }
        for (int v = 0; v < 600; v++) if (hist[v]) printf("UA+UB %d: %lld\n", v, hist[v]);
        for (int i = 0; i < top; i++) printf("best %d: class index %lld UA+UB %d\n", i, bestk[i], bestv[i]);
        return 0;
    }
    if (!strcmp(argv[2], "bf")) {
        long long K = atoll(argv[3] + (argv[3][0] == 'q')), c = 0; uint64_t r;
        if (argv[3][0] == 'q') { for (r = 0; r < N4; r++) if (par[r] == (int32_t)r && qv[r] == K) break; }   /* first class with q = K */
        else for (r = 0; r < N4; r++) if (par[r] == (int32_t)r) { if (c == K) break; c++; }
        int s[4]; unrank4(r, s); int e1[5] = {0, s[0], s[1], s[2], s[3]};
        noswap = 1; quiet = 1; bestcost = 1 << 30;
        double t1 = now(); run_E1(e1); long long ndfs = hcount; double tdfs = now() - t1;
        /* brute force: all 5-subsets E2 with C1 and C4 */
        bs UA0, UB0; initial_U(&UA0, &UB0);
        printf("E1 %d %d %d %d %d |UA| %d |UB| %d dfs leaves %lld distinct %lld (%.2f s)\n", e1[0], e1[1], e1[2], e1[3], e1[4], bcount(&UA0), bcount(&UB0), nleaf, ndfs, tdfs);
        long long nbf = 0; t1 = now();
        int y[5];
        for (y[0] = 0; y[0] < m; y[0]++) for (y[1] = y[0] + 1; y[1] < m; y[1]++) for (y[2] = y[1] + 1; y[2] < m; y[2]++) {
            bs ua3 = UA0, ub3 = UB0;
            for (int i = 0; i < 3; i++) { for (int w = 0; w < NW; w++) { ua3.w[w] &= ~linA[y[i]].w[w]; ub3.w[w] &= ~linB[y[i]].w[w]; } }
            for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (i != j) { int a = T[y[i]][inv_[y[j]]], b = T[inv_[y[i]]][y[j]]; ua3.w[a >> 6] &= ~(1ULL << (a & 63)); ub3.w[b >> 6] &= ~(1ULL << (b & 63)); }
            for (y[3] = y[2] + 1; y[3] < m; y[3]++) {
                bs ua4 = ua3, ub4 = ub3;
                for (int w = 0; w < NW; w++) { ua4.w[w] &= ~linA[y[3]].w[w]; ub4.w[w] &= ~linB[y[3]].w[w]; }
                for (int j = 0; j < 3; j++) { int a1 = T[y[3]][inv_[y[j]]], a2 = T[y[j]][inv_[y[3]]], b1 = T[inv_[y[3]]][y[j]], b2 = T[inv_[y[j]]][y[3]];
                    ua4.w[a1 >> 6] &= ~(1ULL << (a1 & 63)); ua4.w[a2 >> 6] &= ~(1ULL << (a2 & 63)); ub4.w[b1 >> 6] &= ~(1ULL << (b1 & 63)); ub4.w[b2 >> 6] &= ~(1ULL << (b2 & 63)); }
                for (y[4] = y[3] + 1; y[4] < m; y[4]++) {
                    bs ua = ua4, ub = ub4;
                    for (int w = 0; w < NW; w++) { ua.w[w] &= ~linA[y[4]].w[w]; ub.w[w] &= ~linB[y[4]].w[w]; }
                    for (int j = 0; j < 4; j++) { int a1 = T[y[4]][inv_[y[j]]], a2 = T[y[j]][inv_[y[4]]], b1 = T[inv_[y[4]]][y[j]], b2 = T[inv_[y[j]]][y[4]];
                        ua.w[a1 >> 6] &= ~(1ULL << (a1 & 63)); ua.w[a2 >> 6] &= ~(1ULL << (a2 & 63)); ub.w[b1 >> 6] &= ~(1ULL << (b1 & 63)); ub.w[b2 >> 6] &= ~(1ULL << (b2 & 63)); }
                    if (bempty(&ua) && bempty(&ub)) nbf++;
                }
            }
        }
        printf("brute force: %lld E2 with C1 and C4 (%.1f s); dfs distinct %lld -> %s\n", nbf, now() - t1, ndfs, nbf == ndfs ? "AGREE" : "DISAGREE");
        return 0;
    }
    /* ex */
    int NP = argc > 3 ? atoi(argv[3]) : 1, PR = argc > 4 ? atoi(argv[4]) : 0;
    long long idx = 0, done = 0; double tl = now();
    for (uint64_t r = 0; r < N4; r++) {
        if (par[r] != (int32_t)r) continue;
        if (idx++ % NP != PR) continue;
        int s[4]; unrank4(r, s); int e1[5] = {0, s[0], s[1], s[2], s[3]};
        run_E1(e1); done++;
        if (now() - tl > 60) { tl = now(); fprintf(stderr, "progress %lld/%lld E1, leaves %lld distinct-checked %lld sols %lld best %d (%.0f s)\n", done, nclass / NP, nleaf, ncheck, nsol, bestcost, now() - t0); }
    }
    printf("DONE m %d E1 %lld leaves %lld dup %lld swap %lld checked %lld solutions %lld best %d E1 %d %d %d %d %d E2 %d %d %d %d %d secs %.1f\n",
           m, done, nleaf, ndup, nswap, ncheck, nsol, bestcost, bestE1[0], bestE1[1], bestE1[2], bestE1[3], bestE1[4], bestE2[0], bestE2[1], bestE2[2], bestE2[3], bestE2[4], now() - t0);
    return 0;
}
