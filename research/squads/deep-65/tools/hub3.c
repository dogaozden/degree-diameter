/* hub3.c (deep-65): the hub family of type "1,3|1,3", block counts 5,1,1,1 (Haar part of degree 5, hubs of size 3
 * that are also joined to 3 hubs on the other side), as six covering conditions; validation against BFS; exact search.
 *
 * Model: G of order m, S subset of G (|S| = 5), K, H subgroups of order 3, z in G with H n zKz^-1 = 1.
 *   A0 = G, B0 = G: x ~ xs.   B1 = G/K: hub xK ~ A0 vertices xK.   A1 = G/H: hub yH ~ B0 vertices yH.
 *   hub-hub: A1 hub yH ~ B1 hub xK iff y^-1 x in H z K (each hub gets 3 hubs).  n = 2m + 2m/3, 6-regular.
 * (t18 with k = 3, N = 5,1,1,1 is the same family; its (g01, g10, g11, H, K) map to K^g01, H^g10, z.)
 * Same-side distance <= 4 for every pair <=> diameter <= 5. With T = SS^-1, T' = S^-1 S:
 *  (1) A0-A0: {e} u T u K u TT u TK u KT u SHS^-1 u SHzK u Kz^-1HS^-1 u Kz^-1HzK = G
 *  (2) A0-A1: [(T u K) S u K z^-1 H u (T u SHz u Kz^-1Hz) K z^-1] H = G
 *  (3) A1-A1: H T' H u H S^-1 K z^-1 H u H z K S H u (H z K z^-1 H)^2 = G
 *  (4)-(6): the same with (S, K, H, z) -> (S^-1, H, K, z^-1) (swap sides).
 * Symmetries used by the exact search: (S, K, H, z) ~ (d^-1 S c, K^d, H^c, c^-1 z d) and z ~ h z k.
 *
 * usage: hub3 TABLE eval "S" "Kgens" "Hgens" z [OUT.edges]
 *        hub3 TABLE rand N SEED              (random parameters: condition counts vs BFS from the 4 representatives)
 *        hub3 TABLE ex [NPROC PROC]           (exact search over all class pairs of order-3 subgroups)
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
static int m, q, *T, inv[MAXM];
#define MUL(x, y) T[(x) * m + (y)]
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static int K[3], H[3], S[5], z;
static int lcK[MAXM], lcH[MAXM];         /* left coset index of g (gK, gH) */

static int gensub(int *gens, int ng, int *el) {
    char in[MAXM]; memset(in, 0, m); int n = 1; el[0] = 0; in[0] = 1;
    for (int i = 0; i < n; i++) for (int j = 0; j < ng; j++) { int x = MUL(el[i], gens[j]); if (!in[x]) { in[x] = 1; el[n++] = x; } }
    return n;
}
static void setup_cosets(void) {
    for (int x = 0; x < m; x++) lcK[x] = lcH[x] = -1;
    int c = 0; for (int x = 0; x < m; x++) if (lcK[x] < 0) { for (int i = 0; i < 3; i++) lcK[MUL(x, K[i])] = c; c++; }
    c = 0; for (int x = 0; x < m; x++) if (lcH[x] < 0) { for (int i = 0; i < 3; i++) lcH[MUL(x, H[i])] = c; c++; }
}

/* ---- general evaluation with element sets (char arrays) ---- */
typedef struct { int n; int e[8192]; } set_t;
static void sadd(set_t *s, int x) { s->e[s->n++] = x; }
static void prod(set_t *out, const int *a, int na, const int *b, int nb) { for (int i = 0; i < na; i++) for (int j = 0; j < nb; j++) sadd(out, MUL(a[i], b[j])); }
static void prod3(set_t *out, const int *a, int na, const int *b, int nb, const int *c, int nc) {
    for (int i = 0; i < na; i++) for (int j = 0; j < nb; j++) { int x = MUL(a[i], b[j]); for (int k = 0; k < nc; k++) sadd(out, MUL(x, c[k])); } }
static int miss_elems(set_t *s) { char c[MAXM]; memset(c, 0, m); for (int i = 0; i < s->n; i++) c[s->e[i]] = 1; int k = 0; for (int x = 0; x < m; x++) k += !c[x]; return k; }
static int miss_cos(set_t *s, int *lc) { char c[MAXM]; memset(c, 0, q); for (int i = 0; i < s->n; i++) c[lc[s->e[i]]] = 1; int k = 0; for (int x = 0; x < q; x++) k += !c[x]; return k; }

/* conditions for parameters (S, K, H, z): returns misses: (1) elements, (2) A1 cosets, (3) elements, (4)-(6) dual */
static void conditions(const int *S_, const int *K_, const int *H_, int z_, int *miss, int *lcH_, int *lcK_) {
    static set_t s; int Sinv[5], Tl[25], nT = 0, zi = inv[z_];
    for (int i = 0; i < 5; i++) Sinv[i] = inv[S_[i]];
    for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) Tl[nT++] = MUL(S_[i], Sinv[j]);   /* T (with e) */
    int Tp[25], nTp = 0; for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) Tp[nTp++] = MUL(Sinv[i], S_[j]);
    int e0 = 0, zz[1] = {z_}, zzi[1] = {zi};
    /* (1) */
    s.n = 0; sadd(&s, e0);
    prod(&s, Tl, 25, Tl, 25); prod(&s, Tl, 25, K_, 3); prod(&s, K_, 3, Tl, 25);
    prod3(&s, S_, 5, H_, 3, Sinv, 5);
    { set_t *t = &s; int SH[15], n = 0; for (int i = 0; i < 5; i++) for (int j = 0; j < 3; j++) SH[n++] = MUL(S_[i], H_[j]);
      int SHz[15]; for (int i = 0; i < 15; i++) SHz[i] = MUL(SH[i], z_);
      prod(t, SHz, 15, K_, 3);
      int Kzi[3]; for (int i = 0; i < 3; i++) Kzi[i] = MUL(K_[i], zi);
      int KziH[9], n2 = 0; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) KziH[n2++] = MUL(Kzi[i], H_[j]);
      prod(t, KziH, 9, Sinv, 5);
      int KziHz[9]; for (int i = 0; i < 9; i++) KziHz[i] = MUL(KziH[i], z_);
      prod(t, KziHz, 9, K_, 3); }
    miss[0] = miss_elems(&s);
    /* (2): A1 cosets */
    s.n = 0;
    { int TK[28], n = 0; for (int i = 0; i < 25; i++) TK[n++] = Tl[i]; for (int i = 0; i < 3; i++) TK[n++] = K_[i];
      prod(&s, TK, 28, S_, 5);
      for (int i = 0; i < 3; i++) sadd(&s, MUL(K_[i], zi));
      int U[25 + 15 + 9], nu = 0; for (int i = 0; i < 25; i++) U[nu++] = Tl[i];
      for (int i = 0; i < 5; i++) for (int j = 0; j < 3; j++) U[nu++] = MUL(MUL(S_[i], H_[j]), z_);
      for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) U[nu++] = MUL(MUL(MUL(K_[i], zi), H_[j]), z_);
      int Kzi[3]; for (int i = 0; i < 3; i++) Kzi[i] = MUL(K_[i], zi);
      prod(&s, U, nu, Kzi, 3); }
    miss[1] = miss_cos(&s, lcH_);
    /* (3) */
    s.n = 0;
    prod3(&s, H_, 3, Tp, 25, H_, 3);
    { int SiK[15], n = 0; for (int i = 0; i < 5; i++) for (int j = 0; j < 3; j++) SiK[n++] = MUL(MUL(Sinv[i], K_[j]), zi);
      prod3(&s, H_, 3, SiK, 15, H_, 3);
      int zKS[15]; n = 0; for (int i = 0; i < 3; i++) for (int j = 0; j < 5; j++) zKS[n++] = MUL(MUL(z_, K_[i]), S_[j]);
      prod3(&s, H_, 3, zKS, 15, H_, 3);
      /* (H z K z^-1 H)^2 */
      static set_t a; a.n = 0; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) for (int k = 0; k < 3; k++) sadd(&a, MUL(MUL(MUL(MUL(H_[i], z_), K_[j]), zi), H_[k]));
      char c[MAXM]; memset(c, 0, m); int L[MAXM], nl = 0; for (int i = 0; i < a.n; i++) if (!c[a.e[i]]) { c[a.e[i]] = 1; L[nl++] = a.e[i]; }
      prod(&s, L, nl, L, nl); }
    miss[2] = miss_elems(&s);
    (void)zz; (void)zzi;
}
static void all_conditions(int *miss) {
    conditions(S, K, H, z, miss, lcH, lcK);
    int Si[5]; for (int i = 0; i < 5; i++) Si[i] = inv[S[i]];
    conditions(Si, H, K, inv[z], miss + 3, lcK, lcH);
}

/* ---- graph ---- */
static int nv, adj[4 * MAXM][6], dg[4 * MAXM];
static void addedge(int u, int v) { adj[u][dg[u]++] = v; adj[v][dg[v]++] = u; }
static void build(void) {
    nv = 2 * m + 2 * q; memset(dg, 0, sizeof(int) * nv);
    int A1 = m, B0 = m + q, B1 = 2 * m + q;
    for (int x = 0; x < m; x++) { for (int i = 0; i < 5; i++) addedge(x, B0 + MUL(x, S[i])); addedge(x, B1 + lcK[x]); }
    for (int y = 0; y < m; y++) addedge(A1 + lcH[y], B0 + y);
    /* hub-hub: hub yH ~ hubs y h z K */
    char done[MAXM]; memset(done, 0, q);
    for (int y = 0; y < m; y++) { int c = lcH[y]; if (done[c]) continue; done[c] = 1;
        for (int i = 0; i < 3; i++) addedge(A1 + c, B1 + lcK[MUL(MUL(y, H[i]), z)]); }
}
static int bfs_far(int src, int *far_by_orbit) {  /* counts same-side vertices at distance > 4, per orbit */
    static int dist[4 * MAXM], qu[4 * MAXM];
    for (int i = 0; i < nv; i++) dist[i] = -1;
    int h = 0, t = 0; dist[src] = 0; qu[t++] = src;
    while (h < t) { int x = qu[h++]; if (dist[x] >= 4) continue; for (int i = 0; i < dg[x]; i++) { int y = adj[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
    int A1 = m, B0 = m + q, B1 = 2 * m + q;
    for (int i = 0; i < 4; i++) far_by_orbit[i] = 0;
    for (int v = 0; v < nv; v++) if (dist[v] < 0) { int o = v < A1 ? 0 : v < B0 ? 1 : v < B1 ? 2 : 3; far_by_orbit[o]++; }
    return 0;
}

static int rand_order3(int *el) { /* random subgroup of order 3 */
    for (;;) { int g = 1 + rnd() % (m - 1); int g2 = MUL(g, g), g3 = MUL(g2, g); if (g3 == 0 && g != 0) { el[0] = 0; el[1] = g; el[2] = g2; return 1; } }
}


/* ---------------- exact search ---------------- */
static int dcH[MAXM], dcK[MAXM], ndcH, ndcK;
static uint64_t F3, F6, full3, full6;
static uint64_t fullq[2];
static long long nleaf, np36, np25, nsol; static long long hist[64];
static int bestm;
static inline void setb(uint64_t *c, int x) { c[x >> 6] |= 1ULL << (x & 63); }
static int Kzi[3], KziHz_K[27], nKzHzK;   /* fixed sets */
static int check25_fast(void) {
    /* (2) cosets of H, (5) cosets of K, by element products (q <= 128) */
    uint64_t a[2] = {0, 0}, b[2] = {0, 0};
    int zi = inv[z], Si[5]; for (int i = 0; i < 5; i++) Si[i] = inv[S[i]];
    /* (2): (T u K) S, K z^-1, (T u SHz u Kz^-1Hz) K z^-1  -> lcH */
    for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) { int t = MUL(S[i], Si[j]);
        for (int l = 0; l < 5; l++) setb(a, lcH[MUL(t, S[l])]);
        for (int k = 0; k < 3; k++) setb(a, lcH[MUL(t, Kzi[k])]); }
    for (int k = 1; k < 3; k++) for (int l = 0; l < 5; l++) setb(a, lcH[MUL(K[k], S[l])]);
    for (int i = 0; i < 27; i++) setb(a, lcH[KziHz_K[i]]);   /* K z^-1 H z K z^-1 (incl. K z^-1) */
    for (int i = 0; i < 5; i++) for (int h = 0; h < 3; h++) { int x = MUL(MUL(S[i], H[h]), z); for (int k = 0; k < 3; k++) setb(a, lcH[MUL(x, Kzi[k])]); }
    if (a[0] != fullq[0] || a[1] != fullq[1]) return 0;
    /* (5): dual: (T' u H) S^-1, H z, (T' u S^-1 K z^-1 u H z K z^-1) H z -> lcK */
    int Hz[3]; for (int h = 0; h < 3; h++) Hz[h] = MUL(H[h], z);
    for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) { int t = MUL(Si[i], S[j]);
        for (int l = 0; l < 5; l++) setb(b, lcK[MUL(t, Si[l])]);
        for (int h = 0; h < 3; h++) setb(b, lcK[MUL(t, Hz[h])]); }
    for (int h = 1; h < 3; h++) for (int l = 0; l < 5; l++) setb(b, lcK[MUL(H[h], Si[l])]);
    for (int h = 0; h < 3; h++) for (int k = 0; k < 3; k++) for (int h2 = 0; h2 < 3; h2++) setb(b, lcK[MUL(MUL(MUL(MUL(H[h], z), K[k]), zi), Hz[h2])]);
    for (int i = 0; i < 5; i++) for (int k = 0; k < 3; k++) { int x = MUL(MUL(Si[i], K[k]), zi); for (int h = 0; h < 3; h++) setb(b, lcK[MUL(x, Hz[h])]); }
    return b[0] == fullq[0] && b[1] == fullq[1];
}
static void run_ex(int NPROC, int PROC) {
    /* order-3 subgroups and classes */
    static int sub[MAXM][3]; int ns = 0;
    for (int g = 1; g < m; g++) { int g2 = MUL(g, g); if (MUL(g2, g) != 0) continue; int dup = 0;
        for (int i = 0; i < ns; i++) if (sub[i][1] == g || sub[i][2] == g) dup = 1;
        if (!dup) { sub[ns][0] = 0; sub[ns][1] = g; sub[ns][2] = g2; ns++; } }
    int cls[MAXM], ncls = 0, rep[MAXM];
    for (int i = 0; i < ns; i++) cls[i] = -1;
    for (int i = 0; i < ns; i++) if (cls[i] < 0) { rep[ncls] = i;
        for (int x = 0; x < m; x++) { int y = MUL(MUL(inv[x], sub[i][1]), x); for (int j = 0; j < ns; j++) if (sub[j][1] == y || sub[j][2] == y) cls[j] = ncls; }
        ncls++; }
    printf("order %d: %d subgroups of order 3 in %d classes\n", m, ns, ncls); fflush(stdout);
    for (int ca = 0; ca < ncls; ca++) for (int cb = ca; cb < ncls; cb++) {
        double t0 = now();
        memcpy(K, sub[rep[ca]], sizeof K); memcpy(H, sub[rep[cb]], sizeof H); setup_cosets();
        int NK[MAXM], nNK = 0, NH[MAXM], nNH = 0;
        for (int x = 0; x < m; x++) { int y = MUL(MUL(inv[x], K[1]), x); if (y == K[1] || y == K[2]) NK[nNK++] = x;
                                      y = MUL(MUL(inv[x], H[1]), x); if (y == H[1] || y == H[2]) NH[nNH++] = x; }
        for (int x = 0; x < m; x++) dcH[x] = dcK[x] = -1;
        ndcH = ndcK = 0;
        for (int x = 0; x < m; x++) if (dcH[x] < 0) { for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) dcH[MUL(MUL(H[i], x), H[j])] = ndcH; ndcH++; }
        for (int x = 0; x < m; x++) if (dcK[x] < 0) { for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) dcK[MUL(MUL(K[i], x), K[j])] = ndcK; ndcK++; }
        if (ndcH > 64 || ndcK > 64 || q > 128) { printf("pair %d,%d: too many double cosets (%d, %d) or cosets %d; skipped\n", ca, cb, ndcH, ndcK, q); continue; }
        full3 = ndcH == 64 ? ~0ULL : (1ULL << ndcH) - 1; full6 = ndcK == 64 ? ~0ULL : (1ULL << ndcK) - 1;
        fullq[0] = q >= 64 ? ~0ULL : (1ULL << q) - 1; fullq[1] = q > 64 ? (q == 128 ? ~0ULL : (1ULL << (q - 64)) - 1) : 0;
        /* H-K double cosets of full size; z orbits under z -> c^-1 z d */
        int dcHK[MAXM], ndcHK = 0, fullz[MAXM];
        for (int x = 0; x < m; x++) dcHK[x] = -1;
        for (int x = 0; x < m; x++) if (dcHK[x] < 0) { int cnt = 0; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) { int y = MUL(MUL(H[i], x), K[j]); if (dcHK[y] < 0) { dcHK[y] = ndcHK; cnt++; } } fullz[ndcHK] = cnt == 9; ndcHK++; }
        int zorb[MAXM], nzo = 0, zrep[MAXM];
        for (int i = 0; i < ndcHK; i++) zorb[i] = -1;
        for (int x = 0; x < m; x++) { int dx = dcHK[x]; if (!fullz[dx] || zorb[dx] >= 0) continue;
            zrep[nzo] = x;
            for (int i = 0; i < nNH; i++) for (int j = 0; j < nNK; j++) zorb[dcHK[MUL(MUL(inv[NH[i]], x), NK[j])]] = nzo;
            nzo++; }
        printf("pair K class %d, H class %d: |N(K)| %d |N(H)| %d, H-dc %d, K-dc %d, cosets %d, z-orbits %d\n", ca, cb, nNK, nNH, ndcH, ndcK, q, nzo); fflush(stdout);
        nleaf = np36 = np25 = nsol = 0; memset(hist, 0, sizeof hist); bestm = 1 << 30;
        for (int zo = 0; zo < nzo; zo++) {
            z = zrep[zo]; int zi = inv[z];
            for (int k = 0; k < 3; k++) Kzi[k] = MUL(K[k], zi);
            nKzHzK = 0; for (int k = 0; k < 3; k++) for (int h = 0; h < 3; h++) for (int k2 = 0; k2 < 3; k2++) KziHz_K[nKzHzK++] = MUL(MUL(MUL(MUL(K[k], zi), H[h]), z), Kzi[k2]);
            /* fixed parts of (3), (6): (HzKz^-1H)^2, (Kz^-1HzK)^2 */
            { char c[MAXM]; int L[MAXM], nl = 0; memset(c, 0, m);
              for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) for (int k = 0; k < 3; k++) { int x = MUL(MUL(MUL(MUL(H[i], z), K[j]), zi), H[k]); if (!c[x]) { c[x] = 1; L[nl++] = x; } }
              F3 = 0; for (int i = 0; i < nl; i++) for (int j = 0; j < nl; j++) F3 |= 1ULL << dcH[MUL(L[i], L[j])];
              memset(c, 0, m); nl = 0;
              for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) for (int k = 0; k < 3; k++) { int x = MUL(MUL(MUL(MUL(K[i], zi), H[j]), z), K[k]); if (!c[x]) { c[x] = 1; L[nl++] = x; } }
              F6 = 0; for (int i = 0; i < nl; i++) for (int j = 0; j < nl; j++) F6 |= 1ULL << dcK[MUL(L[i], L[j])]; }
            /* stabiliser of z and its orbits on G */
            int sd[MAXM * 4], sc[MAXM * 4], nst = 0;
            for (int i = 0; i < nNK; i++) for (int j = 0; j < nNH; j++) if (dcHK[MUL(MUL(inv[NH[j]], z), NK[i])] == dcHK[z]) { sd[nst] = NK[i]; sc[nst] = NH[j]; nst++; }
            int orb[MAXM], norb = 0, osz[MAXM], orep[MAXM];
            for (int x = 0; x < m; x++) orb[x] = -1;
            for (int x = 0; x < m; x++) if (orb[x] < 0) { int cnt = 0;
                for (int i = 0; i < nst; i++) { int y = MUL(MUL(inv[sd[i]], x), sc[i]); if (orb[y] < 0) { orb[y] = norb; cnt++; } }
                osz[norb] = cnt; orep[norb] = x; norb++; }
            int oord[MAXM]; for (int o = 0; o < norb; o++) oord[o] = o;
            for (int i = 0; i < norb; i++) for (int j = i + 1; j < norb; j++) if (osz[oord[j]] > osz[oord[i]]) { int t = oord[i]; oord[i] = oord[j]; oord[j] = t; }
            int elist[MAXM], ne = 0; for (int i = 0; i < norb; i++) for (int x = 0; x < m; x++) if (orb[x] == oord[i]) elist[ne++] = x;
            /* per-element masks for (3) and (6) */
            static uint64_t e3[MAXM], e6[MAXM];
            for (int s = 0; s < m; s++) { uint64_t a = 0, b = 0; int si = inv[s];
                for (int k = 0; k < 3; k++) { a |= 1ULL << dcH[MUL(MUL(si, K[k]), zi)]; a |= 1ULL << dcH[MUL(MUL(z, K[k]), s)]; }
                for (int h = 0; h < 3; h++) { b |= 1ULL << dcK[MUL(MUL(s, H[h]), z)]; b |= 1ULL << dcK[MUL(MUL(zi, H[h]), si)]; }
                e3[s] = a; e6[s] = b; }
            int start = 0;
            for (int p = 0; p < norb; p++) {
                int o = oord[p], r = orep[o];
                int cand[MAXM], nc = 0; for (int i = start; i < ne; i++) if (elist[i] != r) cand[nc++] = elist[i];
                start += osz[o];
                if (nc < 4) break;
                S[0] = r;
                int idx[5]; uint64_t m3[5], m6[5];
                m3[0] = F3 | e3[r] | (1ULL << dcH[0]); m6[0] = F6 | e6[r] | (1ULL << dcK[0]);
                int lvl = 1; idx[1] = -1;
                while (lvl >= 1) {
                    idx[lvl]++;
                    if (idx[lvl] > nc - (5 - lvl)) { lvl--; continue; }
                    if (lvl == 1 && (idx[1] % NPROC) != PROC) continue;
                    int s = cand[idx[lvl]]; S[lvl] = s;
                    uint64_t a = m3[lvl - 1] | e3[s], b = m6[lvl - 1] | e6[s];
                    for (int i = 0; i < lvl; i++) {
                        a |= (1ULL << dcH[MUL(inv[s], S[i])]) | (1ULL << dcH[MUL(inv[S[i]], s)]);
                        b |= (1ULL << dcK[MUL(s, inv[S[i]])]) | (1ULL << dcK[MUL(S[i], inv[s])]);
                    }
                    m3[lvl] = a; m6[lvl] = b;
                    if (lvl < 4) { lvl++; idx[lvl] = idx[lvl - 1]; continue; }
                    nleaf++;
                    if (a != full3 || b != full6) continue;
                    np36++;
                    if (!check25_fast()) continue;
                    np25++;
                    int miss[6]; all_conditions(miss);
                    int tot = miss[0] + miss[3] + miss[1] + miss[4] + miss[2] + miss[5];
                    hist[tot < 63 ? tot : 63]++;
                    if (tot < bestm) bestm = tot;
                    if (tot <= 2) { printf("%s z %d S = %d %d %d %d %d  K = %d %d %d  H = %d %d %d  miss %d %d %d %d %d %d\n", tot ? "near" : "SOLUTION", z, S[0], S[1], S[2], S[3], S[4], K[0], K[1], K[2], H[0], H[1], H[2], miss[0], miss[1], miss[2], miss[3], miss[4], miss[5]); fflush(stdout); }
                    if (tot == 0) nsol++;
                }
            }
            printf("  z-orbit %d (z = %d, |stab| %d, orbits %d): leaves so far %lld, pass (3)(6) %lld, pass (2)(5) %lld, best %d, %.0f s\n", zo, z, nst, norb, nleaf, np36, np25, bestm, now() - t0); fflush(stdout);
        }
        printf("pair %d,%d done: leaves %lld, pass (3)(6) %lld, pass (2)(5) %lld, solutions %lld, best miss %d, %.1f s\n  hist:", ca, cb, nleaf, np36, np25, nsol, bestm, now() - t0);
        for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]);
        printf("\n"); fflush(stdout);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see header\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1) return 1;
    T = malloc(sizeof(int) * m * m); for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &T[i]) != 1) return 1; fclose(f);
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) if (MUL(x, y) == 0) inv[x] = y;
    q = m / 3;
    if (!strcmp(argv[2], "eval")) {
        int g[16], ng = 0, k; const char *p = argv[3]; int v;
        int n = 0; while (sscanf(p, "%d%n", &v, &k) == 1) { S[n++] = v; p += k; }
        p = argv[4]; ng = 0; while (sscanf(p, "%d%n", &v, &k) == 1) { g[ng++] = v; p += k; } gensub(g, ng, K);
        p = argv[5]; ng = 0; while (sscanf(p, "%d%n", &v, &k) == 1) { g[ng++] = v; p += k; } gensub(g, ng, H);
        z = atoi(argv[6]); setup_cosets();
        int miss[6]; all_conditions(miss);
        printf("misses (1..6): %d %d %d %d %d %d\n", miss[0], miss[1], miss[2], miss[3], miss[4], miss[5]);
        build(); int fa[4]; bfs_far(0, fa); printf("BFS A0 rep: far A0 %d A1 %d\n", fa[0], fa[1]);
        if (argc > 7) { FILE *o = fopen(argv[7], "w"); fprintf(o, "%d\n", nv);
            for (int u = 0; u < nv; u++) for (int i = 0; i < dg[u]; i++) if (adj[u][i] > u) fprintf(o, "%d %d\n", u, adj[u][i]);
            fclose(o); printf("wrote %s n=%d\n", argv[7], nv); }
        return 0;
    }
    if (!strcmp(argv[2], "rand")) {
        int N = atoi(argv[3]); rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
        int bad = 0, zero = 0;
        for (int it = 0; it < N; it++) {
            rand_order3(K); rand_order3(H);
            for (;;) { z = rnd() % m; /* need H n zKz^-1 = 1 */ int ok = 1; for (int i = 1; i < 3; i++) for (int j = 1; j < 3; j++) if (MUL(MUL(z, K[i]), inv[z]) == H[j]) ok = 0; if (ok) break; }
            for (int i = 0; i < 5; i++) { again: S[i] = rnd() % m; for (int j = 0; j < i; j++) if (S[j] == S[i]) goto again; }
            setup_cosets();
            int miss[6]; all_conditions(miss); build();
            int fa[4], fb1[4], fb[4], fbb[4];
            bfs_far(0, fa);                      /* A0 rep */
            bfs_far(m + lcH[0], fb1);            /* A1 rep (hub of coset H) */
            bfs_far(m + q + 0, fb);              /* B0 rep */
            bfs_far(2 * m + q + lcK[0], fbb);    /* B1 rep */
            int pred[6] = {fa[0], fa[1], fb1[1] * 3, fb[2], fb[3], fbb[3] * 3};
            int ok = 1; for (int i = 0; i < 6; i++) if (pred[i] != miss[i]) ok = 0;
            /* also cross terms: A1 rep to A0 must be consistent with (2) (A1 rep far A0 count = 3 * (2)-missing cosets?) */
            if (!ok) { bad++; if (bad < 5) printf("MISMATCH it %d: cond %d %d %d %d %d %d bfs %d %d %d %d %d %d\n", it, miss[0], miss[1], miss[2], miss[3], miss[4], miss[5], pred[0], pred[1], pred[2], pred[3], pred[4], pred[5]); }
            int tot = 0; for (int i = 0; i < 6; i++) tot += miss[i]; if (tot == 0) zero++;
        }
        printf("rand: %d trials, %d mismatches, %d with all conditions met\n", N, bad, zero);
        return 0;
    }
    if (!strcmp(argv[2], "ex")) { run_ex(argc > 4 ? atoi(argv[3]) : 1, argc > 4 ? atoi(argv[4]) : 0); return 0; }
    fprintf(stderr, "mode?\n"); return 1;
}
