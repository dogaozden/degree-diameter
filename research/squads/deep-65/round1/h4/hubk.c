/* hubk.c (deep-65): exact search of the family "Haar part of degree 5 + hubs of size k + hub graph of degree 6-k".
 *
 * Model: G of order m; S subset of G with |S| = 5; K, H subgroups of order k (k = 2..6); R subset of G that is a union
 * of H-K double cosets with |R| = k(6-k) (R empty for k = 6).
 *   A0 = G, B0 = G, x ~ xs.  B1 = G/K: hub xK ~ A0 vertices xK.  A1 = G/H: hub yH ~ B0 vertices yH.
 *   hub-hub: A1 hub yH ~ B1 hub xK iff y^-1 x in R (each hub then has 6-k hub neighbours).   n = 2m + 2m/k.
 * k = 6 is hubex.c (1,6|1,6); k = 3 with one full double coset is hub3.c (1,3|1,3, 5,1,1,1). k = 5 (R = zK with
 * z^-1 H z = K, a perfect matching between the hub orbits), k = 4 and k = 2 use double cosets that mcos/t18 cannot.
 * Diameter <= 5 iff (T = SS^-1, T' = S^-1 S):
 *  (1) {e} u T u K u TT u TK u KT u SHS^-1 u SR u R^-1S^-1 u R^-1R = G                  (A0 to A0)
 *  (2) [(T u K)S u TR^-1 u SRR^-1 u R^-1RR^-1] H = G                                    (A0 to A1, as H-cosets)
 *  (3) HT'H u HS^-1R^-1 u RSH u (RR^-1)^2 = G                                           (A1 to A1)
 *  (4)-(6) the same with (S, K, H, R) -> (S^-1, H, K, R^-1).
 * Symmetry: (S, K, H, R) ~ (d^-1 S c, K^d, H^c, c^-1 R d) and the side swap; K, H are fixed to class
 * representatives (unordered pairs), R runs over orbit representatives under N(H) x N(K), S over 5-subsets that contain
 * the representative of their smallest Stab(R)-orbit (as in hubex.c).
 *
 * usage: hubk TABLE K rand N SEED     (random parameters: condition counts vs BFS; prints mismatches)
 *        hubk TABLE K ex [NPROC PROC]
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 1024
#define WM 16          /* words for element bitsets (m <= 1024) */
static int m, q, k, W, WQ, *T, inv[MAXM];
#define MUL(x, y) T[(x) * m + (y)]
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
typedef struct { uint64_t w[WM]; } bs_t;
static inline void bset(bs_t *b, int x) { b->w[x >> 6] |= 1ULL << (x & 63); }
static inline void bor(bs_t *a, const bs_t *b, int nw) { for (int i = 0; i < nw; i++) a->w[i] |= b->w[i]; }
static inline int bcnt(const bs_t *b, int nw) { int c = 0; for (int i = 0; i < nw; i++) c += __builtin_popcountll(b->w[i]); return c; }

static int K[8], H[8], R[64], nR, S[5];
static int lcK[MAXM], lcH[MAXM];

static void setup_cosets(void) {
    for (int x = 0; x < m; x++) lcK[x] = lcH[x] = -1;
    int c = 0; for (int x = 0; x < m; x++) if (lcK[x] < 0) { for (int i = 0; i < k; i++) lcK[MUL(x, K[i])] = c; c++; }
    c = 0; for (int x = 0; x < m; x++) if (lcH[x] < 0) { for (int i = 0; i < k; i++) lcH[MUL(x, H[i])] = c; c++; }
}

/* ---- generic (slow) evaluation of all six conditions; returns misses ---- */
static int dedup(int *a, int n) { static char c[MAXM]; memset(c, 0, m); int o = 0; for (int i = 0; i < n; i++) if (!c[a[i]]) { c[a[i]] = 1; a[o++] = a[i]; } return o; }
static void cond_side(const int *S_, const int *K_, const int *H_, const int *R_, int nR_, const int *lcH_, int *miss) {
    int Si[5], Ri[64]; for (int i = 0; i < 5; i++) Si[i] = inv[S_[i]]; for (int i = 0; i < nR_; i++) Ri[i] = inv[R_[i]];
    static int Tl[64], Tp[64]; int nT = 0, nTp = 0;
    for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) { Tl[nT++] = MUL(S_[i], Si[j]); Tp[nTp++] = MUL(Si[i], S_[j]); }
    nT = dedup(Tl, nT); nTp = dedup(Tp, nTp);
    static int RRi[4096], RiR[4096]; int nRRi = 0, nRiR = 0;
    for (int i = 0; i < nR_; i++) for (int j = 0; j < nR_; j++) { RRi[nRRi++] = MUL(R_[i], Ri[j]); RiR[nRiR++] = MUL(Ri[i], R_[j]); }
    nRRi = dedup(RRi, nRRi); nRiR = dedup(RiR, nRiR);
    static char c[MAXM];
    /* (1) */
    memset(c, 0, m); c[0] = 1;
    for (int i = 0; i < nT; i++) { c[Tl[i]] = 1; for (int j = 0; j < nT; j++) c[MUL(Tl[i], Tl[j])] = 1;
        for (int a = 0; a < k; a++) { c[MUL(Tl[i], K_[a])] = 1; c[MUL(K_[a], Tl[i])] = 1; } }
    for (int i = 0; i < 5; i++) for (int a = 0; a < k; a++) for (int j = 0; j < 5; j++) c[MUL(MUL(S_[i], H_[a]), Si[j])] = 1;
    for (int i = 0; i < 5; i++) for (int r = 0; r < nR_; r++) { c[MUL(S_[i], R_[r])] = 1; c[MUL(Ri[r], Si[i])] = 1; }
    for (int i = 0; i < nRiR; i++) c[RiR[i]] = 1;
    { int x = 0; for (int g = 0; g < m; g++) x += !c[g]; miss[0] = x; }
    /* (2): cosets of H */
    memset(c, 0, q);
    for (int i = 0; i < nT; i++) { for (int j = 0; j < 5; j++) c[lcH_[MUL(Tl[i], S_[j])]] = 1; for (int r = 0; r < nR_; r++) c[lcH_[MUL(Tl[i], Ri[r])]] = 1; }
    for (int a = 0; a < k; a++) for (int j = 0; j < 5; j++) c[lcH_[MUL(K_[a], S_[j])]] = 1;
    for (int i = 0; i < 5; i++) for (int j = 0; j < nRRi; j++) c[lcH_[MUL(S_[i], RRi[j])]] = 1;
    for (int i = 0; i < nRiR; i++) for (int r = 0; r < nR_; r++) c[lcH_[MUL(RiR[i], Ri[r])]] = 1;
    { int x = 0; for (int g = 0; g < q; g++) x += !c[g]; miss[1] = x; }
    /* (3) */
    memset(c, 0, m);
    for (int a = 0; a < k; a++) for (int i = 0; i < nTp; i++) for (int b = 0; b < k; b++) c[MUL(MUL(H_[a], Tp[i]), H_[b])] = 1;
    for (int a = 0; a < k; a++) for (int i = 0; i < 5; i++) for (int r = 0; r < nR_; r++) c[MUL(MUL(H_[a], Si[i]), Ri[r])] = 1;
    for (int r = 0; r < nR_; r++) for (int i = 0; i < 5; i++) for (int a = 0; a < k; a++) c[MUL(MUL(R_[r], S_[i]), H_[a])] = 1;
    for (int i = 0; i < nRRi; i++) for (int j = 0; j < nRRi; j++) c[MUL(RRi[i], RRi[j])] = 1;
    { int x = 0; for (int g = 0; g < m; g++) x += !c[g]; miss[2] = x; }
}
static void all_conditions(int *miss) {
    cond_side(S, K, H, R, nR, lcH, miss);
    int Si[5], Ri[64]; for (int i = 0; i < 5; i++) Si[i] = inv[S[i]]; for (int i = 0; i < nR; i++) Ri[i] = inv[R[i]];
    cond_side(Si, H, K, Ri, nR, lcK, miss + 3);
}

/* ---- graph and BFS (validation) ---- */
static int nv, adj[4 * MAXM][8], dg[4 * MAXM];
static void addedge(int u, int v) { adj[u][dg[u]++] = v; adj[v][dg[v]++] = u; }
static int build(void) {
    nv = 2 * m + 2 * q; memset(dg, 0, sizeof(int) * nv);
    int A1 = m, B0 = m + q, B1 = 2 * m + q;
    for (int x = 0; x < m; x++) { for (int i = 0; i < 5; i++) addedge(x, B0 + MUL(x, S[i])); addedge(x, B1 + lcK[x]); }
    for (int y = 0; y < m; y++) addedge(A1 + lcH[y], B0 + y);
    static char done[MAXM]; memset(done, 0, q);
    for (int y = 0; y < m; y++) { int c = lcH[y]; if (done[c]) continue; done[c] = 1;
        int seen[64], ns = 0;
        for (int r = 0; r < nR; r++) { int t = lcK[MUL(y, R[r])]; int d = 0; for (int i = 0; i < ns; i++) if (seen[i] == t) d = 1; if (!d) { seen[ns++] = t; addedge(A1 + c, B1 + t); } } }
    for (int v = 0; v < nv; v++) if (dg[v] != 6) return 0;
    return 1;
}
static void bfs_far(int src, int *far) {
    static int dist[4 * MAXM], qu[4 * MAXM];
    for (int i = 0; i < nv; i++) dist[i] = -1;
    int h = 0, t = 0; dist[src] = 0; qu[t++] = src;
    while (h < t) { int x = qu[h++]; if (dist[x] >= 4) continue; for (int i = 0; i < dg[x]; i++) { int y = adj[x][i]; if (dist[y] < 0) { dist[y] = dist[x] + 1; qu[t++] = y; } } }
    int A1 = m, B0 = m + q, B1 = 2 * m + q;
    for (int i = 0; i < 4; i++) far[i] = 0;
    for (int v = 0; v < nv; v++) if (dist[v] < 0) far[v < A1 ? 0 : v < B0 ? 1 : v < B1 ? 2 : 3]++;
}

/* ---- subgroups of order k ---- */
static int nsub, subel[4096][8];
static int closure(int *g, int ng, int *el) {
    char in[MAXM]; memset(in, 0, m); int n = 1; el[0] = 0; in[0] = 1;
    for (int i = 0; i < n; i++) for (int j = 0; j < ng; j++) { int z = MUL(el[i], g[j]); if (!in[z]) { if (n >= k) return -1; in[z] = 1; el[n++] = z; } }
    return n;
}
static int same_set(const int *a, const int *b) { for (int i = 0; i < k; i++) { int f = 0; for (int j = 0; j < k; j++) if (a[i] == b[j]) f = 1; if (!f) return 0; } return 1; }
static void add_sub(int *el) { for (int s = 0; s < nsub; s++) if (same_set(subel[s], el)) return; memcpy(subel[nsub++], el, sizeof(int) * k); }
static void find_subgroups(void) {
    nsub = 0; int el[8];
    for (int a = 1; a < m; a++) { int n = closure(&a, 1, el); if (n == k) add_sub(el); if (n < 0 || k % n) continue;
        for (int b = a + 1; b < m; b++) { int g2[2] = {a, b}; if (closure(g2, 2, el) == k) add_sub(el); } }
}
static int conj_index(int s, int x) { int el[8]; for (int i = 0; i < k; i++) el[i] = MUL(MUL(inv[x], subel[s][i]), x); for (int t = 0; t < nsub; t++) if (same_set(subel[t], el)) return t; return -1; }

/* ---------------- exact search ---------------- */
static bs_t hh[MAXM], kk[MAXM], a3[MAXM], a6[MAXM], F3, F6, full;
static bs_t c2[MAXM], c5[MAXM], b2[MAXM], b5[MAXM], F2, F5, fullq;
static long long nleaf, np36, np25, nsol, hist[64]; static int bestm;

static void precompute_R(void) {
    int Ri[64]; for (int i = 0; i < nR; i++) Ri[i] = inv[R[i]];
    static int RRi[4096], RiR[4096]; int nRRi = 0, nRiR = 0;
    for (int i = 0; i < nR; i++) for (int j = 0; j < nR; j++) { RRi[nRRi++] = MUL(R[i], Ri[j]); RiR[nRiR++] = MUL(Ri[i], R[j]); }
    nRRi = dedup(RRi, nRRi); nRiR = dedup(RiR, nRiR);
    if (nR == 0) { nRRi = nRiR = 0; }
    memset(&F3, 0, sizeof F3); memset(&F6, 0, sizeof F6); memset(&F2, 0, sizeof F2); memset(&F5, 0, sizeof F5);
    for (int i = 0; i < nRRi; i++) for (int j = 0; j < nRRi; j++) bset(&F3, MUL(RRi[i], RRi[j]));
    for (int i = 0; i < nRiR; i++) for (int j = 0; j < nRiR; j++) bset(&F6, MUL(RiR[i], RiR[j]));
    bor(&F3, &hh[0], W); bor(&F6, &kk[0], W);
    for (int i = 0; i < nRiR; i++) for (int r = 0; r < nR; r++) bset(&F2, lcH[MUL(RiR[i], Ri[r])]);
    for (int i = 0; i < nRRi; i++) for (int r = 0; r < nR; r++) bset(&F5, lcK[MUL(RRi[i], R[r])]);
    for (int s = 0; s < m; s++) {
        int si = inv[s];
        memset(&a3[s], 0, sizeof(bs_t)); memset(&a6[s], 0, sizeof(bs_t)); memset(&b2[s], 0, sizeof(bs_t)); memset(&b5[s], 0, sizeof(bs_t));
        for (int a = 0; a < k; a++) for (int r = 0; r < nR; r++) {
            bset(&a3[s], MUL(MUL(H[a], si), Ri[r])); bset(&a3[s], MUL(MUL(R[r], s), H[a]));
            bset(&a6[s], MUL(MUL(K[a], s), R[r])); bset(&a6[s], MUL(MUL(Ri[r], si), K[a])); }
        for (int a = 0; a < k; a++) { bset(&b2[s], lcH[MUL(K[a], s)]); bset(&b5[s], lcK[MUL(H[a], si)]); }
        for (int j = 0; j < nRRi; j++) bset(&b2[s], lcH[MUL(s, RRi[j])]);
        for (int j = 0; j < nRiR; j++) bset(&b5[s], lcK[MUL(si, RiR[j])]);
        /* c2[t] = cosets of t R^-1 (H); c5[t] = cosets of t R (K) */
        memset(&c2[s], 0, sizeof(bs_t)); memset(&c5[s], 0, sizeof(bs_t));
        for (int r = 0; r < nR; r++) { bset(&c2[s], lcH[MUL(s, Ri[r])]); bset(&c5[s], lcK[MUL(s, R[r])]); }
    }
}
static int check25(void) {
    bs_t a = F2, b = F5; int Si[5]; for (int i = 0; i < 5; i++) Si[i] = inv[S[i]];
    for (int i = 0; i < 5; i++) { bor(&a, &b2[S[i]], WQ); bor(&b, &b5[S[i]], WQ); }
    for (int i = 0; i < 5; i++) for (int j = 0; j < 5; j++) {
        int t = MUL(S[i], Si[j]), tp = MUL(Si[i], S[j]);
        bor(&a, &c2[t], WQ); bor(&b, &c5[tp], WQ);
        for (int l = 0; l < 5; l++) { bset(&a, lcH[MUL(t, S[l])]); bset(&b, lcK[MUL(tp, Si[l])]); }
    }
    for (int i = 0; i < WQ; i++) if (a.w[i] != fullq.w[i] || b.w[i] != fullq.w[i]) return 0;
    return 1;
}
static void run_ex(int NPROC, int PROC) {
    find_subgroups();
    int cls[4096], ncls = 0, rep[4096];
    for (int i = 0; i < nsub; i++) cls[i] = -1;
    for (int i = 0; i < nsub; i++) if (cls[i] < 0) { rep[ncls] = i; for (int x = 0; x < m; x++) cls[conj_index(i, x)] = ncls; ncls++; }
    printf("order %d, k %d: %d subgroups in %d classes\n", m, k, nsub, ncls); fflush(stdout);
    W = (m + 63) / 64; WQ = (q + 63) / 64;
    memset(&full, 0, sizeof full); for (int x = 0; x < m; x++) bset(&full, x);
    memset(&fullq, 0, sizeof fullq); for (int x = 0; x < q; x++) bset(&fullq, x);
    long long gsol = 0; int gbest = 1 << 30;
    for (int ca = 0; ca < ncls; ca++) for (int cb = ca; cb < ncls; cb++) {
        double t0 = now();
        memcpy(K, subel[rep[ca]], sizeof(int) * k); memcpy(H, subel[rep[cb]], sizeof(int) * k); setup_cosets();
        int NK[MAXM], nNK = 0, NH[MAXM], nNH = 0;
        for (int x = 0; x < m; x++) { if (conj_index(rep[ca], x) == rep[ca]) NK[nNK++] = x; if (conj_index(rep[cb], x) == rep[cb]) NH[nNH++] = x; }
        for (int g = 0; g < m; g++) { memset(&hh[g], 0, sizeof(bs_t)); memset(&kk[g], 0, sizeof(bs_t));
            for (int a = 0; a < k; a++) for (int b = 0; b < k; b++) { bset(&hh[g], MUL(MUL(H[a], g), H[b])); bset(&kk[g], MUL(MUL(K[a], g), K[b])); } }
        /* H-K double cosets */
        int dcHK[MAXM], ndc = 0, dsz[MAXM], drep[MAXM];
        for (int x = 0; x < m; x++) dcHK[x] = -1;
        for (int x = 0; x < m; x++) if (dcHK[x] < 0) { int c = 0; for (int a = 0; a < k; a++) for (int b = 0; b < k; b++) { int y = MUL(MUL(H[a], x), K[b]); if (dcHK[y] < 0) { dcHK[y] = ndc; c++; } } dsz[ndc] = c; drep[ndc] = x; ndc++; }
        /* all sets of double cosets with total size k(6-k), up to 4 parts */
        int target = k * (6 - k);
        static int Rsets[200000][4]; int nRs = 0, Rlen[200000];
        if (target == 0) { Rlen[0] = 0; nRs = 1; }
        else {
            for (int a = 0; a < ndc; a++) { if (nRs >= 199999) break; if (dsz[a] == target) { Rsets[nRs][0] = a; Rlen[nRs++] = 1; } if (dsz[a] >= target) continue;
              for (int b = a + 1; b < ndc; b++) { int s2 = dsz[a] + dsz[b]; if (s2 == target) { Rsets[nRs][0] = a; Rsets[nRs][1] = b; Rlen[nRs++] = 2; } if (s2 >= target) continue;
                for (int c = b + 1; c < ndc; c++) { int s3 = s2 + dsz[c]; if (s3 == target) { Rsets[nRs][0] = a; Rsets[nRs][1] = b; Rsets[nRs][2] = c; Rlen[nRs++] = 3; } if (s3 >= target) continue;
                  for (int d = c + 1; d < ndc; d++) if (s3 + dsz[d] == target && nRs < 199999) { Rsets[nRs][0] = a; Rsets[nRs][1] = b; Rsets[nRs][2] = c; Rsets[nRs][3] = d; Rlen[nRs++] = 4; } } } }
        }
        /* orbits of R-sets under (d, c): R -> c^-1 R d, d in N(K), c in N(H); hash of sorted double-coset tuples */
        if (nRs >= 200000) { printf("pair %d,%d: too many R-sets (cap 200000), skipped\n", ca, cb); continue; }
        static int Rorb[200000]; int nRo = 0; static int Rorep[200000];
        static long long hkey[1 << 20]; static int hval[1 << 20];
        for (int i = 0; i < (1 << 20); i++) hkey[i] = -1;
        #define RKEY(a) ({ int _t[4] = {-1, -1, -1, -1}; for (int _u = 0; _u < Rlen[a]; _u++) _t[_u] = Rsets[a][_u]; \
             long long _k = 0; for (int _u = 0; _u < 4; _u++) _k = _k * 1024 + (_t[_u] + 1); _k; })
        for (int i = 0; i < nRs; i++) { long long key = RKEY(i); unsigned h = (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 44);
            while (hkey[h] >= 0) h = (h + 1) & ((1 << 20) - 1); hkey[h] = key; hval[h] = i; Rorb[i] = -1; }
        for (int i = 0; i < nRs; i++) if (Rorb[i] < 0) {
            Rorep[nRo] = i;
            for (int a = 0; a < nNK; a++) for (int b = 0; b < nNH; b++) {
                int img[4] = {-1, -1, -1, -1}; for (int t = 0; t < Rlen[i]; t++) img[t] = dcHK[MUL(MUL(inv[NH[b]], drep[Rsets[i][t]]), NK[a])];
                for (int x = 0; x < Rlen[i]; x++) for (int y = x + 1; y < Rlen[i]; y++) if (img[y] < img[x]) { int t = img[x]; img[x] = img[y]; img[y] = t; }
                long long key = 0; for (int u = 0; u < 4; u++) key = key * 1024 + (img[u] + 1);
                unsigned h = (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 44);
                while (hkey[h] >= 0 && hkey[h] != key) h = (h + 1) & ((1 << 20) - 1);
                if (hkey[h] == key) { int j = hval[h]; if (Rorb[j] < 0) Rorb[j] = nRo; }
            }
            nRo++;
        }
        printf("pair %d,%d: |N(K)| %d |N(H)| %d, H-K double cosets %d, R-sets %d in %d orbits\n", ca, cb, nNK, nNH, ndc, nRs, nRo); fflush(stdout);
        nleaf = np36 = np25 = nsol = 0; memset(hist, 0, sizeof hist); bestm = 1 << 30;
        for (int ro = 0; ro < nRo; ro++) {
            int ri = Rorep[ro]; nR = 0;
            for (int t = 0; t < Rlen[ri]; t++) for (int x = 0; x < m; x++) if (dcHK[x] == Rsets[ri][t]) R[nR++] = x;
            precompute_R();
            /* stabiliser of R and its orbits on G */
            static int sd[MAXM * 8], sc[MAXM * 8]; int nst = 0;
            for (int a = 0; a < nNK; a++) for (int b = 0; b < nNH; b++) {
                int ok = 1; for (int t = 0; t < Rlen[ri] && ok; t++) { int im = dcHK[MUL(MUL(inv[NH[b]], drep[Rsets[ri][t]]), NK[a])]; int f = 0; for (int u = 0; u < Rlen[ri]; u++) if (Rsets[ri][u] == im) f = 1; if (!f) ok = 0; }
                if (ok) { sd[nst] = NK[a]; sc[nst] = NH[b]; nst++; } }
            int orb[MAXM], norb = 0, osz[MAXM], orep[MAXM];
            for (int x = 0; x < m; x++) orb[x] = -1;
            for (int x = 0; x < m; x++) if (orb[x] < 0) { int cnt = 0;
                for (int i = 0; i < nst; i++) { int y = MUL(MUL(inv[sd[i]], x), sc[i]); if (orb[y] < 0) { orb[y] = norb; cnt++; } }
                osz[norb] = cnt; orep[norb] = x; norb++; }
            int oord[MAXM]; for (int o = 0; o < norb; o++) oord[o] = o;
            for (int i = 0; i < norb; i++) for (int j = i + 1; j < norb; j++) if (osz[oord[j]] > osz[oord[i]]) { int t = oord[i]; oord[i] = oord[j]; oord[j] = t; }
            int elist[MAXM], ne = 0; for (int i = 0; i < norb; i++) for (int x = 0; x < m; x++) if (orb[x] == oord[i]) elist[ne++] = x;
            int start = 0;
            for (int p = 0; p < norb; p++) {
                int o = oord[p], r0 = orep[o];
                int cand[MAXM], nc = 0; for (int i = start; i < ne; i++) if (elist[i] != r0) cand[nc++] = elist[i];
                start += osz[o];
                if (nc < 4) break;
                S[0] = r0;
                int idx[5]; bs_t m3[5], m6[5];
                m3[0] = F3; bor(&m3[0], &a3[r0], W); m6[0] = F6; bor(&m6[0], &a6[r0], W);
                int lvl = 1; idx[1] = -1;
                while (lvl >= 1) {
                    idx[lvl]++;
                    if (idx[lvl] > nc - (5 - lvl)) { lvl--; continue; }
                    if (lvl == 1 && (idx[1] % NPROC) != PROC) continue;
                    int s = cand[idx[lvl]]; S[lvl] = s;
                    bs_t a = m3[lvl - 1], b = m6[lvl - 1];
                    bor(&a, &a3[s], W); bor(&b, &a6[s], W);
                    for (int i = 0; i < lvl; i++) {
                        bor(&a, &hh[MUL(inv[s], S[i])], W); bor(&a, &hh[MUL(inv[S[i]], s)], W);
                        bor(&b, &kk[MUL(s, inv[S[i]])], W); bor(&b, &kk[MUL(S[i], inv[s])], W);
                    }
                    m3[lvl] = a; m6[lvl] = b;
                    if (lvl < 4) { lvl++; idx[lvl] = idx[lvl - 1]; continue; }
                    nleaf++;
                    int ok = 1; for (int i = 0; i < W; i++) if (a.w[i] != full.w[i] || b.w[i] != full.w[i]) { ok = 0; break; }
                    if (!ok) continue;
                    np36++;
                    if (!check25()) continue;
                    np25++;
                    int miss[6]; all_conditions(miss);
                    int tot = 0; for (int i = 0; i < 6; i++) tot += miss[i];
                    hist[tot < 63 ? tot : 63]++;
                    if (tot < bestm) bestm = tot;
                    static int nprint = 0; if (tot <= 2 && nprint++ < 20) { printf("%s R-orbit %d S = %d %d %d %d %d K = <%d", tot ? "near" : "SOLUTION", ro, S[0], S[1], S[2], S[3], S[4], K[0]);
                        for (int i = 1; i < k; i++) printf(",%d", K[i]); printf("> H = <%d", H[0]); for (int i = 1; i < k; i++) printf(",%d", H[i]);
                        printf("> R = {"); for (int i = 0; i < nR; i++) printf("%s%d", i ? "," : "", R[i]);
                        printf("} miss %d %d %d %d %d %d\n", miss[0], miss[1], miss[2], miss[3], miss[4], miss[5]); fflush(stdout); }
                    if (tot == 0) nsol++;
                }
            }
        }
        printf("pair %d,%d done: leaves %lld, pass (3)(6) %lld, pass (2)(5) %lld, solutions %lld, best miss %d, %.1f s\n  hist:", ca, cb, nleaf, np36, np25, nsol, bestm, now() - t0);
        for (int i = 0; i < 64; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]);
        printf("\n"); fflush(stdout);
        gsol += nsol; if (bestm < gbest) gbest = bestm;
    }
    printf("TOTAL solutions %lld best %d\n", gsol, gbest);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: see header\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1) return 1;
    T = malloc(sizeof(int) * m * m); for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &T[i]) != 1) return 1; fclose(f);
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) if (MUL(x, y) == 0) inv[x] = y;
    k = atoi(argv[2]); if (m % k || m > MAXM) { fprintf(stderr, "bad k\n"); return 1; }
    q = m / k; W = (m + 63) / 64; WQ = (q + 63) / 64;
    if (!strcmp(argv[3], "rand")) {
        int N = atoi(argv[4]); rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
        find_subgroups(); if (!nsub) { printf("no subgroups of order %d\n", k); return 0; }
        int bad = 0, zero = 0, tried = 0;
        for (int it = 0; it < N * 20 && tried < N; it++) {
            memcpy(K, subel[rnd() % nsub], sizeof(int) * k); memcpy(H, subel[rnd() % nsub], sizeof(int) * k); setup_cosets();
            /* random R: union of random double cosets until size target (skip if overshoot) */
            int target = k * (6 - k); nR = 0; int dc[MAXM]; for (int x = 0; x < m; x++) dc[x] = -1;
            int tries = 0;
            while (nR < target && tries++ < 50) { int x = rnd() % m; if (dc[x] >= 0) continue; int el[64], ne = 0;
                for (int a = 0; a < k; a++) for (int b = 0; b < k; b++) { int y = MUL(MUL(H[a], x), K[b]); int d = 0; for (int i = 0; i < ne; i++) if (el[i] == y) d = 1; if (!d) el[ne++] = y; }
                int clash = 0; for (int i = 0; i < ne; i++) if (dc[el[i]] >= 0) clash = 1;
                if (clash || nR + ne > target) continue;
                for (int i = 0; i < ne; i++) { dc[el[i]] = 1; R[nR++] = el[i]; } }
            if (nR != target) continue;
            for (int i = 0; i < 5; i++) { again: S[i] = rnd() % m; for (int j = 0; j < i; j++) if (S[j] == S[i]) goto again; }
            if (!build()) continue;   /* multi-edges: skip */
            tried++;
            int miss[6]; all_conditions(miss);
            int fa[4], fA1[4], fb[4], fB1[4];
            bfs_far(0, fa); bfs_far(m + lcH[0], fA1); bfs_far(m + q, fb); bfs_far(2 * m + q + lcK[0], fB1);
            int pred[6] = {fa[0], fa[1], fA1[1] * k, fb[2], fb[3], fB1[3] * k};
            int ok = 1; for (int i = 0; i < 6; i++) if (pred[i] != miss[i]) ok = 0;
            if (!ok) { bad++; if (bad < 5) printf("MISMATCH: cond %d %d %d %d %d %d bfs %d %d %d %d %d %d\n", miss[0], miss[1], miss[2], miss[3], miss[4], miss[5], pred[0], pred[1], pred[2], pred[3], pred[4], pred[5]); }
            int tot = 0; for (int i = 0; i < 6; i++) tot += miss[i]; if (!tot) zero++;
        }
        printf("rand k=%d: %d trials, %d mismatches, %d all-zero\n", k, tried, bad, zero);
        return 0;
    }
    if (!strcmp(argv[3], "ex")) { run_ex(argc > 5 ? atoi(argv[4]) : 1, argc > 5 ? atoi(argv[5]) : 0); return 0; }
    return 1;
}
