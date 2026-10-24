/* cover_match2.c (squad c157-r1, card c6): cover_match with an exact matching step.
   Same flags (same RNG use), same masks and same sampled warm start as cover_match, so the first number printed
   ("sampled stage") is the unmatched count cover_match reports. Then:
   (a) exact Hopcroft-Karp on the FULL compatibility graph. Neighbourhoods are enumerated from the G4 lists instead of
       sampled. Point u with sigP[u] != 0: every compatible line lies in G4L[b], b = lowest bit of sigP[u].
       Point u with sigP[u] == 0: compatible lines are freeL (sigL == 0) and the lines n in G4L[a] (a in A4[u]) with
       lowest sigL-bit a and sigL[n] inside A4[u]. Lines are symmetric. Each compatible pair is produced exactly once,
       so the final deficiency D is the true maximum-matching deficiency of the cover-0 graph (a Hall violation count).
   (c) leftover pairing: the D leftover points are paired with the D leftover lines by a cost-greedy and then 2-opt
       swaps, cost = popcount(sigL[n] & ~A4[u]) + popcount(sigP[u] & ~B4[n]), instead of random sampling.
   Usage as cover_match: cover_match2 HEXBIN K seed rounds OUT.sol [HGFILE] [place]
     place 0: random flags; 1: points pairwise opposite; 2: flags from file FLAGS (env) "p l" per line. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <limits.h>
static int q, N, Q1, K; static int32_t *LP, *PL;
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); int32_t h[3]; if (!f || fread(h, 4, 3, f) != 3) exit(1);
    q = h[0]; N = h[1]; Q1 = q + 1; LP = malloc(4L * N * Q1); if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) exit(1); fclose(f);
    PL = malloc(4L * N * Q1); int *c = calloc(N, 4);
    for (int l = 0; l < N; l++) for (int t = 0; t < Q1; t++) { int p = LP[l * Q1 + t]; PL[p * Q1 + c[p]++] = l; }
    free(c);
}
static void hbfs(int x, int isline, uint8_t *hd) {
    memset(hd, 255, 2 * N); int *qq = malloc(sizeof(int) * 2 * N), h = 0, t = 0; int s = isline ? N + x : x; hd[s] = 0; qq[t++] = s;
    while (h < t) { int v = qq[h++];
        if (v < N) { for (int k = 0; k < Q1; k++) { int w = N + PL[v * Q1 + k]; if (hd[w] == 255) { hd[w] = hd[v] + 1; qq[t++] = w; } } }
        else { int l = v - N; for (int k = 0; k < Q1; k++) { int w = LP[l * Q1 + k]; if (hd[w] == 255) { hd[w] = hd[v] + 1; qq[t++] = w; } } } }
    free(qq);
}
static uint64_t *sigP, *A4, *sigL, *B4;
static int *P, *L, *isFP, *isFL;
static inline int compat(int u, int n) { return (sigL[n] & ~A4[u]) == 0 && (sigP[u] & ~B4[n]) == 0; }
/* sampled machinery, as in cover_match */
static int **cand, *ncand, *capc;
static void addc(int u, int n) {
    for (int i = 0; i < ncand[u]; i++) if (cand[u][i] == n) return;
    if (ncand[u] == capc[u]) { capc[u] = capc[u] ? 2 * capc[u] : 16; cand[u] = realloc(cand[u], sizeof(int) * capc[u]); }
    cand[u][ncand[u]++] = n;
}
static int **G4P, *nG4P, **G4L, *nG4L, *freeP, nfreeP, *freeL, nfreeL;
static int pick_line_for(int u) {
    uint64_t s = sigP[u];
    if (s) { int bits[64], nb = 0; for (int a = 0; a < K; a++) if (s >> a & 1) bits[nb++] = a; int a = bits[rndi(nb)]; return G4L[a][rndi(nG4L[a])]; }
    uint64_t t = A4[u];
    if (t && rndi(2)) { int bits[64], nb = 0; for (int a = 0; a < K; a++) if (t >> a & 1) bits[nb++] = a; int a = bits[rndi(nb)];
        return G4L[a][rndi(nG4L[a])]; }
    return nfreeL ? freeL[rndi(nfreeL)] : rndi(N);
}
static int pick_point_for(int n) {
    uint64_t s = sigL[n];
    if (s) { int bits[64], nb = 0; for (int a = 0; a < K; a++) if (s >> a & 1) bits[nb++] = a; int a = bits[rndi(nb)]; return G4P[a][rndi(nG4P[a])]; }
    uint64_t t = B4[n];
    if (t && rndi(2)) { int bits[64], nb = 0; for (int a = 0; a < K; a++) if (t >> a & 1) bits[nb++] = a; int a = bits[rndi(nb)]; return G4P[a][rndi(nG4P[a])]; }
    return nfreeP ? freeP[rndi(nfreeP)] : rndi(N);
}
static int *mP, *mL, *distHK, *qHK;
static int bfsHK(void) {
    int h = 0, t = 0, found = 0;
    for (int u = 0; u < N; u++) { if (isFP[u]) { distHK[u] = -1; continue; } if (mP[u] < 0) { distHK[u] = 0; qHK[t++] = u; } else distHK[u] = -1; }
    while (h < t) { int u = qHK[h++];
        for (int i = 0; i < ncand[u]; i++) { int n = cand[u][i]; int w = mL[n]; if (w < 0) found = 1; else if (distHK[w] < 0) { distHK[w] = distHK[u] + 1; qHK[t++] = w; } } }
    return found;
}
static int dfsHK(int u) {
    for (int i = 0; i < ncand[u]; i++) { int n = cand[u][i]; int w = mL[n];
        if (w < 0 || (distHK[w] == distHK[u] + 1 && dfsHK(w))) { mP[u] = n; mL[n] = u; return 1; } }
    distHK[u] = -1; return 0;
}

/* ---- exact part: implicit compatibility neighbourhoods ---- */
typedef struct { int id; uint64_t s, m; } ent;   /* EL[a][i] = {line, sigL, B4} for line in G4L[a]; EP[a][i] = {point, sigP, A4} */
static ent **EL, **EP;
static inline void pushi(int **b, int *cnt, int *cap, int x) {
    if (*cnt == *cap) { *cap = *cap ? 2 * *cap : 4096; *b = realloc(*b, sizeof(int) * (size_t)*cap); }
    (*b)[(*cnt)++] = x;
}
/* all non-freed lines compatible with point u, exactly once each */
static int nb_point(int u, int **pb, int *pcap) {
    int cnt = 0, cap = *pcap, *b = *pb;
    uint64_t S = sigP[u], A = A4[u];
    if (S) {
        int f = __builtin_ctzll(S); const ent *E = EL[f]; int len = nG4L[f];
        for (int i = 0; i < len; i++) if ((E[i].s & ~A) == 0 && (S & ~E[i].m) == 0) pushi(&b, &cnt, &cap, E[i].id);
    } else {
        for (int i = 0; i < nfreeL; i++) pushi(&b, &cnt, &cap, freeL[i]);
        for (uint64_t t = A; t; t &= t - 1) {
            int a = __builtin_ctzll(t); const ent *E = EL[a]; int len = nG4L[a];
            for (int i = 0; i < len; i++) { uint64_t s = E[i].s; if (s && __builtin_ctzll(s) == a && (s & ~A) == 0) pushi(&b, &cnt, &cap, E[i].id); }
        }
    }
    *pb = b; *pcap = cap; return cnt;
}
/* all non-freed points compatible with line n, exactly once each */
static int nb_line(int n, int **pb, int *pcap) {
    int cnt = 0, cap = *pcap, *b = *pb;
    uint64_t Sl = sigL[n], B = B4[n];
    if (Sl) {
        int a = __builtin_ctzll(Sl); const ent *E = EP[a]; int len = nG4P[a];
        for (int i = 0; i < len; i++) if ((Sl & ~E[i].m) == 0 && (E[i].s & ~B) == 0) pushi(&b, &cnt, &cap, E[i].id);
    } else {
        for (int i = 0; i < nfreeP; i++) pushi(&b, &cnt, &cap, freeP[i]);
        for (uint64_t t = B; t; t &= t - 1) {
            int f = __builtin_ctzll(t); const ent *E = EP[f]; int len = nG4P[f];
            for (int i = 0; i < len; i++) { uint64_t s = E[i].s; if (s && __builtin_ctzll(s) == f && (s & ~B) == 0) pushi(&b, &cnt, &cap, E[i].id); }
        }
    }
    *pb = b; *pcap = cap; return cnt;
}
static int *bbuf = NULL, bcap = 0;                 /* BFS scratch */
static int **dbuf = NULL, *dcap = NULL, dmax = 0;  /* DFS scratch per recursion depth */
static int bfs_exact(void) {
    int h = 0, t = 0, found = 0, lim = INT_MAX;
    for (int u = 0; u < N; u++) {
        if (isFP[u]) { distHK[u] = -1; continue; }
        if (mP[u] < 0) { distHK[u] = 0; qHK[t++] = u; } else distHK[u] = -1;
    }
    while (h < t) {
        int u = qHK[h++];
        if (distHK[u] > lim) break;
        int cnt = nb_point(u, &bbuf, &bcap);
        for (int i = 0; i < cnt; i++) {
            int n = bbuf[i], w = mL[n];
            if (w < 0) { found = 1; if (lim == INT_MAX) lim = distHK[u]; }
            else if (distHK[w] < 0) { distHK[w] = distHK[u] + 1; qHK[t++] = w; }
        }
    }
    return found;
}
static int dfs_exact(int u, int depth) {
    if (depth >= dmax) {
        int nm = dmax ? 2 * dmax : 256;
        dbuf = realloc(dbuf, sizeof(int *) * nm); dcap = realloc(dcap, sizeof(int) * nm);
        for (int d = dmax; d < nm; d++) { dbuf[d] = NULL; dcap[d] = 0; }
        dmax = nm;
    }
    int cnt = nb_point(u, &dbuf[depth], &dcap[depth]);
    int *bl = dbuf[depth];
    for (int i = 0; i < cnt; i++) {
        int n = bl[i], w = mL[n];
        if (w < 0 || (distHK[w] == distHK[u] + 1 && dfs_exact(w, depth + 1))) { mP[u] = n; mL[n] = u; return 1; }
    }
    distHK[u] = -1; return 0;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: see header\n"); return 1; }
    time_t t0 = time(NULL);
    load(argv[1]); K = atoi(argv[2]); rs ^= atoll(argv[3]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    int rounds = atoi(argv[4]); const char *out = argv[5]; const char *hgf = argc > 6 ? argv[6] : NULL; int place = argc > 7 ? atoi(argv[7]) : 0;
    if (K > 64) { fprintf(stderr, "K <= 64\n"); return 1; }
    P = malloc(4 * K); L = malloc(4 * K); isFP = calloc(N, 4); isFL = calloc(N, 4);
    uint8_t **dp = malloc(sizeof(void *) * K), **dl = malloc(sizeof(void *) * K);
    if (place == 2) {
        FILE *f = fopen(getenv("FLAGS"), "r"); for (int a = 0; a < K; a++) if (fscanf(f, "%d %d", &P[a], &L[a]) != 2) { fprintf(stderr, "flags\n"); return 1; } fclose(f);
        for (int a = 0; a < K; a++) { dp[a] = malloc(2 * N); hbfs(P[a], 0, dp[a]); dl[a] = malloc(2 * N); hbfs(L[a], 1, dl[a]); }
    } else for (int a = 0; a < K; a++) {
        for (int tr = 0; ; tr++) {
            int p = rndi(N), l = PL[p * Q1 + rndi(Q1)], ok = !isFP[p] && !isFL[l];
            for (int b = 0; b < a && ok; b++) if (place == 1 && dp[b][p] != 6) ok = 0;
            if (ok) { P[a] = p; L[a] = l; break; }
            if (tr > 1000000) { fprintf(stderr, "placement failed\n"); return 1; }
        }
        isFP[P[a]] = 1; isFL[L[a]] = 1;
        dp[a] = malloc(2 * N); hbfs(P[a], 0, dp[a]); dl[a] = malloc(2 * N); hbfs(L[a], 1, dl[a]);
    }
    for (int a = 0; a < K; a++) { isFP[P[a]] = a + 1; isFL[L[a]] = a + 1; }
    for (int a = 0; a < K; a++) for (int b = 0; b < K; b++) if (a != b && L[a] == L[b]) { fprintf(stderr, "repeated freed line\n"); return 1; }
    sigP = calloc(N, 8); A4 = calloc(N, 8); sigL = calloc(N, 8); B4 = calloc(N, 8);
    G4P = malloc(sizeof(int *) * K); G4L = malloc(sizeof(int *) * K); nG4P = calloc(K, 4); nG4L = calloc(K, 4);
    for (int a = 0; a < K; a++) {
        G4P[a] = malloc(4 * N); G4L[a] = malloc(4 * N);
        for (int v = 0; v < N; v++) {
            if (dp[a][v] == 4) { A4[v] |= 1ULL << a; if (dl[a][v] == 5) sigP[v] |= 1ULL << a; if (!isFP[v]) G4P[a][nG4P[a]++] = v; }
            if (dl[a][N + v] == 4) { B4[v] |= 1ULL << a; if (dp[a][N + v] == 5) sigL[v] |= 1ULL << a; if (!isFL[v]) G4L[a][nG4L[a]++] = v; }
        }
    }
    freeP = malloc(4 * N); freeL = malloc(4 * N);
    for (int v = 0; v < N; v++) { if (!isFP[v] && !sigP[v]) freeP[nfreeP++] = v; if (!isFL[v] && !sigL[v]) freeL[nfreeL++] = v; }
    long consP = 0, consL = 0; for (int v = 0; v < N; v++) { if (sigP[v] && !isFP[v]) consP++; if (sigL[v] && !isFL[v]) consL++; }
    fprintf(stderr, "K=%d: constrained points %ld, constrained lines %ld, free points %d, free lines %d\n", K, consP, consL, nfreeP, nfreeL);
    EL = malloc(sizeof(ent *) * K); EP = malloc(sizeof(ent *) * K);
    for (int a = 0; a < K; a++) {
        EL[a] = malloc(sizeof(ent) * (nG4L[a] + 1)); for (int i = 0; i < nG4L[a]; i++) { int n = G4L[a][i]; EL[a][i] = (ent){n, sigL[n], B4[n]}; }
        EP[a] = malloc(sizeof(ent) * (nG4P[a] + 1)); for (int i = 0; i < nG4P[a]; i++) { int u = G4P[a][i]; EP[a][i] = (ent){u, sigP[u], A4[u]}; }
    }
    /* ---- sampled warm start: identical to cover_match ---- */
    cand = calloc(N, sizeof(int *)); ncand = calloc(N, 4); capc = calloc(N, 4);
    mP = malloc(4 * N); mL = malloc(4 * N); distHK = malloc(4 * N); qHK = malloc(4 * N);
    for (int v = 0; v < N; v++) { mP[v] = -1; mL[v] = -1; }
    for (int rd = 0; rd < rounds; rd++) {
        int per = rd == 0 ? 24 : 48;
        for (int u = 0; u < N; u++) {
            if (isFP[u] || (rd > 0 && mP[u] >= 0)) continue;
            int got = 0; for (int tr = 0; tr < per * 8 && got < per; tr++) { int n = pick_line_for(u); if (!isFL[n] && compat(u, n)) { addc(u, n); got++; } }
        }
        for (int n = 0; n < N; n++) {
            if (isFL[n] || (rd > 0 && mL[n] >= 0)) continue;
            int got = 0; for (int tr = 0; tr < per * 8 && got < per; tr++) { int u = pick_point_for(n); if (!isFP[u] && compat(u, n)) { addc(u, n); got++; } }
        }
        while (bfsHK()) for (int u = 0; u < N; u++) if (!isFP[u] && mP[u] < 0) dfsHK(u);
        int um = 0; for (int u = 0; u < N; u++) if (!isFP[u] && mP[u] < 0) um++;
        long ne = 0; for (int u = 0; u < N; u++) ne += ncand[u];
        fprintf(stderr, "round %d: candidate edges %ld, unmatched %d (%lds)\n", rd, ne, um, (long)(time(NULL) - t0));
        if (!um) break;
    }
    int U0 = 0; for (int u = 0; u < N; u++) if (!isFP[u] && mP[u] < 0) U0++;
    printf("sampled stage: unmatched %d\n", U0);
    for (int u = 0; u < N; u++) { free(cand[u]); cand[u] = NULL; }
    /* ---- (a) exact Hopcroft-Karp on the full compatibility graph ---- */
    int phases = 0;
    while (bfs_exact()) {
        for (int u = 0; u < N; u++) if (!isFP[u] && mP[u] < 0 && distHK[u] == 0) dfs_exact(u, 0);
        phases++;
        int still = 0; for (int u = 0; u < N; u++) if (!isFP[u] && mP[u] < 0) still++;
        fprintf(stderr, "exact phase %d: unmatched %d (%lds)\n", phases, still, (long)(time(NULL) - t0));
    }
    int *up = malloc(4 * (size_t)N), *ul = malloc(4 * (size_t)N), nup = 0, nul = 0;
    for (int u = 0; u < N; u++) if (!isFP[u] && mP[u] < 0) up[nup++] = u;
    for (int n = 0; n < N; n++) if (!isFL[n] && mL[n] < 0) ul[nul++] = n;
    if (nup != nul) { fprintf(stderr, "BUG: unmatched points %d, lines %d\n", nup, nul); return 1; }
    int D = nup;
    printf("exact stage: maximum matching deficiency D = %d (sampled stage %d), exact phases %d\n", D, U0, phases);
    /* diagnostics: exact compatibility degrees of the deficient vertices (0 = isolated, i.e. a plain Hall violation) */
    {
        int *tb = NULL, tcap = 0; long iso_p = 0, iso_l = 0, hp[8] = {0}, hl[8] = {0};
        for (int i = 0; i < D; i++) { int u = up[i]; if (!nb_point(u, &tb, &tcap)) iso_p++; int k = __builtin_popcountll(sigP[u]); hp[k > 7 ? 7 : k]++; }
        for (int i = 0; i < D; i++) { int n = ul[i]; if (!nb_line(n, &tb, &tcap)) iso_l++; int k = __builtin_popcountll(sigL[n]); hl[k > 7 ? 7 : k]++; }
        printf("deficient points: isolated %ld, |sigP| hist 0..7+:", iso_p); for (int k = 0; k < 8; k++) printf(" %ld", hp[k]); printf("\n");
        printf("deficient lines:  isolated %ld, |sigL| hist 0..7+:", iso_l); for (int k = 0; k < 8; k++) printf(" %ld", hl[k]); printf("\n");
        free(tb);
    }
    /* ---- (c) leftover pairing: cost-greedy then 2-opt on the D x D leftover cost ---- */
    uint64_t *pS = malloc(8 * (size_t)D + 8), *pA = malloc(8 * (size_t)D + 8), *lS = malloc(8 * (size_t)D + 8), *lB = malloc(8 * (size_t)D + 8);
    for (int i = 0; i < D; i++) { pS[i] = sigP[up[i]]; pA[i] = A4[up[i]]; lS[i] = sigL[ul[i]]; lB[i] = B4[ul[i]]; }
#define CST(i, j) (__builtin_popcountll(lS[j] & ~pA[i]) + __builtin_popcountll(pS[i] & ~lB[j]))
    int *pm = malloc(4 * (size_t)D + 4), *fl = malloc(4 * (size_t)D + 4), *perm = malloc(4 * (size_t)D + 4);
    for (int i = 0; i < D; i++) { perm[i] = i; fl[i] = i; }
    for (int i = D - 1; i > 0; i--) { int j = rndi(i + 1), tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp; }
    int nfl = D;
    for (int k = 0; k < D; k++) {
        int i = perm[k], bt = -1, bc = 1 << 30;
        for (int t = 0; t < nfl; t++) { int c = CST(i, fl[t]); if (c < bc) { bc = c; bt = t; if (!c) break; } }
        pm[i] = fl[bt]; fl[bt] = fl[--nfl];
    }
    long greedy_cost = 0; for (int i = 0; i < D; i++) greedy_cost += CST(i, pm[i]);
    int passes = 0, improved = 1; long swaps = 0;
    while (improved && passes < 200 && time(NULL) - t0 < 700) {
        improved = 0; passes++;
        for (int i = 0; i < D; i++) for (int k = i + 1; k < D; k++) {
            int a = pm[i], b = pm[k];
            int cur = CST(i, a) + CST(k, b), alt = CST(i, b) + CST(k, a);
            if (alt < cur) { pm[i] = b; pm[k] = a; improved = 1; swaps++; }
        }
        fprintf(stderr, "2-opt pass %d: swaps so far %ld (%lds)\n", passes, swaps, (long)(time(NULL) - t0));
    }
    long totc = 0, hc[4] = {0};
    for (int i = 0; i < D; i++) { int c = CST(i, pm[i]); totc += c; hc[c > 3 ? 3 : c]++; }
    printf("leftover pairing: greedy cost %ld, after %d 2-opt passes (%ld swaps) cost %ld; pair cost hist 0,1,2,3+: %ld %ld %ld %ld\n",
           greedy_cost, passes, swaps, totc, hc[0], hc[1], hc[2], hc[3]);
    for (int i = 0; i < D; i++) { int u = up[i], n = ul[pm[i]]; mP[u] = n; mL[n] = u; }
    /* consistency: every matched non-leftover pair is compatible */
    long bad = 0; for (int u = 0; u < N; u++) if (!isFP[u] && mP[u] >= 0 && !compat(u, mP[u])) bad++;
    printf("RESULT K=%d unmatched-after-matching %d, leftover cost %ld (incompatible matched pairs in exact part: %ld)\n", K, D, totc, bad);
    /* write solution (d7hex format) */
    FILE *f = fopen(out, "w");
    int HGm = 0, *hj = NULL, *hk = NULL;
    if (hgf) { FILE *h = fopen(hgf, "r"); int kk; if (!h || fscanf(h, "%d %d", &kk, &HGm) != 2 || kk != K) { fprintf(stderr, "hub graph file K mismatch\n"); return 1; }
        hj = malloc(4 * (HGm + 1)); hk = malloc(4 * (HGm + 1)); for (int e = 0; e < HGm; e++) if (fscanf(h, "%d %d", &hj[e], &hk[e]) != 2) return 1; fclose(h); }
    fprintf(f, "d7hex %d %d %d %d\nfreed", q, N, K, 6 * N + 2 * K);
    for (int a = 0; a < K; a++) fprintf(f, " %d", P[a]);
    fprintf(f, "\nhubedges %d", HGm); for (int e = 0; e < HGm; e++) fprintf(f, " %d %d", hj[e], hk[e]); fprintf(f, "\n");
    for (int u = 0; u < N; u++) { int n = isFP[u] ? L[isFP[u] - 1] : mP[u]; fprintf(f, "%d%c", n, (u % 20 == 19 || u == N - 1) ? '\n' : ' '); }
    fclose(f);
    return 0;
}
