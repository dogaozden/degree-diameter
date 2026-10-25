/* cover_match.c: choose the bijection M (points -> lines of H(q)) so that every freed flag keeps an exact cover.
   cell-15-7 job, 2026-10-24.

   Freed flags (p_a, l_a), p_a on l_a, M(p_a) = l_a. For a single flag the exp2-squad "algebraic cover" is
   S'(p) = {u : d(u,p)=4, d(u,l)=5} -> S(l) = {N : d(N,l)=4, d(N,p)=5}: every point opposite p lies on exactly one
   line of S(l), every line opposite l contains exactly one point of S'(p). The routes it gives are
     side A: (p,0) ~> (u,0) -> (M(u), j) -> (x, j),  needs d(u,p) = 4 and x on M(u);
     side B: (l,0) ~> (M(y),0) -> (y,-j) -> (t,-j),  needs d(M(y),l) = 4 and y on t.
   So side A of flag a holds if every line N in S(l_a) has M^-1(N) at distance 4 from p_a, and side B holds if every
   point u in S'(p_a) has M(u) at distance 4 from l_a. With masks
     sigP(u) = {a : u in S'(p_a)},  A4(u) = {a : d(u,p_a) = 4},  sigL(N) = {a : N in S(l_a)},  B4(N) = {a : d(N,l_a) = 4},
   the pair u -> N keeps every cover iff sigL(N) is inside A4(u) and sigP(u) is inside B4(N). A perfect matching of
   non-freed points to non-freed lines using only such pairs makes every freed source reach everything within 7 (in the
   3-, 5- and 7-copy graphs alike). This program samples compatible pairs, runs Hopcroft-Karp, adds candidates for
   unmatched vertices and repeats; leftovers are matched at random (the proxy/BFS search in d7hexr can finish them).

   Usage: cover_match HEXBIN K seed rounds OUT.sol [HGFILE] [place]
     place 0: random flags; 1: points pairwise opposite; 2: flags from file FLAGS (env) "p l" per line
   Writes a d7hex solution file (freed points, hub edges from HGFILE, M). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
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
static inline int cost(int u, int n) { return __builtin_popcountll(sigL[n] & ~A4[u]) + __builtin_popcountll(sigP[u] & ~B4[n]); }

/* candidate graph: adjacency lists point -> lines */
static int **cand, *ncand, *capc;
static void addc(int u, int n) {
    for (int i = 0; i < ncand[u]; i++) if (cand[u][i] == n) return;
    if (ncand[u] == capc[u]) { capc[u] = capc[u] ? 2 * capc[u] : 16; cand[u] = realloc(cand[u], sizeof(int) * capc[u]); }
    cand[u][ncand[u]++] = n;
}
static int **G4P, *nG4P, **G4L, *nG4L, *freeP, nfreeP, *freeL, nfreeL;
static int pick_line_for(int u) {    /* a random line likely compatible with point u */
    uint64_t s = sigP[u];
    if (s) { int bits[64], nb = 0; for (int a = 0; a < K; a++) if (s >> a & 1) bits[nb++] = a; int a = bits[rndi(nb)]; return G4L[a][rndi(nG4L[a])]; }
    uint64_t t = A4[u];
    if (t && rndi(2)) { int bits[64], nb = 0; for (int a = 0; a < K; a++) if (t >> a & 1) bits[nb++] = a; int a = bits[rndi(nb)];
        /* lines of S(l_a) are the constrained ones: sample from Gamma_4(l_a) */ return G4L[a][rndi(nG4L[a])]; }
    return nfreeL ? freeL[rndi(nfreeL)] : rndi(N);
}
static int pick_point_for(int n) {   /* a random point likely compatible with line n */
    uint64_t s = sigL[n];
    if (s) { int bits[64], nb = 0; for (int a = 0; a < K; a++) if (s >> a & 1) bits[nb++] = a; int a = bits[rndi(nb)]; return G4P[a][rndi(nG4P[a])]; }
    uint64_t t = B4[n];
    if (t && rndi(2)) { int bits[64], nb = 0; for (int a = 0; a < K; a++) if (t >> a & 1) bits[nb++] = a; int a = bits[rndi(nb)]; return G4P[a][rndi(nG4P[a])]; }
    return nfreeP ? freeP[rndi(nfreeP)] : rndi(N);
}
/* Hopcroft-Karp */
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
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: see header\n"); return 1; }
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
    cand = calloc(N, sizeof(int *)); ncand = calloc(N, 4); capc = calloc(N, 4);
    mP = malloc(4 * N); mL = malloc(4 * N); distHK = malloc(4 * N); qHK = malloc(4 * N);
    for (int v = 0; v < N; v++) { mP[v] = -1; mL[v] = -1; }
    time_t t0 = time(NULL);
    int unmatched = N - K;
    for (int rd = 0; rd < rounds; rd++) {
        /* add candidates: every unmatched point and line gets new compatible candidates; also a few for everybody in round 0 */
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
        unmatched = 0; for (int u = 0; u < N; u++) if (!isFP[u] && mP[u] < 0) unmatched++;
        long ne = 0; for (int u = 0; u < N; u++) ne += ncand[u];
        fprintf(stderr, "round %d: candidate edges %ld, unmatched %d (%lds)\n", rd, ne, unmatched, (long)(time(NULL) - t0));
        if (!unmatched) break;
    }
    /* leftovers: pair unmatched points and lines greedily by least cost */
    int *up = malloc(4 * N), *ul = malloc(4 * N), nup = 0, nul = 0; long totc = 0;
    for (int u = 0; u < N; u++) if (!isFP[u] && mP[u] < 0) up[nup++] = u;
    for (int n = 0; n < N; n++) if (!isFL[n] && mL[n] < 0) ul[nul++] = n;
    for (int i = 0; i < nup; i++) { int u = up[i], best = -1, bc = 1 << 30;
        for (int c = 0; c < 2000 && nul > 0; c++) { int j = rndi(nul); int cc = cost(u, ul[j]); if (cc < bc) { bc = cc; best = j; } }
        int n = ul[best]; ul[best] = ul[--nul]; mP[u] = n; mL[n] = u; totc += bc; }
    printf("RESULT K=%d unmatched-after-matching %d, leftover cost %ld\n", K, unmatched, totc);
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
