/* affine75.c (card c6): Haar graphs H(G,S) whose S is invariant under an affine map phi(x) = g*alpha(x),
 * g in G, alpha in Aut(G).  Input: G table + Aut class reps (aff_export.g).
 * Reduction: H(G,S) ~ H(G,beta(S)) for beta in Aut(G) and H(G,S) ~ H(G,tS) for t in G, and conjugating phi by
 * beta or by a left translation gives beta(phi)beta^-1 / t phi t^-1 which fixes beta(S) / tS.  So alpha runs over
 * Aut-class reps and g over all of G.  For each phi, every S that is a union of phi-cycles with total size 7 is
 * evaluated: partition of 7 into cycle lengths, all choices of distinct cycles.
 * Cost = |G \ YY| over the sets with XX = G (near-miss convention of haar75; sets with XX != G are rejected fast);
 * a cost-0 set is then checked for the odd condition YY S = G.  TLIM=seconds stops the scan.
 * usage: affine75 FILE.aff      env: EDGES=out (first valid), CAP=max sets per phi and partition (default 3e6)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n, ninv;
static int *ordT; static uint32_t *mkX; static uint32_t tX = 0;
static uint16_t *mul; static int *inv;
static int nal; static int *alp[2048]; static int alpord[2048], alpsz[2048];
#define M(a,b) mul[(size_t)(a) * n + (b)]

static int *phi, *cycel, *cyc_off, *cyc_len, ncyc;
static int *bylen[8]; static int nbylen[8];
static uint32_t *stA, *stB; static uint32_t tA = 0, tB = 0;
static int S[7];
static int dl[8], dm[8], nd;
static long long nevalS = 0, n_xx0 = 0, nsol = 0, nphi = 0, nphi_cap = 0;
static double skipped_sets = 0;
static int best = 1 << 30, bestA = -1, bestG = -1, bestS[7], bestPart[8], bestNd;
static const char *edges_out; static int edges_written = 0; static long long CAP = 3000000;
static int cur_a, cur_g;

static void fail(const char *m) { fprintf(stderr, "%s\n", m); exit(1); }
static int rdtok(FILE *f, char *w) { return fscanf(f, "%31s", w) == 1; }
static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    if (fscanf(f, "%d %d", &n, &ninv) != 2) fail("header");
    mul = malloc(sizeof(uint16_t) * (size_t)n * n); inv = malloc(sizeof(int) * n);
    for (size_t i = 0; i < (size_t)n * n; i++) { int x; if (fscanf(f, "%d", &x) != 1) fail("table"); mul[i] = x; }
    for (int i = 0; i < n; i++) { if (fscanf(f, "%d", &inv[i]) != 1) fail("inv"); }
    char w[32];
    while (rdtok(f, w)) {
        if (!strcmp(w, "AUT")) { int sz, ncl; if (fscanf(f, "%d %d", &sz, &ncl) != 2) fail("AUT"); }
        else if (!strcmp(w, "ALPHA")) {
            int o, sz; if (fscanf(f, "%d %d", &o, &sz) != 2) fail("ALPHA");
            alp[nal] = malloc(sizeof(int) * n); alpord[nal] = o; alpsz[nal] = sz;
            for (int i = 0; i < n; i++) { if (fscanf(f, "%d", &alp[nal][i]) != 1) fail("perm"); }
            nal++;
        } else fail("unexpected token");
    }
    fclose(f);
    for (int i = 0; i < n; i++) if (M(0, i) != i || M(i, inv[i]) != 0) fail("bad table");
    stA = calloc(n, sizeof(uint32_t)); stB = calloc(n, sizeof(uint32_t)); mkX = calloc(n, sizeof(uint32_t));
    ordT = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) ordT[i] = i;
    phi = malloc(sizeof(int) * n); cycel = malloc(sizeof(int) * n); cyc_off = malloc(sizeof(int) * n);
    cyc_len = malloc(sizeof(int) * n);
    for (int L = 1; L <= 7; L++) { bylen[L] = malloc(sizeof(int) * n); nbylen[L] = 0; }
}

/* uncovered count of XX (left=1: X = {S_i^-1 S_j}) or YY (left=0: Y = {S_i S_j^-1}) */
static int uncov(const int *Sx, int left) {
    int X[64], nx = 0; tB++;
    for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) {
        int x = left ? M(inv[Sx[i]], Sx[j]) : M(Sx[i], inv[Sx[j]]);
        if (stB[x] != tB) { stB[x] = tB; X[nx++] = x; }
    }
    tA++; int cov = 0;
    for (int i = 0; i < nx; i++) { const uint16_t *row = mul + (size_t)X[i] * n;
        for (int j = 0; j < nx; j++) { int z = row[X[j]]; if (stA[z] != tA) { stA[z] = tA; cov++; } } }
    return n - cov;
}
static int fullcheck(const int *Sx) {
    for (int i = 0; i < 7; i++) for (int j = i + 1; j < 7; j++) if (Sx[i] == Sx[j]) return 0;
    if (uncov(Sx, 1) != 0 || uncov(Sx, 0) != 0) return 0;
    int Y[64], ny = 0; tB++;
    for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) { int x = M(Sx[i], inv[Sx[j]]); if (stB[x] != tB) { stB[x] = tB; Y[ny++] = x; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1); int ok = 1;
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[M(Y[i], Y[j])] = 1;
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < 7; i++) odd[M(z, Sx[i])] = 1;
    for (int z = 0; z < n; z++) if (!odd[z]) { ok = 0; break; }
    free(yy); free(odd); return ok;
}
static void write_edges(const int *Sx, const char *path) {
    FILE *f = fopen(path, "w"); if (!f) return;
    fprintf(f, "%d\n", 2 * n);
    for (int g = 0; g < n; g++) for (int i = 0; i < 7; i++) fprintf(f, "%d %d\n", g, n + M(Sx[i], g));
    fclose(f);
}
/* fast test of P P = G (P = X if left, else Y): z in PP iff some p in P has p^-1 z in P.  Targets in move-to-front order. */
static int cover_full(const int *Sx, int left) {
    int P[64], np = 0; tX++;
    for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) {
        int x = left ? M(inv[Sx[i]], Sx[j]) : M(Sx[i], inv[Sx[j]]);
        if (mkX[x] != tX) { mkX[x] = tX; P[np++] = x; }
    }
    const uint16_t *rows[64]; for (int i = 0; i < np; i++) rows[i] = mul + (size_t)inv[P[i]] * n;
    for (int t = 0; t < n; t++) { int z = ordT[t], ok = 0;
        for (int i = 0; i < np; i++) if (mkX[rows[i][z]] == tX) { ok = 1; break; }
        if (!ok) { if (t) { int u = t / 2; ordT[t] = ordT[u]; ordT[u] = z; } return 0; } }
    return 1;
}
static long long nrej = 0;
static void evaluate(void) {
    nevalS++;
    { static long long chk=0, mism=0, pass=0, pu=0; if (getenv("CHK") && chk < 200000) { chk++; int a1 = cover_full(S,1); int u1 = uncov(S,1); if (u1==0) pu++; if (a1) pass++; if ((u1==0) != (a1!=0)) mism++; if (chk==200000 || chk % 50000 == 0) fprintf(stderr, "CHK %lld mism %lld fastpass %lld uncovpass %lld\n", chk, mism, pass, pu); } }
    if (!cover_full(S, 1)) { nrej++; return; }
    n_xx0++;
    int c = uncov(S, 0);
    if (c < best) { best = c; bestA = cur_a; bestG = cur_g; memcpy(bestS, S, sizeof S); bestNd = nd;
        memcpy(bestPart, dl, sizeof dl); }
    if (c == 0 && fullcheck(S)) {
        nsol++;
        printf("SOL alpha %d g %d S", cur_a, cur_g); for (int i = 0; i < 7; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout);
        if (edges_out && !edges_written) { write_edges(S, edges_out); edges_written = 1; }
    }
}
static void rec_d(int d, int pos);
static void choose_cycle(int d, int t, int start, int pos) {
    if (t == 0) { rec_d(d + 1, pos); return; }
    int L = dl[d];
    for (int i = start; i <= nbylen[L] - t; i++) {
        int c = bylen[L][i];
        memcpy(S + pos, cycel + cyc_off[c], sizeof(int) * L);
        choose_cycle(d, t - 1, i + 1, pos + L);
    }
}
static void rec_d(int d, int pos) {
    if (d == nd) { if (pos == 7) evaluate(); return; }
    choose_cycle(d, dm[d], 0, pos);
}

static void do_phi(int a, int g) {
    int *al = alp[a];
    for (int x = 0; x < n; x++) phi[x] = M(g, al[x]);
    /* cycles, keeping those of length <= 7 */
    for (int L = 1; L <= 7; L++) nbylen[L] = 0;
    static char *vis = NULL; if (!vis) vis = malloc(n);
    memset(vis, 0, n); int ne = 0; ncyc = 0;
    for (int x = 0; x < n; x++) if (!vis[x]) {
        int c = 0, y = x; do { vis[y] = 1; c++; y = phi[y]; } while (y != x);
        if (c <= 7) {
            cyc_off[ncyc] = ne; cyc_len[ncyc] = c; y = x;
            do { cycel[ne++] = y; y = phi[y]; } while (y != x);
            bylen[c][nbylen[c]++] = ncyc; ncyc++;
        }
    }
    /* partitions of 7 */
    static const int parts[15][8] = {
        {7,0}, {6,1,0}, {5,2,0}, {5,1,1,0}, {4,3,0}, {4,2,1,0}, {4,1,1,1,0}, {3,3,1,0}, {3,2,2,0},
        {3,2,1,1,0}, {3,1,1,1,1,0}, {2,2,2,1,0}, {2,2,1,1,1,0}, {2,1,1,1,1,1,0}, {1,1,1,1,1,1,1,0} };
    cur_a = a; cur_g = g; nphi++;
    for (int p = 0; p < 15; p++) {
        /* distinct lengths and multiplicities */
        nd = 0;
        for (int i = 0; parts[p][i]; i++) {
            if (nd && dl[nd - 1] == parts[p][i]) dm[nd - 1]++;
            else { dl[nd] = parts[p][i]; dm[nd] = 1; nd++; }
        }
        double cnt = 1; int ok = 1;
        for (int d = 0; d < nd; d++) {
            int c = nbylen[dl[d]], m = dm[d];
            if (c < m) { ok = 0; break; }
            double b = 1; for (int t = 0; t < m; t++) b = b * (c - t) / (t + 1);
            cnt *= b;
        }
        if (!ok) continue;
        if (cnt > (double)CAP) { nphi_cap++; skipped_sets += cnt; continue; }
        rec_d(0, 0);
    }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: affine75 FILE.aff\n"); return 1; }
    load(argv[1]);
    edges_out = getenv("EDGES"); if (getenv("CAP")) CAP = atoll(getenv("CAP"));
    double tlim = getenv("TLIM") ? atof(getenv("TLIM")) : 1e9; time_t t0 = time(NULL); int timed_out = 0;
    for (int a = 0; a < nal && !timed_out; a++) {
        for (int g = 0; g < n; g++) {
            /* identity phi (alpha = id, g = e): every set is invariant, skip (too many sets, handled by other cards) */
            if (g == 0) { int id = 1; for (int x = 0; x < n && id; x++) if (alp[a][x] != x) id = 0; if (id) continue; }
            if (getenv("DBG")) fprintf(stderr, "phi a=%d g=%d\n", a, g); do_phi(a, g);
            if (difftime(time(NULL), t0) > tlim) { timed_out = 1; break; }
        }
        fprintf(stderr, "alpha %d/%d (order %d) phis %lld evals %lld xxpass %lld best %d secs %.0f\n", a + 1, nal, alpord[a], nphi, nevalS, n_xx0, best, difftime(time(NULL), t0));
    }
    printf("SUMMARY N %d nal %d phis %lld evalsets %lld xx_rejected %lld xx0 %lld cap_phis %lld skipped_sets %.3g sols %lld best_cost %d alpha %d alpha_ord %d g %d timed_out %d\n",
           n, nal, nphi, nevalS, nrej, n_xx0, nphi_cap, skipped_sets, nsol, best, bestA, bestA >= 0 ? alpord[bestA] : 0, bestG, timed_out);
    if (best < (1 << 30)) { printf("BEST S"); for (int i = 0; i < 7; i++) printf(" %d", bestS[i]); printf("  parts"); for (int d = 0; d < bestNd; d++) printf(" %d", bestPart[d]); printf("\n"); }
    if (nsol) printf("VALID\n");
    return 0;
}
