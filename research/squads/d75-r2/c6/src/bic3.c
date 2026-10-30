/* bic3.c (squad d75-r2, card c6): bi-coset graphs B(G;H,K;D) with |H| = |K| = 3, valency 7, diameter 5.
 * Sides: right cosets Hx (A) and Ky (B), |G|/3 each, N = 2|G|/3.  Hx ~ Ky iff y x^-1 in D, D a union of (K,H)
 * double cosets KgH (D = K D H).  |KgH| = 9 (contribution 3 to the valency) or 3 (contribution 1, g in N(H) when K = H).
 * Valency 7 = ones + 3 threes needs ones >= 1, hence K conjugate to H; conjugating K to H gives K = H WLOG,
 * so every pair is (H,H) with H over the conjugacy classes of order-3 subgroups (file "H" lines).
 * Plain mode: all unions (t threes, 7-3t ones) of HgH.  Self-dual mode (sd): for each beta in Aut(G) with
 * beta(H) = H (one per Stab(H)-class, "BETA" lines), psi(x) = beta(x)^-1 permutes the double cosets; D must be a
 * union of psi-orbits (valency 7 over orbits).  Colour swap (Hx,Ky) -> (K beta(x), H beta(y)) then gives
 * YY = G from XX = G; we test XX first, and YY/odd checks as a verification (counted, not assumed).
 * Tests (as bic75): XX = G (A-A within 4), YY = G (B-B within 4), D XX = G (A-B within 5); cost = |G \ XX| (+ |G \ YY|
 * in plain mode) for the best-cost report.
 * Input: export3.g file ("n 0", table, inverses, "H a NORM" lines, "BETA" + perm lines).
 * env: MODE=plain|sd|both (default sd), HIDX=i (only H index i), ALLH=1 (also normal H; default skips them since
 *   H normal gives a Haar graph of G/H), MAXEV=cap per H and mode (default 3e8), EDGES=out (first solution),
 *   FORCE=e1,...,ek (test the union of the double cosets of these element indices; calibration), FORCEH=i,
 *   BETAMAX=k (only the first k betas of each H).
 * usage: bic3 FILE.bh
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n; static uint16_t *mul; static int *inv;
#define M(a, b) mul[(size_t)(a) * n + (b)]
static uint32_t *mk; static uint32_t stM = 0; static int *ordA, *ordB;
static long long evals = 0, cap_ev = 300000000LL; static int capped = 0;
static const char *edges_out = NULL; static int nsol = 0;
static long long cnt_xx = 0, cnt_yy = 0, cnt_odd = 0, cnt_sol = 0, bad_beta = 0;
static long long best = 1LL << 40;

#define MAXH 512
static int nH; static int Ha[MAXH], Hnorm[MAXH], Hbeta[MAXH]; static int **beta[MAXH];

/* ---- fast rejection (as bic75/haar75): is every z in P P ? left: P = {x^-1 y}, else {x y^-1} over D ---- */
static int pp_full(const int *D, int k, int left, int *ord) {
    static int X[1024]; int nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[D[i]], D[j]) : M(D[i], inv[D[j]]);
        if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; } }
    static const uint16_t *rows[1024]; for (int i = 0; i < nx; i++) rows[i] = mul + (size_t)inv[X[i]] * n;
    for (int t = 0; t < n; t++) { int z = ord[t], ok = 0;
        for (int i = 0; i < nx; i++) if (mk[rows[i][z]] == stM) { ok = 1; break; }
        if (!ok) { if (t) { int u = t / 2; ord[t] = ord[u]; ord[u] = z; } return 0; } }
    return 1;
}
/* number of z not in P P (no early exit on failure) */
static int uncov(const int *D, int k, int left) {
    static int X[1024]; int nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[D[i]], D[j]) : M(D[i], inv[D[j]]);
        if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; } }
    static const uint16_t *rows[1024]; for (int i = 0; i < nx; i++) rows[i] = mul + (size_t)inv[X[i]] * n;
    int c = 0;
    for (int z = 0; z < n; z++) { int ok = 0;
        for (int i = 0; i < nx; i++) if (mk[rows[i][z]] == stM) { ok = 1; break; }
        if (!ok) c++; }
    return c;
}
/* every z in D XX ?  (XX = the set X X with X = D^-1 D) */
static int oddcheck(const int *D, int k) {
    static int X[1024]; int nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(inv[D[i]], D[j]); if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; } }
    static char xx[8192], o[8192];
    memset(xx, 0, n); memset(o, 0, n);
    for (int i = 0; i < nx; i++) for (int j = 0; j < nx; j++) xx[M(X[i], X[j])] = 1;
    for (int z = 0; z < n; z++) if (xx[z]) for (int i = 0; i < k; i++) o[M(D[i], z)] = 1;
    for (int z = 0; z < n; z++) if (!o[z]) return 0;
    return 1;
}

/* ---- double cosets H g H for the current H ---- */
static int Hel[3]; static int ndc; static int *dcid, *dcsz, *dcel; /* dcel[d*9 + i] */
static int *ones, *threes, n1, n3; static int *dcmark;
static void build_dc(int a) {
    Hel[0] = 0; Hel[1] = a; Hel[2] = M(a, a);
    for (int g = 0; g < n; g++) dcid[g] = -1;
    ndc = 0; n1 = n3 = 0;
    for (int g = 0; g < n; g++) if (dcid[g] < 0) {
        int s = 0, *e = dcel + (size_t)ndc * 9;
        for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) {
            int x = M(M(Hel[i], g), Hel[j]); int dup = 0;
            for (int t = 0; t < s; t++) if (e[t] == x) { dup = 1; break; }
            if (!dup) e[s++] = x; }
        if (s != 3 && s != 9) { fprintf(stderr, "bad double coset size %d\n", s); exit(1); }
        dcsz[ndc] = s; for (int t = 0; t < s; t++) dcid[e[t]] = ndc;
        if (s == 3) ones[n1++] = ndc; else threes[n3++] = ndc;
        ndc++;
    }
}
static int contrib(int d) { return dcsz[d] / 3; }

/* ---- output ---- */
static void write_edges(const int *D, int k) {
    if (!edges_out || nsol > 1) return;
    int *ca = malloc(sizeof(int) * n), *cb = malloc(sizeof(int) * n), na = 0, nb = 0;
    for (int x = 0; x < n; x++) ca[x] = cb[x] = -1;
    for (int x = 0; x < n; x++) if (ca[x] < 0) { for (int i = 0; i < 3; i++) ca[M(Hel[i], x)] = na; na++; }
    for (int y = 0; y < n; y++) if (cb[y] < 0) { for (int i = 0; i < 3; i++) cb[M(Hel[i], y)] = nb; nb++; }
    FILE *f = fopen(edges_out, "w"); fprintf(f, "%d\n", na + nb);
    char *done = calloc(na, 1);
    for (int x = 0; x < n; x++) { if (done[ca[x]]) continue; done[ca[x]] = 1;
        int nbr[64], nn = 0;
        for (int i = 0; i < k; i++) { int b = cb[M(D[i], x)], dup = 0; for (int j = 0; j < nn; j++) if (nbr[j] == b) dup = 1; if (!dup) nbr[nn++] = b; }
        for (int j = 0; j < nn; j++) fprintf(f, "%d %d\n", ca[x], na + nbr[j]); }
    fclose(f); free(ca); free(cb); free(done);
}

static int curH, curBeta; static const char *curmode = "";
/* test a candidate union D (k elements) */
static void test(const int *D, int k) {
    evals++;
    if (!pp_full(D, k, 1, ordA)) {
        int c = uncov(D, k, 1); if (c < best) best = c;
        return; }
    cnt_xx++;
    int yy = pp_full(D, k, 0, ordB);
    if (yy) cnt_yy++;
    int od = oddcheck(D, k);
    if (od) cnt_odd++;
    if (yy && od) {
        nsol++; cnt_sol++;
        printf("SOL H %d H_el %d mode %s beta %d |", curH, Ha[curH], curmode, curBeta);
        for (int i = 0; i < k; i++) printf(" %d", D[i]);
        printf("\n"); fflush(stdout);
        if (nsol == 1) write_edges(D, k);
        best = 0;
    } else if (!yy) {
            int c = uncov(D, k, 0); if (c < best) best = c;
        if (!strcmp(curmode, "sd")) { static int warned = 0; if (!warned) { warned = 1; fprintf(stderr, "note: XX ok, YY fails in sd mode (cost %d)\n", c); } }
    }
}
/* union of double cosets chosen from the list (valency 7 = sum of contributions) */
static int chosen[64], nch;
static void emit(void) {
    int D[64], k = 0;
    for (int i = 0; i < nch; i++) { int d = chosen[i]; for (int j = 0; j < dcsz[d]; j++) D[k++] = dcel[d * 9 + j]; }
    test(D, k);
}
/* extend chosen[0..nch) with 'need' size-3 double cosets (ones) from ones[start..] */
static void rec_ones_after(int need, int start) {
    if (capped) return;
    if (need == 0) { emit(); if (evals >= cap_ev) capped = 1; return; }
    for (int i = start; i < n1; i++) { chosen[nch++] = ones[i]; rec_ones_after(need - 1, i + 1); nch--; if (capped) return; }
}
/* plain: all unions of t size-9 double cosets (contribution 3) and 7 - 3t size-3 ones, t = 2, 1, 0 */
static void plain_search(void) {
    for (int t = 2; t >= 0; t--) {
        int w1 = 7 - 3 * t;
        if (w1 > n1) continue;
        if (t == 0) { nch = 0; rec_ones_after(w1, 0); continue; }
        if (t == 1) { for (int a = 0; a < n3 && !capped; a++) { nch = 0; chosen[nch++] = threes[a]; rec_ones_after(w1, 0); } continue; }
        for (int a = 0; a < n3 && !capped; a++) for (int b = a + 1; b < n3 && !capped; b++) {
            nch = 0; chosen[nch++] = threes[a]; chosen[nch++] = threes[b]; rec_ones_after(w1, 0); }
    }
}
/* sd mode: orbits of psi on double cosets; choose orbits with total valency 7 */
static int norb; static int *orbstart, *orbmem, *orbval, *orbn;
static int pi_[8192];
static void rec_orb(int start, int need) {
    if (capped) return;
    if (need == 0) { /* emit union of chosen orbits */
        int D[64], k = 0;
        for (int i = 0; i < nch; i++) { int o = chosen[i];
            for (int j = 0; j < orbn[o]; j++) { int d = orbmem[orbstart[o] + j];
                for (int t = 0; t < dcsz[d]; t++) D[k++] = dcel[d * 9 + t]; } }
        test(D, k); if (evals >= cap_ev) capped = 1; return; }
    for (int o = start; o < norb; o++) {
        if (orbval[o] > need) continue;
        chosen[nch++] = o; rec_orb(o + 1, need - orbval[o]); nch--;
        if (capped) return; }
}
static void sd_search(int *beta_) {
    /* psi(x) = inv[beta(x)]; check psi maps double cosets to double cosets */
    for (int d = 0; d < ndc; d++) {
        int e0 = dcel[d * 9 + 0], img = dcid[inv[beta_[e0]]];
        for (int t = 0; t < dcsz[d]; t++) if (dcid[inv[beta_[dcel[d * 9 + t]]]] != img) { bad_beta++; return; }
        pi_[d] = img; }
    static int seen[8192]; static int stamp = 0; stamp++;
    int *os = orbstart, *om = orbmem; (void)os; (void)om;
    norb = 0; int pos = 0;
    for (int d = 0; d < ndc; d++) if (seen[d] != stamp) {
        orbstart[norb] = pos; int e = d;
        while (seen[e] != stamp) { seen[e] = stamp; orbmem[pos++] = e; e = pi_[e]; }
        orbn[norb] = pos - orbstart[norb]; int v = 0;
        for (int j = 0; j < orbn[norb]; j++) v += contrib(orbmem[orbstart[norb] + j]);
        orbval[norb] = v; norb++; }
    nch = 0; rec_orb(0, 7);
}

/* ---- main ---- */
static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }
static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); rdint(f);
    mul = malloc(2 * (size_t)n * n); inv = malloc(sizeof(int) * n);
    for (long i = 0; i < (long)n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    char w[32]; nH = 0;
    while (fscanf(f, "%31s", w) == 1) {
        if (!strcmp(w, "H")) { Ha[nH] = rdint(f); Hnorm[nH] = rdint(f); Hbeta[nH] = 0; beta[nH] = NULL; nH++; }
        else if (!strcmp(w, "BETA")) { int h = nH - 1; int *b = malloc(sizeof(int) * n);
            for (int i = 0; i < n; i++) b[i] = rdint(f);
            beta[h] = realloc(beta[h], sizeof(int *) * (Hbeta[h] + 1)); beta[h][Hbeta[h]++] = b; }
    }
    fclose(f);
    mk = calloc(n, 4); ordA = malloc(sizeof(int) * n); ordB = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) ordA[i] = ordB[i] = i;
}
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: bic3 FILE.bh\n"); return 2; }
    edges_out = getenv("EDGES"); if (getenv("MAXEV")) cap_ev = atoll(getenv("MAXEV"));
    const char *mode = getenv("MODE") ? getenv("MODE") : "sd";
    int allh = getenv("ALLH") != NULL; int hidx = getenv("HIDX") ? atoi(getenv("HIDX")) : -1;
    int betamax = getenv("BETAMAX") ? atoi(getenv("BETAMAX")) : 1 << 30;
    load(argv[1]);
    printf("GROUP %s n %d H-classes %d\n", argv[1], n, nH);
    dcid = malloc(sizeof(int) * n); dcsz = malloc(sizeof(int) * n); dcel = malloc(sizeof(int) * n * 9);
    ones = malloc(sizeof(int) * n); threes = malloc(sizeof(int) * n); dcmark = malloc(sizeof(int) * n);
    orbstart = malloc(sizeof(int) * n); orbmem = malloc(sizeof(int) * n); orbval = malloc(sizeof(int) * n); orbn = malloc(sizeof(int) * n);
    if (getenv("FORCE")) {   /* calibration: test the union of the double cosets of the listed elements */
        int h = getenv("FORCEH") ? atoi(getenv("FORCEH")) : 0; build_dc(Ha[h]);
        int D[64], k = 0, cnt = 0; char *s = strdup(getenv("FORCE")); char *t = strtok(s, ",");
        int seen_d[64]; int nd = 0;
        while (t) { int e = atoi(t); int d = dcid[e]; int dup = 0; for (int i = 0; i < nd; i++) if (seen_d[i] == d) dup = 1;
            if (!dup) { seen_d[nd++] = d; for (int j = 0; j < dcsz[d]; j++) D[k++] = dcel[d * 9 + j]; } t = strtok(NULL, ","); cnt++; }
        printf("FORCE H %d: %d double cosets, %d elements, valency %d\n", h, nd, k, k / 3);
        curmode = "force"; curH = h; curBeta = -1;
        if (k / 3 != 7) { printf("FORCE valency is not 7\n"); return 1; }
        test(D, k); printf("FORCE result: xx %lld yy %lld odd %lld sol %lld cost %lld\n", cnt_xx, cnt_yy, cnt_odd, cnt_sol, best);
        if (nsol == 0) printf("FORCE not a solution\n");
        return 0;
    }
    for (int h = 0; h < nH; h++) {
        if (hidx >= 0 && h != hidx) continue;
        if (!allh && Hnorm[h] == n) { printf("H %d (el %d) normal in G: skipped (Haar graph of G/H)\n", h, Ha[h]); continue; }
        build_dc(Ha[h]);
        printf("H %d el %d norm %d: double cosets %d (size 3: %d, size 9: %d), betas %d\n", h, Ha[h], Hnorm[h], ndc, n1, n3, Hbeta[h]);
        curH = h;
        if (!strcmp(mode, "plain") || !strcmp(mode, "both")) {
            curmode = "plain"; curBeta = -1; evals = 0; capped = 0; best = 1LL << 40; long long x0 = cnt_xx, s0 = cnt_sol;
            if (n3 * 0 == 0) plain_search();
            printf("PLAIN H %d evals %lld capped %d xx %lld sol %lld best %lld\n", h, evals, capped, cnt_xx - x0, cnt_sol - s0, best);
            fflush(stdout);
        }
        if (!strcmp(mode, "sd") || !strcmp(mode, "both")) {
            curmode = "sd";
            long long s0 = cnt_sol, x0 = cnt_xx; int nb = Hbeta[h] < betamax ? Hbeta[h] : betamax; long long ev0 = 0;
            best = 1LL << 40; evals = 0; capped = 0;
            for (int b = 0; b < nb && !capped; b++) { curBeta = b; long long e0 = evals; sd_search(beta[h][b]); ev0 += evals - e0; }
            printf("SD H %d betas %d evals %lld capped %d xx %lld sol %lld best %lld badbeta %lld\n", h, nb, evals, capped, cnt_xx - x0, cnt_sol - s0, best, bad_beta);
            fflush(stdout);
        }
    }
    printf("DONE sols %lld xx %lld yy %lld odd %lld best %lld\n", cnt_sol, cnt_xx, cnt_yy, cnt_odd, best);
    return 0;
}
