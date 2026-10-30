/* bsd75.c: SELF-DUAL bi-coset search (card c1 of squad d75-r2).  Derived from research/d75-raise/src/bic75.c.
 * Graph B(G;H,H;D): H = <h>, |h| = 2, h non-central.  Sides: right cosets Hx (A), Hy (B); Hx ~ Hy iff y x^-1 in D,
 * D a union of double cosets HgH (each contributes |HgH|/2 = 1 or 2 to the valency DEG = 7).
 * Self-dual: beta in Aut(G) with beta(h) = h, beta^2 = 1, and D = beta(D)^-1.  Then Hx -> H beta(x) (A<->B) is a
 * colour-swapping automorphism, so only X X = G (X = D^-1 D) and D X X = G need checking (Y Y = G is checked too,
 * on solutions only, as a sanity test of the theory).
 * psi(HgH) = H beta(g)^-1 H is an involution on double cosets (beta^2 = 1); D runs over unions of psi-orbits of
 * double cosets with total contribution DEG (exhaustive).  Automorphisms come from allaut.g (AUT file).
 * usage: bsd75 FILE.ht AUT.txt        env: EDGES=out.edges (first solution), MAXEV=cap per (h,beta), DELTA=7,
 *        PSI=i (only the i-th distinct psi), HIDX=i (only the i-th non-central involution class)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n; static uint16_t *mul; static int *inv;
#define M(a,b) mul[(size_t)(a) * n + (b)]
static int ninvc, invsz[64], invrep[64];
static uint32_t *mk; static uint32_t stM = 0; static int *ordA, *ordB;
static long long evals = 0, cap_ev = 300000000LL; static int capped = 0; static long long npassA = 0, npassD = 0;
static const char *edges_out; static int nsol = 0; static int DEG = 7;
static int naut; static int *AUT;

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }
static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); rdint(f);
    mul = malloc(2 * (size_t)n * n); inv = malloc(sizeof(int) * n);
    for (long i = 0; i < (long)n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    char w[32];
    while (fscanf(f, "%31s", w) == 1) {
        if (!strcmp(w, "INV")) { invsz[ninvc] = rdint(f); invrep[ninvc] = rdint(f); ninvc++; }
    }
    fclose(f);
    mk = calloc(n, 4); ordA = malloc(sizeof(int) * n); ordB = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) ordA[i] = ordB[i] = i;
}
static void load_aut(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    naut = rdint(f);
    AUT = malloc(sizeof(int) * (size_t)naut * n);
    for (long i = 0; i < (long)naut * n; i++) AUT[i] = rdint(f);
    fclose(f);
}
/* is every z in P P, P = {a^-1 b} (left) or {a b^-1} over a, b in D? */
static int pp_full(const int *D, int k, int left, int *ord) {
    static int X[512]; int nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[D[i]], D[j]) : M(D[i], inv[D[j]]);
        if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; } }
    static const uint16_t *rows[512]; for (int i = 0; i < nx; i++) rows[i] = mul + (size_t)inv[X[i]] * n;
    for (int t = 0; t < n; t++) { int z = ord[t], ok = 0;
        for (int i = 0; i < nx; i++) if (mk[rows[i][z]] == stM) { ok = 1; break; }
        if (!ok) { if (t) { int u = t / 2; ord[t] = ord[u]; ord[u] = z; } return 0; } }
    return 1;
}
/* D X X = G with X = D^-1 D */
static int oddcheck(const int *D, int k) {
    int X[512], nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(inv[D[i]], D[j]); if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; } }
    char *xx = calloc(n, 1), *o = calloc(n, 1);
    for (int i = 0; i < nx; i++) for (int j = 0; j < nx; j++) xx[M(X[i], X[j])] = 1;
    for (int z = 0; z < n; z++) if (xx[z]) for (int i = 0; i < k; i++) o[M(D[i], z)] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!o[z]) ok = 0;
    free(xx); free(o); return ok;
}

/* double cosets of H = <h> (both sides) */
static int h, ndc, *dcid, dcsz[4096], dcel[4096][4];
static int *psi_list; static int npsi;          /* distinct psi maps on double cosets */
static int norb, orbw[4096], orbn[4096], orbm[4096][2];
static int chosen[64], nch; static char tag[64]; static long long casesol, passDD;
static int ordsorted[4096];

static void write_edges(const int *D, int k) {
    if (!edges_out || nsol > 1) return;
    int *ca = malloc(sizeof(int) * n), *cb = malloc(sizeof(int) * n), na = 0, nb = 0;
    for (int x = 0; x < n; x++) ca[x] = cb[x] = -1;
    for (int x = 0; x < n; x++) if (ca[x] < 0) { ca[x] = ca[M(h, x)] = na++; }
    for (int y = 0; y < n; y++) if (cb[y] < 0) { cb[y] = cb[M(h, y)] = nb++; }
    FILE *f = fopen(edges_out, "w"); fprintf(f, "%d\n", na + nb);
    char *done = calloc(na, 1);
    for (int x = 0; x < n; x++) { if (done[ca[x]]) continue; done[ca[x]] = 1;
        int nb_[64], nn = 0;
        for (int i = 0; i < k; i++) { int b = cb[M(D[i], x)], dup = 0; for (int j = 0; j < nn; j++) if (nb_[j] == b) dup = 1; if (!dup) nb_[nn++] = b; }
        for (int j = 0; j < nn; j++) fprintf(f, "%d %d\n", ca[x], na + nb_[j]); }
    fclose(f); free(ca); free(cb); free(done);
}
static void test(void) {
    if (evals >= cap_ev) { capped = 1; return; }
    evals++;
    int D[64], k = 0;
    for (int i = 0; i < nch; i++) { int o = chosen[i]; for (int m = 0; m < orbn[o]; m++) { int d = orbm[o][m]; for (int j = 0; j < dcsz[d]; j++) D[k++] = dcel[d][j]; } }
    if (k != 2 * DEG) { fprintf(stderr, "bad size %d\n", k); exit(1); }
    if (!pp_full(D, k, 1, ordA)) return;
    npassA++;
    if (!oddcheck(D, k)) return;
    passDD++;
    int yy = pp_full(D, k, 0, ordB);
    if (!yy) { printf("YYFAIL %s (self-duality theory violated?)\n", tag); return; }
    nsol++; casesol++;
    printf("SOL %s orbits", tag); for (int i = 0; i < nch; i++) printf(" %d", chosen[i]); printf(" | D"); for (int i = 0; i < k; i++) printf(" %d", D[i]); printf("\n"); fflush(stdout);
    if (nsol == 1) write_edges(D, k);
}
static void rec_orb(int start, int rem) {
    if (capped) return;
    if (rem == 0) { test(); return; }
    for (int i = start; i < norb; i++) {
        int o = ordsorted[i]; if (orbw[o] > rem) break;   /* sorted by weight */
        chosen[nch++] = o; rec_orb(i + 1, rem - orbw[o]); nch--;
        if (capped) return;
    }
}
static int cmp_w(const void *a, const void *b) { return orbw[*(const int *)a] - orbw[*(const int *)b]; }

static void run_h(int ci) {
    h = invrep[ci];
    if (!dcid) dcid = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) dcid[i] = -1;
    ndc = 0;
    for (int g = 0; g < n; g++) if (dcid[g] < 0) {
        int e[4] = { g, M(h, g), M(g, h), M(M(h, g), h) }, s = 0;
        for (int a = 0; a < 4; a++) { int dup = 0; for (int b = 0; b < s; b++) if (dcel[ndc][b] == e[a]) dup = 1; if (!dup) dcel[ndc][s++] = e[a]; }
        dcsz[ndc] = s; for (int a = 0; a < s; a++) dcid[dcel[ndc][a]] = ndc;
        ndc++; if (ndc >= 4096) { fprintf(stderr, "too many double cosets\n"); exit(1); }
    }
    int nones = 0, ntwos = 0; for (int d = 0; d < ndc; d++) { if (dcsz[d] == 2) nones++; else if (dcsz[d] == 4) ntwos++; else { fprintf(stderr, "dc size\n"); exit(1); } }
    /* psi maps from all automorphisms beta with beta(h) = h, beta^2 = 1 */
    npsi = 0; int nbeta = 0;
    if (!psi_list) psi_list = malloc(sizeof(int) * 4096 * 64);
    int *psi = malloc(sizeof(int) * ndc);
    for (int a = 0; a < naut; a++) {
        int *be = AUT + (size_t)a * n;
        if (be[h] != h) continue;
        int inv2 = 1; for (int x = 0; x < n && inv2; x++) if (be[be[x]] != x) inv2 = 0;
        if (!inv2) continue;
        nbeta++;
        for (int d = 0; d < ndc; d++) { psi[d] = dcid[inv[be[dcel[d][0]]]]; }
        int ok = 1;
        for (int d = 0; d < ndc && ok; d++) { if (psi[psi[d]] != d || dcsz[psi[d]] != dcsz[d]) ok = 0; }
        if (!ok) { fprintf(stderr, "psi not an involution on double cosets\n"); exit(1); }
        int dup = 0;
        for (int p = 0; p < npsi && !dup; p++) if (!memcmp(psi_list + (size_t)p * ndc, psi, sizeof(int) * ndc)) dup = 1;
        if (!dup) { if ((npsi + 1) * (size_t)ndc > 4096 * 64) { fprintf(stderr, "too many psi\n"); exit(1); }
            memcpy(psi_list + (size_t)npsi * ndc, psi, sizeof(int) * ndc); npsi++; }
    }
    free(psi);
    printf("CLASS %d h %d size %d centralizer %d dc %d ones %d twos %d beta(h)=h,beta^2=1: %d distinct psi %d\n",
           ci, h, invsz[ci], n / invsz[ci], ndc, nones, ntwos, nbeta, npsi); fflush(stdout);
    int pidx = getenv("PSI") ? atoi(getenv("PSI")) : -1;
    for (int p = 0; p < npsi; p++) {
        if (pidx >= 0 && p != pidx) continue;
        int *ps = psi_list + (size_t)p * ndc;
        /* orbits of psi on double cosets */
        char *vis = calloc(ndc, 1); norb = 0;
        int nfix1 = 0, nfix2 = 0, npair1 = 0, npair2 = 0;
        for (int d = 0; d < ndc; d++) if (!vis[d]) {
            vis[d] = 1; int o = norb++; orbn[o] = 0; orbm[o][orbn[o]++] = d; orbw[o] = dcsz[d] / 2;
            if (ps[d] != d) { vis[ps[d]] = 1; orbm[o][orbn[o]++] = ps[d]; orbw[o] += dcsz[ps[d]] / 2; }
            if (orbn[o] == 1) { if (dcsz[d] == 2) nfix1++; else nfix2++; } else { if (dcsz[d] == 2) npair1++; else npair2++; }
        }
        for (int o = 0; o < norb; o++) ordsorted[o] = o;
        /* sort orbits by weight (stable enough: qsort on indices) */
        qsort(ordsorted, norb, sizeof(int), cmp_w);
        free(vis);
        long long e0 = evals, pa0 = npassA, pd0 = passDD; clock_t c0 = clock(); capped = 0; casesol = 0;
        long long sv = cap_ev; cap_ev = evals + sv;
        snprintf(tag, sizeof tag, "h%d_p%d", ci, p);
        nch = 0; rec_orb(0, DEG);
        cap_ev = sv;
        printf("PSI %s fixed1 %d fixed2 %d pair1 %d pair2 %d evals %lld passXX %lld passDXX %lld sols %lld secs %.1f%s\n",
               tag, nfix1, nfix2, npair1, npair2, evals - e0, npassA - pa0, passDD - pd0, casesol,
               (double)(clock() - c0) / CLOCKS_PER_SEC, capped ? " CAPPED" : "");
        fflush(stdout);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: bsd75 FILE.ht AUT.txt\n"); return 2; }
    edges_out = getenv("EDGES"); if (getenv("DELTA")) DEG = atoi(getenv("DELTA")); if (getenv("MAXEV")) cap_ev = atoll(getenv("MAXEV"));
    load(argv[1]); load_aut(argv[2]);
    printf("GROUP %s n %d invclasses %d auts %d\n", argv[1], n, ninvc, naut);
    int hi = getenv("HIDX") ? atoi(getenv("HIDX")) : -1;
    for (int i = 0; i < ninvc; i++) {
        if (invsz[i] == 1) continue;   /* central involution: H normal */
        if (hi >= 0 && i != hi) continue;
        run_h(i);
    }
    printf("DONE evals %lld passXX %lld passDXX %lld sols %d\n", evals, npassA, passDD, nsol);
    return 0;
}
