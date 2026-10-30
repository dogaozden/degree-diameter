/* bic75.c: exhaustive search over bi-coset graphs B(G; H, K; D) with H = <h>, K = <k> of order 2, valency 7,
 * diameter 5.  Sides: right cosets Hx (A) and Ky (B), |G|/2 each; Hx ~ Ky iff y x^-1 in D, D a union of double
 * cosets K g H (each contributes |KgH|/2 = 1 or 2 to the valency).  G is transitive on each side, so diameter <= 5
 * iff X X = G (X = D^-1 D, A to A within 4), Y Y = G (Y = D D^-1, B to B), D X X = G (A to B within 5).
 * Tested with haar75's fast rejection (z in XX iff x^-1 z in X for some x in X, targets in move-to-front order).
 * Input: export.g file with INVS (involution class reps) and IDX2 lines; pairs of non-central involution classes.
 * The first double coset of each union runs over representatives under conjugation by C_G(h) n C_G(k).
 * usage: bic75 FILE.ht [EDGES=out.edges] [MAXEV per case, default 3e8] [PAIR=i,j only that pair]
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int n; static uint16_t *mul; static int *inv;
#define M(a,b) mul[(size_t)(a) * n + (b)]
static int ninvc, invsz[64], invrep[64];
static int nidx2; static unsigned long long idx2mask[64];
static uint32_t *mk; static uint32_t stM = 0; static int *ordA, *ordB;
static long long evals = 0, cap_ev = 300000000LL; static int capped = 0; static long long npassA = 0;
static const char *edges_out; static int nsol = 0;

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
        else if (!strcmp(w, "IDX2")) { int c = rdint(f); unsigned long long m = 0; for (int i = 0; i < c; i++) m |= 1ULL << rdint(f); idx2mask[nidx2++] = m; }
    }
    fclose(f);
    mk = calloc(n, 4); ordA = malloc(sizeof(int) * n); ordB = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) ordA[i] = ordB[i] = i;
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
static int uncov(const int *D, int k, int left) {   /* exact uncovered count of PP */
    int X[512], nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = left ? M(inv[D[i]], D[j]) : M(D[i], inv[D[j]]); if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; } }
    char *c = calloc(n, 1); int cov = 0;
    for (int i = 0; i < nx; i++) for (int j = 0; j < nx; j++) { int z = M(X[i], X[j]); if (!c[z]) { c[z] = 1; cov++; } }
    free(c); return n - cov;
}
static int oddcheck(const int *D, int k) {
    int X[512], nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(inv[D[i]], D[j]); if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; } }
    char *xx = calloc(n, 1), *o = calloc(n, 1);
    for (int i = 0; i < nx; i++) for (int j = 0; j < nx; j++) xx[M(X[i], X[j])] = 1;
    for (int z = 0; z < n; z++) if (xx[z]) for (int i = 0; i < k; i++) o[M(D[i], z)] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!o[z]) ok = 0;
    free(xx); free(o); return ok;
}

/* double cosets of the current pair */
static int h, kk, ndc, *dcid, dcsz[4096], dcel[4096][4];
static int n1, n2, ones[4096], twos[4096], isrep[4096];
static int chosen[16], nch; static long long casebest; static long long casesol; static char tag[64];

static void write_edges(const int *D, int k) {
    if (!edges_out || nsol > 1) return;
    int *ca = malloc(sizeof(int) * n), *cb = malloc(sizeof(int) * n), na = 0, nb = 0;
    for (int x = 0; x < n; x++) ca[x] = cb[x] = -1;
    for (int x = 0; x < n; x++) if (ca[x] < 0) { ca[x] = ca[M(h, x)] = na++; }
    for (int y = 0; y < n; y++) if (cb[y] < 0) { cb[y] = cb[M(kk, y)] = nb++; }
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
    for (int i = 0; i < nch; i++) { int d = chosen[i]; for (int j = 0; j < dcsz[d]; j++) D[k++] = dcel[d][j]; }
    long long pa = npassA;
    if (pp_full(D, k, 1, ordA)) { npassA++;
        if (pp_full(D, k, 0, ordB)) {
            if (oddcheck(D, k)) { nsol++; casesol++; casebest = 0;
                printf("SOL %s", tag); for (int i = 0; i < nch; i++) printf(" %d", chosen[i]); printf(" | D"); for (int i = 0; i < k; i++) printf(" %d", D[i]); printf("\n"); fflush(stdout);
                if (nsol == 1) write_edges(D, k); }
        } else { int c = uncov(D, k, 0); if (c < casebest) casebest = c; }
    }
    (void)pa;
}
/* choose: n2 twos (first from reps if n2 > 0), n1 ones (first from reps if n2 == 0) */
static void rec_ones(int need, int start, int first) {
    if (capped) return;
    if (need == 0) { test(); return; }
    for (int i = start; i < n1; i++) { if (first && !isrep[ones[i]]) continue; chosen[nch++] = ones[i]; rec_ones(need - 1, first ? 0 : i + 1, 0); nch--; }
}
static int want1; static int DEG = 7;
static void rec_twos(int need, int start, int first, int firstid) {
    if (capped) return;
    if (need == 0) { rec_ones(want1, 0, 0); return; }
    for (int i = start; i < n2; i++) { int d = twos[i];
        if (first) { if (!isrep[d]) continue; chosen[nch++] = d; rec_twos(need - 1, 0, 0, d); nch--; }
        else { if (d == firstid) continue; chosen[nch++] = d; rec_twos(need - 1, i + 1, 0, firstid); nch--; } }
}
static void run_pair(int ci, int cj) {
    h = invrep[ci]; kk = invrep[cj];
    if (!dcid) dcid = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) dcid[i] = -1;
    ndc = 0; n1 = n2 = 0;
    for (int g = 0; g < n; g++) if (dcid[g] < 0) {
        int e[4] = { g, M(kk, g), M(g, h), M(M(kk, g), h) }, s = 0;
        for (int a = 0; a < 4; a++) { int dup = 0; for (int b = 0; b < s; b++) if (dcel[ndc][b] == e[a]) dup = 1; if (!dup) dcel[ndc][s++] = e[a]; }
        dcsz[ndc] = s; for (int a = 0; a < s; a++) dcid[dcel[ndc][a]] = ndc;
        if (s == 2) ones[n1++] = ndc; else if (s == 4) twos[n2++] = ndc; else { fprintf(stderr, "dc size %d\n", s); exit(1); }
        ndc++; if (ndc >= 4096) { fprintf(stderr, "too many double cosets\n"); exit(1); }
    }
    /* C = C_G(h) n C_G(k) acting by conjugation on double cosets: union-find */
    int *uf = malloc(sizeof(int) * ndc); for (int i = 0; i < ndc; i++) uf[i] = i;
    int nc = 0;
    for (int c = 0; c < n; c++) if (M(c, h) == M(h, c) && M(c, kk) == M(kk, c)) { nc++;
        int ci_ = inv[c];
        for (int d = 0; d < ndc; d++) { int d2 = dcid[M(M(c, dcel[d][0]), ci_)];
            int r1 = d, r2 = d2; while (uf[r1] != r1) r1 = uf[r1]; while (uf[r2] != r2) r2 = uf[r2];
            if (r1 != r2) { if (r1 < r2) uf[r2] = r1; else uf[r1] = r2; } } }
    int nr = 0; for (int d = 0; d < ndc; d++) { int r = d; while (uf[r] != r) r = uf[r]; isrep[d] = (r == d); nr += isrep[d]; }
    free(uf);
    int haar = 0; for (int r = 0; r < nidx2; r++) if ((idx2mask[r] >> ci & 1) && (idx2mask[r] >> cj & 1)) haar = 1;
    long long e0 = evals, p0 = npassA; clock_t c0 = clock(); casebest = 1LL << 40; casesol = 0; capped = 0;
    long long sv = cap_ev; cap_ev = evals + sv;
    snprintf(tag, sizeof tag, "c%d_c%d", ci, cj);
    for (int n2w = DEG / 2; n2w >= 0; n2w--) { want1 = DEG - 2 * n2w; if (want1 > n1) continue; if (n2w > n2) continue;
        if (n2w > 0) rec_twos(n2w, 0, 1, -1); else rec_ones(want1, 0, 1); }
    cap_ev = sv;
    printf("PAIR %d %d h %d k %d sizes %d %d dc %d ones %d twos %d cent %d reps %d haartype %d best %lld sols %lld evals %lld passXX %lld secs %.1f%s\n",
           ci, cj, h, kk, invsz[ci], invsz[cj], ndc, n1, n2, nc, nr, haar, casebest, casesol, evals - e0, npassA - p0,
           (double)(clock() - c0) / CLOCKS_PER_SEC, capped ? " CAPPED" : "");
    fflush(stdout);
}
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: bic75 FILE.ht\n"); return 2; }
    edges_out = getenv("EDGES"); if (getenv("DELTA")) DEG = atoi(getenv("DELTA")); if (getenv("MAXEV")) cap_ev = atoll(getenv("MAXEV"));
    load(argv[1]);
    printf("GROUP %s n %d invclasses %d idx2 %d\n", argv[1], n, ninvc, nidx2);
    int pi = -1, pj = -1; if (getenv("PAIR")) sscanf(getenv("PAIR"), "%d,%d", &pi, &pj);
    for (int i = 0; i < ninvc; i++) for (int j = i; j < ninvc; j++) {
        if (invsz[i] == 1 || invsz[j] == 1) continue;   /* central involution: H normal */
        if (pi >= 0 && (i != pi || j != pj)) continue;
        run_pair(i, j);
    }
    printf("DONE evals %lld sols %d\n", evals, nsol);
    return 0;
}
