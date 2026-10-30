/* sdk.c: self-dual Haar graphs H(G,S) of valency K and diameter 5, i.e. K-valent bipartite Cayley graphs on 2|G|
 * vertices, for a group G given by its multiplication table (export_sd.g).
 *
 * H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S.  With X = S^-1 S the graph has diameter <= 5 iff
 * X X = G, Y Y = G (Y = S S^-1) and Y Y S = G.  Let G^ = G u G t be an extension with t^2 = c, t x t^-1 = beta(x)
 * (beta(c) = c, beta^2 = conjugation by c).  For T = t S, T = T^-1 iff S is a union of orbits of the involution
 * psi(x) = c^-1 beta(x)^-1, and then H(G,S) = Cay(G^, T), which is vertex-transitive: X X = G alone gives
 * diameter <= 5.  Every K-valent bipartite Cayley graph arises so, with t in T (so e in S):
 *   ALPHA records (c = e, beta = identity or an involution class of Aut(G)): t an involution of T; S = e + (f-1)
 *     psi-fixed elements + m psi-2-orbits, f + 2m = K, f >= 1, f = K mod 2;
 *   EXT records (c <> e, all Aut(G)-classes of (beta, c)): T has no involution (K even), t of order > 2;
 *     S = {e, c^-1} + (K/2 - 1) further 2-orbits.
 * Normalisation: the first 2-orbit chosen freely (or, for m = 0, the first non-identity fixed element) runs over
 * representatives of the orbits of the stabilizer of (beta, c) in Aut(G) (CENT generators).
 * Fast rejection: z is in X X iff x^-1 z is in X for some x in X; targets in move-to-front order.  Every set passing
 * X X = G gets the full three-condition check (both sides and the odd condition) before it is reported.
 * Env: K (valency, default 6), MAXEV (cap per type, default 1e8), MAXEVF (cap for types with f >= 4, default MAXEV),
 *   NEAR (exact |G \ XX| for sets surviving NEAR targets), EDGES (edge list of the first solution), ONLY (ALPHA|EXT),
 *   SAMPLE: 2 (default) = a type with more sets than its cap is not enumerated but sampled: MAXEV (MAXEVF) uniformly
 *   random sets (SEED); 1 = sample every type; 0 = enumerate and cut at the cap (CAPPED); TYPES=f1,f2,..: only these
 *   numbers of psi-fixed elements.
 * Output: "SOL tag s_0 .. s_K-1" (element indices), one "TYPE" line per (record, type), "DONE".
 * usage: sdk FILE.ht
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int n, ninv, K = 6;
static uint16_t *mul, *mulT;   /* mulT[z*n + y] = y z */
static int *inv;
#define MAXREC 4096
static int nrec, rkind[MAXREC], rp[MAXREC], rc[MAXREC], *rbeta[MAXREC], ncent[MAXREC], **cent[MAXREC];
static uint32_t *stA, *mk; static uint32_t sA = 0, sM = 0;
static long long evals = 0, npassA = 0;
static int *ordA; static int last_fail_t = 0, NEAR = 0;
static const char *edges_out = NULL; static int nsol = 0;
#define M(a,b) mul[(size_t)(a) * n + (b)]

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }
static int *rdperm(FILE *f) { int *p = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) p[i] = rdint(f); return p; }

static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); ninv = rdint(f);
    mul = malloc(sizeof(uint16_t) * n * n); inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    mulT = malloc(sizeof(uint16_t) * n * n);
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) mulT[(size_t)b * n + a] = mul[(size_t)a * n + b];
    char w[32];
    while (fscanf(f, "%31s", w) == 1 && nrec < MAXREC) {
        if (!strcmp(w, "ALPHA")) { rkind[nrec] = 0; rp[nrec] = rdint(f); rc[nrec] = 0; }
        else if (!strcmp(w, "EXT")) { rkind[nrec] = 1; rp[nrec] = 0; rc[nrec] = rdint(f); }
        else { fprintf(stderr, "format: %s\n", w); exit(1); }
        rbeta[nrec] = rdperm(f);
        if (fscanf(f, "%31s", w) != 1 || strcmp(w, "CENT")) { fprintf(stderr, "format\n"); exit(1); }
        int k = rdint(f); ncent[nrec] = k; cent[nrec] = malloc(sizeof(int *) * (k ? k : 1));
        for (int j = 0; j < k; j++) cent[nrec][j] = rdperm(f);
        nrec++;
    }
    fclose(f);
    stA = calloc(n, sizeof(uint32_t)); mk = calloc(n, sizeof(uint32_t));
    ordA = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) ordA[i] = i;
    for (int i = 0; i < n; i++) if (M(0, i) != i || M(i, 0) != i || M(i, inv[i]) != 0) { fprintf(stderr, "bad table\n"); exit(1); }
}

/* |G \ P P|, P = S^-1 S (left = 1) or S S^-1 (left = 0) */
static int pp_uncov(const int *S, int k, int left) {
    int X[128], nx = 0; sM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[S[i]], S[j]) : M(S[i], inv[S[j]]);
        if (mk[x] != sM) { mk[x] = sM; X[nx++] = x; } }
    sA++; int cov = 0;
    for (int i = 0; i < nx; i++) { const uint16_t *row = mul + (size_t)X[i] * n;
        for (int j = 0; j < nx; j++) { int z = row[X[j]]; if (stA[z] != sA) { stA[z] = sA; cov++; } } }
    return n - cov;
}
/* fast test of S^-1 S S^-1 S = G with move-to-front targets */
static int xx_full(const int *S, int k) {
    int X[128], ix[128], nx = 0; sM++;
    for (int i = 0; i < k; i++) { const uint16_t *row = mul + (size_t)inv[S[i]] * n;
        for (int j = 0; j < k; j++) { int x = row[S[j]]; if (mk[x] != sM) { mk[x] = sM; X[nx++] = x; } } }
    for (int i = 0; i < nx; i++) ix[i] = inv[X[i]];
    for (int t = 0; t < n; t++) { int z = ordA[t], ok = 0; const uint16_t *col = mulT + (size_t)z * n;
        for (int i = 0; i < nx; i++) if (mk[col[ix[i]]] == sM) { ok = 1; break; }
        if (!ok) { last_fail_t = t; if (t) { int u = t / 2; ordA[t] = ordA[u]; ordA[u] = z; } return 0; } }
    return 1;
}
/* full check: X X = G, Y Y = G, Y Y S = G, K distinct elements */
static int fullcheck(const int *S, int k) {
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) if (S[i] == S[j]) return 0;
    if (pp_uncov(S, k, 1) || pp_uncov(S, k, 0)) return 0;
    int Y[128], ny = 0; sM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(S[i], inv[S[j]]); if (mk[x] != sM) { mk[x] = sM; Y[ny++] = x; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1);
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[M(Y[i], Y[j])] = 1;
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < k; i++) odd[M(z, S[i])] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!odd[z]) ok = 0;
    free(yy); free(odd); return ok;
}
static void report(const int *S, int k, const char *tag) {
    nsol++;
    printf("SOL %s", tag); for (int i = 0; i < k; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout);
    if (edges_out && nsol == 1) {
        FILE *f = fopen(edges_out, "w"); fprintf(f, "%d\n", 2 * n);
        for (int g = 0; g < n; g++) for (int i = 0; i < k; i++) fprintf(f, "%d %d\n", g, n + M(S[i], g));
        fclose(f);
    }
}

/* ---------- enumeration ---------- */
static int *psi, *fl, nfl, (*ol)[2], nol, *orbof, *isrep_o, *isrep_f;
static int Sb[32]; static char tag[96];
static long long cap_ev = 100000000LL, cap_lo = 100000000LL, cap_hi = -1, type_e0; static int capped;
static long long tbest, tsol;
static int excl_o1 = -1, excl_o2 = -1, excl_f = -1, fneed;

static void eval_set(void) {
    if (evals - type_e0 >= cap_ev) { capped = 1; return; }
    evals++;
    if (xx_full(Sb, K)) {
        npassA++;
        if (fullcheck(Sb, K)) { tsol++; tbest = 0; report(Sb, K, tag); }
        else fprintf(stderr, "WARNING %s: X X = G but the full check fails (not self-dual?)\n", tag);
    } else if (NEAR && last_fail_t >= NEAR) { int c = pp_uncov(Sb, K, 1); if (c < tbest) tbest = c; }
}
static void rec_f(int need, int from, int at) {
    if (capped) return;
    if (need == 0) { eval_set(); return; }
    for (int i = from; i < nfl; i++) if (i != excl_f) { Sb[at] = fl[i]; rec_f(need - 1, i + 1, at + 1); if (capped) return; }
}
static void rec_o(int need, int from, int at) {
    if (capped) return;
    if (need == 0) { rec_f(fneed, 0, at); return; }
    for (int o = from; o < nol; o++) if (o != excl_o1 && o != excl_o2) {
        Sb[at] = ol[o][0]; Sb[at + 1] = ol[o][1]; rec_o(need - 1, o + 1, at + 2); if (capped) return; }
}

static int uf_find(int *uf, int x) { while (uf[x] != x) x = uf[x] = uf[uf[x]]; return x; }
static void uf_join(int *uf, int a, int b) { a = uf_find(uf, a); b = uf_find(uf, b); if (a != b) { if (a < b) uf[b] = a; else uf[a] = b; } }

static void setup(int r) {
    int *be = rbeta[r], c = rc[r];
    for (int i = 0; i < n; i++) psi[i] = M(inv[c], inv[be[i]]);
    /* sanity: psi is an involution; EXT: beta(c) = c, beta^2 = conjugation by c */
    for (int i = 0; i < n; i++) if (psi[psi[i]] != i) { fprintf(stderr, "record %d: psi is not an involution\n", r); exit(1); }
    if (rkind[r]) { if (be[c] != c) { fprintf(stderr, "record %d: beta(c) != c\n", r); exit(1); }
        for (int i = 0; i < n; i++) if (be[be[i]] != M(M(c, i), inv[c])) { fprintf(stderr, "record %d: beta^2 != conj(c)\n", r); exit(1); } }
    nfl = 0; nol = 0;
    for (int i = 0; i < n; i++) {
        if (psi[i] == i) { orbof[i] = -1; if (i != 0) fl[nfl++] = i; }
        else if (i < psi[i]) { ol[nol][0] = i; ol[nol][1] = psi[i]; orbof[i] = orbof[psi[i]] = nol; nol++; }
    }
    /* orbits of the stabilizer on 2-orbits and on fixed points */
    int *uf = malloc(sizeof(int) * (nol + 1)), *uff = malloc(sizeof(int) * n), *fpos = malloc(sizeof(int) * n);
    for (int o = 0; o < nol; o++) uf[o] = o;
    for (int i = 0; i < n; i++) fpos[i] = -1;
    for (int i = 0; i < nfl; i++) { uff[i] = i; fpos[fl[i]] = i; }
    for (int g = 0; g < ncent[r]; g++) { int *p = cent[r][g];
        for (int o = 0; o < nol; o++) { int o2 = orbof[p[ol[o][0]]]; if (o2 < 0) { fprintf(stderr, "cent does not commute with psi\n"); exit(1); } uf_join(uf, o, o2); }
        for (int i = 0; i < nfl; i++) { int j = fpos[p[fl[i]]]; if (j < 0) { fprintf(stderr, "cent moves a fixed point out\n"); exit(1); } uf_join(uff, i, j); } }
    for (int o = 0; o < nol; o++) isrep_o[o] = uf_find(uf, o) == o;
    for (int i = 0; i < nfl; i++) isrep_f[i] = uf_find(uff, i) == i;
    free(uf); free(uff); free(fpos);
}

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int sample = 2;
/* random set of the type: e (+ c^-1 for EXT), f-1 distinct non-identity fixed elements, the remaining 2-orbits distinct */
static void sample_type(int r, int f, int m) {
    int pick[32];
    while (!capped) {
        int at = 0, np = 0;
        if (rkind[r] == 0) { Sb[at++] = 0;
            for (int i = 0; i < f - 1; i++) { int x; again: x = (int)(rnd() % nfl); for (int j = 0; j < np; j++) if (pick[j] == x) goto again; pick[np++] = x; Sb[at++] = fl[x]; }
            np = 0;
            for (int i = 0; i < m; i++) { int o; again2: o = (int)(rnd() % nol); for (int j = 0; j < np; j++) if (pick[j] == o) goto again2; pick[np++] = o; Sb[at++] = ol[o][0]; Sb[at++] = ol[o][1]; }
        } else { int oe = orbof[0]; pick[np++] = oe; Sb[at++] = ol[oe][0]; Sb[at++] = ol[oe][1];
            for (int i = 1; i < m; i++) { int o; again3: o = (int)(rnd() % nol); for (int j = 0; j < np; j++) if (pick[j] == o) goto again3; pick[np++] = o; Sb[at++] = ol[o][0]; Sb[at++] = ol[o][1]; }
        }
        eval_set();
    }
}
static double binom(int a, int b) { if (b < 0 || a < b) return 0; double x = 1; for (int i = 0; i < b; i++) x = x * (a - i) / (i + 1); return x; }
/* number of sets the enumeration of this type visits */
static double type_size(int r, int f, int m) {
    int nro = 0, nrf = 0; for (int o = 0; o < nol; o++) nro += isrep_o[o]; for (int i = 0; i < nfl; i++) nrf += isrep_f[i];
    if (rkind[r]) { int oe = orbof[0]; return m == 1 ? 1 : (nro - isrep_o[oe]) * binom(nol - 2, m - 2); }
    if (m >= 1) return nro * binom(nol - 1, m - 1) * binom(nfl, f - 1);
    return nrf * binom(nfl - 1, f - 2);
}
static void run_type(int r, int f, int m) {
    tbest = 1LL << 40; tsol = 0; capped = 0; type_e0 = evals;
    cap_ev = (f >= 4 && cap_hi >= 0) ? cap_hi : cap_lo;
    double tsz = type_size(r, f, m);
    int smp = sample == 1 || (sample == 2 && tsz > (double)cap_ev);   /* SAMPLE=2 (default): sample only types larger than the cap */
    long long p0 = npassA; clock_t c0 = clock();
    snprintf(tag, sizeof tag, "r%d_%s%d_f%d_m%d%s", r, rkind[r] ? "ext" : "alpha", rkind[r] ? rc[r] : rp[r], f, m, smp ? "_rnd" : "");
    Sb[0] = 0; excl_o1 = excl_o2 = excl_f = -1;
    if (smp) sample_type(r, f, m);
    else if (rkind[r] == 0) {
        if (m >= 1) {
            fneed = f - 1;
            for (int o = 0; o < nol && !capped; o++) if (isrep_o[o]) {
                Sb[1] = ol[o][0]; Sb[2] = ol[o][1]; excl_o1 = o; rec_o(m - 1, 0, 3); }
        } else {
            fneed = f - 2;
            for (int i = 0; i < nfl && !capped; i++) if (isrep_f[i]) { Sb[1] = fl[i]; excl_f = i; rec_f(fneed, 0, 2); }
        }
    } else {
        int oe = orbof[0]; excl_o1 = oe; fneed = 0;
        Sb[0] = ol[oe][0]; Sb[1] = ol[oe][1];
        if (m == 1) eval_set();
        else for (int o = 0; o < nol && !capped; o++) if (o != oe && isrep_o[o]) {
            Sb[2] = ol[o][0]; Sb[3] = ol[o][1]; excl_o2 = o; rec_o(m - 2, 0, 4); }
    }
    printf("TYPE rec %d %s %d f %d m %d best %lld sols %lld evals %lld size %.3g passXX %lld secs %.1f%s\n", r, rkind[r] ? "ext" : "alpha",
           rkind[r] ? rc[r] : rp[r], f, m, tbest, tsol, evals - type_e0, tsz, npassA - p0, (double)(clock() - c0) / CLOCKS_PER_SEC,
           smp ? " SAMPLED" : capped ? " CAPPED" : "");
    fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: sdk FILE.ht\n"); return 2; }
    if (getenv("K")) K = atoi(getenv("K"));
    if (K < 3 || K > 11) { fprintf(stderr, "K out of range\n"); return 2; }
    edges_out = getenv("EDGES");
    if (getenv("MAXEV")) cap_lo = atoll(getenv("MAXEV"));
    if (getenv("MAXEVF")) cap_hi = atoll(getenv("MAXEVF"));
    if (getenv("NEAR")) NEAR = atoi(getenv("NEAR"));
    const char *only = getenv("ONLY"), *types = getenv("TYPES");
    if (getenv("SAMPLE")) sample = atoi(getenv("SAMPLE"));
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd(); }
    load(argv[1]);
    int next = 0; for (int r = 0; r < nrec; r++) next += rkind[r];
    printf("GROUP %s n %d ninv %d K %d records %d (ext %d)\n", argv[1], n, ninv, K, nrec, next);
    psi = malloc(sizeof(int) * n); fl = malloc(sizeof(int) * n); ol = malloc(sizeof(int) * 2 * n); orbof = malloc(sizeof(int) * n);
    isrep_o = malloc(sizeof(int) * n); isrep_f = malloc(sizeof(int) * n);
    for (int r = 0; r < nrec; r++) {
        if (rkind[r] == 0 && rp[r] != 1 && rp[r] != 2) continue;
        if (only && strcmp(only, rkind[r] ? "EXT" : "ALPHA")) continue;
        if (rkind[r] == 1 && K % 2) continue;
        setup(r);
        int nrep = 0; for (int o = 0; o < nol; o++) nrep += isrep_o[o];
        fprintf(stderr, "record %d %s: fixed %d (non-identity) orbits %d reps %d\n", r, rkind[r] ? "EXT" : "ALPHA", nfl, nol, nrep);
        if (rkind[r] == 0) {
            for (int f = (K % 2 ? 1 : 2); f <= K; f += 2) { int m = (K - f) / 2;
                if (f - 1 > nfl || m > nol) continue;
                if (types) { char b[8]; snprintf(b, sizeof b, "%d", f); if (!strstr(types, b)) continue; }
                run_type(r, f, m); }
        } else {
            if (types && !strstr(types, "0")) continue;
            if (K / 2 <= nol) run_type(r, 0, K / 2);
        }
    }
    printf("DONE evals %lld sols %d\n", evals, nsol);
    return 0;
}
