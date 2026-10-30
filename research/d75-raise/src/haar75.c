/* haar75.c: Haar graphs H(G,S) of valency 7 and diameter 5 for a small group G given by its multiplication table
 * (export.g).  H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S.  Right multiplication by G is
 * transitive on each side, so diameter <= 5 iff, with X = S^-1 S and Y = S S^-1,
 *   X X = G (A to A within 4), Y Y = G (B to B within 4), Y Y S = G (A to B / B to A within 5).
 * Cost = |G \ XX| + |G \ YY| (the odd condition is checked for every cost-0 set).
 *
 * MODE exh: for each automorphism alpha of prime order p in the file, every alpha-invariant S of size 7 with
 *   p = 2: f fixed + m orbits of size 2, (f,m) = (1,3), (3,2), (5,1);  p = 3: (1,2), (4,1);  p = 5: (2,1);
 *   p = 7: (0,1).  One fixed element is the identity (H(G,S) ~ H(G,f^-1 S)).  The first non-trivial orbit runs over
 *   representatives of the orbits of the centralizer of alpha (on alpha-orbits).
 * MODE sa: simulated annealing over plain S containing e (SECS, SEED env).
 * Output: "SOL ..." lines (element indices of S) and the best cost per (alpha, type); EDGES=file writes the first
 * solution as an edge list (vertex g of A = g, of B = n + g).
 * usage: haar75 FILE.ht exh|sa
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int n, ninv;
static uint16_t *mul;   /* n*n */
static int *inv;
static int nal; static int alp[64]; static int *aperm[64]; static int ncent[64]; static int **cent[64];
static uint32_t *stampA, *stampB; static uint32_t stA = 0, stB = 0;
static long long evals = 0;
static int *ordA, *ordB; static uint32_t *mk;
static const char *edges_out = NULL; static int nsol = 0;

#define M(a,b) mul[(size_t)(a) * n + (b)]

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }

static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); ninv = rdint(f);
    mul = malloc(sizeof(uint16_t) * n * n); inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    char w[32];
    while (fscanf(f, "%31s", w) == 1) {
        if (!strcmp(w, "ALPHA")) {
            int p = rdint(f); alp[nal] = p; aperm[nal] = malloc(sizeof(int) * n);
            for (int i = 0; i < n; i++) aperm[nal][i] = rdint(f);
            if (fscanf(f, "%31s", w) != 1 || strcmp(w, "CENT")) { fprintf(stderr, "format\n"); exit(1); }
            int k = rdint(f); ncent[nal] = k; cent[nal] = malloc(sizeof(int *) * (k ? k : 1));
            for (int j = 0; j < k; j++) { cent[nal][j] = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) cent[nal][j][i] = rdint(f); }
            nal++; if (nal >= 64) break;
        }
    }
    fclose(f);
    stampA = calloc(n, sizeof(uint32_t)); stampB = calloc(n, sizeof(uint32_t)); mk = calloc(n, sizeof(uint32_t));
    ordA = malloc(sizeof(int) * n); ordB = malloc(sizeof(int) * n); for (int i = 0; i < n; i++) ordA[i] = ordB[i] = i;
    /* sanity: identity row */
    for (int i = 0; i < n; i++) if (M(0, i) != i || M(i, 0) != i || M(i, inv[i]) != 0) { fprintf(stderr, "bad table\n"); exit(1); }
}

/* uncovered count of P P where P = {a^-1 b} (left=1) or {a b^-1} (left=0); stops early when > lim */
static int xx_uncov(const int *S, int k, int left, int lim) {
    int X[64], nx = 0;
    stB++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[S[i]], S[j]) : M(S[i], inv[S[j]]);
        if (stampB[x] != stB) { stampB[x] = stB; X[nx++] = x; }
    }
    stA++; int cov = 0;
    for (int i = 0; i < nx; i++) { const uint16_t *row = mul + (size_t)X[i] * n;
        for (int j = 0; j < nx; j++) { int z = row[X[j]]; if (stampA[z] != stA) { stampA[z] = stA; cov++; } } }
    (void)lim;
    return n - cov;
}
static int cost(const int *S, int k, int lim) {
    evals++;
    int c = xx_uncov(S, k, 1, lim); if (c > lim) return c + n;   /* lower bound only */
    return c + xx_uncov(S, k, 0, lim - c);
}
/* fast rejection: is every z in P P?  z in PP iff x^-1 z in P for some x in P.  Targets are tried in a
 * move-to-front order (recent failures first), so a typical bad set is rejected after a few targets. */
static uint32_t stM = 0; static int last_fail_t = 0, NEAR = 0;
static int pp_full(const int *S, int k, int left, int *ord) {
    int X[64], nx = 0; stM++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? M(inv[S[i]], S[j]) : M(S[i], inv[S[j]]);
        if (mk[x] != stM) { mk[x] = stM; X[nx++] = x; }
    }
    const uint16_t *rows[64]; for (int i = 0; i < nx; i++) rows[i] = mul + (size_t)inv[X[i]] * n;
    for (int t = 0; t < n; t++) { int z = ord[t], ok = 0;
        for (int i = 0; i < nx; i++) if (mk[rows[i][z]] == stM) { ok = 1; break; }
        if (!ok) { last_fail_t = t; if (t) { int u = t / 2; ord[t] = ord[u]; ord[u] = z; } return 0; } }
    return 1;
}
static long long npassA = 0;
static int fast_ok(const int *S, int k) {
    evals++;
    if (!pp_full(S, k, 1, ordA)) return 0;
    npassA++;
    return pp_full(S, k, 0, ordB);
}
/* full check including the odd condition */
static int fullcheck(const int *S, int k) {
    if (cost(S, k, 0) != 0) return 0;
    int Y[64], ny = 0; stB++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = M(S[i], inv[S[j]]); if (stampB[x] != stB) { stampB[x] = stB; Y[ny++] = x; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1);
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[M(Y[i], Y[j])] = 1;
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < k; i++) odd[M(z, S[i])] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!odd[z]) ok = 0;
    /* distinct S */
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) if (S[i] == S[j]) ok = 0;
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

/* ---------- exhaustive orbit-type search ---------- */
static int norb, *orbstart, *orbel, *orbid;   /* non-trivial orbits of alpha: elements orbel[orbstart[o]..] */
static int nfix, *fixel;
static int *isrep;
static long long typebest; static long long typesol;
static int Sbuf[16];

static int anti = 0, *apm; static int NFIXBIG = 150;   /* psi with more fixed elements: low cap (abelian-like, no hits seen) */
static void build_orbits(int a) {
    int p = alp[a]; int *pm = aperm[a];
    if (anti) {   /* psi(x) = beta(x)^-1, beta = alpha_a of order 1 or 2: orbits of size 1 (beta(x) = x^-1) and 2 */
        if (!apm) apm = malloc(sizeof(int) * n);
        for (int i = 0; i < n; i++) apm[i] = inv[pm[i]];
        pm = apm; p = 2;
    }
    free(orbstart); free(orbel); free(orbid); free(fixel); free(isrep);
    orbstart = malloc(sizeof(int) * (n + 1)); orbel = malloc(sizeof(int) * n); orbid = malloc(sizeof(int) * n);
    fixel = malloc(sizeof(int) * n); isrep = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) orbid[i] = -2;
    norb = 0; nfix = 0; int ne = 0;
    for (int i = 0; i < n; i++) if (orbid[i] == -2) {
        if (pm[i] == i) { orbid[i] = -1; fixel[nfix++] = i; continue; }
        orbstart[norb] = ne; int x = i, c = 0;
        do { orbid[x] = norb; orbel[ne++] = x; x = pm[x]; c++; } while (x != i);
        if (c != p && !(p == 1)) { fprintf(stderr, "orbit size %d != %d\n", c, p); exit(1); }
        norb++;
    }
    orbstart[norb] = ne;
    /* centralizer orbits on alpha-orbits: union-find */
    int *uf = malloc(sizeof(int) * (norb ? norb : 1));
    for (int o = 0; o < norb; o++) uf[o] = o;
    for (int g = 0; g < ncent[a]; g++) for (int o = 0; o < norb; o++) {
        int o2 = orbid[cent[a][g][orbel[orbstart[o]]]]; if (o2 < 0) continue;
        int r1 = o, r2 = o2; while (uf[r1] != r1) r1 = uf[r1]; while (uf[r2] != r2) r2 = uf[r2];
        if (r1 != r2) { if (r1 < r2) uf[r2] = r1; else uf[r1] = r2; }
    }
    int nrep = 0;
    for (int o = 0; o < norb; o++) { int r = o; while (uf[r] != r) r = uf[r]; isrep[o] = (r == o); nrep += isrep[o]; }
    free(uf);
    fprintf(stderr, "alpha %d: p %d fixed %d orbits %d reps %d\n", a, p, nfix, norb, nrep);
}

static int use_fast = 1; static long long cap_ev = 30000000, cap_ev_lo = 30000000, cap_ev_hi = 30000000, type_e0 = 0; static int capped = 0;
static void eval_set(int k, const char *tag) {
    if (evals - type_e0 >= cap_ev) { capped = 1; return; }
    if (use_fast) {
        long long pa = npassA;
        if (fast_ok(Sbuf, k)) { if (fullcheck(Sbuf, k)) { typesol++; typebest = 0; report(Sbuf, k, tag); } return; }
        if (npassA > pa) {   /* XX = G but YY != G: record the YY cost as a near miss */
            int c = cost(Sbuf, k, 1 << 30); evals--; if (c < typebest) typebest = c; }
        else if (anti && NEAR && last_fail_t >= NEAR) {   /* self-dual near miss: exact |G \ XX| */
            int c = xx_uncov(Sbuf, k, 1, 1 << 30); if (c < typebest) typebest = c; }
        return;
    }
    int c = cost(Sbuf, k, typebest < 1000000 ? (int)typebest : 1000000);
    if (c < typebest) typebest = c;
    if (c == 0 && fullcheck(Sbuf, k)) { typesol++; report(Sbuf, k, tag); }
}
static void put_orbit(int o, int at) { int p = orbstart[o + 1] - orbstart[o]; for (int j = 0; j < p; j++) Sbuf[at + j] = orbel[orbstart[o] + j]; }

/* choose 'need' fixed elements from fixel (excluding identity) starting at index fs, then the orbits */
static int want_m, want_f; static char tagbuf[64];
static void rec_orb(int depth, int start, int at) {
    if (capped) return;
    if (depth == want_m) { eval_set(at, tagbuf); return; }
    if (depth == 0) {
        for (int o = 0; o < norb; o++) if (isrep[o]) { put_orbit(o, at); rec_orb(1, -1, at + alp[0] * 0 + (orbstart[o + 1] - orbstart[o])); }
        return;
    }
    /* depth >= 1: orbits other than the first, increasing among themselves */
    int first = orbid[Sbuf[want_f]];
    for (int o = (start < 0 ? 0 : start); o < norb; o++) if (o != first) {
        if (depth >= 2) { int prev = orbid[Sbuf[at - (orbstart[o + 1] - orbstart[o])]]; (void)prev; }
        put_orbit(o, at); rec_orb(depth + 1, o + 1, at + (orbstart[o + 1] - orbstart[o]));
    }
}
static void rec_fix(int need, int fs, int at) {
    if (capped) return;
    if (need == 0) { rec_orb(0, 0, at); return; }
    for (int i = fs; i < nfix; i++) if (fixel[i] != 0) { Sbuf[at] = fixel[i]; rec_fix(need - 1, i + 1, at + 1); }
}

/* beta of order 4: psi = inv o beta has order 4, orbits of size 1, 2, 4; S = {e} + one 2-orbit + one 4-orbit, or
 * {e} + 2 fixed + one 4-orbit (sets without a 4-orbit are psi^3- or beta^2-invariant, covered elsewhere) */
static void run_anti4(int a) {
    int *pm = aperm[a]; int *ps = malloc(sizeof(int) * n), *seen = calloc(n, sizeof(int));
    for (int i = 0; i < n; i++) ps[i] = inv[pm[i]];
    int *fx = malloc(sizeof(int) * n), nf = 0, (*o2)[2] = malloc(sizeof(int) * 2 * n), n2 = 0, (*o4)[4] = malloc(sizeof(int) * 4 * n), n4 = 0;
    for (int i = 0; i < n; i++) if (!seen[i]) {
        int c[8], k = 0, x = i; do { if (k < 8) c[k] = x; k++; seen[x] = 1; x = ps[x]; } while (x != i);
        if (k == 1) fx[nf++] = i; else if (k == 2) { o2[n2][0] = c[0]; o2[n2][1] = c[1]; n2++; }
        else if (k == 4) { for (int j = 0; j < 4; j++) o4[n4][j] = c[j]; n4++; }
    }
    long long e0 = evals, p0 = npassA; clock_t c0 = clock(); typebest = 1LL << 40; typesol = 0;
    snprintf(tagbuf, sizeof tagbuf, "anti4_a%d", a);
    for (int q = 0; q < n4; q++) {
        for (int j = 0; j < 4; j++) Sbuf[1 + j] = o4[q][j]; Sbuf[0] = 0;
        for (int t = 0; t < n2; t++) { Sbuf[5] = o2[t][0]; Sbuf[6] = o2[t][1]; eval_set(7, tagbuf); }
        for (int u = 0; u < nf; u++) if (fx[u] != 0) for (int v = u + 1; v < nf; v++) if (fx[v] != 0) { Sbuf[5] = fx[u]; Sbuf[6] = fx[v]; eval_set(7, tagbuf); }
    }
    /* sets made of psi's fixed points and 2-cycles only: (1,3), (3,2), (5,1) (still self-dual; beta^2-invariant) */
    long long lim = evals + cap_ev_lo; int fz[64];
    for (int i = 0, k = 0; i < nf && k < 64; i++) if (fx[i] != 0) fz[k++] = fx[i];
    int nz = nf - 1 < 64 ? nf - 1 : 64; Sbuf[0] = 0;
    for (int a1 = 0; a1 < n2 && evals < lim; a1++) for (int a2 = a1 + 1; a2 < n2; a2++) {
        Sbuf[1] = o2[a1][0]; Sbuf[2] = o2[a1][1]; Sbuf[3] = o2[a2][0]; Sbuf[4] = o2[a2][1];
        for (int a3 = a2 + 1; a3 < n2; a3++) { Sbuf[5] = o2[a3][0]; Sbuf[6] = o2[a3][1]; eval_set(7, tagbuf); }
        for (int u = 0; u < nz; u++) for (int v = u + 1; v < nz; v++) { Sbuf[5] = fz[u]; Sbuf[6] = fz[v]; eval_set(7, tagbuf); } }
    for (int a1 = 0; a1 < n2 && evals < lim; a1++) { Sbuf[1] = o2[a1][0]; Sbuf[2] = o2[a1][1];
        for (int u = 0; u < nz; u++) for (int v = u + 1; v < nz; v++) for (int w = v + 1; w < nz; w++) for (int z = w + 1; z < nz; z++) {
            Sbuf[3] = fz[u]; Sbuf[4] = fz[v]; Sbuf[5] = fz[w]; Sbuf[6] = fz[z]; eval_set(7, tagbuf); } }
    printf("ANTI4 alpha %d p 4 fixed %d two %d four %d best %lld sols %lld evals %lld passXX %lld secs %.1f\n", a, nf, n2, n4,
           typebest, typesol, evals - e0, npassA - p0, (double)(clock() - c0) / CLOCKS_PER_SEC);
    fflush(stdout); free(ps); free(seen); free(fx); free(o2); free(o4);
}
static void run_anti(void) {
    static const int types[][2] = { {1,3}, {3,2}, {5,1}, {7,0} };
    anti = 1;
    for (int a = 0; a < nal; a++) {
        if (alp[a] == 4) { type_e0 = evals; cap_ev = 1LL << 62; capped = 0; run_anti4(a); continue; }
        if (alp[a] != 1 && alp[a] != 2) continue;
        build_orbits(a);
        for (int t = 0; t < 4; t++) {
            int f = types[t][0], m = types[t][1];
            if (f > nfix || m > norb) continue;
            want_m = m; want_f = f; typebest = 1LL << 40; typesol = 0;
            long long e0 = evals, p0 = npassA; clock_t c0 = clock(); type_e0 = evals; capped = 0;
            cap_ev = (f >= 4 || nfix > NFIXBIG) ? cap_ev_hi : cap_ev_lo;
            snprintf(tagbuf, sizeof tagbuf, "anti_a%d_p%d_f%d_m%d", a, alp[a], f, m);
            Sbuf[0] = 0; rec_fix(f - 1, 0, 1);
            printf("ANTI alpha %d p %d f %d m %d best %lld sols %lld evals %lld passXX %lld secs %.1f%s\n", a, alp[a], f, m,
                   typebest, typesol, evals - e0, npassA - p0, (double)(clock() - c0) / CLOCKS_PER_SEC, capped ? " CAPPED" : "");
            fflush(stdout);
        }
    }
}

static void run_exh(void) {
    static const int types[][3] = { {2,1,3}, {2,3,2}, {2,5,1}, {3,1,2}, {3,4,1}, {5,2,1}, {7,0,1} };
    for (int a = 0; a < nal; a++) {
        if (alp[a] == 1 || alp[a] == 4) continue;   /* identity and order 4: anti mode only */
        build_orbits(a);
        for (int t = 0; t < 7; t++) if (types[t][0] == alp[a]) {
            int f = types[t][1], m = types[t][2];
            if (f > nfix || m > norb) continue;
            want_m = m; want_f = f; typebest = 1LL << 40; typesol = 0;
            long long e0 = evals, p0 = npassA; clock_t c0 = clock(); type_e0 = evals; capped = 0;
            cap_ev = f >= 4 ? cap_ev_hi : cap_ev_lo;
            snprintf(tagbuf, sizeof tagbuf, "a%d_p%d_f%d_m%d", a, alp[a], f, m);
            if (f >= 1) { Sbuf[0] = 0; rec_fix(f - 1, 0, 1); } else rec_fix(0, 0, 0);
            printf("TYPE alpha %d p %d f %d m %d best %lld sols %lld evals %lld passXX %lld secs %.1f%s\n", a, alp[a], f, m,
                   typebest, typesol, evals - e0, npassA - p0, (double)(clock() - c0) / CLOCKS_PER_SEC, capped ? " CAPPED" : "");
            fflush(stdout);
        }
    }
}

/* ---------- plain annealing ---------- */
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void run_sa(void) {
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 60; int seed = getenv("SEED") ? atoi(getenv("SEED")) : 1;
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int k = 7, S[7], B[7]; S[0] = 0;
    for (int i = 1; i < k; i++) { again: S[i] = 1 + rnd() % (n - 1); for (int j = 1; j < i; j++) if (S[j] == S[i]) goto again; }
    int c = cost(S, k, 1 << 30), best = c; memcpy(B, S, sizeof S);
    double T0 = 3.0, T = T0; time_t t0 = time(NULL); long it = 0;
    while (1) {
        if ((it & 1023) == 0) { double el = difftime(time(NULL), t0); if (el > secs) break; T = T0 * (1 - el / secs) + 0.05; }
        it++;
        int i = 1 + rnd() % (k - 1), old = S[i], v;
        do { v = 1 + rnd() % (n - 1); int dup = 0; for (int j = 0; j < k; j++) if (S[j] == v) dup = 1; if (!dup) break; } while (1);
        S[i] = v; int c2 = cost(S, k, 1 << 30);
        if (c2 <= c || (double)(rnd() % 1000000) / 1e6 < __builtin_exp((c - c2) / T)) { c = c2;
            if (c < best) { best = c; memcpy(B, S, sizeof S); if (best == 0 && fullcheck(B, k)) { report(B, k, "sa"); break; } } }
        else S[i] = old;
    }
    printf("SA best %d evals %lld set", best, evals); for (int i = 0; i < k; i++) printf(" %d", B[i]); printf("\n");
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: haar75 FILE.ht exh|sa\n"); return 2; }
    edges_out = getenv("EDGES");
    load(argv[1]);
    printf("GROUP %s n %d ninv %d nalpha %d\n", argv[1], n, ninv, nal);
    if (getenv("SLOW")) use_fast = 0;
    if (getenv("MAXEV")) cap_ev_lo = cap_ev_hi = atoll(getenv("MAXEV"));
    if (getenv("NEAR")) NEAR = atoi(getenv("NEAR"));
    if (getenv("NFIXBIG")) NFIXBIG = atoi(getenv("NFIXBIG"));
    if (getenv("MAXEVF")) cap_ev_hi = atoll(getenv("MAXEVF"));   /* cap for types with >= 4 fixed elements */
    if (!strcmp(argv[2], "exh")) run_exh();
    else if (!strcmp(argv[2], "anti")) run_anti();
    else if (!strcmp(argv[2], "both")) { run_exh(); run_anti(); } else run_sa();
    printf("DONE evals %lld sols %d\n", evals, nsol);
    return 0;
}
