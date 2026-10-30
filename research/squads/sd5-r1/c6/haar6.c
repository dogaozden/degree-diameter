/* haar6.c: automorphism-invariant Haar graphs H(G,S) of valency 6 (adapted from research/d75-raise/src/haar75.c,
 * mode exh, K = 6).  G is given by its multiplication table (export.g format, identity index 0).
 *
 * H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S.  Diameter <= 5 iff, with X = S^-1 S and Y = S S^-1,
 *   X X = G (A to A within 4), Y Y = G (B to B within 4), (Y Y) S = G (A to B within 5).
 * Cost = |G \ XX| + |G \ YY|; sets of cost 0 are checked for the odd condition (Y Y S = G) too.
 *
 * S is invariant under alpha in Aut(G) of prime order p in {3, 5} (ALPHA records of the file).  S is a union of
 * alpha-orbits (size p) and fixed points; f = number of fixed elements of S (the identity counts when f >= 1), m = number
 * of orbits, f + p m = 6:
 *   p = 3: (f,m) = (0,2), (3,1), (6,0);     p = 5: (1,1), (6,0).
 * If f >= 1 the identity is in S (WLOG: H(G,S) ~ H(G, f^-1 S) and f^-1 S is alpha-invariant for alpha-fixed f).
 * f = 0 sets contain no identity; they are enumerated as they are (no translation normalization).
 * The first orbit runs over representatives of C_Aut(G)(alpha) acting on the alpha-orbits (valid because gamma in
 * C(alpha) maps alpha-invariant sets to alpha-invariant sets and H(G,S) to H(G,gamma S)); all other fixed points and
 * orbits are enumerated.
 *
 * usage: haar6 FILE.ht          env: EDGES=prefix (writes prefix_<k>.el for the first EDGESMAX solutions, default 5)
 *                                    CAP=evals per type (default 3e7); ONLYP=3 or 5 (default both)
 * output: "SOL tag s1..s6" lines (element indices), "TYPE ..." lines per (alpha, f, m), "DONE ..." line.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define K 6

static int n, ninv;
static uint16_t *mul;
static int *inv;
static int nal, alp[64], ncent[64];
static int *aperm[64];
static int **cent[64];
static uint32_t *stampA, *stampB; static uint32_t stA = 0, stB = 0;
static long long evals = 0, cap_limit = 0;
static int capped = 0, nsol = 0, oddfail = 0;
static long long typesol = 0; static long long typebest = 0; static long long gbest = 1LL << 40;
static char gbest_tag[64];
static const char *edges_pfx = NULL; static int edges_max = 5;
static long long CAP = 30000000LL; static int onlyp = 0, with2 = 0;   /* with2: also order-2 alpha (calibration only) */
static char tag[64];

#define M(a, b) mul[(size_t)(a) * n + (b)]

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }

static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); ninv = rdint(f);
    mul = malloc(sizeof(uint16_t) * (size_t)n * n); inv = malloc(sizeof(int) * n);
    for (int i = 0; i < n * n; i++) mul[i] = (uint16_t)rdint(f);
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
    stampA = calloc(n, sizeof(uint32_t)); stampB = calloc(n, sizeof(uint32_t));
    for (int i = 0; i < n; i++) if (M(0, i) != i || M(i, 0) != i || M(i, inv[i]) != 0) { fprintf(stderr, "bad table\n"); exit(1); }
}

/* |G \ P P| for P = {S_i^-1 S_j} (left = 1) or P = {S_i S_j^-1} (left = 0) */
static int uncov(const int *S, int left) {
    int X[K * K], nx = 0;
    stB++;
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) {
        int x = left ? M(inv[S[i]], S[j]) : M(S[i], inv[S[j]]);
        if (stampB[x] != stB) { stampB[x] = stB; X[nx++] = x; }
    }
    stA++; int cov = 0;
    for (int i = 0; i < nx; i++) { const uint16_t *row = mul + (size_t)X[i] * n;
        for (int j = 0; j < nx; j++) { int z = row[X[j]]; if (stampA[z] != stA) { stampA[z] = stA; cov++; } } }
    return n - cov;
}
static int cost(const int *S) { evals++; return uncov(S, 1) + uncov(S, 0); }

/* cost 0: check the odd condition (Y Y) S = G and that the elements of S are distinct */
static int fullcheck(const int *S) {
    for (int i = 0; i < K; i++) for (int j = i + 1; j < K; j++) if (S[i] == S[j]) return 0;
    int Y[K * K], ny = 0; stB++;
    for (int i = 0; i < K; i++) for (int j = 0; j < K; j++) { int x = M(S[i], inv[S[j]]); if (stampB[x] != stB) { stampB[x] = stB; Y[ny++] = x; } }
    char *yy = calloc(n, 1), *odd = calloc(n, 1);
    for (int i = 0; i < ny; i++) for (int j = 0; j < ny; j++) yy[M(Y[i], Y[j])] = 1;
    for (int z = 0; z < n; z++) if (yy[z]) for (int i = 0; i < K; i++) odd[M(z, S[i])] = 1;
    int ok = 1; for (int z = 0; z < n; z++) if (!odd[z]) { ok = 0; break; }
    free(yy); free(odd); return ok;
}

static void report(const int *S) {
    nsol++;
    printf("SOL %s", tag); for (int i = 0; i < K; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout);
    if (edges_pfx && nsol <= edges_max) {
        char fn[1024]; snprintf(fn, sizeof fn, "%s_%d.el", edges_pfx, nsol);
        FILE *f = fopen(fn, "w"); if (!f) { perror(fn); exit(1); }
        fprintf(f, "%d\n", 2 * n);
        for (int g = 0; g < n; g++) for (int i = 0; i < K; i++) fprintf(f, "%d %d\n", g, n + M(S[i], g));
        fclose(f);
    }
}

static void eval_set(const int *S) {
    if (evals >= cap_limit) { capped = 1; return; }
    int c = cost(S);
    if (c < typebest) typebest = c;
    if (c < gbest) { gbest = c; snprintf(gbest_tag, sizeof gbest_tag, "%s", tag); }
    if (c == 0) { if (fullcheck(S)) { typesol++; report(S); } else oddfail++; }
}

/* ---------- orbits of alpha ---------- */
static int norb, *orbstart, *orbel, *orbid, nfix, *fixel, *isrep, plen;
static void build_orbits(int a) {
    int p = alp[a]; int *pm = aperm[a]; plen = p;
    free(orbstart); free(orbel); free(orbid); free(fixel); free(isrep);
    orbstart = malloc(sizeof(int) * (n + 1)); orbel = malloc(sizeof(int) * n); orbid = malloc(sizeof(int) * n);
    fixel = malloc(sizeof(int) * n); isrep = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) orbid[i] = -2;
    norb = 0; nfix = 0; int ne = 0;
    for (int i = 0; i < n; i++) if (orbid[i] == -2) {
        if (pm[i] == i) { orbid[i] = -1; fixel[nfix++] = i; continue; }
        orbstart[norb] = ne; int x = i, c = 0;
        do { orbid[x] = norb; orbel[ne++] = x; x = pm[x]; c++; } while (x != i);
        if (c != p) { fprintf(stderr, "orbit size %d != %d\n", c, p); exit(1); }
        norb++;
    }
    orbstart[norb] = ne;
    /* orbits of C(alpha) (the centralizer generators in the file) on alpha-orbits: union-find */
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
    printf("ALPHA %d: p %d fixed %d (incl. identity) orbits %d centralizer-reps %d\n", a, p, nfix, norb, nrep);
}

/* ---------- enumeration ---------- */
static int Sb[K];
static int want_f, want_m;
static void put_orbit(int o, int at) { for (int j = 0; j < plen; j++) Sb[at + j] = orbel[orbstart[o] + j]; }

static void rec_orb(int depth, int start, int at) {
    if (capped) return;
    if (depth == want_m) { eval_set(Sb); return; }
    if (depth == 0) {
        for (int o = 0; o < norb; o++) if (isrep[o]) { put_orbit(o, at); rec_orb(1, -1, at + plen); }
        return;
    }
    int first = orbid[Sb[want_f]];   /* the first orbit (rep) is never repeated */
    for (int o = (start < 0 ? 0 : start); o < norb; o++) if (o != first) {
        put_orbit(o, at); rec_orb(depth + 1, o + 1, at + plen);
    }
}
static void rec_fix(int need, int fs, int at) {
    if (capped) return;
    if (need == 0) { rec_orb(0, 0, at); return; }
    for (int i = fs; i < nfix; i++) if (fixel[i] != 0) { Sb[at] = fixel[i]; rec_fix(need - 1, i + 1, at + 1); }
}

static void run(void) {
    for (int a = 0; a < nal; a++) {
        int p = alp[a];
        if ((p != 3 && p != 5 && !(p == 2 && with2)) || (onlyp && p != onlyp)) continue;
        build_orbits(a);
        for (int m = 1; p * m <= K; m++) {   /* m = 0: S inside Fix(alpha), a proper subgroup, so XX != G: skipped */
            int f = K - p * m;
            if (f > nfix || m > norb) continue;
            want_f = f; want_m = m; typebest = 1LL << 40; typesol = 0; oddfail = 0;
            long long e0 = evals; clock_t c0 = clock(); cap_limit = evals + CAP; capped = 0;
            snprintf(tag, sizeof tag, "a%d_p%d_f%d_m%d", a, p, f, m);
            if (f >= 1) { Sb[0] = 0; rec_fix(f - 1, 0, 1); } else rec_fix(0, 0, 0);
            printf("TYPE alpha %d p %d f %d m %d best %lld sols %lld oddfail %d evals %lld secs %.2f%s\n", a, p, f, m,
                   typebest, typesol, oddfail, evals - e0, (double)(clock() - c0) / CLOCKS_PER_SEC, capped ? " CAPPED" : "");
            fflush(stdout);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haar6 FILE.ht\n"); return 2; }
    edges_pfx = getenv("EDGES");
    if (getenv("EDGESMAX")) edges_max = atoi(getenv("EDGESMAX"));
    if (getenv("CAP")) CAP = atoll(getenv("CAP"));
    if (getenv("ONLYP")) onlyp = atoi(getenv("ONLYP"));
    if (getenv("WITH2")) with2 = 1;
    load(argv[1]);
    printf("GROUP %s n %d ninv %d nalpha %d\n", argv[1], n, ninv, nal);
    if (getenv("SETS")) {   /* check mode: lines "tag s1 .. s6" (e.g. the SOL lines of an sdk run); prints cost and odd */
        FILE *g = fopen(getenv("SETS"), "r"); if (!g) { perror("SETS"); return 1; }
        char t[64]; int S[K];
        while (fscanf(g, "%63s", t) == 1) {
            for (int i = 0; i < K; i++) S[i] = rdint(g);
            int c = cost(S), od = (c == 0) ? fullcheck(S) : -1;
            printf("CHK %s cost %d odd %d\n", t, c, od);
            if (c == 0 && od == 1 && edges_pfx) { snprintf(tag, sizeof tag, "%s", t); report(S); }
        }
        fclose(g); return 0;
    }
    run();
    printf("DONE evals %lld sols %d best_cost %lld at %s\n", evals, nsol, gbest, gbest_tag);
    return 0;
}
