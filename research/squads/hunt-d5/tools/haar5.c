/* haar5: Haar graphs of diameter <= 5 over any group given by a multiplication table (hunt-d5 job).

   H(G,S): vertices (g,A), (g,B); edges (g,A) ~ (s g, B), s in S.  Right multiplication is transitive on each side, so
   diameter <= 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G (research/d5/REPORT.md, Lemma).
   cost(S) = |G \ (S^-1 S)^2| + |G \ (S S^-1)^2|.

   Usage:
     haar5 anneal TABLE.bin d seconds seed [OUT]      simulated annealing (best-of-K replacement moves)
     haar5 exh TABLE.bin d [LIMIT]                    exhaustive over S = {e} + (d-1)-subsets (small d, N); prints
                                                      the minimum cost and every S with cost <= LIMIT (default 0)
     haar5 eval TABLE.bin d < sets                    one S per line (d element indices), prints the cost
   Env:
     AUT=file.autK  ALINE=i  ORBIT="k m f"   S = {e} + (f-1) alpha-fixed elements + m alpha-orbits of size k
                    (f = 0: no identity, S = m free orbits); alpha = line i (default 0) of a gapgroup.py .aut file.
     K (candidates per move, default 16), T0 (start temperature, default 2.0), COOL (seconds per halving, 10),
     REHEAT (seconds without improvement before a restart from the best, 40), RESTART=1 (restart from random),
     THREADS (exh only, OpenMP).
   TABLE.bin: int32 N, then N*N uint16 row-major (row g: g*h), identity = index 0 (gapgroup.py, b48 groups.py). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#ifdef _OPENMP
#include <omp.h>
#endif

static int N, d;
static uint16_t *MT;
static int *INV;
static inline int mul(int x, int y) { return MT[(size_t)x * N + y]; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(2); }
    if (fread(&N, 4, 1, f) != 1) exit(2);
    MT = malloc((size_t)N * N * 2);
    if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short table\n"); exit(2); }
    fclose(f);
    INV = malloc(N * sizeof(int));
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul(x, y) == 0) { INV[x] = y; break; }
    for (int x = 0; x < N; x++) if (mul(0, x) != x || mul(x, 0) != x) { fprintf(stderr, "identity is not 0\n"); exit(2); }
}

/* per-thread scratch */
typedef struct { uint32_t *stamp; uint32_t ep; int *T; } scr_t;
static scr_t mkscr(void) { scr_t s; s.stamp = calloc(N, 4); s.ep = 0; s.T = malloc(sizeof(int) * 128 * 128); return s; }

/* number of elements of G not in (X)^2, X = {a_i^-1 a_j} (side A) or {a_i a_j^-1} (side B) */
static int side_cost(const int *S, int n, int sideB, scr_t *sc, int limit) {
    int nt = 0;
    sc->ep++; if (sc->ep == 0) { memset(sc->stamp, 0, N * 4); sc->ep = 1; }
    uint32_t ep = sc->ep;
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) {
        int t = sideB ? mul(S[i], INV[S[j]]) : mul(INV[S[i]], S[j]);
        if (sc->stamp[t] != ep) { sc->stamp[t] = ep; sc->T[nt++] = t; }
    }
    sc->ep++; if (sc->ep == 0) { memset(sc->stamp, 0, N * 4); sc->ep = 1; }
    ep = sc->ep; int cov = 0;
    for (int i = 0; i < nt; i++) {
        const uint16_t *row = MT + (size_t)sc->T[i] * N;
        for (int j = 0; j < nt; j++) { int g = row[sc->T[j]]; if (sc->stamp[g] != ep) { sc->stamp[g] = ep; cov++; } }
        if (N - cov <= 0) break;
    }
    (void)limit;
    return N - cov;
}
static int cost(const int *S, int n, scr_t *sc) { return side_cost(S, n, 0, sc, 0) + side_cost(S, n, 1, sc, 0); }

/* ---------- orbit structure ---------- */
static int *ALPHA, kord = 1, morb = 0, ffix = 0; /* S = (ffix>0: e + ffix-1 fixed) + morb orbits */
static int *fixl, nfixl, *orbl, norbl; /* candidate fixed elements (not e), orbit representatives */
static void load_aut(const char *fn, int line) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    ALPHA = malloc(N * sizeof(int));
    for (int l = 0; l <= line; l++) {
        int nf; if (fscanf(f, "%d", &nf) != 1) { fprintf(stderr, "no line %d in %s\n", line, fn); exit(2); }
        for (int j = 0; j < N; j++) if (fscanf(f, "%d", &ALPHA[j]) != 1) exit(2);
    }
    fclose(f);
}
static void setup_orbits(void) {
    fixl = malloc(N * sizeof(int)); orbl = malloc(N * sizeof(int)); nfixl = norbl = 0;
    char *seen = calloc(N, 1);
    for (int x = 1; x < N; x++) {
        if (seen[x]) continue;
        int len = 0, y = x; do { seen[y] = 1; y = ALPHA[y]; len++; } while (y != x);
        if (len == 1) fixl[nfixl++] = x; else if (len == kord) orbl[norbl++] = x;
    }
    free(seen);
}
/* expand units -> S. units[0..nf-1] fixed (indices into G), units[nf..] orbit reps */
static int expand(const int *units, int *S) {
    int n = 0;
    if (ffix > 0) S[n++] = 0;
    int nf = ffix > 0 ? ffix - 1 : 0;
    for (int i = 0; i < nf; i++) S[n++] = units[i];
    for (int i = 0; i < morb; i++) { int y = units[nf + i]; for (int r = 0; r < kord; r++) { S[n++] = y; y = ALPHA[y]; } }
    return n;
}

static int nunits(void) { return ALPHA ? (ffix > 0 ? ffix - 1 : 0) + morb : d - 1; }
static int rand_unit(int slot) {
    if (!ALPHA) return 1 + rnd() % (N - 1);
    int nf = ffix > 0 ? ffix - 1 : 0;
    if (slot < nf) return fixl[rnd() % nfixl];
    return orbl[rnd() % norbl];
}
static int valid_units(const int *u, int nu) {
    /* distinct elements in S */
    int S[512]; int n = ALPHA ? expand(u, S) : 0;
    if (!ALPHA) { S[n++] = 0; for (int i = 0; i < nu; i++) S[n++] = u[i]; }
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (S[i] == S[j]) return 0;
    return 1;
}
static int units_cost(const int *u, int nu, scr_t *sc) {
    int S[512], n;
    if (ALPHA) n = expand(u, S); else { n = 0; S[n++] = 0; for (int i = 0; i < nu; i++) S[n++] = u[i]; }
    return cost(S, n, sc);
}
static void print_S(FILE *f, const int *u, int nu) {
    int S[512], n;
    if (ALPHA) n = expand(u, S); else { n = 0; S[n++] = 0; for (int i = 0; i < nu; i++) S[n++] = u[i]; }
    for (int i = 0; i < n; i++) fprintf(f, "%d%c", S[i], i + 1 < n ? ' ' : '\n');
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: see source\n"); return 2; }
    const char *mode = argv[1];
    load(argv[2]); d = atoi(argv[3]);
    const char *aut = getenv("AUT");
    if (aut) {
        load_aut(aut, getenv("ALINE") ? atoi(getenv("ALINE")) : 0);
        const char *o = getenv("ORBIT"); if (!o || sscanf(o, "%d %d %d", &kord, &morb, &ffix) != 3) { fprintf(stderr, "ORBIT=\"k m f\" needed\n"); return 2; }
        if (kord * morb + ffix != d) { fprintf(stderr, "k*m+f != d\n"); return 2; }
        setup_orbits();
        fprintf(stderr, "alpha: %d fixed (excluding e), %d orbits of size %d\n", nfixl, norbl, kord);
    }
    scr_t sc = mkscr();
    if (!strcmp(mode, "eval")) {
        int S[512]; char line[1 << 16];
        while (fgets(line, sizeof line, stdin)) {
            int n = 0; char *p = line, *e;
            while (n < 512) { long v = strtol(p, &e, 10); if (e == p) break; S[n++] = (int)v; p = e; }
            if (n == 0) continue;
            printf("%d\n", cost(S, n, &sc));
        }
        return 0;
    }
    if (!strcmp(mode, "exh")) {
        int limit = argc > 4 ? atoi(argv[4]) : 0;
        if (ALPHA) { fprintf(stderr, "exh with orbits: not implemented\n"); return 2; }
        if (d != 5 && d != 4 && d != 6) { fprintf(stderr, "exh: d in 4..6\n"); return 2; }
        int best = 1 << 30; long long cnt = 0;
#pragma omp parallel
        {
            scr_t s2 = mkscr(); int lbest = 1 << 30; long long lcnt = 0;
            int S[8]; S[0] = 0;
#pragma omp for schedule(dynamic, 1)
            for (int a = 1; a < N; a++) {
                S[1] = a;
                for (int b = a + 1; b < N; b++) { S[2] = b;
                    for (int c = b + 1; c < N; c++) { S[3] = c;
                        if (d == 4) { int cc = cost(S, 4, &s2); lcnt++; if (cc < lbest) lbest = cc;
                            if (cc <= limit) {
#pragma omp critical
                                { printf("cost %d S %d %d %d %d\n", cc, S[0], S[1], S[2], S[3]); fflush(stdout); } }
                            continue; }
                        for (int e = c + 1; e < N; e++) { S[4] = e;
                            if (d == 5) { int c1 = side_cost(S, 5, 0, &s2, 0); int cc = c1;
                                if (c1 <= limit || c1 < lbest) cc += side_cost(S, 5, 1, &s2, 0); else cc += 0;
                                lcnt++;
                                if (cc < lbest && (c1 <= limit || c1 < lbest)) lbest = cc;
                                if (cc <= limit) {
#pragma omp critical
                                    { printf("cost %d S %d %d %d %d %d\n", cc, S[0], S[1], S[2], S[3], S[4]); fflush(stdout); } }
                                continue; }
                            for (int g = e + 1; g < N; g++) { S[5] = g; int cc = cost(S, 6, &s2); lcnt++;
                                if (cc < lbest) lbest = cc;
                                if (cc <= limit) {
#pragma omp critical
                                    { printf("cost %d S %d %d %d %d %d %d\n", cc, S[0], S[1], S[2], S[3], S[4], S[5]); fflush(stdout); } }
                            }
                        }
                    }
                }
            }
#pragma omp critical
            { if (lbest < best) best = lbest; cnt += lcnt; }
        }
        printf("RESULT exh N=%d d=%d sets=%lld min=%d\n", N, d, cnt, best);
        return 0;
    }
    /* anneal */
    double secs = atof(argv[4]); uint64_t seed = argc > 5 ? strtoull(argv[5], 0, 10) : 1;
    const char *out = argc > 6 ? argv[6] : NULL;
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    int K = getenv("K") ? atoi(getenv("K")) : 16;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, COOL = getenv("COOL") ? atof(getenv("COOL")) : 10;
    double REHEAT = getenv("REHEAT") ? atof(getenv("REHEAT")) : 40; int RESTART = getenv("RESTART") ? atoi(getenv("RESTART")) : 0;
    int nu = nunits(); int u[512], bu[512], cand[512];
    do { for (int i = 0; i < nu; i++) u[i] = rand_unit(i); } while (!valid_units(u, nu));
    int cur = units_cost(u, nu, &sc), best = cur; memcpy(bu, u, sizeof(int) * nu);
    double t0 = now(), tl = t0, tstart = t0; long long ev = 1, steps = 0;
    int div = ALPHA ? kord : 1;
    while (best > 0 && now() - tstart < secs) {
        double T = T0 * pow(0.5, (now() - t0) / COOL);
        int slot = rnd() % nu, bc = 1 << 30, bval = -1;
        for (int k = 0; k < K; k++) {
            memcpy(cand, u, sizeof(int) * nu); cand[slot] = rand_unit(slot);
            if (!valid_units(cand, nu)) continue;
            int c = units_cost(cand, nu, &sc); ev++;
            if (c < bc) { bc = c; bval = cand[slot]; }
        }
        steps++;
        if (bval < 0) continue;
        double dl = (double)(bc - cur) / div;
        if (dl <= 0 || rnd01() < exp(-dl / fmax(T, 1e-9))) { u[slot] = bval; cur = bc; }
        if (cur < best) { best = cur; memcpy(bu, u, sizeof(int) * nu); tl = now();
            fprintf(stderr, "t=%.1f steps=%lld evals=%lld best=%d\n", now() - tstart, steps, ev, best); }
        if (now() - tl > REHEAT) {
            if (RESTART) { do { for (int i = 0; i < nu; i++) u[i] = rand_unit(i); } while (!valid_units(u, nu)); }
            else memcpy(u, bu, sizeof(int) * nu);
            cur = units_cost(u, nu, &sc); t0 = now(); tl = now();
        }
    }
    printf("RESULT haar5 table=%s N=%d d=%d best=%d evals=%lld time=%.1f S= ", argv[2], N, d, best, ev, now() - tstart);
    print_S(stdout, bu, nu);
    if (out && best == 0) { FILE *f = fopen(out, "w"); fprintf(f, "# haar5 table %s N %d d %d; S (element indices), edges (g,A)~(s*g,B)\n", argv[2], N, d); print_S(f, bu, nu); fclose(f); }
    return best == 0 ? 0 : 1;
}
