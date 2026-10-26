/* ga (hunt-d5 r4 w2): genetic algorithm over connection sets S (|S| = d, 0 in S) of Haar graphs H(G,S), diameter <= 5.
 * cost(S) = uncovered elements of (S^-1 S)^2 plus of (S S^-1)^2, exactly as haar5 eval.
 * Usage: ga TABLE d SECONDS SEED POP OUT [INIT]
 *   INIT: optional, one set per line (d indices); normalised by right multiplication (cost invariant) so 0 is in S.
 *   Population = INIT sets, rest uniform random.  Crossover (prob PX): union of two tournament parents, then greedy
 *   completion (add the element giving the least partial cost).  Mutation: best of K=8 random 1-swaps (0 kept).
 *   Replacement: child replaces the worst member if not worse and not a duplicate.  Stall (no population-best gain for
 *   STALL seconds): the worse half is re-randomised.
 *   OUT: "cost i0 ... i(d-1)" lines for every distinct set with cost <= 4 that was generated (cap 50000), sorted later.
 * Env: PX (0.7), PM (0.9), KC (8), STALL (40), REPORT (20 s). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 16
#define MAXSTORE 50000
static int N, d;
static uint16_t *MT;
static int *INV;
static uint32_t *stamp;
static uint32_t ep = 0;
static int TT[MAXD * MAXD];

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static inline int mul(int x, int y) { return MT[(size_t)x * N + y]; }

static void load(const char *fn) {
    FILE *f = fopen(fn, "rb"); if (!f) { perror(fn); exit(2); }
    if (fread(&N, 4, 1, f) != 1) exit(2);
    MT = malloc((size_t)N * N * 2);
    if (fread(MT, 2, (size_t)N * N, f) != (size_t)N * N) { fprintf(stderr, "short table\n"); exit(2); }
    fclose(f);
    INV = malloc(N * sizeof(int));
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++) if (mul(x, y) == 0) { INV[x] = y; break; }
    for (int x = 0; x < N; x++) if (mul(0, x) != x || mul(x, 0) != x) { fprintf(stderr, "identity is not 0\n"); exit(2); }
    stamp = calloc(N, 4);
}

static int side_cost(const int *S, int n, int sideB) {
    int nt = 0;
    ep++; if (ep == 0) { memset(stamp, 0, N * 4); ep = 1; }
    uint32_t e = ep;
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) {
        int t = sideB ? mul(S[i], INV[S[j]]) : mul(INV[S[i]], S[j]);
        if (stamp[t] != e) { stamp[t] = e; TT[nt++] = t; }
    }
    ep++; if (ep == 0) { memset(stamp, 0, N * 4); ep = 1; }
    e = ep; int cov = 0;
    for (int i = 0; i < nt; i++) {
        const uint16_t *row = MT + (size_t)TT[i] * N;
        for (int j = 0; j < nt; j++) { int g = row[TT[j]]; if (stamp[g] != e) { stamp[g] = e; cov++; } }
    }
    return N - cov;
}
static long long nevals = 0;
static int cost(const int *S, int n) { nevals++; return side_cost(S, n, 0) + side_cost(S, n, 1); }

static void sortset(int *S, int n) { for (int i = 1; i < n; i++) { int v = S[i], j = i - 1; while (j >= 0 && S[j] > v) { S[j + 1] = S[j]; j--; } S[j + 1] = v; } }
static int inset(const int *S, int n, int x) { for (int i = 0; i < n; i++) if (S[i] == x) return 1; return 0; }
static int sameset(const int *A, const int *B) { for (int i = 0; i < d; i++) if (A[i] != B[i]) return 0; return 1; }
static uint64_t shash(const int *S) { uint64_t h = 1469598103934665603ULL; for (int i = 0; i < d; i++) { h ^= (uint64_t)S[i] + 1; h *= 1099511628211ULL; } return h | 1; }

/* distinct-set hash set */
#define HSZ (1 << 22)
static uint64_t *hset;
static long long nset = 0;
static int hins(uint64_t h) {
    uint64_t i = h & (HSZ - 1);
    while (hset[i]) { if (hset[i] == h) return 0; i = (i + 1) & (HSZ - 1); }
    hset[i] = h; nset++; return 1;
}
static int store[MAXSTORE][MAXD], storec[MAXSTORE], nstore = 0;
static long long cnt_cost[64];
static double t_first[64];

static void record(const int *S, int c, double t0) {
    if (c > 4) return;
    if (!hins(shash(S))) return;
    if (c < 64) { cnt_cost[c]++; }
    if (c <= 4 && t_first[c] < 0) t_first[c] = now() - t0;
    if (nstore < MAXSTORE) { memcpy(store[nstore], S, sizeof(int) * d); storec[nstore] = c; nstore++; }
}

/* greedy completion: S = {0} + d-1 elements from U, each step the element minimising the partial cost */
static void build(const int *U, int nu, int *out) {
    int cur[MAXD]; int n = 1; cur[0] = 0;
    while (n < d) {
        int best = 1 << 30, cnt = 0, pick = -1;
        for (int u = 0; u < nu; u++) {
            int x = U[u];
            if (inset(cur, n, x)) continue;
            cur[n] = x; int c = cost(cur, n + 1);
            if (c < best) { best = c; cnt = 1; pick = x; }
            else if (c == best && rint_(++cnt) == 0) pick = x;
        }
        if (pick < 0) { do pick = 1 + rint_(N - 1); while (inset(cur, n, pick)); }
        cur[n++] = pick;
    }
    memcpy(out, cur, sizeof(int) * d); sortset(out, d);
}

static void randset(int *S) {
    S[0] = 0; int n = 1;
    while (n < d) { int x = 1 + rint_(N - 1); if (!inset(S, n, x)) S[n++] = x; }
    sortset(S, d);
}

static int KC = 8;
static void mutate(int *S) {
    int pos = 1 + rint_(d - 1), best = 1 << 30, bx = -1, cnt = 0;
    for (int k = 0; k < KC; k++) {
        int x; do x = 1 + rint_(N - 1); while (inset(S, d, x));
        int T2[MAXD]; memcpy(T2, S, sizeof(int) * d); T2[pos] = x;
        int c = cost(T2, d);
        if (c < best) { best = c; bx = x; cnt = 1; }
        else if (c == best && rint_(++cnt) == 0) bx = x;
    }
    S[pos] = bx; sortset(S, d);
}

static int ntour(const int *pc, int POP) {
    int a = rint_(POP), b = rint_(POP), c = rint_(POP);
    int r = a; if (pc[b] < pc[r]) r = b; if (pc[c] < pc[r]) r = c; return r;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: ga TABLE d SECONDS SEED POP OUT [INIT]\n"); return 2; }
    load(argv[1]); d = atoi(argv[2]);
    double secs = atof(argv[3]); uint64_t seed = strtoull(argv[4], 0, 10);
    int POP = atoi(argv[5]); const char *OUT = argv[6]; const char *INIT = argc > 7 ? argv[7] : NULL;
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    double PX = getenv("PX") ? atof(getenv("PX")) : 0.7, PM = getenv("PM") ? atof(getenv("PM")) : 0.9;
    KC = getenv("KC") ? atoi(getenv("KC")) : 8;
    double STALL = getenv("STALL") ? atof(getenv("STALL")) : 40, REPORT = getenv("REPORT") ? atof(getenv("REPORT")) : 20;
    if (d > MAXD || d < 2) { fprintf(stderr, "d out of range\n"); return 2; }
    hset = calloc(HSZ, sizeof(uint64_t));
    for (int c = 0; c < 64; c++) t_first[c] = -1;

    int (*pop)[MAXD] = malloc(sizeof(int[MAXD]) * POP); int *pc = malloc(sizeof(int) * POP);
    int np = 0, ninit = 0;
    if (INIT) {
        FILE *f = fopen(INIT, "r"); if (!f) { perror(INIT); return 2; }
        char line[1 << 14];
        while (fgets(line, sizeof line, f) && np < POP) {
            int S[MAXD], n = 0; char *p = line, *e;
            while (n < MAXD) { long v = strtol(p, &e, 10); if (e == p) break; S[n++] = (int)v; p = e; }
            if (n != d) continue;
            int t = INV[S[0]];
            for (int i = 0; i < d; i++) S[i] = mul(S[i], t);
            sortset(S, d);
            if (S[0] != 0) continue;
            int dup = 0; for (int q = 0; q < np && !dup; q++) dup = sameset(pop[q], S);
            if (!dup) { memcpy(pop[np], S, sizeof(int) * d); np++; ninit++; }
        }
        fclose(f);
    }
    while (np < POP) {
        int S[MAXD]; randset(S);
        int dup = 0; for (int q = 0; q < np && !dup; q++) dup = sameset(pop[q], S);
        if (!dup) { memcpy(pop[np], S, sizeof(int) * d); np++; }
    }
    int gbest = 1 << 30; double t0 = now();
    for (int i = 0; i < POP; i++) { pc[i] = cost(pop[i], d); record(pop[i], pc[i], t0); if (pc[i] < gbest) gbest = pc[i]; }
    int popbest = gbest; double lastimp = 0, lastrep = 0; long long gen = 0;
    int gbestS[MAXD];
    for (int i = 0; i < POP; i++) if (pc[i] == gbest) { memcpy(gbestS, pop[i], sizeof(int) * d); break; }
    fprintf(stderr, "init: N=%d d=%d POP=%d init_from_file=%d init popbest=%d\n", N, d, POP, ninit, popbest);

    while (now() - t0 < secs) {
        gen++;
        int i1 = ntour(pc, POP), i2 = ntour(pc, POP);
        int child[MAXD];
        if (rnd01() < PX) {
            int U[2 * MAXD], nu = 0;
            for (int k = 1; k < d; k++) U[nu++] = pop[i1][k];
            for (int k = 1; k < d; k++) if (!inset(U, nu, pop[i2][k])) U[nu++] = pop[i2][k];
            build(U, nu, child);
        } else memcpy(child, pop[i1], sizeof(int) * d);
        if (rnd01() < PM) { mutate(child); if (rnd01() < 0.3) mutate(child); }
        int c = cost(child, d);
        record(child, c, t0);
        if (c < gbest) { gbest = c; memcpy(gbestS, child, sizeof(int) * d); }
        int dup = 0, worst = 0;
        for (int q = 0; q < POP; q++) { if (sameset(pop[q], child)) { dup = 1; break; } if (pc[q] > pc[worst]) worst = q; }
        if (!dup && c <= pc[worst]) {
            memcpy(pop[worst], child, sizeof(int) * d); pc[worst] = c;
            if (c < popbest) { popbest = c; lastimp = now() - t0; }
        }
        if (now() - t0 - lastimp > STALL) {  /* re-randomise the worse half, keep the best */
            int ord[1024]; for (int q = 0; q < POP; q++) ord[q] = q;
            for (int a = 1; a < POP; a++) { int v = ord[a], b = a - 1; while (b >= 0 && pc[ord[b]] > pc[v]) { ord[b + 1] = ord[b]; b--; } ord[b + 1] = v; }
            for (int a = POP / 2; a < POP; a++) {
                int S[MAXD]; randset(S); memcpy(pop[ord[a]], S, sizeof(int) * d); pc[ord[a]] = cost(S, d); record(S, pc[ord[a]], t0);
            }
            popbest = 1 << 30; for (int q = 0; q < POP; q++) if (pc[q] < popbest) popbest = pc[q];
            lastimp = now() - t0;
        }
        if (now() - t0 - lastrep > REPORT) {
            lastrep = now() - t0;
            int med = 0; { int tmp[1024]; for (int q = 0; q < POP; q++) tmp[q] = pc[q];
              for (int a = 1; a < POP; a++) { int v = tmp[a], b = a - 1; while (b >= 0 && tmp[b] > v) { tmp[b + 1] = tmp[b]; b--; } tmp[b + 1] = v; }
              med = tmp[POP / 2]; }
            fprintf(stderr, "T=%.0f gen=%lld evals=%lld popbest=%d popmed=%d gbest=%d distinct<=4: %lld (<=2: %lld)\n",
                    now() - t0, gen, nevals, popbest, med, gbest, nset, cnt_cost[2] + cnt_cost[1] + cnt_cost[0]);
        }
    }
    double el = now() - t0;
    printf("RESULT ga table=%s N=%d d=%d POP=%d secs=%.1f gens=%lld evals=%lld best=%d distinct_le4=%lld le2=%lld first4=%.1f first3=%.1f first2=%.1f\n",
           argv[1], N, d, POP, el, gen, nevals, gbest, nset, cnt_cost[2] + cnt_cost[1] + cnt_cost[0],
           t_first[4], t_first[3], t_first[2]);
    printf("best S = 0"); for (int k = 1; k < d; k++) printf(" %d", gbestS[k]); printf("\n");
    FILE *f = fopen(OUT, "w");
    if (f) {
        for (int q = 0; q < nstore; q++) { fprintf(f, "%d", storec[q]); for (int k = 0; k < d; k++) fprintf(f, " %d", store[q][k]); fprintf(f, "\n"); }
        fclose(f);
    }
    return 0;
}
