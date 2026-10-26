/* cos5: Haar graphs H(G,S) of diameter <= 5 where S is a disjoint union of left cosets x*K of cyclic subgroups K
   (card w1, round 2). Block sizes given as a list, e.g. "1 3 3" (S = {y} + x1 K1 + x2 K2, |K_b| = block size).
   Cost as in haar5: uncovered elements of (S^-1 S)^2 plus of (S S^-1)^2 (cost is invariant under S -> aS and S -> Sh).

   Usage:
     cos5 anneal TABLE.bin "k1 k2 ..." SECONDS SEED [OUT]   simulated annealing over (x_b, K_b) per block
     cos5 exh TABLE.bin "k1 k2 ..." [LIMIT]                 exhaustive over the family (first block of size 1 fixed to e)
   Env: K (candidates per move, 16), T0 (2.0), COOL (10 s), REHEAT (40 s), RESTART (0).
   Table format: as haar5 (int32 N, N*N uint16, identity 0). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

static int N;
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

typedef struct { uint32_t *stamp; uint32_t ep; int *T; } scr_t;
static scr_t EXSC;
static scr_t mkscr(void) { scr_t s; s.stamp = calloc(N, 4); s.ep = 0; s.T = malloc(sizeof(int) * N * N + 16); return s; }

static int side_cost(const int *S, int n, int sideB, scr_t *sc) {
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
    return N - cov;
}
static int cost(const int *S, int n, scr_t *sc) { return side_cost(S, n, 0, sc) + side_cost(S, n, 1, sc); }

/* ---------- subgroups: cyclic subgroups of each order k (list per block size) ---------- */
static int *ORD;            /* element orders */
static int *subs[64]; static int nsubs[64];   /* subs[k][j*k + i] = i-th element of subgroup j of order k */
static void build_subs(int k) {
    int cap = 0; int *L = NULL; int ns = 0;
    if (k == 1) { L = malloc(sizeof(int)); L[0] = 0; ns = 1; subs[k] = L; nsubs[k] = ns; return; }
    for (int g = 1; g < N; g++) {
        if (ORD[g] != k) continue;
        int el[64]; el[0] = 0; int x = g;
        for (int i = 1; i < k; i++) { el[i] = x; x = mul(x, g); }
        /* dedupe: same subgroup iff it contains g's min generator; check against existing by membership of min element */
        int mn = N; for (int i = 0; i < k; i++) if (el[i] < mn) mn = el[i];
        int dup = 0;
        for (int j = 0; j < ns && !dup; j++) {
            int hit = 0; for (int i = 0; i < k; i++) if (L[j * k + i] == g) { hit = 1; break; }
            if (hit) dup = 1;
        }
        if (dup) continue;
        if (ns == cap) { cap = cap ? 2 * cap : 64; L = realloc(L, sizeof(int) * (size_t)cap * k); }
        for (int i = 0; i < k; i++) L[ns * k + i] = el[i];
        ns++; (void)mn;
    }
    subs[k] = L; nsubs[k] = ns;
}
static void setup_orders(void) {
    ORD = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) { int x = g, o = 1; while (x != 0) { x = mul(x, g); o++; } ORD[g] = o; }
}

/* ---------- block structure ---------- */
static int nb, bsz[64];
static int blk_sub[64], blk_x[64];   /* subgroup index j in subs[k], coset representative x */

static int expand(const int *sub, const int *xs, int *S) {
    int n = 0;
    for (int b = 0; b < nb; b++) {
        int k = bsz[b], j = sub[b];
        for (int i = 0; i < k; i++) S[n++] = mul(xs[b], subs[k][j * k + i]);
    }
    return n;
}
static int distinct(const int *S, int n) {
    for (int i = 0; i < n; i++) for (int j = i + 1; j < n; j++) if (S[i] == S[j]) return 0;
    return 1;
}
static int state_cost(const int *sub, const int *xs, scr_t *sc, int *nS, int *S) {
    int n = expand(sub, xs, S); *nS = n;
    if (!distinct(S, n)) return -1;
    return cost(S, n, sc);
}
static void print_S(FILE *f, const int *sub, const int *xs) {
    int S[512]; int n = expand(sub, xs, S);
    for (int i = 0; i < n; i++) fprintf(f, "%d%c", S[i], i + 1 < n ? ' ' : '\n');
}
static int parse_blocks(const char *s) {
    nb = 0; const char *p = s; char *e;
    while (nb < 64) { long v = strtol(p, &e, 10); if (e == p) break; bsz[nb++] = (int)v; p = e; }
    int tot = 0; for (int b = 0; b < nb; b++) { if (bsz[b] < 1 || bsz[b] > 63) return 0; tot += bsz[b]; }
    return nb > 0 && tot > 0;
}
static int rand_sub(int b) { int k = bsz[b]; return (int)(rnd() % nsubs[k]); }
static int rand_x(void) { return (int)(rnd() % N); }

/* ---------- exhaustive (recursive over blocks; equal-size consecutive blocks non-decreasing) ---------- */
static long long ex_sets = 0; static int ex_min = 1 << 30, ex_limit = 0;
static int *cand_sub[64], *cand_x[64], ncand[64];   /* per block size k: candidate (subgroup j, canonical coset x) */
static void build_cands(int k) {
    int cap = 0; int *cs = NULL, *cx = NULL; int nc = 0;
    char *seen = calloc((size_t)N, 1);
    for (int j = 0; j < nsubs[k]; j++) {
        memset(seen, 0, N);
        for (int x = 0; x < N; x++) {
            if (seen[x]) continue;
            int ok = 1;
            for (int i = 0; i < k; i++) { int y = mul(x, subs[k][j * k + i]); seen[y] = 1; if (y < x) ok = 0; }
            if (!ok) continue;
            if (nc == cap) { cap = cap ? 2 * cap : 1024; cs = realloc(cs, sizeof(int) * cap); cx = realloc(cx, sizeof(int) * cap); }
            cs[nc] = j; cx[nc] = x; nc++;
        }
    }
    free(seen);
    cand_sub[k] = cs; cand_x[k] = cx; ncand[k] = nc;
}
static int ex_sub[64], ex_x[64], ex_idx[64];
static void ex_rec(int b) {
    if (b == nb) {
        int S[512], n = expand(ex_sub, ex_x, S); ex_sets++;
        if (!distinct(S, n)) return;
        int c = cost(S, n, &EXSC);
        if (c < ex_min) ex_min = c;
        if (c <= ex_limit) { printf("cost %d S", c); for (int i = 0; i < n; i++) printf(" %d", S[i]); printf("\n"); fflush(stdout); }
        return;
    }
    int k = bsz[b];
    if (b == 0 && k == 1) { ex_sub[0] = 0; ex_x[0] = 0; ex_idx[0] = -1; ex_rec(1); return; }   /* normalized: S contains e */
    int start = (b > 0 && bsz[b - 1] == k) ? ex_idx[b - 1] : 0;
    for (int c = start; c < ncand[k]; c++) {
        ex_idx[b] = c; ex_sub[b] = cand_sub[k][c]; ex_x[b] = cand_x[k][c];
        ex_rec(b + 1);
    }
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: see source\n"); return 2; }
    const char *mode = argv[1];
    load(argv[2]);
    if (!parse_blocks(argv[3])) { fprintf(stderr, "bad block list\n"); return 2; }
    setup_orders();
    for (int b = 0; b < nb; b++) { int k = bsz[b]; if (!subs[k]) build_subs(k); }
    for (int b = 0; b < nb; b++) {
        if (nsubs[bsz[b]] == 0) { fprintf(stderr, "no cyclic subgroup of order %d\n", bsz[b]); return 3; }
    }
    scr_t sc = mkscr();
    if (!strcmp(mode, "exh")) {
        ex_limit = argc > 4 ? atoi(argv[4]) : 0;
        EXSC = mkscr();
        for (int b = 0; b < nb; b++) { int k = bsz[b]; if (!cand_sub[k]) build_cands(k); }
        for (int b = 0; b < nb; b++) fprintf(stderr, " block %d: %d candidates\n", bsz[b], ncand[bsz[b]]);
        ex_rec(0);
        printf("RESULT cos5 exh N=%d blocks=%s sets=%lld min=%d\n", N, argv[3], ex_sets, ex_min);
        return 0;
    }
    /* anneal */
    double secs = atof(argv[4]); uint64_t seed = argc > 5 ? strtoull(argv[5], 0, 10) : 1;
    const char *out = argc > 6 ? argv[6] : NULL;
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    int K = getenv("K") ? atoi(getenv("K")) : 16;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, COOL = getenv("COOL") ? atof(getenv("COOL")) : 10;
    double REHEAT = getenv("REHEAT") ? atof(getenv("REHEAT")) : 40; int RESTART = getenv("RESTART") ? atoi(getenv("RESTART")) : 0;
    int sub[64], xs[64], bsub[64], bxs[64], csub[64], cxs[64];
    int S[512], n, c;
    /* random valid start */
    do { for (int b = 0; b < nb; b++) { sub[b] = rand_sub(b); xs[b] = rand_x(); } c = state_cost(sub, xs, &sc, &n, S); } while (c < 0);
    int cur = c, best = c; memcpy(bsub, sub, sizeof sub); memcpy(bxs, xs, sizeof xs);
    double t0 = now(), tl = t0, tstart = t0; long long ev = 1, steps = 0;
    while (best > 0 && now() - tstart < secs) {
        double T = T0 * pow(0.5, (now() - t0) / COOL);
        int b = rnd() % nb, bc = 1 << 30, bsub_v = 0, bx_v = 0, bk = 0;
        for (int q = 0; q < K; q++) {
            memcpy(csub, sub, sizeof sub); memcpy(cxs, xs, sizeof xs);
            int kind = (nsubs[bsz[b]] > 1 && (rnd() % 4 == 0)) ? 1 : 0;   /* 25%: change subgroup, else change coset */
            if (kind) csub[b] = rand_sub(b); else cxs[b] = rand_x();
            int cc = state_cost(csub, cxs, &sc, &n, S); ev++;
            if (cc < 0) continue;
            if (cc < bc) { bc = cc; bsub_v = csub[b]; bx_v = cxs[b]; bk = kind; }
        }
        steps++;
        if (bc == (1 << 30)) continue;
        double dl = (double)(bc - cur);
        if (dl <= 0 || rnd01() < exp(-dl / fmax(T, 1e-9))) {
            if (bk) sub[b] = bsub_v; else xs[b] = bx_v;
            cur = bc;
        }
        if (cur < best) { best = cur; memcpy(bsub, sub, sizeof sub); memcpy(bxs, xs, sizeof xs); tl = now();
            fprintf(stderr, "t=%.1f steps=%lld evals=%lld best=%d\n", now() - tstart, steps, ev, best); }
        if (now() - tl > REHEAT) {
            if (RESTART) { do { for (int i = 0; i < nb; i++) { sub[i] = rand_sub(i); xs[i] = rand_x(); } c = state_cost(sub, xs, &sc, &n, S); } while (c < 0); }
            else { memcpy(sub, bsub, sizeof sub); memcpy(xs, bxs, sizeof xs); }
            cur = state_cost(sub, xs, &sc, &n, S); if (cur < 0) cur = 1 << 20; t0 = now(); tl = now();
        }
    }
    printf("RESULT cos5 table=%s N=%d blocks=%s best=%d evals=%lld time=%.1f S= ", argv[2], N, argv[3], best, ev, now() - tstart);
    print_S(stdout, bsub, bxs);
    if (out && best == 0) {
        FILE *f = fopen(out, "w"); fprintf(f, "# cos5 table %s N %d blocks %s; S (element indices)\n", argv[2], N, argv[3]);
        print_S(f, bsub, bxs); fclose(f);
    }
    return best == 0 ? 0 : 1;
}
