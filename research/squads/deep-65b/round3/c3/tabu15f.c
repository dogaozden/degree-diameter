/* c6 (deep-65b round 2): tabu15f = shared/tabu15.c with the SAME search rule and the same RNG use,
 * faster evaluation of the six conditions C1..C6 of the [[1,5],[5,1]] split family.
 *   - E = M u F with M the moved 5-set, F the fixed 5-set. EE^-1 = QM u QF u X u X^-1 and E^-1E = PM u PF u Y u Y^-1
 *     with X = M F^-1, Y = M^-1 F (exact set identities), so only 50 products are needed for these.
 *   - everything that depends on F only (QF, PF, QF^2, PF^2, QF F, the lists) is cached once per step; the moved
 *     side's products are computed once per candidate.
 *   - the cheap conditions (C2, C3, C5, C6) are done first; a candidate is abandoned as soon as the partial sum of
 *     computed miss counts exceeds thr, where thr = bv (non-tabu) or min(bv, best_all-1) (tabu). Such a candidate can
 *     never be chosen or tie, so the trajectory (move choice, tie RNG calls, restarts) is identical to tabu15.
 * usage: tabu15f TAB SEED SECS [EDGES_OUT]     (prints one RES line, same format as tabu15)
 *        tabu15f TAB cost e1x5 e2x5            (six miss counts, labels as split15)
 *        tabu15f TAB check NSTATES             (self-test: fast vs reference cost on random states and moves)
 * gcc -O3 -march=native -o tabu15f tabu15f.c
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 256
#define INF 1000000
#define TENURE 10
#ifndef RESTART
#define RESTART 1500
#endif

typedef struct { uint64_t w[4]; } bs;
static int m, NW;
static uint8_t T[MAXM][MAXM];
static int inv_[MAXM];
static bs FULL;

static inline void bset(bs *b, int x) { b->w[x >> 6] |= 1ULL << (x & 63); }
static inline void bzero4(bs *b) { b->w[0] = b->w[1] = b->w[2] = b->w[3] = 0; }
static inline void bor4(bs *a, const bs *b) { a->w[0] |= b->w[0]; a->w[1] |= b->w[1]; a->w[2] |= b->w[2]; a->w[3] |= b->w[3]; }
static inline int bmiss(const bs *b) { int c = 0; for (int i = 0; i < NW; i++) c += __builtin_popcountll(FULL.w[i] & ~b->w[i]); return c; }
static inline int blist(const bs *b, int *out) {
    int n = 0;
    for (int i = 0; i < NW; i++) { uint64_t w = b->w[i]; while (w) { out[n++] = (i << 6) | __builtin_ctzll(w); w &= w - 1; } }
    return n;
}
static inline void prod_into(bs *c, const int *A, int na, const int *B, int nb) {
    for (int i = 0; i < na; i++) { const uint8_t *row = T[A[i]]; for (int j = 0; j < nb; j++) bset(c, row[B[j]]); }
}
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void readtab(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f || fscanf(f, "%d", &m) != 1 || m > MAXM) { fprintf(stderr, "bad table %s\n", fn); exit(2); }
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) { int x; if (fscanf(f, "%d", &x) != 1) exit(2); T[i][j] = (uint8_t)x; }
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (T[i][j] == 0) inv_[i] = j;
    NW = (m + 63) / 64;
    memset(&FULL, 0, sizeof FULL);
    for (int x = 0; x < m; x++) bset(&FULL, x);
}

/* reference: the six miss counts exactly as tabu15.c computes them (used only by the self-test and the final print) */
static int cost_ref(const int *E1, const int *E2, int *brk) {
    int I1[5], I2[5], E[10], EI[10];
    for (int i = 0; i < 5; i++) {
        I1[i] = inv_[E1[i]]; I2[i] = inv_[E2[i]];
        E[i] = E1[i]; E[5 + i] = E2[i]; EI[i] = I1[i]; EI[5 + i] = I2[i];
    }
    bs bQ1, bQ2, bP1, bP2, bEEi, bEiE, bE;
    bzero4(&bQ1); bzero4(&bQ2); bzero4(&bP1); bzero4(&bP2); bzero4(&bEEi); bzero4(&bEiE); bzero4(&bE);
    prod_into(&bQ1, E1, 5, I1, 5); prod_into(&bQ2, E2, 5, I2, 5);
    prod_into(&bP1, I1, 5, E1, 5); prod_into(&bP2, I2, 5, E2, 5);
    prod_into(&bEEi, E, 10, EI, 10); prod_into(&bEiE, EI, 10, E, 10);
    for (int i = 0; i < 10; i++) bset(&bE, E[i]);
    int Q1[64], Q2[64], P1[64], P2[64], n1, n2, n3, n4;
    n1 = blist(&bQ1, Q1); n2 = blist(&bQ2, Q2); n3 = blist(&bP1, P1); n4 = blist(&bP2, P2);
    bs c;
    c = bEEi; prod_into(&c, Q1, n1, Q1, n1); brk[0] = bmiss(&c);
    c = bEEi; prod_into(&c, Q2, n2, Q2, n2); brk[1] = bmiss(&c);
    c = bEiE; prod_into(&c, P2, n4, P2, n4); brk[2] = bmiss(&c);
    c = bEiE; prod_into(&c, P1, n3, P1, n3); brk[3] = bmiss(&c);
    c = bE; prod_into(&c, Q1, n1, E1, 5); prod_into(&c, Q1, n1, E2, 5); prod_into(&c, E1, 5, P2, n4); prod_into(&c, Q2, n2, E2, 5);
    brk[4] = bmiss(&c);
    c = bE; prod_into(&c, Q1, n1, E1, 5); prod_into(&c, E2, 5, P1, n3); prod_into(&c, Q2, n2, E1, 5); prod_into(&c, Q2, n2, E2, 5);
    brk[5] = bmiss(&c);
    return brk[0] + brk[1] + brk[2] + brk[3] + brk[4] + brk[5];
}

/* cache for the fixed side F (5 elements): built once per search step */
typedef struct {
    int qf[64], nqf, pf[64], npf;
    bs QFb, PFb, QFsq, PFsq, QFF, Fb;
} fixc;

static void build_fix(const int *F, fixc *fc) {
    int IF[5];
    for (int i = 0; i < 5; i++) IF[i] = inv_[F[i]];
    bzero4(&fc->QFb); prod_into(&fc->QFb, F, 5, IF, 5);          /* F F^-1 */
    bzero4(&fc->PFb); prod_into(&fc->PFb, IF, 5, F, 5);          /* F^-1 F */
    fc->nqf = blist(&fc->QFb, fc->qf); fc->npf = blist(&fc->PFb, fc->pf);
    bzero4(&fc->QFsq); prod_into(&fc->QFsq, fc->qf, fc->nqf, fc->qf, fc->nqf);
    bzero4(&fc->PFsq); prod_into(&fc->PFsq, fc->pf, fc->npf, fc->pf, fc->npf);
    bzero4(&fc->QFF); prod_into(&fc->QFF, fc->qf, fc->nqf, F, 5);  /* F F^-1 F */
    bzero4(&fc->Fb); for (int i = 0; i < 5; i++) bset(&fc->Fb, F[i]);
}

/* moved side M against fixed side F (cache fc). g[0..5] = miss counts of C1..C6 with M playing E1 (for M = E2
 * the labels are the swapped ones: g0<->C2, g2<->C4, g4<->C6; the total is the same).
 * Returns the sum of the miss counts; if the partial sum exceeds thr it returns early with a value > thr. */
static int eval_side(const int *M, const int *F, const fixc *fc, int thr, int *g) {
    int IM[5], IF[5];
    for (int i = 0; i < 5; i++) { IM[i] = inv_[M[i]]; IF[i] = inv_[F[i]]; }
    bs QM, PM, X, Y, Mb, Eb, c;
    bzero4(&QM); prod_into(&QM, M, 5, IM, 5);     /* M M^-1 */
    bzero4(&PM); prod_into(&PM, IM, 5, M, 5);     /* M^-1 M */
    bzero4(&X);  prod_into(&X, M, 5, IF, 5);      /* M F^-1 */
    bzero4(&Y);  prod_into(&Y, IM, 5, F, 5);      /* M^-1 F */
    int xl[64], yl[64], nx, ny;
    nx = blist(&X, xl); ny = blist(&Y, yl);
    bs EEi, EiE;
    EEi = QM; bor4(&EEi, &fc->QFb); bor4(&EEi, &X);
    for (int k = 0; k < nx; k++) bset(&EEi, inv_[xl[k]]);          /* X^-1 = F M^-1 */
    EiE = PM; bor4(&EiE, &fc->PFb); bor4(&EiE, &Y);
    for (int k = 0; k < ny; k++) bset(&EiE, inv_[yl[k]]);          /* Y^-1 = F^-1 M */
    bzero4(&Mb); for (int i = 0; i < 5; i++) bset(&Mb, M[i]);
    Eb = Mb; bor4(&Eb, &fc->Fb);
    int sum = 0;
    /* C2 = EE^-1 u (F F^-1)^2 */
    c = EEi; bor4(&c, &fc->QFsq); g[1] = bmiss(&c); sum += g[1];
    if (sum > thr) return sum;
    /* C3 = E^-1 E u (F^-1 F)^2 */
    c = EiE; bor4(&c, &fc->PFsq); g[2] = bmiss(&c); sum += g[2];
    if (sum > thr) return sum;
    int qm[64], pm[64], nqm, npm;
    nqm = blist(&QM, qm); npm = blist(&PM, pm);
    bs A; bzero4(&A); prod_into(&A, qm, nqm, M, 5);               /* (M M^-1) M */
    /* C5 = E u (MM^-1)M u (MM^-1)F u M(F^-1F) u (FF^-1)F */
    c = Eb; bor4(&c, &A); bor4(&c, &fc->QFF);
    prod_into(&c, qm, nqm, F, 5); prod_into(&c, M, 5, fc->pf, fc->npf);
    g[4] = bmiss(&c); sum += g[4];
    if (sum > thr) return sum;
    /* C6 = E u (MM^-1)M u F(M^-1M) u (FF^-1)M u (FF^-1)F */
    c = Eb; bor4(&c, &A); bor4(&c, &fc->QFF);
    prod_into(&c, F, 5, pm, npm); prod_into(&c, fc->qf, fc->nqf, M, 5);
    g[5] = bmiss(&c); sum += g[5];
    if (sum > thr) return sum;
    /* C1 = EE^-1 u (MM^-1)^2 */
    bs sq; bzero4(&sq); prod_into(&sq, qm, nqm, qm, nqm);
    c = EEi; bor4(&c, &sq); g[0] = bmiss(&c); sum += g[0];
    if (sum > thr) return sum;
    /* C4 = E^-1 E u (M^-1M)^2 */
    bzero4(&sq); prod_into(&sq, pm, npm, pm, npm);
    c = EiE; bor4(&c, &sq); g[3] = bmiss(&c); sum += g[3];
    return sum;
}

static void write_edges(const int *E1, const int *E2, const char *fn) {
    FILE *f = fopen(fn, "w"); if (!f) { perror(fn); return; }
    fprintf(f, "%d\n", 4 * m);
    for (int h = 0; h < m; h++) {
        fprintf(f, "%d %d\n", h, 2 * m + h);              /* A0_h - B0_h */
        fprintf(f, "%d %d\n", m + h, 3 * m + h);          /* A1_h - B1_h */
        for (int i = 0; i < 5; i++) {
            fprintf(f, "%d %d\n", h, 3 * m + T[h][E1[i]]);   /* A0_h - B1_{h e} */
            fprintf(f, "%d %d\n", 2 * m + h, m + T[h][E2[i]]); /* B0_h - A1_{h e} */
        }
    }
    fclose(f);
}

static inline int inset(const int *S, int x) { for (int k = 0; k < 5; k++) if (S[k] == x) return 1; return 0; }
static void rand_set(int *S) {   /* 5 distinct random elements */
    int n = 0;
    while (n < 5) { int x = rnd() % m; int ok = 1; for (int k = 0; k < n; k++) if (S[k] == x) ok = 0; if (ok) S[n++] = x; }
}

static int check(int nst) {
    long long nmove = 0, bad = 0;
    rs = 0x1234567ULL;
    for (int s = 0; s < nst; s++) {
        int E1[5], E2[5], brk[6], g[6];
        rand_set(E1); rand_set(E2);
        fixc f1, f2;
        build_fix(E1, &f1); build_fix(E2, &f2);
        int ref = cost_ref(E1, E2, brk);
        if (eval_side(E1, E2, &f2, INF, g) != ref) bad++;
        if (eval_side(E2, E1, &f1, INF, g) != ref) bad++;   /* swapped roles give the same total */
        for (int p = 0; p < 10; p++) {
            int *S = p < 5 ? E1 : E2, *Fo = p < 5 ? E2 : E1;
            const fixc *fc = p < 5 ? &f2 : &f1;
            int idx = p % 5, old = S[idx];
            for (int t = 0; t < 3; t++) {
                int y; do { y = rnd() % m; } while (inset(S, y));
                S[idx] = y;
                int rc = cost_ref(E1, E2, brk);
                int fcost = eval_side(S, Fo, fc, INF, g);
                int thr = (int)(rnd() % (2 * rc + 2));
                int ft = eval_side(S, Fo, fc, thr, g);
                if (fcost != rc) bad++;
                if (rc <= thr ? ft != rc : ft <= thr) bad++;
                S[idx] = old;
                nmove++;
            }
        }
    }
    printf("check: states=%d moves=%lld mismatches=%lld\n", nst, nmove, bad);
    return bad ? 1 : 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: tabu15f TAB SEED SECS [EDGES_OUT] | tabu15f TAB cost e1x5 e2x5 | tabu15f TAB check N\n"); return 2; }
    readtab(argv[1]);
    if (!strcmp(argv[2], "cost")) {
        int E1[5], E2[5], brk[6];
        if (argc < 13) return 2;
        for (int i = 0; i < 5; i++) { E1[i] = atoi(argv[3 + i]); E2[i] = atoi(argv[8 + i]); }
        fixc f2; build_fix(E2, &f2);
        int s = eval_side(E1, E2, &f2, INF, brk);   /* brk left as labels C1..C6 for the first print below */
        (void)s;
        int ref = cost_ref(E1, E2, brk);
        printf("%d %d %d %d %d %d total %d\n", brk[0], brk[1], brk[2], brk[3], brk[4], brk[5], ref);
        return 0;
    }
    if (!strcmp(argv[2], "check")) return check(argc > 3 ? atoi(argv[3]) : 20);
    uint64_t seed = strtoull(argv[2], NULL, 10);
    double secs = atof(argv[3]);
    const char *outf = argc > 4 ? argv[4] : NULL;
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 1);
    for (int i = 0; i < 20; i++) rnd();
    double t0 = now();
    int best_all = INF, bE1[5] = {0,0,0,0,0}, bE2[5] = {0,0,0,0,0};
    double tbest = 0;
    long long iters = 0;
    int restarts = 0;
    static long long tabu[10][MAXM];
    int E1[5], E2[5], g[6];
    fixc fE1, fE2;
    while (now() - t0 < secs && best_all > 0) {
        rand_set(E1); rand_set(E2);
        memset(tabu, 0, sizeof tabu);
        build_fix(E2, &fE2);
        int cur = eval_side(E1, E2, &fE2, INF, g);
        int run_best = cur, since = 0;
        restarts++;
        for (long long it = 1;; it++) {
            iters++;
            build_fix(E2, &fE2);     /* fixed side for moves of E1 */
            build_fix(E1, &fE1);     /* fixed side for moves of E2 */
            int bv = INF, bp = -1, by = -1, nt = 0;
            for (int p = 0; p < 10; p++) {
                int *S = p < 5 ? E1 : E2, *Fo = p < 5 ? E2 : E1;
                const fixc *fc = p < 5 ? &fE2 : &fE1;
                int idx = p % 5, old = S[idx];
                for (int y = 0; y < m; y++) {
                    if (inset(S, y)) continue;
                    int c, thr, tb = tabu[p][y] > it;
                    S[idx] = y;
                    thr = bv;
                    if (tb && best_all - 1 < thr) thr = best_all - 1;   /* tabu moves must beat best_all */
                    c = eval_side(S, Fo, fc, thr, g);
                    S[idx] = old;
                    if (tb && c >= best_all) continue;   /* tabu unless it beats the global best */
                    if (c < bv) { bv = c; bp = p; by = y; nt = 1; }
                    else if (c == bv) { nt++; if (rnd() % nt == 0) { bp = p; by = y; } }
                }
            }
            if (bp < 0) break;
            int *S = bp < 5 ? E1 : E2;
            int idx = bp % 5, old = S[idx];
            S[idx] = by;
            tabu[bp][old] = it + TENURE + (long long)(rnd() % 5);
            int cur2 = bv;
            cur = cur2;
            if (cur < run_best) { run_best = cur; since = 0; } else since++;
            if (cur < best_all) {
                best_all = cur; tbest = now() - t0;
                memcpy(bE1, E1, sizeof bE1); memcpy(bE2, E2, sizeof bE2);
            }
            if (best_all == 0 || since > RESTART || now() - t0 > secs) break;
        }
    }
    double el = now() - t0;
    int b6[6];
    printf("RES n=%d seed=%llu best=%d t_best=%.2f elapsed=%.2f iters=%lld restarts=%d E1=", 4 * m, (unsigned long long)seed,
           best_all, tbest, el, iters, restarts);
    for (int i = 0; i < 5; i++) printf("%s%d", i ? "," : "", bE1[i]);
    printf(" E2=");
    for (int i = 0; i < 5; i++) printf("%s%d", i ? "," : "", bE2[i]);
    if (best_all < INF) { cost_ref(bE1, bE2, b6); printf(" brk=%d,%d,%d,%d,%d,%d", b6[0], b6[1], b6[2], b6[3], b6[4], b6[5]); }
    printf("\n");
    if (best_all == 0 && outf) write_edges(bE1, bE2, outf);
    return 0;
}
