/* qf128.c: exact feasibility test for the quotient images of H(G,S), |S| = 6, diameter <= 5 (job six-five-384, card c6).
 *
 * Same question and input format as research/six-five-384/src/qfeas.c (read its header): does there exist a 6-tuple of
 * images x_1..x_6 in Q such that every element of Q is the value of >= T words, on side A and on side B?
 *
 * Speed-ups over qfeas (each one is an exact symmetry of the problem; checked by calibration against qfeas):
 *  (1) left translation: x_1 = e (label 0 = identity).
 *  (2) symmetry group <Aut(Q), inversion>: inversion y_i = x_i^{-1} maps the A-words of y to the B-words of x and vice
 *      versa (same index rules), so the test is invariant; Aut(Q) acts on tuples; both fix e. Label 1 (x_2) ranges over
 *      orbit representatives of <Aut(Q), inv> on Q.
 *  (3) labels 2..5 are a multiset (word index rules are invariant under relabelling): enumerated nondecreasing.
 *  (4) incremental counting: a word is added at the depth of its largest label, so the innermost loop only adds the
 *      words that involve label 5 (and copies two count vectors).
 *  (5) heuristic first: hill climbing on the total deficit sum_y max(0, T - c_A(y)) + max(0, T - c_B(y)); any witness is
 *      re-verified by an independent evaluation (the same loops as qfeas) before it is printed as FEAS.
 *
 * usage: qf128 FILE T
 * env: HEUR=R,I  restarts R and iterations I of the hill climb (default 30,20000; HEUR=0 disables it)
 *      REPS=a-b  process only orbit representatives with index in [a,b) (exhaustive part; prints PARTIAL/DONE per range)
 *      TL=sec    stop the exhaustive part after sec seconds (prints PARTIAL)
 * output: FEAS x1..x6 (verified) | INFEAS nodes=... | PARTIAL ... | DONE_RANGE ... (no witness in the range)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXN 128
#define S 128                      /* table stride; n <= MAXN */
static int n, T;
static uint8_t Mt[S * S];   /* Mt[a*S+b] = a*b */
static uint8_t INV[MAXN];
static int par[MAXN];

static int findp(int a) { while (par[a] != a) { par[a] = par[par[a]]; a = par[a]; } return a; }
static void unite(int a, int b) { a = findp(a); b = findp(b); if (a != b) { if (a < b) par[b] = a; else par[a] = b; } }

typedef struct { uint8_t p, q; } Word;   /* p = 6a+b; q = 6c+d for a 4-letter word, 255 for a 2-letter word */
static Word W[6][1000];                  /* words whose largest label is k */
static int NW[6];
static uint8_t DA[36], DB[36];           /* DA = x_a^{-1} x_b, DB = x_a x_b^{-1} for the current labels */
static uint8_t x[6];
static uint16_t CA[7][MAXN], CB[7][MAXN];
static long nodes = 0;
static int found = 0;

static void build_words(void) {
    for (int a = 0; a < 6; a++) for (int b = 0; b < 6; b++) if (a != b) {
        int m = a > b ? a : b;
        W[m][NW[m]].p = (uint8_t)(a * 6 + b); W[m][NW[m]].q = 255; NW[m]++;
    }
    for (int a = 0; a < 6; a++) for (int b = 0; b < 6; b++) if (a != b)
    for (int c = 0; c < 6; c++) if (c != b) for (int d = 0; d < 6; d++) if (d != c) {
        int m = a; if (b > m) m = b; if (c > m) m = c; if (d > m) m = d;
        W[m][NW[m]].p = (uint8_t)(a * 6 + b); W[m][NW[m]].q = (uint8_t)(c * 6 + d); NW[m]++;
    }
}

/* set DA, DB for all pairs whose larger label is d (labels 0..d are set) */
static inline void set_tables(int d) {
    int xd = x[d], id = INV[xd];
    for (int j = 0; j < d; j++) {
        int xj = x[j], ij = INV[xj];
        DA[d * 6 + j] = Mt[id*S+xj];   /* x_d^{-1} x_j */
        DB[d * 6 + j] = Mt[xd*S+ij];   /* x_d x_j^{-1} */
        DA[j * 6 + d] = Mt[ij*S+xd];   /* x_j^{-1} x_d */
        DB[j * 6 + d] = Mt[xj*S+id];   /* x_j x_d^{-1} */
    }
}

/* CA[d+1] = CA[d] + words whose largest label is d (labels 0..d are set) */
static inline void step(int d) {
    set_tables(d);
    uint16_t *ca = CA[d + 1], *cb = CB[d + 1];
    memcpy(ca, CA[d], sizeof(uint16_t) * n);
    memcpy(cb, CB[d], sizeof(uint16_t) * n);
    const Word *w = W[d];
    for (int i = 0; i < NW[d]; i++) {
        int p = w[i].p, q = w[i].q;
        if (q == 255) { ca[DA[p]]++; cb[DB[p]]++; }
        else { ca[Mt[DA[p]*S+DA[q]]]++; cb[Mt[DB[p]*S+DB[q]]]++; }
    }
}

static inline int ok6(void) {
    const uint16_t *a = CA[6], *b = CB[6];
    for (int y = 0; y < n; y++) if (a[y] < T || b[y] < T) return 0;
    return 1;
}

static void rec(int d, int lo) {          /* assign label d (2..5), nondecreasing */
    for (int v = lo; v < n && !found; v++) {
        x[d] = (uint8_t)v;
        step(d);
        if (d == 5) { nodes++; if (ok6()) { found = 1; return; } }
        else rec(d + 1, v);
    }
}

/* independent evaluation: the loops of qfeas.c for the 6-tuple q (q[0] must be the identity 0) */
static void verify_indep(const int *q, int *mA, int *mB) {
    static int cA[MAXN], cB[MAXN];
    int DAi[36], DBi[36];
    memset(cA, 0, sizeof cA); memset(cB, 0, sizeof cB);
    cA[0]++; cB[0]++;
    for (int a = 0; a < 6; a++) for (int b = 0; b < 6; b++) {
        DAi[a * 6 + b] = Mt[INV[q[a]]*S+q[b]]; DBi[a * 6 + b] = Mt[q[a]*S+INV[q[b]]]; }
    for (int a = 0; a < 6; a++) for (int b = 0; b < 6; b++) if (a != b) { cA[DAi[a * 6 + b]]++; cB[DBi[a * 6 + b]]++; }
    for (int a = 0; a < 6; a++) for (int b = 0; b < 6; b++) if (a != b)
        for (int c = 0; c < 6; c++) if (c != b) for (int d = 0; d < 6; d++) if (d != c) {
            cA[Mt[DAi[a * 6 + b]*S+DAi[c * 6 + d]]]++; cB[Mt[DBi[a * 6 + b]*S+DBi[c * 6 + d]]]++; }
    int ma = 1 << 30, mb = 1 << 30;
    for (int y = 0; y < n; y++) { if (cA[y] < ma) ma = cA[y]; if (cB[y] < mb) mb = cB[y]; }
    *mA = ma; *mB = mb;
}

/* deficit of the current labels x[0..5] (full evaluation through the same step() chain) */
static int deficit(void) {
    memset(CA[0], 0, sizeof CA[0]); memset(CB[0], 0, sizeof CB[0]);
    CA[0][0] = 1; CB[0][0] = 1;
    for (int d = 0; d < 6; d++) step(d);
    int s = 0;
    for (int y = 0; y < n; y++) {
        if (CA[6][y] < T) s += T - CA[6][y];
        if (CB[6][y] < T) s += T - CB[6][y];
    }
    return s;
}

static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void print_witness(const char *tag, const int *q) {
    int ma, mb;
    verify_indep(q, &ma, &mb);
    printf("FEAS %s %d %d %d %d %d %d verified minA=%d minB=%d%s\n", tag, q[0], q[1], q[2], q[3], q[4], q[5], ma, mb,
           (ma >= T && mb >= T) ? "" : " VERIFY_FAILED");
    fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: qf128 FILE T\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    T = atoi(argv[2]);
    if (fscanf(f, "%d", &n) != 1 || n > MAXN) { fprintf(stderr, "n=%d > %d unsupported\n", n, MAXN); return 2; }
    for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) { int v; if (fscanf(f, "%d", &v) != 1) return 2; Mt[i*S+j] = (uint8_t)v; }
    for (int a = 0; a < n; a++) for (int b = 0; b < n; b++) if (Mt[a*S+b] == 0) INV[a] = (uint8_t)b;
    int k = 0; if (fscanf(f, "%d", &k) != 1) k = 0;
    for (int i = 0; i < n; i++) par[i] = i;
    int *g = malloc(sizeof(int) * n);
    for (int a = 0; a < k; a++) {
        for (int i = 0; i < n; i++) if (fscanf(f, "%d", &g[i]) != 1) return 2;
        for (int i = 0; i < n; i++) unite(i, g[i]);
    }
    fclose(f);
    for (int i = 0; i < n; i++) unite(i, INV[i]);             /* inversion symmetry */
    int *reps = malloc(sizeof(int) * n), nreps = 0;
    for (int i = 0; i < n; i++) if (findp(i) == i) reps[nreps++] = i;   /* includes 0 = e */
    if ((long)T * n > 781) { printf("INFEAS trivially (T*n > 781)\n"); return 0; }

    build_words();
    int hR = 30, hI = 20000;
    if (getenv("HEUR")) { if (sscanf(getenv("HEUR"), "%d,%d", &hR, &hI) < 1) hR = 0; if (hR == 0) hI = 0; }
    /* (5) heuristic: hill climbing on the deficit */
    for (int r = 0; r < hR && !found; r++) {
        x[0] = 0; for (int j = 1; j < 6; j++) x[j] = (uint8_t)(xr() % n);
        int cur = deficit();
        for (int it = 0; it < hI && cur > 0; it++) {
            int j = 1 + (int)(xr() % 5); uint8_t old = x[j];
            x[j] = (uint8_t)(xr() % n);
            int nd = deficit();
            if (nd <= cur || (xr() % 100) < 2) cur = nd; else x[j] = old;
        }
        if (cur == 0) {
            int q[6]; for (int j = 0; j < 6; j++) q[j] = x[j];
            print_witness("heur", q);
            return 0;
        }
    }

    /* (1)-(4) exhaustive over orbit representatives r of label 1 */
    int a0 = 0, a1 = nreps;
    if (getenv("REPS")) sscanf(getenv("REPS"), "%d-%d", &a0, &a1);
    if (a1 > nreps) a1 = nreps;
    double TL = getenv("TL") ? atof(getenv("TL")) : 1e18;
    clock_t t0 = clock();
    for (int ri = a0; ri < a1 && !found; ri++) {
        memset(CA[0], 0, sizeof CA[0]); memset(CB[0], 0, sizeof CB[0]);
        CA[0][0] = 1; CB[0][0] = 1;
        x[0] = 0; x[1] = (uint8_t)reps[ri];
        step(0); step(1);
        rec(2, 0);
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        fprintf(stderr, "rep %d/%d r=%d nodes=%ld t=%.1fs\n", ri, nreps, reps[ri], nodes, el);
        if (!found && el > TL) { printf("PARTIAL nreps=%d done_upto=%d nodes=%ld t=%.1f\n", nreps, ri + 1, nodes, el); return 3; }
    }
    if (found) {
        int q[6]; for (int j = 0; j < 6; j++) q[j] = x[j];
        print_witness("exh", q);
        return 0;
    }
    if (a0 == 0 && a1 == nreps) printf("INFEAS nreps=%d nodes=%ld\n", nreps, nodes);
    else printf("DONE_RANGE %d-%d of %d no FEAS nodes=%ld\n", a0, a1, nreps, nodes);
    return 0;
}
