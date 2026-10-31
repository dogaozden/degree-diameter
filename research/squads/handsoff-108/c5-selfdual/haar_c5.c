/* haar_sym: haar_fast plus structured (automorphism-invariant) generator sets and the Heisenberg family.
 *   ORBIT="k m f": S = {e} + (f-1) generators fixed by an automorphism alpha + m alpha-orbits of size k (d = f + k m),
 *     alpha = (conjugation by an element of the base group) x (z -> r z on Z_n), or (x,y,z) -> (a x, b y, a b z) on heis.
 *     Annealing moves replace a whole orbit (or one fixed generator); energy = uncovered / k (ORBW=w: a fixed element weighs w).
 *   RANDORB=m: cost statistics of m random symmetric S (no search).
 *   ALPHA=<index of the conjugating element>, AR=<r>, AHA/AHB=<a>/<b> override the automatic choice of alpha.
 *   GROUP heis q: Heisenberg group of 3x3 upper unitriangular matrices over GF(q), (a,b,c)(a',b',c') = (a+a', b+b', c+c'+ab').
 * Everything else (CLI, cost, solution files) is haar_fast / haar_gen3.
 *
 * haar_fast: haar_gen3 (research/frontier/haar_gen3.c) with a faster, bit-identical cost evaluation.
 * Same CLI, RESULT line and solution files as haar_gen3.  Changes (all exact; see research/structured/SPEEDUP.md):
 *   - dense BFS levels are pulls (gathers through the inverse tables) instead of scatters;
 *   - the last level only counts: each target row ORs its sources until the row is full (early exit);
 *   - best-of-K: a candidate is abandoned as soon as its partial uncovered count proves it cannot win
 *     (cost >= best earlier candidate), which never changes the selected candidate;
 *   - FAST=0 runs the original evaluation code (for A/B tests in one binary); VCLOCK=x replaces wall-clock time in the
 *     annealing schedule by x seconds per step and MAXSTEPS=n stops after n steps, so FAST=0 and FAST=1 runs with the
 *     same seed follow the identical trajectory (TRACE line = hash of every step); BENCH=m times the parts of one eval.
 *
 * Original haar_gen3 description:
 * haar_gen3: faster annealing search for Haar (bi-Cayley) graphs of diameter D, with more group families.
 * Drop-in replacement for haar_gen (same CLI, same RESULT line, same solution-file format for the old families).
 *
 * Haar graph H(G,S): vertices (g,A), (g,B); edges (g,A) ~ (s g, B), s in S, |S| = d, s_0 = e.
 * Right multiplication by G is transitive on each side, so diam = max(ecc(e,A), ecc(e,B)).
 * Cost (as in haar_gen):  D even: #B-side elements not within D-1 of (e,A);
 *                         D odd : #A not within D-1 of (e,A) + #B not within D-1 of (e,B).
 * The full diameter (all four side pairs within D) is checked before writing a solution.
 *
 * Speed: bitset BFS over left cosets of a cyclic subgroup H = <h> of order nH <= 63.  Element g = rep_r h^b is bit b
 * of row r.  Left multiplication by s maps row r to row r' with a rotation: s rep_r = rep_r' h^j, so
 * s (rep_r h^b) = rep_r' h^(j+b).  One BFS level is then (rows) x d word operations instead of N x d random
 * accesses, and all tables are N/nH long (cache resident).  The table of s^-1 is the inverse permutation of the table
 * of s (no extra multiplications).  Candidates of one move can be evaluated in parallel (env THREADS, default 1).
 *
 * Usage: haar_gen3 d D seconds seed K outfile GROUP... n       (G = GROUP x Z_n)
 *   GROUP = meta m k r          Z_m x|_r Z_k (r^k = 1 mod m)
 *         | sl q | psl q | pgl q   2x2 matrices over GF(q), q a prime or a prime power (q = p^k: field GF(p)[x]/(f),
 *                               f the smallest monic irreducible, written into the spec as "poly x^3+2x+1")
 *         | agl1 q              affine maps x -> a x + b over GF(q)
 *         | prod GROUP GROUP    direct product
 *         | cyc                 trivial group
 * Env: THREADS (default 1), HMAX (max order of H, default 63), UCAP (stored uncovered samples, default 65536),
 *      COOL (seconds per halving of T, default 20), REHEAT (seconds without gain before a reheat, default 150),
 *      PROFILE=1 (timing breakdown on stderr).
 * Solution file: header "d D <spec> n NCYC N NTOT", then d lines "<index> <description> z=Z".  Descriptions:
 *   mat(a,b,c,d) (field elements as integers sum c_i p^i), meta(a=A,j=J), aff(a,b), prod[<desc>;<desc>], or empty.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <signal.h>
#include <limits.h>
#include <immintrin.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define MAXD 32
#define MAXK 64

/* ---------------- finite fields ---------------- */
typedef struct { int q, p, k; int poly[16]; uint16_t *add, *mul; uint16_t *neg, *inv; } field;

static void poly_str(const field *F, char *buf) {   /* "x^3+2x+1" */
    char *s = buf; *s = 0; int first = 1;
    for (int i = F->k; i >= 0; i--) {
        int c = F->poly[i]; if (!c) continue;
        if (!first) *s++ = '+';
        first = 0;
        if (i == 0) s += sprintf(s, "%d", c);
        else { if (c != 1) s += sprintf(s, "%d", c); s += sprintf(s, i == 1 ? "x" : "x^%d", i); }
    }
}
/* polynomial over GF(p), coefficients low->high, degree < 16 */
static int pdeg(const int *a, int n) { for (int i = n - 1; i >= 0; i--) if (a[i]) return i; return -1; }
static int irreducible(const int *f, int k, int p) {  /* brute force: no monic factor of degree 1..k/2 */
    for (int dg = 1; dg <= k / 2; dg++) {
        long long cnt = 1; for (int i = 0; i < dg; i++) cnt *= p;
        for (long long code = 0; code < cnt; code++) {
            int g[16] = {0}; long long c = code; for (int i = 0; i < dg; i++) { g[i] = (int)(c % p); c /= p; } g[dg] = 1;
            int r[16]; memcpy(r, f, sizeof r);
            for (int i = k; i >= dg; i--) {           /* r mod g, g monic */
                int t = r[i]; if (!t) continue;
                for (int j = 0; j <= dg; j++) r[i - dg + j] = ((r[i - dg + j] - t * g[j]) % p + p) % p;
            }
            if (pdeg(r, 16) < 0) return 0;
        }
    }
    return 1;
}
static field *make_field(int q) {
    field *F = calloc(1, sizeof *F); F->q = q;
    int p = 0; for (int t = 2; t <= q; t++) if (q % t == 0) { p = t; break; }
    int k = 0, x = q; while (x % p == 0) { x /= p; k++; }
    if (x != 1) { fprintf(stderr, "%d is not a prime power\n", q); exit(2); }
    F->p = p; F->k = k;
    if (k == 1) { F->poly[1] = 1; }
    else {
        long long cnt = 1; for (int i = 0; i < k; i++) cnt *= p;
        for (long long code = 0; code < cnt; code++) {
            int f[16] = {0}; long long c = code; for (int i = 0; i < k; i++) { f[i] = (int)(c % p); c /= p; } f[k] = 1;
            if (f[0] && irreducible(f, k, p)) { memcpy(F->poly, f, sizeof f); break; }
        }
    }
    F->add = malloc(2 * (size_t)q * q); F->mul = malloc(2 * (size_t)q * q);
    F->neg = malloc(2 * (size_t)q); F->inv = malloc(2 * (size_t)q);
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int da[16] = {0}, db[16] = {0}, s = 0, pw = 1, aa = a, bb = b;
        for (int i = 0; i < k; i++) { da[i] = aa % p; aa /= p; db[i] = bb % p; bb /= p; }
        for (int i = 0; i < k; i++) { s += ((da[i] + db[i]) % p) * pw; pw *= p; }
        F->add[a * q + b] = (uint16_t)s;
        int pr[32] = {0};
        for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) pr[i + j] = (pr[i + j] + da[i] * db[j]) % p;
        for (int i = 2 * k - 2; i >= k; i--) { int t = pr[i]; if (!t) continue; for (int j = 0; j <= k; j++) pr[i - k + j] = ((pr[i - k + j] - t * F->poly[j]) % p + p) % p; }
        s = 0; pw = 1; for (int i = 0; i < k; i++) { s += pr[i] * pw; pw *= p; }
        F->mul[a * q + b] = (uint16_t)s;
    }
    for (int a = 0; a < q; a++) {
        for (int b = 0; b < q; b++) { if (F->add[a * q + b] == 0) F->neg[a] = (uint16_t)b; if (F->mul[a * q + b] == 1) F->inv[a] = (uint16_t)b; }
    }
    /* sanity: field axioms on samples */
    for (int a = 1; a < q; a++) if (F->mul[a * q + F->inv[a]] != 1) { fprintf(stderr, "field error\n"); exit(2); }
    return F;
}
#define FADD(F, a, b) ((F)->add[(a) * (F)->q + (b)])
#define FMUL(F, a, b) ((F)->mul[(a) * (F)->q + (b)])

/* ---------------- base groups ---------------- */
enum { G_META, G_SL, G_PSL, G_PGL, G_TRIV, G_PROD, G_AGL1, G_HEIS };
typedef struct grp {
    int type, order, ident;
    int m, k; int64_t *R;                 /* meta */
    field *F; uint16_t *EL; int *IDXK;    /* matrix groups: EL[4*i..], IDXK[key] -> index */
    uint8_t *IDXS;                        /* psl: 1 if the key is the negative of the stored representative */
    struct grp *g1, *g2;                  /* prod */
    char spec[400];
} grp;

static inline int mkey(const grp *G, int a, int b, int c, int dd) {
    const field *F = G->F; int q = F->q;
    if (G->type == G_PGL) {
        if (a) { int ia = F->inv[a]; return (FMUL(F, b, ia) * q + FMUL(F, c, ia)) * q + FMUL(F, dd, ia); }
        int ib = F->inv[b]; return q * q * q + FMUL(F, c, ib) * q + FMUL(F, dd, ib);
    }
    if (a) return ((a - 1) * q + b) * q + c;
    return (q - 1) * q * q + (b - 1) * q + dd;
}
static int qmul(const grp *G, int x, int y) {
    switch (G->type) {
    case G_TRIV: return 0;
    case G_META: { int a = x / G->k, j = x % G->k, b = y / G->k, l = y % G->k;
        int c = (int)((a + G->R[j] * b) % G->m); return c * G->k + (j + l) % G->k; }
    case G_PROD: { int o2 = G->g2->order; return qmul(G->g1, x / o2, y / o2) * o2 + qmul(G->g2, x % o2, y % o2); }
    case G_AGL1: { const field *F = G->F; int q = F->q; int a1 = x / q + 1, b1 = x % q, a2 = y / q + 1, b2 = y % q;
        int a = FMUL(F, a1, a2), b = FADD(F, FMUL(F, a1, b2), b1); return (a - 1) * q + b; }
    case G_HEIS: { const field *F = G->F; int q = F->q; int a1 = x / (q * q), b1 = x / q % q, c1 = x % q, a2 = y / (q * q), b2 = y / q % q, c2 = y % q;
        return (FADD(F, a1, a2) * q + FADD(F, b1, b2)) * q + FADD(F, FADD(F, c1, c2), FMUL(F, a1, b2)); }
    default: {
        const field *F = G->F; const uint16_t *A = G->EL + 4 * (size_t)x, *B = G->EL + 4 * (size_t)y;
        int a = FADD(F, FMUL(F, A[0], B[0]), FMUL(F, A[1], B[2])), b = FADD(F, FMUL(F, A[0], B[1]), FMUL(F, A[1], B[3]));
        int c = FADD(F, FMUL(F, A[2], B[0]), FMUL(F, A[3], B[2])), dd = FADD(F, FMUL(F, A[2], B[1]), FMUL(F, A[3], B[3]));
        return G->IDXK[mkey(G, a, b, c, dd)]; }
    }
}
static int qinv(const grp *G, int x) {
    switch (G->type) {
    case G_TRIV: return 0;
    case G_META: { int a = x / G->k, j = x % G->k, jj = (G->k - j) % G->k;
        int b = (int)((G->m - (G->R[jj] * a) % G->m) % G->m); return b * G->k + jj; }
    case G_PROD: { int o2 = G->g2->order; return qinv(G->g1, x / o2) * o2 + qinv(G->g2, x % o2); }
    case G_AGL1: { const field *F = G->F; int q = F->q; int a = x / q + 1, b = x % q, ia = F->inv[a];
        return (ia - 1) * q + F->neg[FMUL(F, ia, b)]; }
    case G_HEIS: { const field *F = G->F; int q = F->q; int a = x / (q * q), b = x / q % q, c = x % q;   /* (-a, -b, -c + ab) */
        return (F->neg[a] * q + F->neg[b]) * q + FADD(F, F->neg[c], FMUL(F, a, b)); }
    default: { const field *F = G->F; const uint16_t *A = G->EL + 4 * (size_t)x;
        int a = A[3], b = F->neg[A[1]], c = F->neg[A[2]], dd = A[0];
        if (G->type == G_SL || G->type == G_PSL) return G->IDXK[mkey(G, a, b, c, dd)];
        return G->IDXK[mkey(G, a, b, c, dd)]; }
    }
}
static void qdesc(const grp *G, int x, char *buf) {
    switch (G->type) {
    case G_TRIV: buf[0] = 0; break;
    case G_META: sprintf(buf, "meta(a=%d,j=%d)", x / G->k, x % G->k); break;
    case G_AGL1: sprintf(buf, "aff(%d,%d)", x / G->F->q + 1, x % G->F->q); break;
    case G_HEIS: { int q = G->F->q; sprintf(buf, "heis(%d,%d,%d)", x / (q * q), x / q % q, x % q); break; }
    case G_PROD: { char b1[300], b2[300]; int o2 = G->g2->order; qdesc(G->g1, x / o2, b1); qdesc(G->g2, x % o2, b2);
        sprintf(buf, "prod[%s;%s]", b1, b2); break; }
    default: { const uint16_t *A = G->EL + 4 * (size_t)x; sprintf(buf, "mat(%d,%d,%d,%d)", A[0], A[1], A[2], A[3]); }
    }
}
static void build_matrix(grp *G) {
    field *F = G->F; int q = F->q;
    long long nkeys = (long long)q * q * q + (long long)q * q;
    G->IDXK = malloc(sizeof(int) * nkeys); for (long long i = 0; i < nkeys; i++) G->IDXK[i] = -1;
    long long cap = (long long)q * q * q;   /* >= |G| */
    G->IDXS = calloc(nkeys, 1);
    G->EL = malloc(8 * cap); int n = 0;
    if (G->type == G_PGL) {
        for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) for (int dd = 0; dd < q; dd++) {
            if (FADD(F, dd, F->neg[FMUL(F, b, c)]) == 0) continue;           /* det = d - bc */
            uint16_t *E = G->EL + 4 * (size_t)n; E[0] = 1; E[1] = b; E[2] = c; E[3] = dd;
            G->IDXK[mkey(G, 1, b, c, dd)] = n++;
        }
        for (int c = 1; c < q; c++) for (int dd = 0; dd < q; dd++) {
            uint16_t *E = G->EL + 4 * (size_t)n; E[0] = 0; E[1] = 1; E[2] = c; E[3] = dd;
            G->IDXK[mkey(G, 0, 1, c, dd)] = n++;
        }
    } else {
        for (long long t = 0; t < (long long)q * q * q; t++) {
            int a = (int)(t / ((long long)q * q)), b = (int)(t / q % q), c = (int)(t % q), dd;
            if (a) dd = FMUL(F, F->inv[a], FADD(F, 1, FMUL(F, b, c)));          /* d = (1+bc)/a */
            else { if (!b) continue; dd = c; c = F->neg[F->inv[b]]; }           /* a = 0: c = -1/b, d free */
            int key = mkey(G, a, b, c, dd);
            if (G->IDXK[key] >= 0) continue;
            uint16_t *E = G->EL + 4 * (size_t)n; E[0] = a; E[1] = b; E[2] = c; E[3] = dd;
            G->IDXK[key] = n;
            if (G->type == G_PSL) { int k2 = mkey(G, F->neg[a], F->neg[b], F->neg[c], F->neg[dd]); G->IDXK[k2] = n; G->IDXS[k2] = 1; }
            n++;
        }
    }
    G->order = n;
    G->ident = G->IDXK[mkey(G, 1, 0, 0, 1)];
}
static int TWIST = 0, CSL = 0, top_level = 0;   /* csl q: (SL(2,q) x Z_n)/<(-I, n/2)>, n even */    /* tpgl q: G = Z_n x| PGL(2,q), non-square determinant inverts Z_n */
static grp *parse_group(char **argv, int argc, int *a) {
    top_level++;
    if (*a >= argc) { fprintf(stderr, "bad group\n"); exit(2); }
    grp *G = calloc(1, sizeof *G); const char *t = argv[*a];
    if (!strcmp(t, "meta")) {
        G->type = G_META; G->m = atoi(argv[*a + 1]); G->k = atoi(argv[*a + 2]); long long r = atoll(argv[*a + 3]); *a += 4;
        G->R = malloc(sizeof(int64_t) * G->k); G->R[0] = 1 % G->m;
        for (int j = 1; j < G->k; j++) G->R[j] = G->R[j - 1] * r % G->m;
        if (G->R[G->k - 1] * r % G->m != 1 % G->m) { fprintf(stderr, "r^k != 1\n"); exit(2); }
        G->order = G->m * G->k; G->ident = 0; snprintf(G->spec, sizeof G->spec, "meta %d %d %lld", G->m, G->k, r);
    } else if (!strcmp(t, "sl") || !strcmp(t, "psl") || !strcmp(t, "pgl") || !strcmp(t, "tpgl") || !strcmp(t, "csl")) {
        G->type = !strcmp(t, "sl") ? G_SL : (!strcmp(t, "psl") || !strcmp(t, "csl")) ? G_PSL : G_PGL;
        if (!strcmp(t, "csl")) { if (top_level != 1) { fprintf(stderr, "csl only as the whole group (not inside prod)\n"); exit(2); } CSL = 1; }
        if (!strcmp(t, "tpgl")) { if (top_level != 1) { fprintf(stderr, "tpgl only as the whole group (not inside prod)\n"); exit(2); } TWIST = 1; }
        int q = atoi(argv[*a + 1]); *a += 2; G->F = make_field(q);
        if (G->type == G_PSL && G->F->p == 2) G->type = G_SL;     /* PSL = SL in characteristic 2 */
        build_matrix(G);
        if (G->F->k == 1) snprintf(G->spec, sizeof G->spec, "%s %d", t, q);
        else { char ps[200]; poly_str(G->F, ps); snprintf(G->spec, sizeof G->spec, "%s %d poly %s", t, q, ps); }
    } else if (!strcmp(t, "agl1")) {
        G->type = G_AGL1; int q = atoi(argv[*a + 1]); *a += 2; G->F = make_field(q);
        G->order = q * (q - 1); G->ident = 0;                /* (a=1,b=0) */
        if (G->F->k == 1) snprintf(G->spec, sizeof G->spec, "agl1 %d", q);
        else { char ps[200]; poly_str(G->F, ps); snprintf(G->spec, sizeof G->spec, "agl1 %d poly %s", q, ps); }
    } else if (!strcmp(t, "heis")) {
        G->type = G_HEIS; int q = atoi(argv[*a + 1]); *a += 2; G->F = make_field(q);
        G->order = q * q * q; G->ident = 0;
        if (G->F->k == 1) snprintf(G->spec, sizeof G->spec, "heis %d", q);
        else { char ps[200]; poly_str(G->F, ps); snprintf(G->spec, sizeof G->spec, "heis %d poly %s", q, ps); }
    } else if (!strcmp(t, "prod")) {
        G->type = G_PROD; *a += 1; G->g1 = parse_group(argv, argc, a); G->g2 = parse_group(argv, argc, a);
        G->order = G->g1->order * G->g2->order; G->ident = G->g1->ident * G->g2->order + G->g2->ident;
        snprintf(G->spec, sizeof G->spec, "prod %s %s", G->g1->spec, G->g2->spec);
    } else if (!strcmp(t, "cyc")) { G->type = G_TRIV; G->order = 1; G->ident = 0; *a += 1; snprintf(G->spec, sizeof G->spec, "cyc"); }
    else { fprintf(stderr, "bad group %s\n", t); exit(2); }
    if (G->type == G_PGL && TWIST && G->F->p == 2) { fprintf(stderr, "tpgl needs q odd\n"); exit(2); }
    if (CSL && G->type != G_PSL) { fprintf(stderr, "csl needs q odd\n"); exit(2); }
    return G;
}

/* ---------------- G = Q x Z_n ---------------- */
static grp *Q; static int ncyc, N, ident;
static int8_t *CHI;                /* twist: CHI[q] = +1 or -1 (all +1 for direct products) */
static inline int csl_key(int x, int y) {   /* key of the product of the stored representatives */
    const field *F = Q->F; const uint16_t *A = Q->EL + 4 * (size_t)x, *B = Q->EL + 4 * (size_t)y;
    int a = FADD(F, FMUL(F, A[0], B[0]), FMUL(F, A[1], B[2])), b = FADD(F, FMUL(F, A[0], B[1]), FMUL(F, A[1], B[3]));
    int c = FADD(F, FMUL(F, A[2], B[0]), FMUL(F, A[3], B[2])), dd = FADD(F, FMUL(F, A[2], B[1]), FMUL(F, A[3], B[3]));
    return mkey(Q, a, b, c, dd);
}
static inline int gmul(int x, int y) {
    int xq = x / ncyc, yz = y % ncyc; if (CHI[xq] < 0) yz = (ncyc - yz) % ncyc;
    if (CSL) { int key = csl_key(xq, y / ncyc); return Q->IDXK[key] * ncyc + (x % ncyc + yz + Q->IDXS[key] * (ncyc / 2)) % ncyc; }
    return qmul(Q, xq, y / ncyc) * ncyc + (x % ncyc + yz) % ncyc; }
static inline int ginv(int x) {
    int xq = x / ncyc, z = (ncyc - x % ncyc) % ncyc; if (CHI[xq] < 0) z = (ncyc - z) % ncyc;
    if (CSL) { const uint16_t *A = Q->EL + 4 * (size_t)xq; const field *F = Q->F;
        int key = mkey(Q, A[3], F->neg[A[1]], F->neg[A[2]], A[0]); return Q->IDXK[key] * ncyc + (z + Q->IDXS[key] * (ncyc / 2)) % ncyc; }
    return qinv(Q, xq) * ncyc + z; }

/* cosets of H = <h> */
static int nH, R;                 /* |H|, number of rows */
static uint64_t MASK;
static int *POS;                  /* POS[g] = row * 64 + bit */
static int *REP;                  /* REP[row] */
static int HP[MAXK];              /* h^b */

static int d, D;
static int S[MAXD], SI[MAXD], bestS[MAXD];
static uint32_t *TF[MAXD], *TI[MAXD];    /* tables of s_i and s_i^-1: (row' << 6) | rot */

static unsigned long long rs;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static int *REPQ, *REPZ;          /* REP split into (Q index, z) */
static uint8_t *zero_s;           /* all-zero sign table (non-csl groups) */
#define EMIT(g) do { int ps_ = POS[g], r2_ = ps_ >> 6, j_ = ps_ & 63; \
    tf[r] = ((uint32_t)r2_ << 6) | (uint32_t)j_; ti[r2_] = ((uint32_t)r << 6) | (uint32_t)(j_ ? nH - j_ : 0); } while (0)
static void make_tables(int x, uint32_t *tf, uint32_t *ti) {
    int xq = x / ncyc, xz = x % ncyc, neg = CHI[xq] < 0;
    if (Q->type == G_SL || Q->type == G_PSL || Q->type == G_PGL) {
        /* fast path for matrix groups: rows of the multiplication table for the fixed entries of x */
        const field *F = Q->F; const int q = F->q;
        const uint16_t *A = Q->EL + 4 * (size_t)xq, *EL = Q->EL, *AD = F->add, *IV = F->inv;
        const uint16_t *M0 = F->mul + A[0] * q, *M1 = F->mul + A[1] * q, *M2 = F->mul + A[2] * q, *M3 = F->mul + A[3] * q;
        const int *IDXK = Q->IDXK, pgl = Q->type == G_PGL, prime = F->k == 1, half = CSL ? ncyc / 2 : 0;
        const uint8_t *IDXS = CSL ? Q->IDXS : zero_s;
        for (int r = 0; r < R; r++) {
            const uint16_t *B = EL + 4 * (size_t)REPQ[r];
            int a, b, c, dd;
            if (prime) {
                a = M0[B[0]] + M1[B[2]]; a -= a >= q ? q : 0;  b = M0[B[1]] + M1[B[3]]; b -= b >= q ? q : 0;
                c = M2[B[0]] + M3[B[2]]; c -= c >= q ? q : 0;  dd = M2[B[1]] + M3[B[3]]; dd -= dd >= q ? q : 0;
            } else {
                a = AD[M0[B[0]] * q + M1[B[2]]]; b = AD[M0[B[1]] * q + M1[B[3]]];
                c = AD[M2[B[0]] * q + M3[B[2]]]; dd = AD[M2[B[1]] * q + M3[B[3]]];
            }
            int key;
            if (pgl) {
                if (a) { const uint16_t *Mi = F->mul + IV[a] * q; key = (Mi[b] * q + Mi[c]) * q + Mi[dd]; }
                else { const uint16_t *Mi = F->mul + IV[b] * q; key = q * q * q + Mi[c] * q + Mi[dd]; }
            } else key = a ? ((a - 1) * q + b) * q + c : (q - 1) * q * q + (b - 1) * q + dd;
            int rz = neg && REPZ[r] ? ncyc - REPZ[r] : REPZ[r];
            int z = xz + rz + (IDXS[key] ? half : 0); z -= z >= ncyc ? ncyc : 0; z -= z >= ncyc ? ncyc : 0;
            EMIT(IDXK[key] * ncyc + z);
        }
        return;
    }
    for (int r = 0; r < R; r++) {
        int rz = neg && REPZ[r] ? ncyc - REPZ[r] : REPZ[r];
        int z = xz + rz; z -= z >= ncyc ? ncyc : 0;
        EMIT(qmul(Q, xq, REPQ[r]) * ncyc + z);
    }
}

typedef struct { uint64_t *V[2], *F, *Fn, *NB; int *fl, *fln, *tl; uint32_t *cf, *ci; long long lev[64]; } ctx;
static size_t BITBYTES, NROWS;      /* bytes of one side bitset and number of rows of the active layout (set in main) */
static void *zalloc64(size_t n) { n = (n + 63) / 64 * 64; void *p = aligned_alloc(64, n); if (!p) { fprintf(stderr, "out of memory\n"); exit(2); } memset(p, 0, n); return p; }
static ctx *new_ctx(void) {
    ctx *c = calloc(1, sizeof *c);
    c->V[0] = zalloc64(BITBYTES); c->V[1] = zalloc64(BITBYTES); c->F = zalloc64(BITBYTES); c->Fn = zalloc64(BITBYTES); c->NB = zalloc64(BITBYTES);
    c->fl = malloc(4 * NROWS); c->fln = malloc(4 * NROWS); c->tl = malloc(4 * NROWS);
    c->cf = malloc(4 * NROWS); c->ci = malloc(4 * NROWS);
    return c;
}
static int FAST = 2, TIMING = 0, WIDE = 0;
static double TLEV[64], TTAB;          /* BENCH: seconds per BFS step, in make_tables */
static long long NLEV[64];
static inline uint64_t rotl(uint64_t f, int sh) { return ((f << sh) | (f >> (nH - sh))) & MASK; }

/* BFS from (e, startB) for depth steps with tables tf/ti; returns cnt[side] = #reached on each side (0 = A, 1 = B) */
static void bfs(ctx *c, uint32_t **tf, uint32_t **ti, int startB, int depth, long long cnt[2]) {
    memset(c->V[0], 0, 8 * (size_t)R); memset(c->V[1], 0, 8 * (size_t)R);
    memset(c->F, 0, 8 * (size_t)R); memset(c->Fn, 0, 8 * (size_t)R);
    uint64_t *F = c->F, *Fn = c->Fn, *NB = c->NB; int *fl = c->fl, *fln = c->fln, *tl = c->tl;
    int ps = POS[ident], r0 = ps >> 6; uint64_t b0 = 1ULL << (ps & 63);
    c->V[startB][r0] = b0; F[r0] = b0; fl[0] = r0; int nf = 1, dense = 0;
    cnt[0] = cnt[1] = 0; cnt[startB] = 1;
    int side = startB;
    for (int step = 0; step < depth; step++) {
        double tq = TIMING ? now() : 0;
        uint32_t **T = side == 0 ? tf : ti; int ns = side ^ 1; uint64_t *Vn = c->V[ns]; long long add = 0;
        int last = step == depth - 1;
        if (!dense) {
            int ntl = 0;
            for (int u = 0; u < nf; u++) {
                int r = fl[u]; uint64_t f = F[r]; F[r] = 0;
                for (int s = 0; s < d; s++) {
                    uint32_t t = T[s][r]; int r2 = t >> 6;
                    if (!NB[r2]) tl[ntl++] = r2;
                    NB[r2] |= rotl(f, t & 63);
                }
            }
            int nn = 0;
            for (int u = 0; u < ntl; u++) {
                int r2 = tl[u]; uint64_t nw = NB[r2] & ~Vn[r2]; NB[r2] = 0;
                if (nw) { Vn[r2] |= nw; add += __builtin_popcountll(nw); if (!last) { Fn[r2] = nw; fln[nn++] = r2; } }
            }
            nf = nn; int *tt = fl; fl = fln; fln = tt;
            if (nf > R / 16) dense = 1;
        } else {
            for (int r = 0; r < R; r++) {
                uint64_t f = F[r]; if (!f) continue;
                for (int s = 0; s < d; s++) { uint32_t t = T[s][r]; NB[t >> 6] |= rotl(f, t & 63); }
            }
            if (last) for (int r = 0; r < R; r++) { uint64_t nw = NB[r] & ~Vn[r]; NB[r] = 0; Vn[r] |= nw; add += __builtin_popcountll(nw); }
            else for (int r = 0; r < R; r++) { uint64_t nw = NB[r] & ~Vn[r]; NB[r] = 0; Vn[r] |= nw; Fn[r] = nw; add += __builtin_popcountll(nw); }
        }
        cnt[ns] += add; if (step < 64) c->lev[step] = cnt[ns];
        uint64_t *t2 = F; F = Fn; Fn = t2; side = ns;
        if (TIMING && step < 64) { TLEV[step] += now() - tq; NLEV[step]++; }
    }
    c->F = F; c->Fn = Fn;
}
static inline uint64_t rotr(uint64_t f, int sh) { return ((f >> sh) | (f << (nH - sh))) & MASK; }
static const long long NOBOUND = LLONG_MAX / 4;
/* Same BFS as bfs(), faster: sparse levels push as before; once dense, each level is a pull over all rows through the
 * inverse tables (row r of side ns gathers rotr(F[src], rot) from its d sources, src/rot from the table of the inverse
 * map), and rows already full on side ns are skipped.  The last level only counts: a target row stops gathering as
 * soon as it is full, its uncovered bits are added to unc, and the BFS gives up (returns -1) once
 * off + unc >= *bp + strict (the caller's proof that this candidate cannot be selected).  Returns the number of
 * uncovered elements of the final side (= N - cnt[final side]) and, unless it gave up, the same V, cnt and lev as bfs(). */
static long long bfs_fast(ctx *c, uint32_t **tf, uint32_t **ti, int startB, int depth, long long cnt[2],
                          const volatile long long *bp, long long off, int strict) {
    memset(c->V[0], 0, 8 * (size_t)R); memset(c->V[1], 0, 8 * (size_t)R);
    memset(c->F, 0, 8 * (size_t)R); memset(c->Fn, 0, 8 * (size_t)R);
    uint64_t *F = c->F, *Fn = c->Fn, *NB = c->NB; int *fl = c->fl, *fln = c->fln, *tl = c->tl;
    int ps = POS[ident], r0 = ps >> 6; uint64_t b0 = 1ULL << (ps & 63);
    c->V[startB][r0] = b0; F[r0] = b0; fl[0] = r0; int nf = 1, dense = 0;
    cnt[0] = cnt[1] = 0; cnt[startB] = 1;
    int side = startB; long long unc = -2;
    for (int step = 0; step < depth; step++) {
        double tq = TIMING ? now() : 0;
        uint32_t **T = side == 0 ? tf : ti, **P = side == 0 ? ti : tf; int ns = side ^ 1; uint64_t *Vn = c->V[ns]; long long add = 0;
        int last = step == depth - 1;
        if (!dense) {
            int ntl = 0;
            for (int u = 0; u < nf; u++) {
                int r = fl[u]; uint64_t f = F[r]; F[r] = 0;
                for (int s = 0; s < d; s++) {
                    uint32_t t = T[s][r]; int r2 = t >> 6;
                    if (!NB[r2]) tl[ntl++] = r2;
                    NB[r2] |= rotl(f, t & 63);
                }
            }
            int nn = 0;
            for (int u = 0; u < ntl; u++) {
                int r2 = tl[u]; uint64_t nw = NB[r2] & ~Vn[r2]; NB[r2] = 0;
                if (nw) { Vn[r2] |= nw; add += __builtin_popcountll(nw); if (!last) { Fn[r2] = nw; fln[nn++] = r2; } }
            }
            nf = nn; int *tt = fl; fl = fln; fln = tt;
            if (nf > R / 16) dense = 1;
        } else if (!last) {
            for (int r = 0; r < R; r++) {
                uint64_t v = Vn[r];
                if (v == MASK) { Fn[r] = 0; continue; }
                uint64_t acc = 0;
                for (int s = 0; s < d; s++) { uint32_t t = P[s][r]; acc |= rotr(F[t >> 6], t & 63); }
                uint64_t nw = acc & ~v; Fn[r] = nw; Vn[r] = v | nw; add += __builtin_popcountll(nw);
            }
        } else {
            long long u0 = 0, lim = *bp + strict - off;
            for (int r = 0; r < R; r++) {
                uint64_t cov = Vn[r];
                if (cov == MASK) continue;
                for (int s = 0; s < d; s++) { uint32_t t = P[s][r]; cov |= rotr(F[t >> 6], t & 63); if (cov == MASK) break; }
                Vn[r] = cov; u0 += __builtin_popcountll(~cov & MASK);
                if (u0 >= lim) { c->F = F; c->Fn = Fn; return -1; }
                if (!(r & 1023)) lim = *bp + strict - off;      /* other threads may have lowered the bound */
            }
            unc = u0;
        }
        if (unc >= 0) cnt[ns] = N - unc; else cnt[ns] += add;
        if (step < 64) c->lev[step] = cnt[ns];
        uint64_t *t2 = F; F = Fn; Fn = t2; side = ns;
        if (TIMING && step < 64) { TLEV[step] += now() - tq; NLEV[step]++; }
    }
    c->F = F; c->Fn = Fn;
    return N - cnt[side];
}
/* cost_with() through bfs_fast; returns -1 if the candidate was abandoned (only possible when bp != &NOBOUND) */
static long long cost_fast(ctx *c, uint32_t **tf, uint32_t **ti, double *sec, uint64_t **save, const volatile long long *bp, int strict) {
    long long cnt[2]; int L = D - 4;
    if (D % 2 == 0) { long long u = bfs_fast(c, tf, ti, 0, D - 1, cnt, bp, 0, strict); if (u < 0) return -1;
        *sec = L >= 0 ? (double)(N - c->lev[L]) / N : 0; if (save) memcpy(save[0], c->V[1], 8 * (size_t)R); return u; }
    long long u1 = bfs_fast(c, tf, ti, 0, D - 1, cnt, bp, 0, strict); if (u1 < 0) return -1;
    *sec = L >= 0 ? (double)(N - c->lev[L]) / N : 0;
    if (save) memcpy(save[0], c->V[0], 8 * (size_t)R);
    long long u2 = bfs_fast(c, tf, ti, 1, D - 1, cnt, bp, u1, strict); if (u2 < 0) return -1;
    if (L >= 0) *sec += (double)(N - c->lev[L]) / N;
    if (save) memcpy(save[1], c->V[1], 8 * (size_t)R);
    return u1 + u2;
}
/* primary cost = #uncovered; *sec = fraction of the target side not within D-3 (slack, used only if SEC > 0) */
/* save (optional): copies of the covered target-side bitsets, so an accepted candidate needs no extra BFS */
static long long cost_with(ctx *c, uint32_t **tf, uint32_t **ti, double *sec, uint64_t **save) {
    long long cnt[2]; int L = D - 4;
    if (D % 2 == 0) { bfs(c, tf, ti, 0, D - 1, cnt); *sec = L >= 0 ? (double)(N - c->lev[L]) / N : 0;
        if (save) memcpy(save[0], c->V[1], 8 * (size_t)R); return N - cnt[1]; }
    long long tot; bfs(c, tf, ti, 0, D - 1, cnt); tot = N - cnt[0]; *sec = L >= 0 ? (double)(N - c->lev[L]) / N : 0;
    if (save) memcpy(save[0], c->V[0], 8 * (size_t)R);
    bfs(c, tf, ti, 1, D - 1, cnt); if (L >= 0) *sec += (double)(N - c->lev[L]) / N;
    if (save) memcpy(save[1], c->V[1], 8 * (size_t)R);
    return tot + N - cnt[1];
}
static long long cost_w(ctx *c, uint32_t **tf, uint32_t **ti, double *sec, uint64_t **save, const volatile long long *bp, int strict);
static long long cost_eval(ctx *c, uint32_t **tf, uint32_t **ti, double *sec, uint64_t **save) {
    if (WIDE) return cost_w(c, tf, ti, sec, save, &NOBOUND, 0);
    return FAST ? cost_fast(c, tf, ti, sec, save, &NOBOUND, 0) : cost_with(c, tf, ti, sec, save);
}
static int full_check(ctx *c) {
    long long cnt[2];
    bfs(c, TF, TI, 0, D, cnt); if (cnt[0] != N || cnt[1] != N) return 0;
    bfs(c, TF, TI, 1, D, cnt); return cnt[0] == N && cnt[1] == N;
}

/* uncovered samples (reservoir) from the current state */
static int UCAP = 65536;
static int *UNC[2], nst[2], ust[2], uside[2], nlists; static long long ntrue[2];
static void scan_unc(int t, const uint64_t *V, int startB, int sd) {
    long long seen = 0; int n = 0;
    for (int r = 0; r < R; r++) {
        uint64_t z = ~V[r] & MASK;
        while (z) {
            int b = __builtin_ctzll(z); z &= z - 1; int code = r * 64 + b;
            if (n < UCAP) UNC[t][n++] = code;
            else { unsigned long long j = rnd() % (unsigned long long)(seen + 1); if (j < (unsigned long long)UCAP) UNC[t][j] = code; }
            seen++;
        }
    }
    nst[t] = n; ntrue[t] = seen; ust[t] = startB; uside[t] = sd;
}
static void scan_unc_w(int t, const uint64_t *Vw, int startB, int sd);
static long long bfs_w(ctx *c, uint32_t **tf, uint32_t **ti, int startB, int depth, long long cnt[2], const volatile long long *bp, long long off, int strict);
static void collect1(ctx *c, int t, int startB, int targetSame) {
    long long cnt[2]; int sd = targetSame ? startB : startB ^ 1;
    if (WIDE) { bfs_w(c, TF, TI, startB, D - 1, cnt, &NOBOUND, 0, 0); scan_unc_w(t, c->V[sd], startB, sd); return; }
    bfs(c, TF, TI, startB, D - 1, cnt);
    scan_unc(t, c->V[sd], startB, sd);
}
static void collect(ctx *c) {
    if (D % 2 == 0) { nlists = 1; collect1(c, 0, 0, 0); }
    else { nlists = 2; collect1(c, 0, 0, 1); collect1(c, 1, 1, 1); }
}
static void collect_saved(uint64_t **sv) {   /* same lists as collect(), from the saved bitsets of a candidate */
    void (*sc)(int, const uint64_t *, int, int) = WIDE ? scan_unc_w : scan_unc;
    if (D % 2 == 0) { nlists = 1; sc(0, sv[0], 0, 1); }
    else { nlists = 2; sc(0, sv[0], 0, 0); sc(1, sv[1], 1, 1); }
}

/* ---------------- FAST=2: wide rows ----------------
 * Same coset idea with a second cyclic subgroup HW = <hw> of order nHW in [64, 256]: element g = repw_r hw^b is bit b
 * of a 256-bit row r.  Frontier rows are stored doubled (v | v << nHW, one 64-byte cache line), so the cyclic rotation
 * of a row is a window read: two unaligned 256-bit loads from the same line, two variable shifts, one OR.  A table entry
 * is (row' << 9) | rot.  Each random access now moves 256 useful bits (instead of 64), a candidate's tables need N/nHW
 * group products (instead of N/nH), and the dense levels software-prefetch the source lines a few rows ahead.
 * The uncovered lists handed to the targeted moves are re-expressed in haar_gen3's row-64 codes and sorted, i.e.
 * exactly the lists haar_gen3 builds, so the search trajectory is unchanged. */
static int nHW, RW, PFD = 8;
static uint32_t *POSW;            /* POSW[g] = row << 9 | bit */
static int *REPW, *REPWQ, *REPWZ, HPW[512];
static __m256i MASKW;
static uint64_t MASKWA[4];
/* bits o .. o+nHW-1 of a doubled row = the row rotated right by o (o < nHW) */
static inline __m256i winw(const uint64_t *line, uint32_t o) {
    const uint64_t *p = line + (o >> 6); __m256i bo = _mm256_set1_epi64x(o & 63);
    __m256i a = _mm256_loadu_si256((const __m256i *)p), b = _mm256_loadu_si256((const __m256i *)(p + 1));
    return _mm256_and_si256(_mm256_or_si256(_mm256_srlv_epi64(a, bo), _mm256_sllv_epi64(b, _mm256_sub_epi64(_mm256_set1_epi64x(64), bo))), MASKW);
}
static inline int nzw(__m256i v) { return !_mm256_testz_si256(v, v); }
static inline int fullw(__m256i v) { return _mm256_testc_si256(v, MASKW); }
static __m256i DUPI[4]; static __mmask8 DUPM[4]; static __m128i DUPSA, DUPSB;   /* store_dup constants (256-bit ops only) */
static void init_dup(void) {
    int ws = nHW >> 6, bs = nHW & 63;
    for (int h = 0; h < 2; h++) for (int part = 0; part < 2; part++) {   /* out half h, term part (0: << bs from k-ws, 1: >> 64-bs from k-ws-1) */
        int64_t ix[4]; unsigned m = 0;
        for (int k = 0; k < 4; k++) { int src = 4 * h + k - ws - part; ix[k] = src & 3; if (src >= 0 && src < 4) m |= 1u << k; }
        DUPI[2 * h + part] = _mm256_loadu_si256((const __m256i *)ix); DUPM[2 * h + part] = (__mmask8)m;
    }
    DUPSA = _mm_cvtsi32_si128(bs); DUPSB = _mm_cvtsi32_si128(64 - bs);
}
static inline void store_dup(uint64_t *line, __m256i v) {   /* line = v | v << nHW (8 words, 64-byte aligned) */
    __m256i lo = _mm256_or_si256(_mm256_sll_epi64(_mm256_maskz_permutexvar_epi64(DUPM[0], DUPI[0], v), DUPSA),
                                 _mm256_srl_epi64(_mm256_maskz_permutexvar_epi64(DUPM[1], DUPI[1], v), DUPSB));
    __m256i hi = _mm256_or_si256(_mm256_sll_epi64(_mm256_maskz_permutexvar_epi64(DUPM[2], DUPI[2], v), DUPSA),
                                 _mm256_srl_epi64(_mm256_maskz_permutexvar_epi64(DUPM[3], DUPI[3], v), DUPSB));
    _mm256_store_si256((__m256i *)line, _mm256_or_si256(v, lo)); _mm256_store_si256((__m256i *)(line + 4), hi);
}
/* popcount of 4 x 64 bits as 4 partial sums (nibble lookup) */
static inline __m256i popv(__m256i v) {
    const __m256i lut = _mm256_setr_epi8(0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4, 0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4);
    const __m256i m4 = _mm256_set1_epi8(0x0f);
    __m256i c = _mm256_add_epi8(_mm256_shuffle_epi8(lut, _mm256_and_si256(v, m4)), _mm256_shuffle_epi8(lut, _mm256_and_si256(_mm256_srli_epi16(v, 4), m4)));
    return _mm256_sad_epu8(c, _mm256_setzero_si256());
}
static inline long long hsum(__m256i a) {
    return _mm256_extract_epi64(a, 0) + _mm256_extract_epi64(a, 1) + _mm256_extract_epi64(a, 2) + _mm256_extract_epi64(a, 3);
}
#define EMITW(r, g) do { uint32_t ps_ = POSW[g], r2_ = ps_ >> 9, j_ = ps_ & 511; \
    tf[r] = (r2_ << 9) | j_; ti[r2_] = ((uint32_t)(r) << 9) | (uint32_t)(j_ ? nHW - j_ : 0); } while (0)
static void make_tables_w(int x, uint32_t *tf, uint32_t *ti) {   /* make_tables() for the wide rows, software-pipelined */
    int xq = x / ncyc, xz = x % ncyc, neg = CHI[xq] < 0;
    if (Q->type == G_SL || Q->type == G_PSL || Q->type == G_PGL) {
        const field *F = Q->F; const int q = F->q;
        const uint16_t *A = Q->EL + 4 * (size_t)xq, *EL = Q->EL, *AD = F->add, *IV = F->inv;
        const uint16_t *M0 = F->mul + A[0] * q, *M1 = F->mul + A[1] * q, *M2 = F->mul + A[2] * q, *M3 = F->mul + A[3] * q;
        const int *IDXK = Q->IDXK, pgl = Q->type == G_PGL, prime = F->k == 1, half = CSL ? ncyc / 2 : 0;
        const uint8_t *IDXS = CSL ? Q->IDXS : zero_s;
        enum { BLK = 32 }; int key[BLK], zz[BLK], gg[BLK];
        for (int r0 = 0; r0 < RW; r0 += BLK) {
            int nb = RW - r0 < BLK ? RW - r0 : BLK;
            for (int u = 0; u < nb; u++) {
                int r = r0 + u; const uint16_t *B = EL + 4 * (size_t)REPWQ[r];
                int a, b, c, dd;
                if (prime) {
                    a = M0[B[0]] + M1[B[2]]; a -= a >= q ? q : 0;  b = M0[B[1]] + M1[B[3]]; b -= b >= q ? q : 0;
                    c = M2[B[0]] + M3[B[2]]; c -= c >= q ? q : 0;  dd = M2[B[1]] + M3[B[3]]; dd -= dd >= q ? q : 0;
                } else {
                    a = AD[M0[B[0]] * q + M1[B[2]]]; b = AD[M0[B[1]] * q + M1[B[3]]];
                    c = AD[M2[B[0]] * q + M3[B[2]]]; dd = AD[M2[B[1]] * q + M3[B[3]]];
                }
                int k;
                if (pgl) {
                    if (a) { const uint16_t *Mi = F->mul + IV[a] * q; k = (Mi[b] * q + Mi[c]) * q + Mi[dd]; }
                    else { const uint16_t *Mi = F->mul + IV[b] * q; k = q * q * q + Mi[c] * q + Mi[dd]; }
                } else k = a ? ((a - 1) * q + b) * q + c : (q - 1) * q * q + (b - 1) * q + dd;
                key[u] = k; _mm_prefetch((const char *)(IDXK + k), _MM_HINT_T0);
                int rz = neg && REPWZ[r] ? ncyc - REPWZ[r] : REPWZ[r];
                zz[u] = xz + rz;
            }
            for (int u = 0; u < nb; u++) {
                int z = zz[u] + (IDXS[key[u]] ? half : 0); z -= z >= ncyc ? ncyc : 0; z -= z >= ncyc ? ncyc : 0;
                gg[u] = IDXK[key[u]] * ncyc + z; _mm_prefetch((const char *)(POSW + gg[u]), _MM_HINT_T0);
            }
            for (int u = 0; u < nb; u++) EMITW(r0 + u, gg[u]);
        }
        return;
    }
    for (int r = 0; r < RW; r++) {
        int rz = neg && REPWZ[r] ? ncyc - REPWZ[r] : REPWZ[r];
        int z = xz + rz; z -= z >= ncyc ? ncyc : 0;
        EMITW(r, qmul(Q, xq, REPWQ[r]) * ncyc + z);
    }
}
static void mktab(int x, uint32_t *tf, uint32_t *ti) { if (WIDE) make_tables_w(x, tf, ti); else make_tables(x, tf, ti); }
/* bfs_fast() on wide rows; same contract.  V, NB: 4 words per row; F, Fn: 8 words per row (doubled). */
static long long bfs_w(ctx *c, uint32_t **tf, uint32_t **ti, int startB, int depth, long long cnt[2],
                       const volatile long long *bp, long long off, int strict) {
    memset(c->V[0], 0, 32 * (size_t)RW); memset(c->V[1], 0, 32 * (size_t)RW);
    memset(c->F, 0, 64 * (size_t)RW); memset(c->Fn, 0, 64 * (size_t)RW);
    __m256i *V[2] = {(__m256i *)c->V[0], (__m256i *)c->V[1]}, *NB = (__m256i *)c->NB;
    uint64_t *F = c->F, *Fn = c->Fn;
    int *fl = c->fl, *fln = c->fln, *tl = c->tl;
    uint32_t ps = POSW[ident]; int r0 = ps >> 9, b0 = ps & 511;
    { uint64_t w[4] = {0}; w[b0 >> 6] = 1ULL << (b0 & 63); V[startB][r0] = _mm256_loadu_si256((const __m256i *)w); store_dup(F + 8 * (size_t)r0, V[startB][r0]); }
    fl[0] = r0; int nf = 1, dense = 0;
    cnt[0] = cnt[1] = 0; cnt[startB] = 1;
    int side = startB; long long unc = -2; const __m256i Z = _mm256_setzero_si256();
    for (int step = 0; step < depth; step++) {
        double tq = TIMING ? now() : 0;
        uint32_t **T = side == 0 ? tf : ti, **P = side == 0 ? ti : tf; int ns = side ^ 1; __m256i *Vn = V[ns]; long long add = 0;
        int last = step == depth - 1;
        if (!dense) {
            int ntl = 0;
            for (int u = 0; u < nf; u++) {
                int r = fl[u]; uint64_t *Fr = F + 8 * (size_t)r;
                for (int s = 0; s < d; s++) {
                    uint32_t t = T[s][r], j = t & 511; int r2 = t >> 9; __m256i x = NB[r2];
                    if (!nzw(x)) tl[ntl++] = r2;
                    NB[r2] = _mm256_or_si256(x, winw(Fr, j ? nHW - j : 0));
                }
                _mm256_store_si256((__m256i *)Fr, Z); _mm256_store_si256((__m256i *)(Fr + 4), Z);
            }
            int nn = 0; __m256i pa = Z;
            for (int u = 0; u < ntl; u++) {
                int r2 = tl[u]; __m256i nw = _mm256_andnot_si256(Vn[r2], NB[r2]); NB[r2] = Z;
                if (nzw(nw)) { Vn[r2] = _mm256_or_si256(Vn[r2], nw); pa = _mm256_add_epi64(pa, popv(nw)); if (!last) { store_dup(Fn + 8 * (size_t)r2, nw); fln[nn++] = r2; } }
            }
            add = hsum(pa);
            nf = nn; int *tt = fl; fl = fln; fln = tt;
            if (nf > RW / 16) dense = 1;
        } else if (!last) {
            __m256i pa = Z;
            for (int r = 0; r < RW; r++) {
                if (PFD && r + PFD < RW) for (int s = 0; s < d; s++) _mm_prefetch((const char *)(F + 8 * (size_t)(P[s][r + PFD] >> 9)), _MM_HINT_T0);
                __m256i v = Vn[r];
                uint64_t *Fo = Fn + 8 * (size_t)r;
                if (fullw(v)) { _mm256_store_si256((__m256i *)Fo, Z); _mm256_store_si256((__m256i *)(Fo + 4), Z); continue; }
                __m256i acc = Z;
                for (int s = 0; s < d; s++) { uint32_t t = P[s][r]; acc = _mm256_or_si256(acc, winw(F + 8 * (size_t)(t >> 9), t & 511)); }
                __m256i nw = _mm256_andnot_si256(v, acc); store_dup(Fo, nw); Vn[r] = _mm256_or_si256(v, nw); pa = _mm256_add_epi64(pa, popv(nw));
            }
            add = hsum(pa);
        } else {
            /* uncovered = nHW * (rows not yet full) - covered bits in them; checked against the bound every 64 rows */
            long long lim = *bp + strict - off, nrows = 0; int npf = d < 6 ? d : 6; __m256i pa = Z;
            for (int r = 0; r < RW; r++) {
                if (PFD && r + PFD < RW) for (int s = 0; s < npf; s++) _mm_prefetch((const char *)(F + 8 * (size_t)(P[s][r + PFD] >> 9)), _MM_HINT_T0);
                __m256i cov = Vn[r];
                if (fullw(cov)) continue;
                for (int s = 0; s < d; s++) { uint32_t t = P[s][r]; cov = _mm256_or_si256(cov, winw(F + 8 * (size_t)(t >> 9), t & 511)); if (fullw(cov)) break; }
                Vn[r] = cov; nrows++; pa = _mm256_add_epi64(pa, popv(cov));
                if (!(nrows & 63)) { long long u0 = nrows * nHW - hsum(pa); lim = *bp + strict - off;
                    if (u0 >= lim) { c->F = F; c->Fn = Fn; return -1; } }
            }
            unc = nrows * nHW - hsum(pa);
            if (unc >= *bp + strict - off) { c->F = F; c->Fn = Fn; return -1; }
        }
        if (unc >= 0) cnt[ns] = N - unc; else cnt[ns] += add;
        if (step < 64) c->lev[step] = cnt[ns];
        uint64_t *t2 = F; F = Fn; Fn = t2; side = ns;
        if (TIMING && step < 64) { TLEV[step] += now() - tq; NLEV[step]++; }
    }
    c->F = F; c->Fn = Fn;
    return N - cnt[side];
}
static long long cost_w(ctx *c, uint32_t **tf, uint32_t **ti, double *sec, uint64_t **save, const volatile long long *bp, int strict) {
    long long cnt[2]; int L = D - 4; size_t nb = 32 * (size_t)RW;
    if (D % 2 == 0) { long long u = bfs_w(c, tf, ti, 0, D - 1, cnt, bp, 0, strict); if (u < 0) return -1;
        *sec = L >= 0 ? (double)(N - c->lev[L]) / N : 0; if (save) memcpy(save[0], c->V[1], nb); return u; }
    long long u1 = bfs_w(c, tf, ti, 0, D - 1, cnt, bp, 0, strict); if (u1 < 0) return -1;
    *sec = L >= 0 ? (double)(N - c->lev[L]) / N : 0;
    if (save) memcpy(save[0], c->V[0], nb);
    long long u2 = bfs_w(c, tf, ti, 1, D - 1, cnt, bp, u1, strict); if (u2 < 0) return -1;
    if (L >= 0) *sec += (double)(N - c->lev[L]) / N;
    if (save) memcpy(save[1], c->V[1], nb);
    return u1 + u2;
}
static int full_check_w(ctx *c) {
    long long cnt[2];
    bfs_w(c, TF, TI, 0, D, cnt, &NOBOUND, 0, 0); if (cnt[0] != N || cnt[1] != N) return 0;
    bfs_w(c, TF, TI, 1, D, cnt, &NOBOUND, 0, 0); return cnt[0] == N && cnt[1] == N;
}
static int cmpint(const void *a, const void *b) { int x = *(const int *)a, y = *(const int *)b; return (x > y) - (x < y); }
/* scan_unc() for a wide bitset, producing exactly the list scan_unc() would produce for the same coverage */
static void scan_unc_w(int t, const uint64_t *Vw, int startB, int sd) {
    long long seen = 0; int n = 0;
    for (int r = 0; r < RW && seen <= UCAP; r++)
        for (int k = 0; k < 4; k++) {
            uint64_t z = ~Vw[4 * (size_t)r + k] & MASKWA[k];
            while (z) { int b = 64 * k + __builtin_ctzll(z); z &= z - 1;
                if (seen < UCAP) UNC[t][n++] = POS[gmul(REPW[r], HPW[b])];
                seen++; }
        }
    if (seen <= UCAP) { qsort(UNC[t], n, sizeof(int), cmpint); nst[t] = n; ntrue[t] = seen; ust[t] = startB; uside[t] = sd; return; }
    /* more than UCAP uncovered: replay haar_gen3's reservoir sampling in its own row order (O(N) products; rare) */
    seen = 0; n = 0;
    for (int r = 0; r < R; r++) for (int b = 0; b < nH; b++) {
        uint32_t pw = POSW[gmul(REP[r], HP[b])];
        if ((Vw[4 * (size_t)(pw >> 9) + ((pw & 511) >> 6)] >> (pw & 63)) & 1) continue;
        int code = r * 64 + b;
        if (n < UCAP) UNC[t][n++] = code;
        else { unsigned long long j = rnd() % (unsigned long long)(seen + 1); if (j < (unsigned long long)UCAP) UNC[t][j] = code; }
        seen++;
    }
    nst[t] = n; ntrue[t] = seen; ust[t] = startB; uside[t] = sd;
}
static uint32_t AVOIDMASK = 0;   /* orbit mode: generators the targeted walks must not use (besides avoid) */
static int walk(int g, int *side, int len, int avoid) {
    for (int s = 0; s < len; s++) {
        int j; do j = rnd() % d; while (j == avoid || ((AVOIDMASK >> j) & 1));
        g = (*side == 0) ? gmul(S[j], g) : gmul(SI[j], g);
        *side ^= 1;
    }
    return g;
}
static int targeted(int i) {
    long long tot = 0; for (int t = 0; t < nlists; t++) tot += ntrue[t];
    if (tot == 0) return -1;
    long long z = rnd() % tot; int t = 0; while (z >= ntrue[t]) { z -= ntrue[t]; t++; }
    if (nst[t] == 0) return -1;
    int code = UNC[t][rnd() % nst[t]];
    int u = gmul(REP[code >> 6], HP[code & 63]);
    for (int tries = 0; tries < 20; tries++) {
        int a = rnd() % (D - 1), b = rnd() % (D - 1 - a);
        int sp = ust[t], sq = uside[t];
        int P = walk(ident, &sp, a, i), Qv = walk(u, &sq, b, i);
        if (sp == sq) continue;
        int gA = sp == 0 ? P : Qv, hB = sp == 0 ? Qv : P;
        return gmul(hB, ginv(gA));
    }
    return -1;
}
static int used(int x, int skip) { for (int i = 0; i < d; i++) if (i != skip && S[i] == x) return 1; return 0; }
static volatile int stop_flag = 0;
static void on_term(int s) { (void)s; stop_flag = 1; }

static void desc_elem(int x, char *buf) {
    char qb[400]; qdesc(Q, x / ncyc, qb);
    if (qb[0]) sprintf(buf, "%d %s z=%d", x, qb, x % ncyc); else sprintf(buf, "%d z=%d", x, x % ncyc);
}

static int cmpll(const void *a, const void *b) { long long x = *(const long long *)a, y = *(const long long *)b; return (x > y) - (x < y); }

/* ---------------- ORBIT mode: S = {e} + fixed generators + alpha-orbits ---------------- */
static int OK_ = 0, OM = 0, OF = 0;                 /* orbit size k, number of orbits m, fixed generators f (incl. e) */
static int AQ = -1, AQI = -1, AR = 1, AHA = 0, AHB = 0, AMU = 0, AFROB = 0;   /* AFROB = j: entries x -> x^(p^j) */
static uint16_t *FROBT;   /* AMU: meta scaling (a,j) -> (u a, j) */
static int *FIXL; static long long NFIX;            /* elements fixed by alpha, except e */
static int *FIXG; static long long NFIXG;           /* those eligible as fixed generators (FIXMIN) */
static int alpha(int x) {
    int xq = x / ncyc, z = x % ncyc, yq;
    if (Q->type == G_HEIS && (AHA || AHB)) {
        const field *F = Q->F; int q = F->q, a = xq / (q * q), b = xq / q % q, c = xq % q;
        yq = (FMUL(F, AHA, a) * q + FMUL(F, AHB, b)) * q + FMUL(F, FMUL(F, AHA, AHB), c);
    } else if (AFROB) { const uint16_t *E = Q->EL + 4 * (size_t)xq; yq = Q->IDXK[mkey(Q, FROBT[E[0]], FROBT[E[1]], FROBT[E[2]], FROBT[E[3]])]; }
    else if (Q->type == G_META && AMU) yq = (int)((long long)AMU * (xq / Q->k) % Q->m) * Q->k + xq % Q->k;
    else yq = AQ >= 0 ? qmul(Q, qmul(Q, AQ, xq), AQI) : xq;
    return yq * ncyc + (int)((long long)AR * z % ncyc);
}
static int orbit_of(int x, int *o) {   /* o[i] = alpha^i(x); 1 iff the orbit of x has exactly k elements */
    o[0] = x; for (int i = 1; i < OK_; i++) { o[i] = alpha(o[i - 1]); if (o[i] == x) return 0; }
    return alpha(o[OK_ - 1]) == x;
}
static inline int ostart(int j) { return OF + j * OK_; }
static int orbit_free(const int *o, int j) {        /* orbit o is disjoint from S outside orbit slot j */
    for (int i = 0; i < OK_; i++) for (int u = 0; u < d; u++) {
        if (j >= 0 && u >= ostart(j) && u < ostart(j) + OK_) continue;
        if (S[u] == o[i]) return 0;
    }
    return 1;
}
static double Wwords(int dd, int DD) {
    double w = 0;
    if (DD % 2) { int k = (DD - 1) / 2; w = 1; for (int i = 1; i <= k; i++) w += dd * pow(dd - 1, 2 * i - 1); }
    else { int k = DD / 2; for (int i = 0; i < k; i++) w += dd * pow(dd - 1, 2 * i); }
    return w;
}
static long long ipow_mod(long long b, long long e, long long m) { long long r = 1 % m; b %= m; while (e) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; } return r; }
static int gcdi(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a < 0 ? -a : a; }
static void scan_fix(void) {
    NFIX = 0; FIXL = malloc(sizeof(int) * 1024 * 1024); long long cap = 1024 * 1024;
    for (int x = 0; x < N; x++) if (x != ident && alpha(x) == x) { if (NFIX == cap) { cap *= 2; FIXL = realloc(FIXL, sizeof(int) * cap); } FIXL[NFIX++] = x; }
}
/* choose alpha of order k: r on Z_n with the fewest fixed points, then a conjugating element (or heis scaling) */
static int choose_alpha(void) {
    int k = OK_;
    if (getenv("AR")) AR = atoi(getenv("AR"));
    else if (ncyc > 1) {
        int best = -1, bfix = 1 << 30;
        for (int r = 1; r < ncyc; r++) {
            if (gcdi(r, ncyc) != 1 || ipow_mod(r, k, ncyc) != 1) continue;
            int fx = gcdi(r - 1, ncyc); if (r == 1) fx = ncyc;
            if (fx < bfix) { bfix = fx; best = r; }
        }
        AR = best < 0 ? 1 : best;
    } else AR = 0;
    int ordr = 1; if (ncyc > 1) { long long y = AR % ncyc; while (y != 1 % ncyc) { y = y * AR % ncyc; ordr++; } }
    if (Q->type == G_HEIS) {
        const field *F = Q->F; int q = F->q;
        if (getenv("AHA")) { AHA = atoi(getenv("AHA")); AHB = getenv("AHB") ? atoi(getenv("AHB")) : AHA; }
        else {   /* zeta of order k in GF(q)*, a = zeta, b = zeta (then ab = zeta^2); k = 2: a = -1, b = 1 */
            int zeta = -1;
            for (int g = 2; g < q && zeta < 0; g++) { int y = g, o = 1; while (y != 1) { y = FMUL(F, y, g); o++; } if (o == k) zeta = g; }
            if (k == 2) { AHA = F->neg[1]; AHB = 1; }
            else if (zeta < 0) { fprintf(stderr, "no element of order %d in GF(%d)*\n", k, q); return 0; }
            else { AHA = zeta; AHB = zeta; }
        }
        fprintf(stderr, "alpha: heis scaling a=%d b=%d, z -> %d z on Z_%d (order %d)\n", AHA, AHB, AR, ncyc, ordr);
        return 1;
    }
    if (getenv("AFROB")) {   /* field automorphism x -> x^(p^j) of GF(p^e), order e/gcd(e,j); matrix groups only */
        if (!(Q->type == G_SL || Q->type == G_PSL || Q->type == G_PGL) || Q->F->k == 1) { fprintf(stderr, "AFROB needs sl/psl/pgl over GF(p^e), e > 1\n"); return 0; }
        const field *F = Q->F; int e = F->k, j = atoi(getenv("AFROB")); AFROB = j;
        if (e / gcdi(e, j) != k) { fprintf(stderr, "Frobenius^%d has order %d, not %d\n", j, e / gcdi(e, j), k); return 0; }
        FROBT = malloc(2 * (size_t)F->q);
        for (int x = 0; x < F->q; x++) { int y = 1; for (int t = 0; t < j; t++) for (int u = 0; u < F->p; u++) ; int pw = 1; for (int t = 0; t < j; t++) pw *= F->p;
            y = 1; for (int t = 0; t < pw; t++) y = FMUL(F, y, x); FROBT[x] = (uint16_t)(x ? y : 0); }
        fprintf(stderr, "alpha: Frobenius x -> x^%d on entries, z -> %d z on Z_%d\n", (int)pow(F->p, j), AR, ncyc);
        return 1;
    }
    if (Q->type == G_META && !getenv("ALPHA")) {   /* (a,j) -> (u a, j), u of order k mod m with the fewest fixed a */
        int m = Q->m, best = -1, bfix = 1 << 30;
        if (getenv("AMU")) best = atoi(getenv("AMU"));
        else for (int u = 2; u < m; u++) {
            if (gcdi(u, m) != 1 || ipow_mod(u, k, m) != 1) continue;
            int o = 1; long long y = u; while (y != 1) { y = y * u % m; o++; }
            int l = o / gcdi(o, ordr) * ordr; if (l != k) continue;
            int fx = gcdi(u - 1, m); if (fx < bfix) { bfix = fx; best = u; }
        }
        if (best > 0) { AMU = best; fprintf(stderr, "alpha: meta scaling a -> %d a, z -> %d z on Z_%d\n", AMU, AR, ncyc); return 1; }
        fprintf(stderr, "meta: no scaling of order %d; trying conjugation\n", k);
    }
    if (getenv("ALPHA1ONLY") && Q->type == G_PROD) {   /* c5: alpha = conj by (a1, e) on prod G1 x G2: trivial on G2 */
        int o2 = Q->g2->order, i1 = -1; grp *G1 = Q->g1;
        for (int x = 0; x < G1->order && i1 < 0; x++) { int y = x, o = 1; while (y != G1->ident && o <= 3) { y = qmul(G1, y, x); o++; } if (o == 3 && y == G1->ident) i1 = x; }
        if (i1 < 0) { fprintf(stderr, "ALPHA1ONLY: no element of order 3 in the first factor\n"); return 0; }
        AQ = i1 * o2 + Q->g2->ident; AQI = qinv(Q, AQ); char b[400]; qdesc(Q, AQ, b);
        fprintf(stderr, "alpha: conj by %s (index %d): order 3 on the first factor, trivial on the second; z -> %d z\n", b, AQ, AR);
        return 1;
    }
    if (getenv("ALPHA")) { AQ = !strcmp(getenv("ALPHA"), "e") ? Q->ident : atoi(getenv("ALPHA"));
        if (AQ < 0 || AQ >= Q->order) { fprintf(stderr, "ALPHA out of range (0..%d or e)\n", Q->order - 1); return 0; }
        AQI = qinv(Q, AQ); }
    else {
        unsigned long long sv = rs; rs = 0xC0FFEEULL; int test[6]; for (int u = 0; u < 6; u++) test[u] = rnd() % Q->order;
        int found = -1;
        for (int t = 0; t < 20000 && found < 0; t++) {
            int g = rnd() % Q->order, gi = qinv(Q, g), cur[6], ord = 0; memcpy(cur, test, sizeof cur);
            for (int j = 1; j <= k; j++) {
                int same = 1; for (int u = 0; u < 6; u++) { cur[u] = qmul(Q, qmul(Q, g, cur[u]), gi); if (cur[u] != test[u]) same = 0; }
                if (same) { ord = j; break; }
            }
            if (!ord) continue;
            int l = ord / gcdi(ord, ordr) * ordr;
            if (l == k && (ord == k || ordr == k)) found = g;
        }
        rs = sv;
        if (found < 0) { fprintf(stderr, "no conjugation of order dividing %d found\n", k); return 0; }
        AQ = found; AQI = qinv(Q, AQ);
    }
    char b[400]; qdesc(Q, AQ, b);
    fprintf(stderr, "alpha: conj by %s (index %d), z -> %d z on Z_%d\n", b, AQ, AR, ncyc);
    return 1;
}
static long long cost_any(ctx *c, uint32_t **tf, uint32_t **ti, double *sec, uint64_t **save, const volatile long long *bp, int strict) {
    return WIDE ? cost_w(c, tf, ti, sec, save, bp, strict) : cost_fast(c, tf, ti, sec, save, bp, strict);
}
static int random_orbit(int j, int *o) {   /* random valid orbit for slot j (or -1: any) */
    for (int tries = 0; tries < 100000; tries++) { int x = rnd() % N; if (orbit_of(x, o) && orbit_free(o, j)) return 1; }
    return 0;
}
/* ORBW=w: an uncovered alpha-fixed element weighs w instead of 1 (w = k: every uncovered alpha-orbit counts 1).
 * Integer energy c + (w-1) * (uncovered fixed elements) >= c, so the early abort on the raw count stays exact. */
static int ORBW = 1;
static long long fixmiss(uint64_t **sv) {
    long long m = 0;
    for (int t = 0; t < (D % 2 ? 2 : 1); t++) {
        const uint64_t *V = sv[t];
        for (long long i = -1; i < NFIX; i++) { int g = i < 0 ? ident : FIXL[i], cov;
            if (WIDE) { uint32_t pw = POSW[g]; cov = (V[4 * (size_t)(pw >> 9) + ((pw & 511) >> 6)] >> (pw & 63)) & 1; }
            else { int ps = POS[g]; cov = (V[ps >> 6] >> (ps & 63)) & 1; }
            m += !cov; }
    }
    return m;
}
/* full diameter check of the current S; f = 0: normalise to S s_0^-1 (an isomorphic Haar graph, (g,A) -> (s_0 g, A))
 * so that the first generator is e, and check again; then write the solution file.  Returns 1 iff written. */
static int check_and_write(ctx *c0, const char *out) {
    int ok = WIDE ? full_check_w(c0) : full_check(c0);
    printf("full diameter check: %s\n", ok ? "OK" : "FAIL");
    if (!ok) return 0;
    if (S[0] != ident) { int a0 = ginv(S[0]); for (int i = 0; i < d; i++) S[i] = gmul(S[i], a0);
        for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
        int ok2 = WIDE ? full_check_w(c0) : full_check(c0); printf("full diameter check after normalising s_0 = e: %s\n", ok2 ? "OK" : "FAIL");
        if (!ok2) return 0; }
    FILE *f = fopen(out, "w");
    if (!f) { perror(out); return 0; }
    fprintf(f, "%d %d %s n %d N %d\n", d, D, Q->spec, ncyc, N);
    for (int i = 0; i < d; i++) { char buf[1000]; desc_elem(S[i], buf); fprintf(f, "%s\n", buf); }
    fclose(f); printf("wrote %s\n", out);
    return 1;
}
/* INVPAIR=1 (cell-10-8 session): S = {e} + O + O^-1 + I, where O is an alpha-orbit, O^-1 its inverses (slots 4..6 hold
 * the inverses of slots 1..3) and I an alpha-orbit of involutions (slots 7..9). S is inverse-closed, so the odd words
 * are closed under inversion and the uncovered set is invariant under <alpha, x -> x^-1> (orbits of 6). */
static int INVP = 0, *INVL, NINV = 0;
/* INVPAIR=2: the pairing is iota(x) = beta(x)^-1 with beta an outer involution of the first (PSL/SL) factor of a prod
 * group, commuting with alpha, trivial on the second factor and on Z_n; then S^-1 = beta(S) and the uncovered set is
 * invariant under <alpha, iota>. */
static int *BETA1 = NULL;
static int *BETA2 = NULL;   /* c5: involutory automorphism of the second factor (BETA2SEARCH), else identity */
static int iota_x(int x) {
    if (INVP != 2) return ginv(x);
    int xq = x / ncyc, z = x % ncyc;
    if (Q->type == G_PSL) return ginv(BETA1[xq] * ncyc + z);     /* c5: plain PSL(2,q) x Z_n */
    int o2 = Q->g2->order;
    int y2 = BETA2 ? BETA2[xq % o2] : xq % o2;
    return ginv((BETA1[xq / o2] * o2 + y2) * ncyc + z);
}
/* c5: plain PSL(2,q) x Z_n: beta = conj(M) (M in GL(2,q), any determinant, M not scalar, M^2 scalar) commuting with
 * alpha on PSL. An outer M never commutes with alpha on PSL(2,23) x Z_97 (see NOTES.md), so the inner involution is found. */
/* c5: perm[x] = index of M x M^-1 on G (M a 2x2 matrix over the field of G); 0 if some image is not in G */
static int conj_perm(const grp *G, const int *M, int *perm) {
    const field *F = G->F; int a = M[0], b = M[1], c = M[2], dd = M[3];
    int det = FADD(F, FMUL(F, a, dd), F->neg[FMUL(F, b, c)]); if (!det) return 0;
    int idet = F->inv[det]; int adj[4] = { dd, F->neg[b], F->neg[c], a };
    for (int x = 0; x < G->order; x++) { const uint16_t *E = G->EL + 4 * (size_t)x;
        int T[4] = { FADD(F, FMUL(F, a, E[0]), FMUL(F, b, E[2])), FADD(F, FMUL(F, a, E[1]), FMUL(F, b, E[3])),
                     FADD(F, FMUL(F, c, E[0]), FMUL(F, dd, E[2])), FADD(F, FMUL(F, c, E[1]), FMUL(F, dd, E[3])) };
        int R[4] = { FADD(F, FMUL(F, T[0], adj[0]), FMUL(F, T[1], adj[2])), FADD(F, FMUL(F, T[0], adj[1]), FMUL(F, T[1], adj[3])),
                     FADD(F, FMUL(F, T[2], adj[0]), FMUL(F, T[3], adj[2])), FADD(F, FMUL(F, T[2], adj[1]), FMUL(F, T[3], adj[3])) };
        for (int i = 0; i < 4; i++) R[i] = FMUL(F, R[i], idet);
        int y = G->IDXK[mkey(G, R[0], R[1], R[2], R[3])]; if (y < 0 || y >= G->order) return 0; perm[x] = y; }
    return 1;
}
/* c5 BETA2SEARCH=1: beta2 = conj(M) on the second factor, M an involution of PGL(2,q2) (M^2 scalar, not scalar), chosen
 * among random candidates to minimise the iota-fixed set F2 = {h : beta2(h) = h^-1} and, first of all, the number of
 * involutions in F2 (an iota-fixed letter that is an involution makes words collide: see NOTES.md). */
static int beta2_search(void) {
    grp *G2 = Q->g2; const field *F2 = G2->F; int q2 = F2->q;
    if (!(G2->type == G_PSL || G2->type == G_SL || G2->type == G_PGL)) { fprintf(stderr, "BETA2SEARCH needs a matrix second factor\n"); return 0; }
    int *perm = malloc(sizeof(int) * (size_t)G2->order), *bestp = malloc(sizeof(int) * (size_t)G2->order);
    long long bestscore = LLONG_MAX; int bestM[4] = {0, 0, 0, 0}, valid = 0, tries = getenv("B2TRIES") ? atoi(getenv("B2TRIES")) : 300;
    for (long long it = 0; it < 100000000LL && valid < tries; it++) {
        int M[4]; for (int i = 0; i < 4; i++) M[i] = rnd() % q2;
        int M2[4] = { FADD(F2, FMUL(F2, M[0], M[0]), FMUL(F2, M[1], M[2])), FADD(F2, FMUL(F2, M[0], M[1]), FMUL(F2, M[1], M[3])),
                      FADD(F2, FMUL(F2, M[2], M[0]), FMUL(F2, M[3], M[2])), FADD(F2, FMUL(F2, M[2], M[1]), FMUL(F2, M[3], M[3])) };
        if (M2[1] || M2[2] || M2[0] != M2[3]) continue;                 /* M^2 scalar */
        if (M[1] == 0 && M[2] == 0 && M[0] == M[3]) continue;           /* scalar */
        if (!conj_perm(G2, M, perm)) continue;
        if (getenv("INVERTING") && perm[AQ % Q->g2->order] != qinv(G2, AQ % Q->g2->order)) continue;   /* inverts alpha's second factor */
        valid++;
        long long nfix = 0, ninv = 0;
        for (int x = 0; x < G2->order; x++) if (perm[x] == qinv(G2, x)) { nfix++; if (x != G2->ident && qmul(G2, x, x) == G2->ident) ninv++; }
        long long score = ninv * 1000000LL + nfix;
        if (score < bestscore) { bestscore = score; memcpy(bestM, M, sizeof bestM); memcpy(bestp, perm, sizeof(int) * (size_t)G2->order); }
    }
    if (valid == 0) { fprintf(stderr, "BETA2SEARCH: no involution found\n"); return 0; }
    BETA2 = bestp;
    long long nfix = bestscore % 1000000LL, ninv = bestscore / 1000000LL;
    fprintf(stderr, "BETA2SEARCH: %d candidates; beta2 = conj(mat(%d,%d,%d,%d)); iota-fixed in factor 2: %lld, of them involutions: %lld\n",
            valid, bestM[0], bestM[1], bestM[2], bestM[3], nfix, ninv);
    free(perm);
    return 1;
}
static int setup_beta(void) {
    int plain = Q->type == G_PSL;
    if (!plain && (Q->type != G_PROD || !(Q->g1->type == G_PSL || Q->g1->type == G_SL))) { fprintf(stderr, "INVPAIR=2 needs prod with a psl/sl first factor\n"); return 0; }
    grp *G1 = plain ? Q : Q->g1; const field *F = G1->F; int q = F->q, o2 = plain ? 1 : Q->g2->order, h1 = AQ / o2;
    const uint16_t *H = G1->EL + 4 * (size_t)h1;
    char *sq = calloc(q, 1); for (int v = 1; v < q; v++) sq[FMUL(F, v, v)] = 1;
    for (int m = 0; m < q * q * q * q; m++) {
        int a = m / (q * q * q), b = m / (q * q) % q, c = m / q % q, dd = m % q;
        int det = FADD(F, FMUL(F, a, dd), F->neg[FMUL(F, b, c)]);
        if (!det || (!plain && !getenv("INVERTING") && sq[det])) continue;   /* outer: non-square determinant (prod); plain: any */
        if (plain && b == 0 && c == 0 && a == dd) continue;   /* scalar M: beta = identity */
        /* M H and H M */
        int MH[4] = { FADD(F, FMUL(F, a, H[0]), FMUL(F, b, H[2])), FADD(F, FMUL(F, a, H[1]), FMUL(F, b, H[3])),
                      FADD(F, FMUL(F, c, H[0]), FMUL(F, dd, H[2])), FADD(F, FMUL(F, c, H[1]), FMUL(F, dd, H[3])) };
        int HM[4] = { FADD(F, FMUL(F, H[0], a), FMUL(F, H[1], c)), FADD(F, FMUL(F, H[0], b), FMUL(F, H[1], dd)),
                      FADD(F, FMUL(F, H[2], a), FMUL(F, H[3], c)), FADD(F, FMUL(F, H[2], b), FMUL(F, H[3], dd)) };
        int okp = 1, okm = 1; for (int i = 0; i < 4; i++) { if (MH[i] != HM[i]) okp = 0; if (MH[i] != F->neg[HM[i]]) okm = 0; }
        if (!getenv("INVERTING") && !okp && !(okm && G1->type == G_PSL)) continue;   /* INVERTING: beta alpha beta^-1 = alpha^-1 (checked below) */
        /* M^2 scalar */
        int M2[4] = { FADD(F, FMUL(F, a, a), FMUL(F, b, c)), FADD(F, FMUL(F, a, b), FMUL(F, b, dd)),
                      FADD(F, FMUL(F, c, a), FMUL(F, dd, c)), FADD(F, FMUL(F, c, b), FMUL(F, dd, dd)) };
        if (M2[1] || M2[2] || M2[0] != M2[3]) continue;
        int idet = F->inv[det], adj[4] = { dd, F->neg[b], F->neg[c], a };
        BETA1 = malloc(sizeof(int) * G1->order); int bad = 0;
        for (int x = 0; x < G1->order && !bad; x++) { const uint16_t *E = G1->EL + 4 * (size_t)x;
            int T[4] = { FADD(F, FMUL(F, a, E[0]), FMUL(F, b, E[2])), FADD(F, FMUL(F, a, E[1]), FMUL(F, b, E[3])),
                         FADD(F, FMUL(F, c, E[0]), FMUL(F, dd, E[2])), FADD(F, FMUL(F, c, E[1]), FMUL(F, dd, E[3])) };
            int R[4] = { FADD(F, FMUL(F, T[0], adj[0]), FMUL(F, T[1], adj[2])), FADD(F, FMUL(F, T[0], adj[1]), FMUL(F, T[1], adj[3])),
                         FADD(F, FMUL(F, T[2], adj[0]), FMUL(F, T[3], adj[2])), FADD(F, FMUL(F, T[2], adj[1]), FMUL(F, T[3], adj[3])) };
            for (int i = 0; i < 4; i++) R[i] = FMUL(F, R[i], idet);
            int y = G1->IDXK[mkey(G1, R[0], R[1], R[2], R[3])]; if (y < 0 || y >= G1->order) bad = 1; else BETA1[x] = y; }
        if (bad) { free(BETA1); BETA1 = NULL; continue; }
        int ok = 1;
        for (int t = 0; t < 2000 && ok; t++) { int u = rnd() % G1->order, v = rnd() % G1->order;
            if (BETA1[qmul(G1, u, v)] != qmul(G1, BETA1[u], BETA1[v])) ok = 0;
            if (BETA1[BETA1[u]] != u) ok = 0;
            if (getenv("INVERTING")) { if (BETA1[qmul(G1, qmul(G1, h1, u), qinv(G1, h1))] != qmul(G1, qmul(G1, qinv(G1, h1), BETA1[u]), h1)) ok = 0; }
            else if (BETA1[qmul(G1, qmul(G1, h1, u), qinv(G1, h1))] != qmul(G1, qmul(G1, h1, BETA1[u]), qinv(G1, h1))) ok = 0; }
        if (!ok) { free(BETA1); BETA1 = NULL; continue; }
        if (!plain && getenv("BETA2SEARCH") && !beta2_search()) { free(sq); return 0; }
        fprintf(stderr, "INVPAIR=2: beta = conjugation by mat(%d,%d,%d,%d) (det %d, non-square) on the first factor\n", a, b, c, dd, det);
        free(sq); return 1;
    }
    fprintf(stderr, "INVPAIR=2: no outer involution commuting with alpha found\n"); free(sq); return 0;
}
static int inv_pair_from(int x, int which, int *o6) {   /* x in orbit slot `which` (0: O, 1: O^-1); o6 = O, O^-1 */
    int o[MAXD]; if (x < 0 || x == ident || !orbit_of(x, o)) return 0;
    for (int i = 0; i < 3; i++) { int y = iota_x(o[i]); if (which == 0) { o6[i] = o[i]; o6[3 + i] = y; } else { o6[i] = y; o6[3 + i] = o[i]; } }
    for (int i = 0; i < 6; i++) { if (o6[i] == ident) return 0; for (int u = 0; u < i; u++) if (o6[u] == o6[i]) return 0;
        for (int u = 0; u < d; u++) if ((u < 1 || u >= 7) && S[u] == o6[i]) return 0; }
    return 1;
}
static void inv_random(int *o3) { int x = INVL[rnd() % NINV]; o3[0] = x; o3[1] = alpha(x); o3[2] = alpha(o3[1]); }
static int inv_free(const int *o3) { for (int i = 0; i < 3; i++) for (int u = 0; u < 7; u++) if (S[u] == o3[i]) return 0; return 1; }
static void invpair_random_S(void) {
    int o6[6], o3[3];
    for (int u = 1; u < d; u++) S[u] = -1 - u;
    inv_random(o3); for (int i = 0; i < 3; i++) S[7 + i] = o3[i];
    while (!inv_pair_from(rnd() % N, 0, o6)) ;
    for (int i = 0; i < 6; i++) S[1 + i] = o6[i];
}
/* ---------------- c5 additions (handsoff-108, c5-selfdual) ---------------- */
static int in_set(const int *T, int n, int x) { for (int i = 0; i < n; i++) if (T[i] == x) return 1; return 0; }
/* S is closed under alpha and iota; alpha, iota commute; iota is an anti-automorphism with iota^2 = 1 */
static int verify_S_sym(void) {
    int ok = 1;
    for (int u = 0; u < d; u++) {
        if (!in_set(S, d, alpha(S[u]))) ok = 0;
        if (!in_set(S, d, iota_x(S[u]))) ok = 0;
    }
    for (int t = 0; t < 3000; t++) {
        int x = rnd() % N, y = rnd() % N;
        if (iota_x(gmul(x, y)) != gmul(iota_x(y), iota_x(x))) ok = 0;
        if (iota_x(iota_x(x)) != x) ok = 0;
        if (getenv("INVERTING")) { if (iota_x(alpha(x)) != alpha(alpha(iota_x(x)))) ok = 0; }
        else if (iota_x(alpha(x)) != alpha(iota_x(x))) ok = 0;
        if (alpha(gmul(x, y)) != gmul(alpha(x), alpha(y))) ok = 0;
    }
    return ok;
}
/* uncovered B-side elements of a saved bitset (cost_fast save[0] for even D): counts, and whether the uncovered set is
 * invariant under iota and alpha (the symmetry the family is built for) */
static void verify_unc(const uint64_t *Vb) {
    long long nu = 0, nfix = 0, bad_i = 0, bad_a = 0, nfixu = 0;
    for (int g = 0; g < N; g++) {
        int ps = POS[g]; if ((Vb[ps >> 6] >> (ps & 63)) & 1) continue;
        nu++; if (iota_x(g) == g) nfixu++;
        int h = iota_x(g); ps = POS[h]; if ((Vb[ps >> 6] >> (ps & 63)) & 1) bad_i++;
        h = alpha(g); ps = POS[h]; if ((Vb[ps >> 6] >> (ps & 63)) & 1) bad_a++;
    }
    for (int g = 0; g < N; g++) if (iota_x(g) == g && g != ident) nfix++;
    fprintf(stderr, "verify: uncovered %lld (iota-fixed among them %lld; iota-fixed elements of G %lld), iota-violations %lld, alpha-violations %lld\n",
            nu, nfixu, nfix, bad_i, bad_a);
}

/* diagnostics (VERIFYGEN=1): size of the subgroup <S>, and for each Q-element the number of covered Z-values */
static void diag_gen_zcov(const uint64_t *Vb) {
    char *in = calloc(N, 1); int *qu = malloc(sizeof(int) * (size_t)N); long long h = 0, t = 0;
    in[ident] = 1; qu[t++] = ident;
    while (h < t) { int x = qu[h++]; for (int u = 0; u < d; u++) { int y = gmul(x, S[u]); if (!in[y]) { in[y] = 1; qu[t++] = y; } } }
    fprintf(stderr, "diag: |<S>| = %lld of N = %d\n", t, N);
    long long hist[1024] = {0};
    for (int xq = 0; xq < Q->order; xq++) { int c = 0;
        for (int z = 0; z < ncyc; z++) { int g = xq * ncyc + z; int ps = POS[g]; c += (Vb[ps >> 6] >> (ps & 63)) & 1; }
        hist[c * 1023 / ncyc]++; }
    fprintf(stderr, "diag: Q-elements by covered fraction of their Z-fibre (bins of 1/1023 * count):");
    for (int b = 0; b < 1024; b++) if (hist[b]) fprintf(stderr, " [%d]:%lld", b, hist[b]);
    fprintf(stderr, "\n");
    free(in); free(qu);
}

/* diagnostics (VERIFYCOLL=1): distinct elements of the odd non-backtracking alternating words of length 1,3,5,7 */
static char *COLLBM; static long long COLLCNT[8];
static void coll_rec(int len, int pos, int last, int el) {
    if (pos == len) { COLLCNT[len] += 0; return; }
    (void)last; (void)el;
}
static void diag_collisions(void) {
    COLLBM = calloc(N, 1);
    for (int L = 1; L <= 7; L += 2) {
        memset(COLLBM, 0, N); long long words = 0, distinct = 0;
        int idx[8]; int stack_el[8];
        /* iterative enumeration over letter indices idx[0..L-1], no two consecutive equal */
        for (int u = 0; u < d; u++) idx[0] = u;
        /* recursive via explicit counters */
        long long total = 1; for (int i = 0; i < L; i++) total *= 1; (void)total;
        int cnt[8] = {0}; int depth = 0; idx[0] = -1;
        /* generate all sequences in lexicographic order with non-backtracking constraint */
        int pos = 0; idx[0] = -1;
        while (pos >= 0) {
            idx[pos]++;
            if (idx[pos] >= d) { idx[pos] = -1; pos--; continue; }
            if (pos > 0 && idx[pos] == idx[pos - 1]) continue;
            if (pos == L - 1) {
                int e = ident;
                for (int i = 0; i < L; i++) e = gmul(e, (i & 1) ? SI[idx[i]] : S[idx[i]]);
                words++; if (!COLLBM[e]) { COLLBM[e] = 1; distinct++; }
                continue;
            }
            pos++; idx[pos] = -1;
        }
        (void)cnt; (void)depth; (void)stack_el;
        fprintf(stderr, "diag collisions: odd words length %d: %lld words, %lld distinct elements\n", L, words, distinct);
    }
    free(COLLBM);
}

/* diagnostics (VERIFYCOLL3=1): length-3 odd words that collide, as letter slots (0 = e, 1-3 O, 4-6 iota O, 7-9 F3) */
static void diag_coll3(void) {
    int *first = malloc(sizeof(int) * (size_t)N); for (int g = 0; g < N; g++) first[g] = -1;
    int idx[3]; int shown = 0; long long pairs[8][8] = {{0}}; (void)pairs;
    for (idx[0] = 0; idx[0] < d; idx[0]++) for (idx[1] = 0; idx[1] < d; idx[1]++) for (idx[2] = 0; idx[2] < d; idx[2]++) {
        if (idx[1] == idx[0] || idx[2] == idx[1]) continue;
        int e = gmul(gmul(S[idx[0]], SI[idx[1]]), S[idx[2]]);
        int code = idx[0] * 100 + idx[1] * 10 + idx[2];
        if (first[e] < 0) { first[e] = code; continue; }
        if (shown < 25) { int f = first[e];
            printf("COLL3 (%d,%d,%d) ~ (%d,%d,%d)\n", f / 100, (f / 10) % 10, f % 10, idx[0], idx[1], idx[2]); shown++; }
    }
    free(first);
}

/* diagnostics (CHKINV=1): how often x^-1 y is an involution for the pairs that collide */
static void diag_invpairs(void) {
    long long a1 = 0, a2 = 0, a3 = 0, a4 = 0;
    for (int x = 0; x < N; x++) {
        int y = alpha(x), w = iota_x(x);
        int t1 = gmul(ginv(x), y), t2 = gmul(ginv(x), w);
        if (gmul(t1, t1) == ident) a1++;      /* x^-1 alpha(x) involution */
        if (gmul(t2, t2) == ident) a2++;      /* x^-1 iota(x) involution */
        if (gmul(ginv(x), w) == ident) a3++;  /* iota(x) = x^-1 */
        if (iota_x(x) == x) a4++;
    }
    fprintf(stderr, "diag invpairs: #x with (x^-1 alpha x)^2=1: %lld; (x^-1 iota x)^2=1: %lld; iota x = x^-1: %lld; iota-fixed: %lld (of N=%d)\n", a1, a2, a3, a4, N);
}

static void diag_letter_invmat(void) {
    for (int i = 0; i < d; i++) { fprintf(stderr, "slot %d:", i);
        for (int j = 0; j < d; j++) { int y = gmul(SI[i], S[j]); fprintf(stderr, "%c", (gmul(y, y) == ident) ? (y == ident ? 'E' : '2') : '.'); }
        fprintf(stderr, "\n"); }
}
/* ENUM=1: exhaustive enumeration of the INVPAIR=2 family S = {e} + O + iota(O) + F3 (O an alpha-orbit of size 3 with
 * iota(O) disjoint from O, F3 an alpha-orbit of iota-fixed elements), each unordered pair {O, iota O} once. Every set
 * is evaluated with the early-abort cost (bound THR): costs < THR are exact, larger ones are only counted. */
typedef struct { int o[3], io[3]; } c5pair;
static void enum_family(ctx *c, const char *out) {
    long long thr = getenv("THR") ? atoll(getenv("THR")) : 40;
    char *done = calloc(N, 1);
    c5pair *LA = malloc(sizeof(c5pair) * (size_t)(N / 6 + 16)); long long nA = 0;
    int (*LF)[3] = malloc(sizeof(int) * 3 * (size_t)(N / 3 + 16)); long long nF = 0;
    long long nfixA = 0, nbad = 0;
    for (int x = 0; x < N; x++) {
        if (x == ident || done[x]) continue;
        int o[MAXD];
        if (!orbit_of(x, o)) { done[x] = 1; continue; }
        done[o[0]] = done[o[1]] = done[o[2]] = 1;
        int io[3]; for (int i = 0; i < 3; i++) io[i] = iota_x(o[i]);
        int fixed = 1; for (int i = 0; i < 3; i++) if (io[i] != o[i]) fixed = 0;
        if (fixed) { int mn = o[0]; for (int i = 1; i < 3; i++) if (o[i] < mn) mn = o[i];
            if (x == mn) { LF[nF][0] = o[0]; LF[nF][1] = o[1]; LF[nF][2] = o[2]; nF++; } continue; }
        int inter = 0; for (int i = 0; i < 3; i++) for (int j = 0; j < 3; j++) if (io[i] == o[j]) inter = 1;
        if (inter || in_set(io, 3, ident)) { nbad++; continue; }   /* iota(O) overlapping O: not in the family */
        int mo = o[0], mi = io[0]; for (int i = 1; i < 3; i++) { if (o[i] < mo) mo = o[i]; if (io[i] < mi) mi = io[i]; }
        if (mo < mi) { for (int i = 0; i < 3; i++) { LA[nA].o[i] = o[i]; LA[nA].io[i] = io[i]; } nA++; }
        nfixA += 0;
    }
    fprintf(stderr, "ENUM: %lld pair-orbits {O, iota O}, %lld iota-fixed alpha-orbits, %lld orbits with iota(O) overlapping O\n", nA, nF, nbad);
    if (getenv("ENUMMAX")) {   /* c5: random sub-sample of the pairs (partial Fisher-Yates), for speed tests */
        long long m = atoll(getenv("ENUMMAX")); if (m < nA) { for (long long i = 0; i < m; i++) { long long j = i + (long long)(rnd() % (unsigned long long)(nA - i)); c5pair tmp = LA[i]; LA[i] = LA[j]; LA[j] = tmp; } nA = m; } }
    long long hist[64] = {0}, total = 0, nabort = 0; long long best = thr; double t0 = now(), tlast = t0;
    int bestS[MAXD]; int have = 0; int s0fix = S[0];
    volatile long long bp = thr;
    int S0[MAXD]; memcpy(S0, S, sizeof S0);
    for (long long a = 0; a < nA; a++) for (long long b = 0; b < nF; b++) {
        S[0] = s0fix;
        for (int i = 0; i < 3; i++) { S[1 + i] = LA[a].o[i]; S[4 + i] = LA[a].io[i]; S[7 + i] = LF[b][i]; }
        for (int u = 1; u < d; u++) mktab(S[u], TF[u], TI[u]);
        double sc = 0; bp = best < thr ? best : thr;
        long long cst = cost_any(c, TF, TI, &sc, NULL, &bp, 0);
        total++;
        if (cst < 0) { nabort++; }
        else { if (cst < 64) hist[cst]++;
            if (cst < best || (cst == best && !have)) { best = cst; have = 1; memcpy(bestS, S, sizeof bestS); }
            if (cst <= 9) { printf("CAND cost %lld S", cst); for (int u = 0; u < d; u++) printf(" %d", S[u]); printf("\n"); fflush(stdout); }
            if (cst == 0) { printf("ENUM found cost 0 at set %lld\n", total); fflush(stdout);
                int ok = check_and_write(c, out ? out : "/dev/null"); printf("ENUM written %d\n", ok); fflush(stdout); }
        }
        if (now() - tlast > 60) { tlast = now(); fprintf(stderr, "ENUM progress %lld of %lld (%.0f s, %.0f/s) best %lld\n", total, nA * nF, tlast - t0, total / (tlast - t0), best); }
    }
    printf("ENUM done: sets %lld (pairs %lld x F3 %lld), aborted(>=%lld) %lld, best %lld, time %.1f s\n", total, nA, nF, thr, nabort, best, now() - t0);
    printf("ENUM hist (exact cost counts):"); for (int h = 0; h < 64; h++) if (hist[h]) printf(" %d:%lld", h, hist[h]); printf("\n");
    (void)S0; (void)bestS; free(done); free(LA); free(LF);
}
static int orbit_main(ctx **C, int nth, int K, double secs, const char *out) {
    if (sscanf(getenv("ORBIT"), "%d %d %d", &OK_, &OM, &OF) != 3 || OK_ < 2 || OF < 0 || OM < 1 || OF + OK_ * OM != d || OK_ > MAXD) {
        fprintf(stderr, "ORBIT=\"k m f\" needs k >= 2, m >= 1, f >= 0 (e counts when f >= 1), f + k m = d\n"); return 2; }
    if (TWIST || CSL) { fprintf(stderr, "ORBIT: plain groups only\n"); return 2; }
    if (!choose_alpha()) return 2;
    { int t[6]; for (int u = 0; u < 6; u++) t[u] = rnd() % N;   /* alpha must be a homomorphism of order dividing k */
      for (int u = 0; u < 5; u++) if (alpha(gmul(t[u], t[u + 1])) != gmul(alpha(t[u]), alpha(t[u + 1]))) { fprintf(stderr, "alpha is not an automorphism\n"); return 2; }
      for (int u = 0; u < 6; u++) { int y = t[u]; for (int i = 0; i < OK_; i++) y = alpha(y); if (y != t[u]) { fprintf(stderr, "alpha^k != 1\n"); return 2; } } }
    scan_fix(); FIXG = FIXL; NFIXG = NFIX;
    if (getenv("FIXMIN")) {   /* fixed generators of order >= FIXMIN only (no involutions or order 3: BEYOND_RANDOM 4.5.3) */
        int mo = atoi(getenv("FIXMIN")); FIXG = malloc(sizeof(int) * (NFIX + 1)); NFIXG = 0;
        for (long long i = 0; i < NFIX; i++) { int y = FIXL[i], o = 1; while (y != ident) { y = gmul(y, FIXL[i]); o++; } if (o >= mo) FIXG[NFIXG++] = FIXL[i]; }
        fprintf(stderr, "FIXMIN=%d: %lld of %lld fixed elements eligible as generators\n", mo, NFIXG, NFIX);
    }
    INVP = getenv("INVPAIR") ? atoi(getenv("INVPAIR")) : 0;
    if (INVP) {
        if (OK_ != 3 || OM != 3 || OF != 1) { fprintf(stderr, "INVPAIR needs ORBIT=\"3 3 1\"\n"); return 2; }
        if (INVP == 2 && !setup_beta()) return 2;
        INVL = malloc(sizeof(int) * (N / 3 + 1)); NINV = 0;
        for (int x = 0; x < N; x++) if (x != ident && iota_x(x) == x && alpha(x) != x) { int y = alpha(x), z = alpha(y); if (x < y && x < z) INVL[NINV++] = x; }
        fprintf(stderr, "INVPAIR: S = {e} + O + O^-1 + alpha-orbit of involutions; %d involution orbits\n", NINV);
        if (!NINV) return 2;
    }
    double W = Wwords(d, D), lam = W / N, mu = N * exp(-lam);
    double nb = D % 2 ? 2 : 1;   /* odd D: two conditions, each with half the targets in inverse pairs; mu is the total */
    fprintf(stderr, "ORBIT k=%d m=%d f=%d: |Fix(alpha)| = %lld (+e); mu = %.2f, mu/k = %.2f, fixed-point misses ~ %.2f\n",
            OK_, OM, OF, NFIX, mu, mu / OK_, nb * (NFIX + 1) * exp(-lam / OK_));
    int nth_ = nth; (void)nth_;
    /* initial S */
    if (OF) S[0] = ident;
    if (OF && getenv("FIXI")) {   /* c5: the fixed letter is an alpha-fixed iota-fixed element (not e) */
        int found = -1; for (long long i = 0; i < NFIX && found < 0; i++) if (iota_x(FIXL[i]) == FIXL[i]) found = FIXL[i];
        if (found < 0) { fprintf(stderr, "FIXI: no alpha-fixed iota-fixed element\n"); return 2; }
        S[0] = found; fprintf(stderr, "FIXI: fixed letter %d (alpha-fixed, iota-fixed) instead of e\n", found); }
    if (OF && getenv("F0")) {   /* F0=i (cell-10-8 session): the fixed letter is the i-th non-identity alpha-fixed element, not e */
        int i0 = atoi(getenv("F0")); if (i0 < 1 || i0 > NFIX) { fprintf(stderr, "F0 must be 1..%lld\n", NFIX); return 2; }
        S[0] = FIXL[i0 - 1]; fprintf(stderr, "F0=%d: fixed letter %d instead of e\n", i0, S[0]); }
    for (int u = 1; u < OF; u++) { if (NFIXG < OF) { fprintf(stderr, "not enough fixed elements\n"); return 2; } int x; do x = FIXG[rnd() % NFIXG]; while (used(x, u)); S[u] = x; }
    for (int u = OF; u < d; u++) S[u] = -1 - u;
    for (int j = 0; j < OM; j++) { int o[MAXD]; if (!random_orbit(j, o)) { fprintf(stderr, "no orbit found\n"); return 2; } for (int i = 0; i < OK_; i++) S[ostart(j) + i] = o[i]; }
    if (INVP) invpair_random_S();
    for (int i = 0; i < d; i++) { SI[i] = ginv(S[i]); mktab(S[i], TF[i], TI[i]); }
    if (INVP && getenv("VERIFY")) {   /* c5: symmetry checks of a random member, before any search */
        int ok = verify_S_sym(); fprintf(stderr, "VERIFY: S closed under alpha and iota, iota anti-automorphism, iota^2 = 1, iota alpha = alpha iota: %s\n", ok ? "OK" : "FAIL");
        for (int t = 0; t < (getenv("VERIFYN") ? atoi(getenv("VERIFYN")) : 3); t++) {
            if (t) { invpair_random_S(); for (int u = 0; u < d; u++) mktab(S[u], TF[u], TI[u]); }
            uint64_t *sv0 = zalloc64(BITBYTES), *sv1 = zalloc64(BITBYTES); uint64_t *svp[2] = { sv0, sv1 };
            double sc = 0; long long cst = cost_fast(C[0], TF, TI, &sc, svp, &NOBOUND, 0);
            fprintf(stderr, "VERIFY sample %d: S closed %s, cost %lld\n", t, verify_S_sym() ? "OK" : "FAIL", cst);
            verify_unc(sv0); if (getenv("VERIFYGEN")) diag_gen_zcov(sv0); free(sv0); free(sv1);
        }
        for (int u = 0; u < d; u++) mktab(S[u], TF[u], TI[u]);
    }
    if (getenv("CHKINV")) { diag_invpairs(); diag_letter_invmat(); }
    if (getenv("VERIFYCOLL")) diag_collisions();
    if (getenv("VERIFYCOLL3")) diag_coll3();
    if (getenv("ENUM")) { enum_family(C[0], out); return 0; }
    double sc0;
    if (getenv("RANDORB")) {   /* screening: random symmetric S */
        int m = atoi(getenv("RANDORB")), saved = 0; long long *v = malloc(sizeof(long long) * m), hist[32] = {0}; double sm = 0, sq = 0, t0 = now();
        for (int t = 0; t < m; t++) {
            for (int u = 1; u < OF; u++) { int x; do x = FIXG[rnd() % NFIXG]; while (used(x, u)); S[u] = x; mktab(S[u], TF[u], TI[u]); }
            for (int j = 0; j < OM; j++) for (int i = 0; i < OK_; i++) S[ostart(j) + i] = -1 - ostart(j) - i;
            for (int j = 0; j < OM; j++) { int o[MAXD]; random_orbit(j, o); for (int i = 0; i < OK_; i++) { S[ostart(j) + i] = o[i]; mktab(o[i], TF[ostart(j) + i], TI[ostart(j) + i]); } }
            if (INVP) { invpair_random_S(); for (int u = 1; u < d; u++) mktab(S[u], TF[u], TI[u]); }
            v[t] = cost_any(C[0], TF, TI, &sc0, NULL, &NOBOUND, 0);
            if (v[t] == 0 && !saved && strcmp(out, "/dev/null")) { printf("RANDORB sample %d has cost 0\n", t); saved = check_and_write(C[0], out); }
            sm += v[t]; sq += (double)v[t] * v[t]; hist[v[t] / OK_ < 31 ? v[t] / OK_ : 31]++;
            if (getenv("LEVELS") && t < atoi(getenv("LEVELS"))) { fprintf(stderr, "levels:"); for (int h = 0; h < D - 1; h++) fprintf(stderr, " %lld", C[0]->lev[h]); fprintf(stderr, " cost %lld\n", v[t]); }
        }
        qsort(v, m, sizeof(long long), cmpll);
        printf("RANDORB d=%d D=%d group=%s x Z_%d N=%d k=%d m=%d f=%d fix=%lld samples=%d min=%lld p1=%lld p10=%lld median=%lld mean=%.2f var=%.1f mu=%.2f time=%.1f\nRANDORB hist (cost/k):",
               d, D, Q->spec, ncyc, N, OK_, OM, OF, NFIX, m, v[0], v[m / 100], v[m / 10], v[m / 2], sm / m, sq / m - (sm / m) * (sm / m), mu, now() - t0);
        for (int h = 0; h < 32; h++) printf(" %lld", hist[h]); printf("\n");
        { long long z = 0; for (int t = 0; t < m; t++) z += v[t] == 0;   /* v is sorted */
          printf("RANDORB cost0=%lld of %d (P=%.4g); cost counts 0..%d:", z, m, (double)z / m, 4 * OK_);
          for (int c0 = 0, t = 0; c0 <= 4 * OK_; c0++) { long long cnt = 0; while (t < m && v[t] < c0) t++; while (t < m && v[t] == c0) { cnt++; t++; } printf(" %lld", cnt); } printf("\n"); }
        return 0;
    }
    double COOL = getenv("COOL") ? atof(getenv("COOL")) : 20.0, REHEAT = getenv("REHEAT") ? atof(getenv("REHEAT")) : 150.0;
    double TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 1.5, TMIN = getenv("TMIN") ? atof(getenv("TMIN")) : 0.15;
    int TARGP = getenv("TARGP") ? atoi(getenv("TARGP")) : 70, PINV = getenv("PINV") ? atoi(getenv("PINV")) : 25;
    long long REHEATSTEPS = getenv("REHEATSTEPS") ? atoll(getenv("REHEATSTEPS")) : 400;
    int ORESTART = getenv("RESTART") ? atoi(getenv("RESTART")) : 0;
    if (K > 64) K = 64;
    /* RESTARTAFTER=r (cell-10-8 session): reheats restart from the best set of the current chain; after r reheats in a
     * row without improving that chain's best, a fresh chain starts from random orbits (the global best is kept for the
     * output and the checkpoint). Unset: the original behaviour (reheat from the global best, or always fresh with
     * RESTART=1). */
    int RA = getenv("RESTARTAFTER") ? atoi(getenv("RESTARTAFTER")) : -1, nfail = 0, nchains = 1;   /* RESTARTAFTER=0: every stall starts a fresh chain */
    double chain_t0 = now(); long long chain_e0 = 0;
    long long lbestE = (1LL << 60); int lbestS[MAXD];
    uint64_t *SV[64][2]; for (int t = 0; t < K; t++) { SV[t][0] = zalloc64(BITBYTES); SV[t][1] = zalloc64(BITBYTES); }
    uint32_t *OTF[64][MAXD], *OTI[64][MAXD];
    for (int t = 0; t < nth; t++) for (int i = 0; i < (INVP ? 6 : OK_); i++) { OTF[t][i] = malloc(4 * NROWS); OTI[t][i] = malloc(4 * NROWS); }
    int cand[64][MAXD]; long long cs[64], craw[64]; int bestS2[MAXD];
    if (getenv("ORBW")) ORBW = atoi(getenv("ORBW"));
    /* CKPT=path: the best S so far (element indices; alpha and the group are deterministic) is written there every
     * 60 s, with the evaluations and seconds spent; if the file exists at start, the run resumes from it (budget,
     * evals and RESULT count both segments; the trajectory after a resume is not that of an uninterrupted run). */
    const char *ckpt = getenv("CKPT"); long long evals0 = 0; double elapsed0 = 0; int resumed = 0;
    if (ckpt) { FILE *f = fopen(ckpt, "r"); int T2[MAXD], ok = 0; long long e0 = 0, b0 = 0; double el = 0;
        if (f) { int dd = 0; ok = fscanf(f, "CKPT d=%d evals=%lld elapsed=%lf best=%lld", &dd, &e0, &el, &b0) == 4 && dd == d;
            for (int i = 0; ok && i < d; i++) ok = fscanf(f, "%d", &T2[i]) == 1 && T2[i] >= 0 && T2[i] < N;
            fclose(f); }
        for (int i = 0; ok && i < OF; i++) ok = (i == 0 && !getenv("F0")) ? T2[0] == ident : alpha(T2[i]) == T2[i];
        for (int j = 0; ok && j < OM; j++) for (int i = 0; ok && i < OK_; i++) ok = T2[ostart(j) + (i + 1) % OK_] == alpha(T2[ostart(j) + i]);
        for (int i = 0; ok && i < d; i++) for (int u = 0; u < i; u++) if (T2[u] == T2[i]) ok = 0;
        if (ok) { memcpy(S, T2, sizeof(int) * d); for (int i = 0; i < d; i++) { SI[i] = ginv(S[i]); mktab(S[i], TF[i], TI[i]); }
                  evals0 = e0; elapsed0 = el; resumed = 1; rs ^= (unsigned long long)(e0 + 1) * 0x9E3779B97F4A7C15ULL;
                  fprintf(stderr, "resumed from %s: evals %lld, %.0f s spent, best %lld\n", ckpt, e0, el, b0); }
        else if (f) fprintf(stderr, "checkpoint %s unusable, fresh start\n", ckpt); }
    if (getenv("EXDESC")) {   /* exhaustive coordinate descent (cell-10-8 session): replace one orbit slot at a time by
        * its best response over ALL alpha-orbits (early abort at the current cost), until no slot improves; then log
        * the local optimum and start again from random orbits (the first start may come from CKPT). */
        double te0 = now(); long long gbest = (1LL << 60); int gS[MAXD]; int ndesc = 0; long long nev = 0;
        uint32_t *XF[MAXD], *XI[MAXD]; for (int i = 0; i < OK_; i++) { XF[i] = malloc(4 * NROWS); XI[i] = malloc(4 * NROWS); }
        while (!stop_flag && now() - te0 < secs && gbest > 0) {
            long long cur = cost_any(C[0], TF, TI, &sc0, NULL, &NOBOUND, 0); double td = now();
            fprintf(stderr, "EXDESC %d start cost %lld\n", ndesc + 1, cur);
            int improved = 1, sweeps = 0;
            while (improved && cur > 0 && !stop_flag) {
                improved = 0; sweeps++;
                int perm[MAXD]; for (int j = 0; j < OM; j++) perm[j] = j;
                for (int j = OM - 1; j > 0; j--) { int r = rnd() % (j + 1), t = perm[j]; perm[j] = perm[r]; perm[r] = t; }
                for (int pj = 0; pj < OM && cur > 0; pj++) {
                    int j = perm[pj], o[MAXD], bo[MAXD], found = 0; long long bnd = cur, nc = 0, off = rnd() % N;
                    for (long long xx = 0; xx < N; xx++) { int x = (int)((xx + off) % N);
                        if (!orbit_of(x, o)) continue;
                        if (o[1] < x || o[2] < x) continue;          /* one representative per orbit (k = 3) */
                        if (!orbit_free(o, j)) continue;
                        uint32_t *tf[MAXD], *ti[MAXD]; memcpy(tf, TF, sizeof(uint32_t *) * d); memcpy(ti, TI, sizeof(uint32_t *) * d);
                        for (int i = 0; i < OK_; i++) { mktab(o[i], XF[i], XI[i]); tf[ostart(j) + i] = XF[i]; ti[ostart(j) + i] = XI[i]; }
                        long long r = cost_any(C[0], tf, ti, &sc0, NULL, &bnd, 0); nc++;
                        if (r >= 0 && r < bnd) { bnd = r; memcpy(bo, o, sizeof(int) * OK_); found = 1; if (r == 0) break; }
                    }
                    nev += nc;
                    if (found) { for (int i = 0; i < OK_; i++) { int u = ostart(j) + i; S[u] = bo[i]; SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
                        fprintf(stderr, "  slot %d: %lld -> %lld (%lld orbits, %.0f s)\n", j, cur, bnd, nc, now() - td); cur = bnd; improved = 1; }
                    else fprintf(stderr, "  slot %d: no improvement on %lld (%lld orbits, %.0f s)\n", j, cur, nc, now() - td);
                }
            }
            ndesc++;
            fprintf(stderr, "EXDESC %d local optimum %lld after %d sweeps, %.0f s (total %.0f s, %lld evals)\n", ndesc, cur, sweeps, now() - td, now() - te0, nev);
            if (cur < gbest) { gbest = cur; memcpy(gS, S, sizeof(int) * d);
                if (ckpt) { FILE *f = fopen(ckpt, "w"); if (f) { fprintf(f, "CKPT d=%d evals=%lld elapsed=%.1f best=%lld\n", d, nev, now() - te0, gbest);
                    for (int i = 0; i < d; i++) fprintf(f, "%d%c", gS[i], i + 1 < d ? ' ' : '\n'); fclose(f); } } }
            if (gbest == 0) break;
            for (int j = 0; j < OM; j++) for (int i = 0; i < OK_; i++) S[ostart(j) + i] = -1 - ostart(j) - i;
            for (int j = 0; j < OM; j++) { int o[MAXD]; random_orbit(j, o); for (int i = 0; i < OK_; i++) S[ostart(j) + i] = o[i]; }
            for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
        }
        memcpy(S, gS, sizeof(int) * d); for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
        printf("RESULT d=%d D=%d group=%s x Z_%d N=%d best=%lld evals=%lld time=%.1f orbit k=%d m=%d f=%d fix=%lld EXDESC descents=%d\n", d, D, Q->spec, ncyc, N, gbest, nev, now() - te0, OK_, OM, OF, NFIX, ndesc);
        if (gbest == 0 && !check_and_write(C[0], out)) return 1;
        return gbest == 0 ? 0 : 1;
    }
    double lastck = now();
    long long c = cost_any(C[0], TF, TI, &sc0, SV[0], &NOBOUND, 0), ce = c + (ORBW > 1 ? (ORBW - 1) * fixmiss(SV[0]) : 0);
    long long best = c, bestE = ce; memcpy(bestS2, S, sizeof(int) * d); collect(C[0]);
    double cE = (double)ce / OK_, t0 = now(), T = TMAX, lastimp = t0, lastprint = t0, lastheat = t0;
    if (ORBW > 1) fprintf(stderr, "ORBW=%d: an uncovered fixed element weighs %d; start energy %lld\n", ORBW, ORBW, ce);
    long long evals = 1 + evals0, steps = 0, lastimpstep = 0;
    if (resumed) t0 -= elapsed0;
    double OVCLOCK = getenv("VCLOCK") ? atof(getenv("VCLOCK")) : 0;   /* deterministic schedule: x seconds per step */
    long long OMAXSTEPS = getenv("MAXSTEPS") ? atoll(getenv("MAXSTEPS")) : 0, ohash = 1469598103934665603ULL;
#define ONOW (OVCLOCK > 0 ? t0 + steps * OVCLOCK : now())
    fprintf(stderr, "start cost=%lld\n", c);
    int nslots = OM + (OF > 1 ? OF - 1 : 0);
    char obuf[96]; int OABORT = getenv("ABORT") ? atoi(getenv("ABORT")) : 1;
    while (!stop_flag && ONOW - t0 < secs && best > 0 && (!OMAXSTEPS || steps < OMAXSTEPS)) {
        int slot = rnd() % nslots, isorb = slot < OM, j = slot, fs = isorb ? -1 : 1 + (slot - OM), ptype = -1;
        if (INVP) { ptype = (int)(rnd() % 100) < PINV ? 2 : 0; isorb = 1; j = ptype; fs = -1; }
        for (int t = 0; t < K; t++) {
            if (INVP && ptype == 2) { int o3[3], tries = 0; do inv_random(o3); while (!inv_free(o3) && ++tries < 100); memcpy(cand[t], o3, sizeof(int) * 3); }
            else if (INVP) { int o6[6], ok = 0;
                if ((int)(rnd() % 100) < TARGP) { int which = rnd() % 2; AVOIDMASK = 0x7e; int x = targeted(ostart(which)); AVOIDMASK = 0;
                    ok = inv_pair_from(x, which, o6); }
                while (!ok) ok = inv_pair_from(rnd() % N, 0, o6);
                memcpy(cand[t], o6, sizeof(int) * 6); }
            else if (isorb) {
                int x = -1, o[MAXD]; AVOIDMASK = 0; for (int i = 0; i < OK_; i++) AVOIDMASK |= 1u << (ostart(j) + i);
                if ((int)(rnd() % 100) < TARGP) x = targeted(ostart(j));
                AVOIDMASK = 0;
                if (x < 0 || x == ident || !orbit_of(x, o) || !orbit_free(o, j)) random_orbit(j, o);
                memcpy(cand[t], o, sizeof(int) * OK_);
            } else { int x; do x = FIXG[rnd() % NFIXG]; while (used(x, fs)); cand[t][0] = x; }
        }
        long long bound = NOBOUND;
        #pragma omp parallel for schedule(dynamic, 1) if (nth > 1)
        for (int t = 0; t < K; t++) {
            int me = 0;
#ifdef _OPENMP
            me = omp_get_thread_num();
#endif
            ctx *cx = C[me]; uint32_t *tf[MAXD], *ti[MAXD]; memcpy(tf, TF, sizeof(uint32_t *) * d); memcpy(ti, TI, sizeof(uint32_t *) * d);
            if (INVP && ptype == 0) for (int i = 0; i < 6; i++) { mktab(cand[t][i], OTF[me][i], OTI[me][i]); tf[1 + i] = OTF[me][i]; ti[1 + i] = OTI[me][i]; }
            else if (isorb) for (int i = 0; i < OK_; i++) { mktab(cand[t][i], OTF[me][i], OTI[me][i]); tf[ostart(j) + i] = OTF[me][i]; ti[ostart(j) + i] = OTI[me][i]; }
            else { mktab(cand[t][0], OTF[me][0], OTI[me][0]); tf[fs] = OTF[me][0]; ti[fs] = OTI[me][0]; }
            double sc; long long r = cost_any(cx, tf, ti, &sc, SV[t], OABORT ? &bound : &NOBOUND, nth > 1);
            if (r >= 0 && ORBW > 1) { craw[t] = r; r += (ORBW - 1) * fixmiss(SV[t]); } else craw[t] = r;
            if (r < 0) cs[t] = NOBOUND;
            else { cs[t] = r; long long bv = __atomic_load_n(&bound, __ATOMIC_RELAXED);
                while (r < bv && !__atomic_compare_exchange_n(&bound, &bv, r, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) ; }
        }
        evals += K;
        int bt = 0; for (int t = 1; t < K; t++) if (cs[t] < cs[bt]) bt = t;
        double bE = (double)cs[bt] / OK_;
        if (bE <= cE || exp((cE - bE) / T) > (rnd() % 1000000) / 1e6) {
            if (INVP && ptype == 0) for (int i = 0; i < 6; i++) { int u = 1 + i; S[u] = cand[bt][i]; SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
            else if (isorb) for (int i = 0; i < OK_; i++) { int u = ostart(j) + i; S[u] = cand[bt][i]; SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
            else { S[fs] = cand[bt][0]; SI[fs] = ginv(S[fs]); mktab(S[fs], TF[fs], TI[fs]); }
            c = craw[bt]; ce = cs[bt]; cE = bE; collect_saved(SV[bt]);
        }
        steps++; ohash = (ohash ^ (unsigned long long)(cs[bt] * 1000003 + bt * 7 + (c == cs[bt]))) * 1099511628211ULL;
        if (ce < bestE) { best = c; bestE = ce; memcpy(bestS2, S, sizeof(int) * d); lastimp = ONOW; lastimpstep = steps; }
        if (RA >= 0 && ce < lbestE) { lbestE = ce; memcpy(lbestS, S, sizeof(int) * d); lastimp = ONOW; lastimpstep = steps; nfail = 0; }
        T = TMAX * pow(0.5, (ONOW - lastheat) / COOL); if (T < TMIN) T = TMIN;
        if (ONOW - lastimp > REHEAT && steps - lastimpstep > REHEATSTEPS) {
            lastheat = ONOW; T = TMAX; memcpy(S, RA >= 0 ? lbestS : bestS2, sizeof(int) * d);
            int fresh = ORESTART;
            if (RA >= 0 && ++nfail > RA) { fresh = 1; nfail = 0;
                fprintf(stderr, "CHAIN %d min %lld secs %.0f evals %lld S", nchains, lbestE, now() - chain_t0, evals - chain_e0);
                for (int i = 0; i < d; i++) fprintf(stderr, " %d", lbestS[i]); fprintf(stderr, "\n");
                chain_t0 = now(); chain_e0 = evals; lbestE = (1LL << 60); nchains++;
                fprintf(stderr, "chain %d: fresh start (global best %lld)\n", nchains, best); }
            if (fresh) {   /* diversify: fresh random orbits (fixed generators kept) */
                for (int j = 0; j < OM; j++) for (int i = 0; i < OK_; i++) S[ostart(j) + i] = -1 - ostart(j) - i;
                for (int j = 0; j < OM; j++) { int o[MAXD]; random_orbit(j, o); for (int i = 0; i < OK_; i++) S[ostart(j) + i] = o[i]; }
                if (INVP) invpair_random_S();
            }
            for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
            c = cost_any(C[0], TF, TI, &sc0, SV[0], &NOBOUND, 0); ce = c + (ORBW > 1 ? (ORBW - 1) * fixmiss(SV[0]) : 0);
            cE = (double)ce / OK_; collect(C[0]); lastimp = ONOW; lastimpstep = steps;
        }
        if (ckpt && now() - lastck > 60) { char tmp[1100]; snprintf(tmp, sizeof tmp, "%s.tmp", ckpt); FILE *f = fopen(tmp, "w");
            if (f) { fprintf(f, "CKPT d=%d evals=%lld elapsed=%.1f best=%lld\n", d, evals, now() - t0, best);
                     for (int i = 0; i < d; i++) fprintf(f, "%d%c", bestS2[i], i + 1 < d ? ' ' : '\n'); fclose(f); rename(tmp, ckpt); }
            lastck = now(); }
        if (ONOW - lastprint > 30) { fprintf(stderr, "t=%.0f steps=%lld evals=%lld cost=%lld best=%lld T=%.2f%s\n", ONOW - t0, steps, evals, c, best, T,
                                                  ORBW > 1 ? (sprintf(obuf, " energy=%lld bestE=%lld", ce, bestE), obuf) : ""); lastprint = ONOW; }
    }
    memcpy(S, bestS2, sizeof(int) * d);
    for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
    if (OVCLOCK > 0 || OMAXSTEPS) fprintf(stderr, "TRACE steps=%lld hash=%016llx best=%lld evals=%lld\n", steps, ohash, best, evals);
    printf("RESULT d=%d D=%d group=%s x Z_%d N=%d best=%lld evals=%lld time=%.1f orbit k=%d m=%d f=%d fix=%lld\n", d, D, Q->spec, ncyc, N, best, evals, now() - t0, OK_, OM, OF, NFIX);
    if (best == 0 && !check_and_write(C[0], out)) return 1;
    return best == 0 ? 0 : 1;
}
int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: haar_gen3 d D seconds seed K outfile GROUP... n\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); double secs = atof(argv[3]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((unsigned long long)atoll(argv[4]) + 1) * 2654435761ULL;
    int K = atoi(argv[5]); const char *out = argv[6];
    if (d < 2 || d > MAXD || K < 1) { fprintf(stderr, "bad d or K\n"); return 2; }
    int a = 7;
    Q = parse_group(argv, argc, &a);
    if (a >= argc) { fprintf(stderr, "missing n\n"); return 2; }
    ncyc = atoi(argv[a]);
    long long NN = (long long)Q->order * ncyc;
    if (NN > (1LL << 30)) { fprintf(stderr, "group too large\n"); return 2; }
    N = (int)NN; ident = Q->ident * ncyc;
    CHI = malloc(Q->order); memset(CHI, 1, Q->order);
    if (CSL && ncyc % 2) { fprintf(stderr, "csl needs n even\n"); return 2; }
    if (Q->type == G_SL || Q->type == G_PSL || Q->type == G_PGL) { long long nk = (long long)Q->F->q * Q->F->q * Q->F->q + (long long)Q->F->q * Q->F->q; zero_s = calloc(nk, 1); }
    if (TWIST) {   /* sign of PGL(2,q) element = quadratic character of det (well defined up to scalars) */
        const field *F = Q->F; int q = F->q; char *sq = calloc(q, 1);
        for (int v = 1; v < q; v++) sq[FMUL(F, v, v)] = 1;
        for (int i = 0; i < Q->order; i++) { const uint16_t *E = Q->EL + 4 * (size_t)i;
            int det = FADD(F, FMUL(F, E[0], E[3]), F->neg[FMUL(F, E[1], E[2])]); CHI[i] = sq[det] ? 1 : -1; }
        free(sq);
    }
    int nth = getenv("THREADS") ? atoi(getenv("THREADS")) : 1; if (nth < 1) nth = 1;
    int hmax = getenv("HMAX") ? atoi(getenv("HMAX")) : 63; if (hmax > 63) hmax = 63; if (hmax < 1) hmax = 1;
    if (getenv("UCAP")) UCAP = atoi(getenv("UCAP"));
    double COOL = getenv("COOL") ? atof(getenv("COOL")) : 20.0, REHEAT = getenv("REHEAT") ? atof(getenv("REHEAT")) : 150.0;
    double TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 1.5, TMIN = getenv("TMIN") ? atof(getenv("TMIN")) : 0.15;
    int TARGP = getenv("TARGP") ? atoi(getenv("TARGP")) : 70;
    int RESTART = getenv("RESTART") ? atoi(getenv("RESTART")) : 0;   /* 1: a reheat starts from a fresh random S */
    long long REHEATSTEPS = getenv("REHEATSTEPS") ? atoll(getenv("REHEATSTEPS")) : 400;
    int prof = getenv("PROFILE") ? atoi(getenv("PROFILE")) : 0;
    if (getenv("FAST")) FAST = atoi(getenv("FAST"));
    int ABORT = getenv("ABORT") ? atoi(getenv("ABORT")) : 1;
    double VCLOCK = getenv("VCLOCK") ? atof(getenv("VCLOCK")) : 0;
    long long MAXSTEPS = getenv("MAXSTEPS") ? atoll(getenv("MAXSTEPS")) : 0;
#ifdef _OPENMP
    omp_set_num_threads(nth);
#else
    nth = 1;
#endif
    signal(SIGTERM, on_term);
    double tsetup = now();
    /* group sanity */
    {
        unsigned long long save = rs; rs = 0x1234567ULL;
        for (int t = 0; t < 2000; t++) {
            int x = rnd() % N, y = rnd() % N, z = rnd() % N;
            if (gmul(gmul(x, y), z) != gmul(x, gmul(y, z)) || gmul(x, ginv(x)) != ident || gmul(ident, x) != x || gmul(x, ident) != x) {
                fprintf(stderr, "group error\n"); return 2; }
        }
        /* cyclic subgroup H of largest order <= hmax (deterministic choice) */
        int bestt = 1, besth = ident;
        for (int t = 0; t < 400 && bestt < hmax; t++) {
            int g = rnd() % N, y = g, o = 1;
            while (y != ident && o <= 200000) { y = gmul(y, g); o++; }
            if (y != ident) continue;
            for (int dv = hmax; dv > bestt; dv--) if (o % dv == 0) {
                int e = o / dv, hh = ident; for (int u = 0; u < e; u++) hh = gmul(hh, g);
                bestt = dv; besth = hh; break;
            }
        }
        nH = bestt; HP[0] = ident; for (int b = 1; b < nH; b++) HP[b] = gmul(HP[b - 1], besth);
        if (gmul(HP[nH - 1], besth) != ident) { fprintf(stderr, "H error\n"); return 2; }
        rs = save;
    }
    MASK = nH == 64 ? ~0ULL : ((1ULL << nH) - 1);
    if (N % nH) { fprintf(stderr, "coset error\n"); return 2; }
    R = N / nH;
    POS = malloc(sizeof(int) * (size_t)N); REP = malloc(sizeof(int) * (size_t)R);
    for (int g = 0; g < N; g++) POS[g] = -1;
    { int r = 0; for (int g = 0; g < N; g++) if (POS[g] < 0) { REP[r] = g; for (int b = 0; b < nH; b++) POS[gmul(g, HP[b])] = r * 64 + b; r++; }
      if (r != R) { fprintf(stderr, "coset count error\n"); return 2; } }
    REPQ = malloc(sizeof(int) * (size_t)R); REPZ = malloc(sizeof(int) * (size_t)R);
    for (int r = 0; r < R; r++) { REPQ[r] = REP[r] / ncyc; REPZ[r] = REP[r] % ncyc; }
    /* self-test of the fast table builder against plain multiplication */
    { uint32_t *t1 = malloc(4 * (size_t)R), *t2 = malloc(4 * (size_t)R);
      unsigned long long save = rs; rs = 0xABCDEFULL;
      for (int t = 0; t < 3; t++) { int x = rnd() % N; make_tables(x, t1, t2);
        for (int r = 0; r < R; r++) { int ps = POS[gmul(x, REP[r])]; if (t1[r] != (((uint32_t)(ps >> 6) << 6) | (uint32_t)(ps & 63))) { fprintf(stderr, "table self-test error\n"); return 2; } } }
      rs = save; free(t1); free(t2); }
    fprintf(stderr, "group %s x Z_%d, N=%d, identity %d, H order %d, rows %d, threads %d, setup %.2fs\n", Q->spec, ncyc, N, ident, nH, R, nth, now() - tsetup);
    if (FAST >= 2) {   /* wide rows: cyclic subgroup of the largest order in [HWMIN, 512] (deterministic sampling) */
        int hwmin = getenv("HWMIN") ? atoi(getenv("HWMIN")) : 64, hwmax = getenv("HWMAX") ? atoi(getenv("HWMAX")) : 256;
        if (hwmax > 256) hwmax = 256;
        if (getenv("PFD")) PFD = atoi(getenv("PFD"));
        unsigned long long save = rs; rs = 0x5DEECE66DULL;
        int bestt = 1, besth = ident;
        for (int t = 0; t < 400 && bestt < hwmax; t++) {
            int g = rnd() % N, y = g, o = 1;
            while (y != ident && o <= 1000000) { y = gmul(y, g); o++; }
            if (y != ident) continue;
            for (int dv = hwmax; dv > bestt; dv--) if (o % dv == 0) {
                int e = o / dv, hh = ident; for (int u = 0; u < e; u++) hh = gmul(hh, g);
                bestt = dv; besth = hh; break;
            }
        }
        rs = save;
        if (bestt >= hwmin && (long long)(N / bestt) < (1LL << 23)) {
            nHW = bestt; HPW[0] = ident; for (int b = 1; b < nHW; b++) HPW[b] = gmul(HPW[b - 1], besth);
            if (gmul(HPW[nHW - 1], besth) != ident) { fprintf(stderr, "HW error\n"); return 2; }
            RW = N / nHW; WIDE = 1;
            POSW = malloc(sizeof(uint32_t) * (size_t)N); REPW = malloc(sizeof(int) * (size_t)RW);
            for (int g = 0; g < N; g++) POSW[g] = 0xFFFFFFFFu;
            { int r = 0; for (int g = 0; g < N; g++) if (POSW[g] == 0xFFFFFFFFu) { REPW[r] = g; for (int b = 0; b < nHW; b++) POSW[gmul(g, HPW[b])] = ((uint32_t)r << 9) | (uint32_t)b; r++; }
              if (r != RW) { fprintf(stderr, "wide coset count error\n"); return 2; } }
            REPWQ = malloc(sizeof(int) * (size_t)RW); REPWZ = malloc(sizeof(int) * (size_t)RW);
            for (int r = 0; r < RW; r++) { REPWQ[r] = REPW[r] / ncyc; REPWZ[r] = REPW[r] % ncyc; }
            for (int b = 0; b < nHW; b++) MASKWA[b >> 6] |= 1ULL << (b & 63);
            MASKW = _mm256_loadu_si256((const __m256i *)MASKWA); init_dup();
            { uint32_t *t1 = malloc(4 * (size_t)RW), *t2 = malloc(4 * (size_t)RW);
              unsigned long long sv = rs; rs = 0xABCDEFULL;
              for (int t = 0; t < 3; t++) { int x = rnd() % N; make_tables_w(x, t1, t2);
                for (int r = 0; r < RW; r++) { if (t1[r] != POSW[gmul(x, REPW[r])]) { fprintf(stderr, "wide table self-test error\n"); return 2; }
                    uint32_t b = t1[r]; if ((t2[b >> 9] >> 9) != (uint32_t)r) { fprintf(stderr, "wide inverse table self-test error\n"); return 2; } } }
              rs = sv; free(t1); free(t2); }
            fprintf(stderr, "wide rows: HW order %d, rows %d, setup %.2fs\n", nHW, RW, now() - tsetup);
        } else { fprintf(stderr, "wide rows: no cyclic subgroup of order >= %d found (best %d); using haar_gen3's evaluation\n", hwmin, bestt); FAST = 0; }
    }
    NROWS = WIDE ? (size_t)RW : (size_t)R; BITBYTES = WIDE ? 64 * (size_t)RW : 8 * (size_t)R;   /* wide: F rows are doubled (64 B); V rows use 32 B */

    for (int i = 0; i < d; i++) { TF[i] = malloc(4 * NROWS); TI[i] = malloc(4 * NROWS); }
    ctx **C = malloc(sizeof(ctx *) * nth); for (int t = 0; t < nth; t++) C[t] = new_ctx();
    UNC[0] = malloc(4 * (size_t)UCAP); UNC[1] = malloc(4 * (size_t)UCAP);
    S[0] = ident;
    for (int i = 1; i < d; i++) { int x; do x = rnd() % N; while (x == ident || used(x, i)); S[i] = x; }
    for (int i = 0; i < d; i++) { SI[i] = ginv(S[i]); mktab(S[i], TF[i], TI[i]); }
    double SEC = getenv("SEC") ? atof(getenv("SEC")) : 0.0, csec;
    if (getenv("RANDSAMPLE")) {   /* screening: cost statistics of random generator sets, no search */
        int m = atoi(getenv("RANDSAMPLE")); double sc; long long *v = malloc(sizeof(long long) * m);
        for (int t = 0; t < m; t++) {
            for (int i = 1; i < d; i++) { int x; do x = rnd() % N; while (x == ident || used(x, i)); S[i] = x; mktab(S[i], TF[i], TI[i]); }
            v[t] = cost_eval(C[0], TF, TI, &sc, NULL);
            if (getenv("LEVELS") && t < atoi(getenv("LEVELS"))) { fprintf(stderr, "levels:"); for (int h = 0; h < D - 1; h++) fprintf(stderr, " %lld", C[0]->lev[h]); fprintf(stderr, " cost %lld\n", v[t]); }
        }
        for (int a1 = 1; a1 < m; a1++) { long long key = v[a1]; int b1 = a1 - 1; while (b1 >= 0 && v[b1] > key) { v[b1 + 1] = v[b1]; b1--; } v[b1 + 1] = key; }
        printf("RANDSAMPLE d=%d D=%d group=%s x Z_%d N=%d samples=%d min=%lld p1=%lld p10=%lld median=%lld\n", d, D, Q->spec, ncyc, N, m, v[0], v[m / 100], v[m / 10], v[m / 2]);
        return 0;
    }
    if (getenv("ORBIT")) { if (FAST == 0) FAST = 1; return orbit_main(C, nth, K, secs, out); }
    if (getenv("BENCH")) {        /* time m evaluations of single-generator replacements of a random S */
        int m = atoi(getenv("BENCH")); TIMING = 1; double sc; long long chk = 0;
        uint32_t *tf[MAXD], *ti[MAXD]; memcpy(tf, TF, sizeof(uint32_t *) * d); memcpy(ti, TI, sizeof(uint32_t *) * d);
        tf[1] = C[0]->cf; ti[1] = C[0]->ci;
        double ta = now();
        for (int t = 0; t < m; t++) {
            int x; do x = rnd() % N; while (x == ident || used(x, 1));
            double tq = now(); mktab(x, C[0]->cf, C[0]->ci); TTAB += now() - tq;
            chk += cost_eval(C[0], tf, ti, &sc, NULL);
        }
        double tot = now() - ta;
        printf("BENCH FAST=%d d=%d D=%d group=%s x Z_%d N=%d nH=%d R=%d evals=%d ms/eval=%.4f tables=%.4f sumcost=%lld levels(ms):",
               FAST, d, D, Q->spec, ncyc, N, WIDE ? nHW : nH, WIDE ? RW : R, m, 1e3 * tot / m, 1e3 * TTAB / m, chk);
        for (int h = 0; h < 64; h++) if (NLEV[h]) printf(" %.4f", 1e3 * TLEV[h] / m);
        printf("\n");
        return 0;
    }
    long long c = cost_eval(C[0], TF, TI, &csec, NULL), best = c; double cE = c + SEC * csec; memcpy(bestS, S, sizeof S); collect(C[0]);
    double t0 = now(), T = TMAX, lastimp = t0, lastprint = t0, lastheat = t0; long long evals = 1, steps = 0, lastimpstep = 0;
    long long nabort = 0; unsigned long long trace = 1469598103934665603ULL;
#define VNOW (VCLOCK > 0 ? t0 + steps * VCLOCK : now())
    double tgen = 0, tev = 0, tacc = 0; int nrestart = 0; long long runbest = c;
    fprintf(stderr, "start cost=%lld\n", c);
    int xs[256]; long long cs[256]; double ce[256]; if (K > 256) K = 256;
    uint64_t *SAVE[256][2];
    for (int t = 0; t < K; t++) { SAVE[t][0] = zalloc64(BITBYTES); SAVE[t][1] = zalloc64(BITBYTES); }
    while (!stop_flag && now() - t0 < secs && best > 0 && (!MAXSTEPS || steps < MAXSTEPS)) {
        double ta = now();
        int i = 1 + rnd() % (d - 1);
        for (int t = 0; t < K; t++) {
            int x = ((int)(rnd() % 100) < TARGP) ? targeted(i) : -1;
            if (x < 0 || x == ident || used(x, i)) do x = rnd() % N; while (x == ident || used(x, i));
            xs[t] = x;
        }
        double tb = now();
        long long bound = NOBOUND;     /* best cost among the candidates finished so far (FAST early abort) */
        #pragma omp parallel for schedule(dynamic, 1) if (nth > 1) reduction(+:nabort)
        for (int t = 0; t < K; t++) {
            int me = 0;
#ifdef _OPENMP
            me = omp_get_thread_num();
#endif
            ctx *cx = C[me];
            mktab(xs[t], cx->cf, cx->ci);
            uint32_t *tf[MAXD], *ti[MAXD]; memcpy(tf, TF, sizeof(uint32_t *) * d); memcpy(ti, TI, sizeof(uint32_t *) * d);
            tf[i] = cx->cf; ti[i] = cx->ci;
            double sc;
            if (!FAST) { cs[t] = cost_with(cx, tf, ti, &sc, SAVE[t]); ce[t] = cs[t] + SEC * sc; }
            else {
                long long r = (WIDE ? cost_w : cost_fast)(cx, tf, ti, &sc, SAVE[t], (ABORT && SEC == 0) ? &bound : &NOBOUND, nth > 1);
                if (r < 0) { cs[t] = NOBOUND; ce[t] = HUGE_VAL; nabort++; }
                else {
                    cs[t] = r; ce[t] = r + SEC * sc;
                    long long bv = __atomic_load_n(&bound, __ATOMIC_RELAXED);
                    while (r < bv && !__atomic_compare_exchange_n(&bound, &bv, r, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) ;
                }
            }
        }
        evals += K;
        double tc = now();
        int bt = 0; for (int t = 1; t < K; t++) if (ce[t] < ce[bt]) bt = t;
        long long bc = cs[bt]; double bE = ce[bt]; int bx = xs[bt];
        int acc = 0;
        if (bE <= cE || exp((cE - bE) / T) > (rnd() % 1000000) / 1e6) {
            S[i] = bx; SI[i] = ginv(bx); mktab(bx, TF[i], TI[i]); c = bc; cE = bE; collect_saved(SAVE[bt]); acc = 1;
        }
        { unsigned long long w[5] = {(unsigned long long)i, (unsigned long long)bx, (unsigned long long)bc, (unsigned long long)acc, (unsigned long long)c};
          for (int u = 0; u < 5; u++) { trace ^= w[u]; trace *= 1099511628211ULL; } }
        steps++;
        if (c < best) { best = c; memcpy(bestS, S, sizeof S); lastimp = VNOW; lastimpstep = steps; }
        if (RESTART && c < runbest) { runbest = c; lastimp = VNOW; lastimpstep = steps; }
        T = TMAX * pow(0.5, (VNOW - lastheat) / COOL); if (T < TMIN) T = TMIN;
        if (VNOW - lastimp > REHEAT && steps - lastimpstep > REHEATSTEPS) {
            lastheat = VNOW; T = TMAX; memcpy(S, bestS, sizeof S);
            if (RESTART) { nrestart++; for (int j = 1; j < d; j++) { int x; do x = rnd() % N; while (x == ident || used(x, j)); S[j] = x; } }
            for (int j = 0; j < d; j++) { SI[j] = ginv(S[j]); mktab(S[j], TF[j], TI[j]); }
            c = cost_eval(C[0], TF, TI, &csec, NULL); cE = c + SEC * csec; collect(C[0]); lastimp = VNOW; lastimpstep = steps; runbest = c;
        }
        double td = now(); tgen += tb - ta; tev += tc - tb; tacc += td - tc;
        if (now() - lastprint > 30) {
            fprintf(stderr, "t=%.0f steps=%lld evals=%lld cost=%lld best=%lld T=%.2f%s\n", now() - t0, steps, evals, c, best, T, RESTART ? " (restarts)" : "");
            if (RESTART) fprintf(stderr, "  restarts=%d\n", nrestart);
            if (prof) fprintf(stderr, "  profile: gen %.2fs eval %.2fs (%.3f ms/eval) accept/collect %.2fs\n", tgen, tev, 1e3 * tev / (evals - 1) * nth, tacc);
            lastprint = now();
        }
    }
    memcpy(S, bestS, sizeof S);
    for (int j = 0; j < d; j++) { SI[j] = ginv(S[j]); mktab(S[j], TF[j], TI[j]); }
    if (prof) fprintf(stderr, "  profile: gen %.2fs eval %.2fs (%.3f ms/eval/thread) accept/collect %.2fs\n", tgen, tev, evals > 1 ? 1e3 * tev / (evals - 1) * nth : 0, tacc);
    printf("RESULT d=%d D=%d group=%s x Z_%d N=%d best=%lld evals=%lld time=%.1f\n", d, D, Q->spec, ncyc, N, best, evals, now() - t0);
    if (getenv("TRACE")) printf("TRACE steps=%lld hash=%016llx best=%lld evals=%lld abandoned=%lld time=%.2f\n", steps, trace, best, evals, nabort, now() - t0);
    if (best == 0) {
        int ok = WIDE ? full_check_w(C[0]) : full_check(C[0]);
        printf("full diameter check: %s\n", ok ? "OK" : "FAIL");
        if (ok) {
            /* f = 0: write S s_0^-1 (an isomorphic Haar graph, (g,A) -> (s_0 g, A)) so that the first generator is e */
            if (S[0] != ident) { int a0 = ginv(S[0]); for (int i = 0; i < d; i++) S[i] = gmul(S[i], a0);
                for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); mktab(S[u], TF[u], TI[u]); }
                int ok2 = WIDE ? full_check_w(C[0]) : full_check(C[0]); printf("full diameter check after normalising s_0 = e: %s\n", ok2 ? "OK" : "FAIL");
                if (!ok2) return 1; }
            FILE *f = fopen(out, "w");
            if (!f) { perror(out); return 1; }
            fprintf(f, "%d %d %s n %d N %d\n", d, D, Q->spec, ncyc, N);
            for (int i = 0; i < d; i++) { char buf[1000]; desc_elem(S[i], buf); fprintf(f, "%s\n", buf); }
            fclose(f); printf("wrote %s\n", out);
        }
    }
    return best == 0 ? 0 : 1;
}
