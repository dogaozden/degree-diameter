/* haar_gen3: faster annealing search for Haar (bi-Cayley) graphs of diameter D, with more group families.
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
enum { G_META, G_SL, G_PSL, G_PGL, G_TRIV, G_PROD, G_AGL1, G_NMETA };
typedef struct grp {
    int type, order, ident;
    int m, k; int64_t *R;                 /* meta */
    int s; int *INV;                      /* nmeta: b^k = a^s; inverse table */
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
    case G_NMETA: { int a = x / G->k, j = x % G->k, b = y / G->k, l = y % G->k;
        int64_t c = a + G->R[j] * b; int t = j + l;   /* a^a b^j * a^b b^l = a^(a + r^j b) b^(j+l) */
        if (t >= G->k) { t -= G->k; c += (int64_t)G->s * G->R[t]; }   /* b^k = a^s, b^t a^s = a^(s r^t) b^t */
        return (int)(c % G->m) * G->k + t; }
    case G_PROD: { int o2 = G->g2->order; return qmul(G->g1, x / o2, y / o2) * o2 + qmul(G->g2, x % o2, y % o2); }
    case G_AGL1: { const field *F = G->F; int q = F->q; int a1 = x / q + 1, b1 = x % q, a2 = y / q + 1, b2 = y % q;
        int a = FMUL(F, a1, a2), b = FADD(F, FMUL(F, a1, b2), b1); return (a - 1) * q + b; }
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
    case G_NMETA: return G->INV[x];
    case G_PROD: { int o2 = G->g2->order; return qinv(G->g1, x / o2) * o2 + qinv(G->g2, x % o2); }
    case G_AGL1: { const field *F = G->F; int q = F->q; int a = x / q + 1, b = x % q, ia = F->inv[a];
        return (ia - 1) * q + F->neg[FMUL(F, ia, b)]; }
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
    case G_NMETA: sprintf(buf, "nmeta(a=%d,j=%d)", x / G->k, x % G->k); break;
    case G_AGL1: sprintf(buf, "aff(%d,%d)", x / G->F->q + 1, x % G->F->q); break;
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
static unsigned rs_small = 12345u;
static int rnd_small(int n) { rs_small = rs_small * 1103515245u + 12345u; return (int)((rs_small >> 8) % (unsigned)n); }
static grp *parse_group(char **argv, int argc, int *a) {
    top_level++;
    if (*a >= argc) { fprintf(stderr, "bad group\n"); exit(2); }
    grp *G = calloc(1, sizeof *G); const char *t = argv[*a];
    if (!strcmp(t, "nmeta")) {   /* Z_m . Z_k non-split: b a b^-1 = a^r, b^k = a^s; needs r^k = 1, s(r-1) = 0 mod m */
        G->type = G_NMETA; G->m = atoi(argv[*a + 1]); G->k = atoi(argv[*a + 2]); long long r = atoll(argv[*a + 3]); G->s = atoi(argv[*a + 4]); *a += 5;
        G->R = malloc(sizeof(int64_t) * G->k); G->R[0] = 1 % G->m;
        for (int j = 1; j < G->k; j++) G->R[j] = G->R[j - 1] * r % G->m;
        if (G->R[G->k - 1] * r % G->m != 1 % G->m) { fprintf(stderr, "r^k != 1\n"); exit(2); }
        if ((long long)G->s * ((r - 1 + G->m) % G->m) % G->m != 0) { fprintf(stderr, "s(r-1) != 0 mod m\n"); exit(2); }
        G->order = G->m * G->k; G->ident = 0; snprintf(G->spec, sizeof G->spec, "nmeta %d %d %lld %d", G->m, G->k, r, G->s);
        G->INV = malloc(sizeof(int) * G->order);
        for (int x = 0; x < G->order; x++) { int found = -1; for (int y = (G->k - x % G->k) % G->k; y < G->order && found < 0; y += G->k) if (qmul(G, x, y) == G->ident) found = y;
            if (found < 0) { fprintf(stderr, "nmeta: element %d has no inverse (not a group)\n", x); exit(2); } G->INV[x] = found; }
        for (int t = 0; t < 200000; t++) { int x = rnd_small(G->order), y = rnd_small(G->order), z = rnd_small(G->order);
            if (qmul(G, qmul(G, x, y), z) != qmul(G, x, qmul(G, y, z))) { fprintf(stderr, "nmeta: not associative\n"); exit(2); } }
    } else if (!strcmp(t, "meta")) {
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
static ctx *new_ctx(void) {
    ctx *c = calloc(1, sizeof *c);
    c->V[0] = calloc(R, 8); c->V[1] = calloc(R, 8); c->F = calloc(R, 8); c->Fn = calloc(R, 8); c->NB = calloc(R, 8);
    c->fl = malloc(4 * (size_t)R); c->fln = malloc(4 * (size_t)R); c->tl = malloc(4 * (size_t)R);
    c->cf = malloc(4 * (size_t)R); c->ci = malloc(4 * (size_t)R);
    return c;
}
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
    }
    c->F = F; c->Fn = Fn;
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
static void collect1(ctx *c, int t, int startB, int targetSame) {
    long long cnt[2]; bfs(c, TF, TI, startB, D - 1, cnt);
    int sd = targetSame ? startB : startB ^ 1; scan_unc(t, c->V[sd], startB, sd);
}
static void collect(ctx *c) {
    if (D % 2 == 0) { nlists = 1; collect1(c, 0, 0, 0); }
    else { nlists = 2; collect1(c, 0, 0, 1); collect1(c, 1, 1, 1); }
}
static void collect_saved(uint64_t **sv) {   /* same lists as collect(), from the saved bitsets of a candidate */
    if (D % 2 == 0) { nlists = 1; scan_unc(0, sv[0], 0, 1); }
    else { nlists = 2; scan_unc(0, sv[0], 0, 0); scan_unc(1, sv[1], 1, 1); }
}
static int walk(int g, int *side, int len, int avoid) {
    for (int s = 0; s < len; s++) {
        int j; do j = rnd() % d; while (j == avoid);
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

    for (int i = 0; i < d; i++) { TF[i] = malloc(4 * (size_t)R); TI[i] = malloc(4 * (size_t)R); }
    ctx **C = malloc(sizeof(ctx *) * nth); for (int t = 0; t < nth; t++) C[t] = new_ctx();
    UNC[0] = malloc(4 * (size_t)UCAP); UNC[1] = malloc(4 * (size_t)UCAP);
    S[0] = ident;
    for (int i = 1; i < d; i++) { int x; do x = rnd() % N; while (x == ident || used(x, i)); S[i] = x; }
    for (int i = 0; i < d; i++) { SI[i] = ginv(S[i]); make_tables(S[i], TF[i], TI[i]); }
    double SEC = getenv("SEC") ? atof(getenv("SEC")) : 0.0, csec;
    if (getenv("RANDSAMPLE")) {   /* screening: cost statistics of random generator sets, no search */
        int m = atoi(getenv("RANDSAMPLE")); double sc; long long *v = malloc(sizeof(long long) * m);
        for (int t = 0; t < m; t++) {
            for (int i = 1; i < d; i++) { int x; do x = rnd() % N; while (x == ident || used(x, i)); S[i] = x; make_tables(S[i], TF[i], TI[i]); }
            v[t] = cost_with(C[0], TF, TI, &sc, NULL);
        }
        for (int a1 = 1; a1 < m; a1++) { long long key = v[a1]; int b1 = a1 - 1; while (b1 >= 0 && v[b1] > key) { v[b1 + 1] = v[b1]; b1--; } v[b1 + 1] = key; }
        printf("RANDSAMPLE d=%d D=%d group=%s x Z_%d N=%d samples=%d min=%lld p1=%lld p10=%lld median=%lld\n", d, D, Q->spec, ncyc, N, m, v[0], v[m / 100], v[m / 10], v[m / 2]);
        return 0;
    }
    long long c = cost_with(C[0], TF, TI, &csec, NULL), best = c; double cE = c + SEC * csec; memcpy(bestS, S, sizeof S); collect(C[0]);
    double t0 = now(), T = TMAX, lastimp = t0, lastprint = t0, lastheat = t0; long long evals = 1, steps = 0, lastimpstep = 0;
    double tgen = 0, tev = 0, tacc = 0; int nrestart = 0; long long runbest = c;
    fprintf(stderr, "start cost=%lld\n", c);
    int xs[256]; long long cs[256]; double ce[256]; if (K > 256) K = 256;
    uint64_t *SAVE[256][2];
    for (int t = 0; t < K; t++) { SAVE[t][0] = malloc(8 * (size_t)R); SAVE[t][1] = malloc(8 * (size_t)R); }
    while (!stop_flag && now() - t0 < secs && best > 0) {
        double ta = now();
        int i = 1 + rnd() % (d - 1);
        for (int t = 0; t < K; t++) {
            int x = ((int)(rnd() % 100) < TARGP) ? targeted(i) : -1;
            if (x < 0 || x == ident || used(x, i)) do x = rnd() % N; while (x == ident || used(x, i));
            xs[t] = x;
        }
        double tb = now();
        #pragma omp parallel for schedule(dynamic, 1) if (nth > 1)
        for (int t = 0; t < K; t++) {
            int me = 0;
#ifdef _OPENMP
            me = omp_get_thread_num();
#endif
            ctx *cx = C[me];
            make_tables(xs[t], cx->cf, cx->ci);
            uint32_t *tf[MAXD], *ti[MAXD]; memcpy(tf, TF, sizeof(uint32_t *) * d); memcpy(ti, TI, sizeof(uint32_t *) * d);
            tf[i] = cx->cf; ti[i] = cx->ci;
            double sc; cs[t] = cost_with(cx, tf, ti, &sc, SAVE[t]); ce[t] = cs[t] + SEC * sc;
        }
        evals += K;
        double tc = now();
        int bt = 0; for (int t = 1; t < K; t++) if (ce[t] < ce[bt]) bt = t;
        long long bc = cs[bt]; double bE = ce[bt]; int bx = xs[bt];
        if (bE <= cE || exp((cE - bE) / T) > (rnd() % 1000000) / 1e6) {
            S[i] = bx; SI[i] = ginv(bx); make_tables(bx, TF[i], TI[i]); c = bc; cE = bE; collect_saved(SAVE[bt]);
        }
        steps++;
        if (c < best) { best = c; memcpy(bestS, S, sizeof S); lastimp = now(); lastimpstep = steps; }
        if (RESTART && c < runbest) { runbest = c; lastimp = now(); lastimpstep = steps; }
        T = TMAX * pow(0.5, (now() - lastheat) / COOL); if (T < TMIN) T = TMIN;
        if (now() - lastimp > REHEAT && steps - lastimpstep > REHEATSTEPS) {
            lastheat = now(); T = TMAX; memcpy(S, bestS, sizeof S);
            if (RESTART) { nrestart++; for (int j = 1; j < d; j++) { int x; do x = rnd() % N; while (x == ident || used(x, j)); S[j] = x; } }
            for (int j = 0; j < d; j++) { SI[j] = ginv(S[j]); make_tables(S[j], TF[j], TI[j]); }
            c = cost_with(C[0], TF, TI, &csec, NULL); cE = c + SEC * csec; collect(C[0]); lastimp = now(); lastimpstep = steps; runbest = c;
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
    for (int j = 0; j < d; j++) { SI[j] = ginv(S[j]); make_tables(S[j], TF[j], TI[j]); }
    if (prof) fprintf(stderr, "  profile: gen %.2fs eval %.2fs (%.3f ms/eval/thread) accept/collect %.2fs\n", tgen, tev, evals > 1 ? 1e3 * tev / (evals - 1) * nth : 0, tacc);
    printf("RESULT d=%d D=%d group=%s x Z_%d N=%d best=%lld evals=%lld time=%.1f\n", d, D, Q->spec, ncyc, N, best, evals, now() - t0);
    if (best == 0) {
        int ok = full_check(C[0]);
        printf("full diameter check: %s\n", ok ? "OK" : "FAIL");
        if (ok) {
            FILE *f = fopen(out, "w");
            if (!f) { perror(out); return 1; }
            fprintf(f, "%d %d %s n %d N %d\n", d, D, Q->spec, ncyc, N);
            for (int i = 0; i < d; i++) { char buf[1000]; desc_elem(S[i], buf); fprintf(f, "%s\n", buf); }
            fclose(f); printf("wrote %s\n", out);
        }
    }
    return best == 0 ? 0 : 1;
}
