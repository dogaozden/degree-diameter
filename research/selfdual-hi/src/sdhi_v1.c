/* sdhi.c: self-dual (bipartite Cayley) Haar graphs H(G,S) of valency K and diameter D, for groups given by formulas
 * (no GAP).  G = Q1 x Q2, each factor one of
 *   sl q | psl q | pgl q     SL(2,q), PSL(2,q), PGL(2,q), q = p^e <= 64 (GF(p^e) from the first irreducible
 *                            x^e + c_(e-1) x^(e-1) + .. + c_0, c = sum c_i p^i taken in increasing order)
 *   meta m k r               C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r>, elements (i,j) = x^i y^j
 *   cyc n                    Z_n (= meta n 1 0)
 * H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S.  X = S^-1 S.
 *
 * Self-duality.  If S is a union of orbits of an involution psi(x) = u0 beta(x)^-1 (beta in Aut(G), u0 in G), then
 * (g,A) -> (u0 beta(g), B), (h,B) -> (beta(h), A) is an automorphism of H(G,S) that swaps the sides.  With the right
 * multiplications the graph is vertex-transitive, so it has diameter <= D iff the ball of radius D-1 around (e,A)
 * contains the whole side of parity D-1:
 *     D = 2k+1:  X^k = G            (side B, Y^k = G, follows from the side swap)
 *     D = 2k:    S X^(k-1) = G      (this one condition suffices for every Haar graph; self-duality makes
 *                                    S X^(k-1) psi-invariant, so the misses come in psi-orbits)
 * The involutions are built per factor from the formulas, modulo inner automorphisms (translating S changes beta by
 * an inner automorphism, so only Out(G) matters, and for each beta the u0 up to u0 ~ u0 beta(w) w, w central):
 *   matrix groups: x -> l (h x h)^-1 for h = I and (q odd, SL/PSL) h = diag(1,nu), nu a non-square, l = +-det h
 *     (SL; PSL/PGL modulo scalars); e even: also x -> l sigma(x)^-1, sigma = Frobenius^(e/2);
 *   meta: beta(x) = x^a, beta(y) = y^v with a^2 = 1 mod m, v = 1 mod ord(r), v^2 = 1 mod k; u0 central and
 *     beta-fixed; a taken up to a ~ a r^j (r^2j = 1).
 * psi on G is the product of one option per factor.  PLAIN=1 adds the trivial "psi" (plain Haar graphs, energy of
 * both sides at odd D).
 *
 * Search: tabu inside the family (as research/selfdual-d5/src/sdtabu.c): S = f psi-fixed elements + m psi-2-orbits
 * (f + 2m = K, f = K mod 2; e need not be in S); a move replaces one fixed element or one orbit; NB random moves per
 * step, best non-tabu taken (aspiration), tenure TEN, restart after STALL steps without improvement.
 * Energy = number of vertices of the side of parity D-1 outside the ball of radius D-1 around (e,A).
 * Every energy-0 set gets a full BFS from (e,A) and (e,B) on the graph itself (no symmetry used) before it is reported.
 *
 * usage: sdhi K D FACTOR1 [FACTOR2]
 * env: PSI=i (only psi option i; default all), TYPES=digits (f values, as in sdtabu), SECS (per psi/type, default 20),
 *      SEED, NB (48), TEN (12), STALL (300), MAXSOL (5), DEEP=thr,secs, EDGES=file (edge list of the first solution),
 *      PLAIN=1, LIST=1 (print the psi options and exit), CHECK="d1 d2 .." (full check of a set given in the printed
 *      element format, edge list to EDGES), RANDS=n (energy statistics of n random sets per psi/type, no search).
 * output: GROUP line, PSI lines, "SOL ..." lines with the elements in readable form, one TABU line per psi/type, DONE.
 * element format: factors joined by '|'; a matrix [a b c d] has rows (a b), (c d) (field elements as integers, base p
 * digits = coefficients of 1, t, t^2, ..); a meta element (i,j) = x^i y^j; a cyclic element is z.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

/* ---------------- finite fields ---------------- */
typedef struct { int q, p, e, poly; int *add, *mul, *neg, *inv; int nonsq; } fld;
static int ipow(int b, int e) { int r = 1; while (e--) r *= b; return r; }
static void pdigits(int x, int p, int e, int *d) { for (int i = 0; i < e; i++) { d[i] = x % p; x /= p; } }
static int pundigits(const int *d, int p, int e) { int x = 0; for (int i = e - 1; i >= 0; i--) x = x * p + d[i]; return x; }
/* is x^e + sum c_i x^i irreducible over GF(p)? brute force: no monic divisor of degree 1..e/2 */
static int irreducible(int c, int p, int e) {
    int f[16]; pdigits(c, p, e, f); f[e] = 1;
    for (int dg = 1; dg <= e / 2; dg++) {
        int ng = ipow(p, dg);
        for (int g0 = 0; g0 < ng; g0++) {
            int g[16]; pdigits(g0, p, dg, g); g[dg] = 1;
            int r[16]; memcpy(r, f, sizeof(int) * (e + 1));
            for (int i = e; i >= dg; i--) { int t = r[i] % p; if (!t) continue;
                for (int j = 0; j <= dg; j++) r[i - dg + j] = ((r[i - dg + j] - t * g[j]) % p + p) % p; }
            int zero = 1; for (int i = 0; i < dg; i++) if (r[i] % p) zero = 0;
            if (zero) return 0;
        }
    }
    return 1;
}
static fld *mkfield(int q) {
    fld *F = calloc(1, sizeof(fld)); F->q = q;
    int p = 2; while (q % p) p++;
    int e = 0, t = q; while (t % p == 0) { t /= p; e++; }
    if (t != 1) { fprintf(stderr, "q = %d is not a prime power\n", q); exit(2); }
    F->p = p; F->e = e; F->poly = -1;
    if (e > 1) { for (int c = 0; c < q; c++) if (irreducible(c, p, e)) { F->poly = c; break; } }
    F->add = malloc(sizeof(int) * q * q); F->mul = malloc(sizeof(int) * q * q);
    F->neg = malloc(sizeof(int) * q); F->inv = malloc(sizeof(int) * q);
    int fc[16]; if (e > 1) pdigits(F->poly, p, e, fc);
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) {
        int da[16], db[16], ds[16], pr[32] = {0};
        pdigits(a, p, e, da); pdigits(b, p, e, db);
        for (int i = 0; i < e; i++) ds[i] = (da[i] + db[i]) % p;
        F->add[a * q + b] = pundigits(ds, p, e);
        for (int i = 0; i < e; i++) for (int j = 0; j < e; j++) pr[i + j] = (pr[i + j] + da[i] * db[j]) % p;
        for (int i = 2 * e - 2; i >= e; i--) { int c = pr[i]; if (!c) continue; pr[i] = 0;
            for (int j = 0; j < e; j++) pr[i - e + j] = ((pr[i - e + j] - c * fc[j]) % p + p) % p; }
        F->mul[a * q + b] = pundigits(pr, p, e);
    }
    for (int a = 0; a < q; a++) { for (int b = 0; b < q; b++) if (F->add[a * q + b] == 0) F->neg[a] = b;
        F->inv[a] = 0; for (int b = 1; b < q; b++) if (F->mul[a * q + b] == 1) F->inv[a] = b; }
    char *sq = calloc(q, 1); for (int a = 1; a < q; a++) sq[F->mul[a * q + a]] = 1;
    F->nonsq = 0; for (int a = 1; a < q; a++) if (!sq[a]) { F->nonsq = a; break; }
    free(sq);
    return F;
}
#define FA(F, a, b) ((F)->add[(a) * (F)->q + (b)])
#define FM(F, a, b) ((F)->mul[(a) * (F)->q + (b)])
static int fpowf(const fld *F, int a, int e) { int r = 1; while (e--) r = FM(F, r, a); return r; }

/* ---------------- group factors ---------------- */
enum { T_SL = 1, T_PSL, T_PGL, T_META };
#define TABMAX 8192
#define MAXOPT 256
typedef struct {
    int type, size;
    fld *F; int *mat; int *lookup;            /* matrix groups: entries of element i at mat[4i..], lookup over q^4 */
    int m, k, r, *RP, *EI, *EJ;               /* meta */
    uint16_t *tab; int *inv;
    int nopt; int *opt[MAXOPT]; char optd[MAXOPT][96];
    char name[64];
} factor;

static void mmul(const fld *F, const int *A, const int *B, int *C) {
    C[0] = FA(F, FM(F, A[0], B[0]), FM(F, A[1], B[2])); C[1] = FA(F, FM(F, A[0], B[1]), FM(F, A[1], B[3]));
    C[2] = FA(F, FM(F, A[2], B[0]), FM(F, A[3], B[2])); C[3] = FA(F, FM(F, A[2], B[1]), FM(F, A[3], B[3]));
}
static int mdet(const fld *F, const int *A) { return FA(F, FM(F, A[0], A[3]), F->neg[FM(F, A[1], A[2])]); }
static void minv(const fld *F, const int *A, int *B) {
    int di = F->inv[mdet(F, A)];
    B[0] = FM(F, di, A[3]); B[1] = FM(F, di, F->neg[A[1]]); B[2] = FM(F, di, F->neg[A[2]]); B[3] = FM(F, di, A[0]);
}
static void mscal(const fld *F, int l, const int *A, int *B) { for (int i = 0; i < 4; i++) B[i] = FM(F, l, A[i]); }
static int lexless(const int *A, const int *B) { for (int i = 0; i < 4; i++) if (A[i] != B[i]) return A[i] < B[i]; return 0; }
/* canonical representative (in place) of the class of A in the factor's group */
static void mcanon(const factor *Q, int *A) {
    const fld *F = Q->F;
    if (Q->type == T_PSL) { int B[4]; mscal(F, F->neg[1], A, B); if (lexless(B, A)) memcpy(A, B, sizeof B); }
    else if (Q->type == T_PGL) { int s = A[0] ? A[0] : A[1]; int si = F->inv[s]; int B[4]; mscal(F, si, A, B); memcpy(A, B, sizeof B); }
}
static int mindex(const factor *Q, const int *A0) {
    int A[4]; memcpy(A, A0, sizeof A); mcanon(Q, A); int q = Q->F->q;
    int x = Q->lookup[((A[0] * q + A[1]) * q + A[2]) * q + A[3]];
    if (x < 0) { fprintf(stderr, "mindex: matrix not in group\n"); exit(3); }
    return x;
}
static inline int fmul(const factor *Q, int a, int b) {
    if (Q->tab) return Q->tab[(size_t)a * Q->size + b];
    /* meta formula: (i,j)(i',j') = (i + r^j i', j + j') */
    int i = Q->EI[a], j = Q->EJ[a], i2 = Q->EI[b], j2 = Q->EJ[b];
    int ni = (int)((i + (long long)Q->RP[j] * i2) % Q->m), nj = j + j2; if (nj >= Q->k) nj -= Q->k;
    return ni * Q->k + nj;
}
static int fmul_slow(const factor *Q, int a, int b) {
    if (Q->type == T_META) {
        int i = Q->EI[a], j = Q->EJ[a], i2 = Q->EI[b], j2 = Q->EJ[b];
        return (int)((i + (long long)Q->RP[j] * i2) % Q->m) * Q->k + (j + j2) % Q->k;
    }
    int C[4]; mmul(Q->F, Q->mat + 4 * a, Q->mat + 4 * b, C); return mindex(Q, C);
}
static void build_tab(factor *Q) {
    if (Q->size > TABMAX) { Q->tab = NULL; return; }
    Q->tab = malloc(sizeof(uint16_t) * (size_t)Q->size * Q->size);
    for (int a = 0; a < Q->size; a++) for (int b = 0; b < Q->size; b++) Q->tab[(size_t)a * Q->size + b] = fmul_slow(Q, a, b);
}
static void add_opt(factor *Q, int *p, const char *d) {
    /* involution check; drop duplicates */
    for (int i = 0; i < Q->size; i++) if (p[p[i]] != i) { fprintf(stderr, "%s: option %s is not an involution (dropped)\n", Q->name, d); free(p); return; }
    for (int o = 0; o < Q->nopt; o++) if (!memcmp(Q->opt[o], p, sizeof(int) * Q->size)) { free(p); return; }
    if (Q->nopt >= MAXOPT) { free(p); return; }
    Q->opt[Q->nopt] = p; snprintf(Q->optd[Q->nopt], 96, "%s", d); Q->nopt++;
}
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a < 0 ? -a : a; }

static factor *mk_matrix(int type, int q) {
    factor *Q = calloc(1, sizeof(factor)); Q->type = type; fld *F = Q->F = mkfield(q);
    snprintf(Q->name, sizeof Q->name, "%s(2,%d)", type == T_SL ? "SL" : type == T_PSL ? "PSL" : "PGL", q);
    if (type == T_PSL && F->p == 2) Q->type = type = T_SL;      /* PSL = SL in characteristic 2 */
    if (type == T_PGL && F->p == 2) Q->type = type = T_SL;      /* PGL = SL in characteristic 2 */
    size_t q4 = (size_t)q * q * q * q; Q->lookup = malloc(sizeof(int) * q4); for (size_t i = 0; i < q4; i++) Q->lookup[i] = -1;
    int cap = q * (q * q - 1) + 1; Q->mat = malloc(sizeof(int) * 4 * cap); Q->size = 0;
    int I[4] = {1, 0, 0, 1};
    /* identity first */
    memcpy(Q->mat, I, sizeof I); Q->lookup[((1 * q + 0) * q + 0) * q + 1] = 0; Q->size = 1;
    for (int a = 0; a < q; a++) for (int b = 0; b < q; b++) for (int c = 0; c < q; c++) for (int d = 0; d < q; d++) {
        int A[4] = {a, b, c, d}; int dt = mdet(F, A);
        if (type == T_PGL) { if (!dt) continue; } else if (dt != 1) continue;
        int B[4]; memcpy(B, A, sizeof B); mcanon(Q, B); if (memcmp(A, B, sizeof A)) continue;
        if (!memcmp(A, I, sizeof I)) continue;
        memcpy(Q->mat + 4 * Q->size, A, sizeof A); Q->lookup[((a * q + b) * q + c) * q + d] = Q->size; Q->size++;
    }
    build_tab(Q);
    Q->inv = malloc(sizeof(int) * Q->size);
    for (int i = 0; i < Q->size; i++) { int B[4]; minv(F, Q->mat + 4 * i, B); Q->inv[i] = mindex(Q, B); }
    /* psi options: x -> l h^-1 x^-1 h^-1 */
    int hs[2][4] = {{1, 0, 0, 1}, {1, 0, 0, F->nonsq}}; int nh = (F->p == 2 || type == T_PGL) ? 1 : 2;
    for (int hi = 0; hi < nh; hi++) {
        int *h = hs[hi], hinv[4]; minv(F, h, hinv); int dh = mdet(F, h);
        int nl = (type == T_SL && F->p != 2) ? 2 : 1;
        for (int li = 0; li < nl; li++) {
            int l = li ? F->neg[dh] : dh;
            int *p = malloc(sizeof(int) * Q->size);
            for (int x = 0; x < Q->size; x++) { int xi[4], t1[4], t2[4]; minv(F, Q->mat + 4 * x, xi);
                mmul(F, hinv, xi, t1); mmul(F, t1, hinv, t2); mscal(F, l, t2, t1); p[x] = mindex(Q, t1); }
            char d[96]; snprintf(d, 96, "x->%s(hxh)^-1,h=diag(1,%d)", li ? "-" : "", hi ? F->nonsq : 1);
            if (hi == 0) snprintf(d, 96, "x->%sx^-1", li ? "-" : "");
            add_opt(Q, p, d);
        }
    }
    if (F->e % 2 == 0) {   /* field automorphism of order 2 */
        int fr = ipow(F->p, F->e / 2);
        int nl = (type == T_SL && F->p != 2) ? 2 : 1;
        for (int li = 0; li < nl; li++) {
            int l = li ? F->neg[1] : 1;
            int *p = malloc(sizeof(int) * Q->size);
            for (int x = 0; x < Q->size; x++) { int sx[4], si[4], t[4];
                for (int i = 0; i < 4; i++) sx[i] = fpowf(F, Q->mat[4 * x + i], fr);
                minv(F, sx, si); mscal(F, l, si, t); p[x] = mindex(Q, t); }
            char d[96]; snprintf(d, 96, "x->%ssigma(x)^-1,sigma=frob^%d", li ? "-" : "", F->e / 2);
            add_opt(Q, p, d);
        }
    }
    return Q;
}
static long long lpow(long long b, long long e, long long m) { long long r = 1 % m; b %= m; if (b < 0) b += m; while (e) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; } return r; }
static factor *mk_meta(int m, int k, int r) {
    factor *Q = calloc(1, sizeof(factor)); Q->type = T_META; Q->m = m; Q->k = k; Q->r = ((r % m) + m) % m; if (k == 1) Q->r = 1 % m;
    if (k == 1) snprintf(Q->name, sizeof Q->name, "Z%d", m); else snprintf(Q->name, sizeof Q->name, "C%d:C%d(r=%d)", m, k, r);
    if (m > 1 && lpow(Q->r, k, m) != 1) { fprintf(stderr, "meta: r^k != 1 mod m\n"); exit(2); }
    if (m > 1 && gcd(Q->r, m) != 1) { fprintf(stderr, "meta: r not a unit\n"); exit(2); }
    Q->size = m * k; Q->RP = malloc(sizeof(int) * k); for (int j = 0; j < k; j++) Q->RP[j] = (int)lpow(Q->r, j, m);
    Q->EI = malloc(sizeof(int) * Q->size); Q->EJ = malloc(sizeof(int) * Q->size);
    for (int i = 0; i < m; i++) for (int j = 0; j < k; j++) { Q->EI[i * k + j] = i; Q->EJ[i * k + j] = j; }
    build_tab(Q);
    Q->inv = malloc(sizeof(int) * Q->size);
    for (int g = 0; g < Q->size; g++) { int i = Q->EI[g], j = Q->EJ[g]; int nj = (k - j) % k;
        int ni = (int)((m - (long long)Q->RP[nj] * i % m) % m); Q->inv[g] = ni * k + nj; }
    for (int g = 0; g < Q->size; g++) if (fmul_slow(Q, g, Q->inv[g]) != 0) { fprintf(stderr, "meta inverse bug\n"); exit(3); }
    /* psi options */
    int d = 1; if (m > 1) { long long t = Q->r; while (t != 1 % m) { t = t * Q->r % m; d++; } }
    int X = (m > 1) ? 1 * k + 0 : 0, Y = (k > 1) ? 0 * k + 1 : 0;
    int *cent = malloc(sizeof(int) * Q->size), nc = 0;
    for (int g = 0; g < Q->size; g++) if (fmul_slow(Q, g, X) == fmul_slow(Q, X, g) && fmul_slow(Q, g, Y) == fmul_slow(Q, Y, g)) cent[nc++] = g;
    for (int a = 1; a <= (m > 1 ? m - 1 : 1); a++) {
        if (m > 1 && (gcd(a, m) != 1 || (long long)a * a % m != 1)) continue;
        /* a up to a r^j with r^2j = 1 */
        int skip = 0; long long rj = 1;
        for (int j = 0; j < d && m > 1; j++, rj = rj * Q->r % m) if (rj * rj % m == 1 && rj * a % m < a) skip = 1;
        if (skip) continue;
        for (int v = 1; v <= k; v++) {
            if (gcd(v, k) != 1 || (v - 1) % d || ((long long)v * v) % k != 1 % k) continue;
            int *be = malloc(sizeof(int) * Q->size);
            for (int g = 0; g < Q->size; g++) { int i = Q->EI[g], j = Q->EJ[g]; be[g] = (int)((long long)a * i % (m > 1 ? m : 1)) * k + (int)((long long)v * j % k); }
            int ok = 1;
            for (int g = 0; g < Q->size && ok; g++) { if (be[fmul_slow(Q, g, X)] != fmul_slow(Q, be[g], be[X])) ok = 0;
                if (be[fmul_slow(Q, g, Y)] != fmul_slow(Q, be[g], be[Y])) ok = 0; }
            if (!ok) { free(be); continue; }
            /* u0: central, beta-fixed, up to u0 ~ u0 beta(w) w (w central) */
            char *seen = calloc(Q->size, 1);
            for (int ci = 0; ci < nc; ci++) {
                int u0 = cent[ci]; if (be[u0] != u0 || seen[u0]) continue;
                for (int wi = 0; wi < nc; wi++) { int w = cent[wi]; seen[fmul_slow(Q, fmul_slow(Q, u0, be[w]), w)] = 1; }
                int *p = malloc(sizeof(int) * Q->size);
                for (int g = 0; g < Q->size; g++) p[g] = fmul_slow(Q, u0, Q->inv[be[g]]);
                char dd[96];
                if (k == 1) snprintf(dd, 96, "z->%d-%d*z", Q->EI[u0], a);
                else snprintf(dd, 96, "u0*beta(g)^-1,beta(x)=x^%d,beta(y)=y^%d,u0=(%d,%d)", a, v, Q->EI[u0], Q->EJ[u0]);
                add_opt(Q, p, dd);
            }
            free(seen); free(be);
        }
    }
    free(cent);
    return Q;
}
static factor *parse_factor(char **argv, int argc, int *ai) {
    if (*ai >= argc) return mk_meta(1, 1, 0);
    const char *w = argv[(*ai)++];
    if (!strcmp(w, "sl") || !strcmp(w, "psl") || !strcmp(w, "pgl")) {
        int q = atoi(argv[(*ai)++]);
        return mk_matrix(!strcmp(w, "sl") ? T_SL : !strcmp(w, "psl") ? T_PSL : T_PGL, q);
    }
    if (!strcmp(w, "meta")) { int m = atoi(argv[(*ai)++]), k = atoi(argv[(*ai)++]), r = atoi(argv[(*ai)++]); return mk_meta(m, k, r); }
    if (!strcmp(w, "cyc")) { int n = atoi(argv[(*ai)++]); return mk_meta(n, 1, 0); }
    fprintf(stderr, "unknown factor %s\n", w); exit(2);
}
static void fdesc(const factor *Q, int x, char *buf) {
    if (Q->type == T_META) { if (Q->k == 1) sprintf(buf, "%d", Q->EI[x]); else sprintf(buf, "(%d,%d)", Q->EI[x], Q->EJ[x]); }
    else { const int *A = Q->mat + 4 * x; sprintf(buf, "[%d %d %d %d]", A[0], A[1], A[2], A[3]); }
}
/* parse one factor element from text; returns pointer after it */
static const char *fparse(const factor *Q, const char *s, int *x) {
    while (*s == ' ') s++;
    if (Q->type == T_META) {
        if (Q->k == 1) { int z; int nch; sscanf(s, "%d%n", &z, &nch); *x = ((z % Q->m) + Q->m) % Q->m * Q->k; return s + nch; }
        int i, j, nch; if (sscanf(s, "(%d,%d)%n", &i, &j, &nch) != 2) { fprintf(stderr, "parse error at %s\n", s); exit(2); }
        *x = (((i % Q->m) + Q->m) % Q->m) * Q->k + ((j % Q->k) + Q->k) % Q->k; return s + nch;
    }
    int A[4], nch; if (sscanf(s, "[%d %d %d %d]%n", A, A + 1, A + 2, A + 3, &nch) != 4) { fprintf(stderr, "parse error at %s\n", s); exit(2); }
    *x = mindex(Q, A); return s + nch;
}

/* ---------------- the group G = Q1 x Q2 ---------------- */
static factor *Q1, *Q2; static int N, n2, K = 5, D = 7;
static int *E1, *E2, *ginvv;
static inline int gm(int a, int b) { return fmul(Q1, E1[a], E1[b]) * n2 + fmul(Q2, E2[a], E2[b]); }
static void gdesc(int g, char *buf) { char b1[64], b2[64]; fdesc(Q1, E1[g], b1); fdesc(Q2, E2[g], b2); sprintf(buf, "%s|%s", b1, b2); }

/* ---------------- energy ---------------- */
static uint32_t *mk, *mk2, st1 = 0, st2 = 0; static int *buf;
static int sd = 1;   /* 1: self-dual family (one side), 0: plain (both sides at odd D) */
/* number of vertices of the target side outside the ball of radius D-1 around (e,A) (left = 1) or (e,B) (left = 0) */
static int uncov_side(const int *S, int k, int left) {
    int X[4096], nx = 0; st1++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) {
        int x = left ? gm(ginvv[S[i]], S[j]) : gm(S[i], ginvv[S[j]]);
        if (mk[x] != st1) { mk[x] = st1; X[nx++] = x; } }
    int half = (D - 1) / 2;   /* odd D: X^half; even D: S X^(half) with D-1 = 2 half + 1 */
    /* buf holds X^j; new elements in [lo, hi) */
    int nb = 0; for (int i = 0; i < nx; i++) buf[nb++] = X[i];
    int lo = 0, hi = nb;
    for (int lev = 2; lev <= half; lev++) {
        for (int t = lo; t < hi; t++) { int b = buf[t];
            for (int i = 0; i < nx; i++) { int z = gm(b, X[i]); if (mk[z] != st1) { mk[z] = st1; buf[nb++] = z; } } }
        lo = hi; hi = nb;
        if (nb == N) break;
    }
    if (D % 2) return N - nb;
    /* even D: count S X^half (left) or S^-1 Y^half (right) */
    st2++; int cov = 0;
    for (int t = 0; t < nb; t++) { int b = buf[t];
        for (int i = 0; i < k; i++) { int z = left ? gm(S[i], b) : gm(ginvv[S[i]], b); if (mk2[z] != st2) { mk2[z] = st2; cov++; } } }
    return N - cov;
}
static int energy(const int *S, int k) {
    int e = uncov_side(S, k, 1);
    if (!sd && D % 2) e += uncov_side(S, k, 0);
    return e;
}
/* full check on the graph: BFS from (e,A) and (e,B), distinct elements; returns 1 iff diameter <= D */
static int fullcheck(const int *S, int k, int *diam_out) {
    for (int i = 0; i < k; i++) for (int j = i + 1; j < k; j++) if (S[i] == S[j]) return 0;
    int *dist = malloc(sizeof(int) * 2 * N), *qq = malloc(sizeof(int) * 2 * N); int ok = 1, diam = 0;
    for (int side = 0; side < 2; side++) {
        for (int i = 0; i < 2 * N; i++) dist[i] = -1;
        int src = side ? N : 0; dist[src] = 0; int h = 0, t = 0; qq[t++] = src;
        while (h < t) { int v = qq[h++];
            for (int i = 0; i < k; i++) { int w = v < N ? N + gm(S[i], v) : gm(ginvv[S[i]], v - N);
                if (dist[w] < 0) { dist[w] = dist[v] + 1; qq[t++] = w; } } }
        if (t != 2 * N) ok = 0;
        for (int i = 0; i < 2 * N; i++) if (dist[i] > diam) diam = dist[i];
    }
    free(dist); free(qq);
    if (diam_out) *diam_out = diam;
    return ok && diam <= D;
}
static void write_edges(const char *path, const int *S, int k) {
    FILE *o = fopen(path, "w"); if (!o) { perror(path); return; }
    fprintf(o, "%d\n", 2 * N);
    for (int g = 0; g < N; g++) for (int i = 0; i < k; i++) fprintf(o, "%d %d\n", g, N + gm(S[i], g));
    fclose(o);
}

/* ---------------- psi and the family ---------------- */
static int *psi, *fl, nfl, (*ol)[2], nol;
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void setup_psi(int o1, int o2) {
    if (o1 < 0) { for (int g = 0; g < N; g++) psi[g] = g; }
    else for (int g = 0; g < N; g++) psi[g] = Q1->opt[o1][E1[g]] * n2 + Q2->opt[o2][E2[g]];
    nfl = nol = 0;
    for (int g = 0; g < N; g++) {
        if (psi[psi[g]] != g) { fprintf(stderr, "psi not an involution\n"); exit(3); }
        if (psi[g] == g) fl[nfl++] = g; else if (g < psi[g]) { ol[nol][0] = g; ol[nol][1] = psi[g]; nol++; }
    }
}

static int nf_, nm_, it[64], nit, S[64];
static long long *tabu_until, step;
static int build(void) {
    int at = 0;
    for (int i = 0; i < nit; i++) { int x = it[i];
        if (x < nfl) S[at++] = fl[x]; else { S[at++] = ol[x - nfl][0]; S[at++] = ol[x - nfl][1]; } }
    return at;
}
static int used(int x) { for (int i = 0; i < nit; i++) if (it[i] == x) return 1; return 0; }
static int rand_item(int isfix) {
    for (int t = 0; t < 1000; t++) { int x = isfix ? (int)(rnd() % nfl) : nfl + (int)(rnd() % nol); if (!used(x)) return x; }
    return -1;
}
static void randomize(void) {
    nit = 0;
    for (int i = 0; i < nf_; i++) { int x = rand_item(1); it[nit++] = x; }
    for (int i = 0; i < nm_; i++) { int x = rand_item(0); it[nit++] = x; }
}
static const char *edges_out; static int nsol = 0;
static void report(const char *tag, const int *SS, int k) {
    int diam; if (!fullcheck(SS, k, &diam)) { fprintf(stderr, "WARNING %s: energy 0 but the full check fails (diam %d)\n", tag, diam); return; }
    nsol++;
    printf("SOL %s diam %d S", tag, diam); for (int i = 0; i < k; i++) printf(" %d", SS[i]);
    printf(" ="); for (int i = 0; i < k; i++) { char b[160]; gdesc(SS[i], b); printf(" %s", b); } printf("\n"); fflush(stdout);
    if (edges_out && nsol == 1) write_edges(edges_out, SS, k);
}

/* ---------------- exhaustive enumeration (ENUM=1, self-dual family only) ----------------
 * Fast rejection: the target side is L P with P = X^j precomputed (stamps) and L a short list of left factors
 * (odd D = 2k+1: L = X, P = X^(k-1); even D = 2k: L = S X, P = X^(k-2)); z is covered iff l^-1 z is in P for some
 * l in L; targets in move-to-front order.  Every set that passes gets energy() and the full check.
 * Normalisation: Gamma = the automorphisms commuting with psi among the inner ones (conj(g), all g in G) and the
 * factor-level ones (z -> c z on cyclic factors, x -> x^c on meta factors, conj by diag(1,nu) and Frobenius on
 * matrix factors); the first orbit (or, for m = 0, the first fixed element) runs over Gamma-orbit representatives. */
static int *ordA; static long long n_enum, n_pass;
static int quick(const int *SS, int k) {
    static int X[4096], L[65536], Li[65536]; int nx = 0; st1++;
    for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) { int x = gm(ginvv[SS[i]], SS[j]); if (mk[x] != st1) { mk[x] = st1; X[nx++] = x; } }
    int half = (D - 1) / 2, plev = (D % 2) ? half - 1 : half - 1;   /* odd: P = X^(half-1), L = X; even: P = X^(half-1), L = S X */
    int nb = 0; for (int i = 0; i < nx; i++) buf[nb++] = X[i];
    int lo = 0, hi = nb;
    if (plev == 0) { st1++; nb = 0; mk[0] = st1; buf[nb++] = 0; }
    for (int lev = 2; lev <= plev; lev++) {
        for (int t = lo; t < hi; t++) { int b = buf[t];
            for (int i = 0; i < nx; i++) { int z = gm(b, X[i]); if (mk[z] != st1) { mk[z] = st1; buf[nb++] = z; } } }
        lo = hi; hi = nb;
    }
    int nl = 0;
    if (D % 2) { for (int i = 0; i < nx; i++) L[nl++] = X[i]; }
    else { st2++; for (int i = 0; i < k; i++) for (int j = 0; j < nx; j++) { int z = gm(SS[i], X[j]); if (mk2[z] != st2) { mk2[z] = st2; L[nl++] = z; } } }
    for (int i = 0; i < nl; i++) Li[i] = ginvv[L[i]];
    for (int t = 0; t < N; t++) { int z = ordA[t], ok = 0;
        for (int i = 0; i < nl; i++) if (mk[gm(Li[i], z)] == st1) { ok = 1; break; }
        if (!ok) { if (t) { int u = t / 2; ordA[t] = ordA[u]; ordA[u] = z; } return 0; } }
    return 1;
}
static int Sb[64], enf, enm; static char etag[160]; static long long ecap = 0; static int ecapped, esols, ebest;
static int *orep, *frep; static int norep, nfrep, *forb;   /* Gamma-orbit representatives of 2-orbits and of fixed points */
static void eval_set(int k) {
    if (ecap && n_enum >= ecap) { ecapped = 1; return; }
    n_enum++;
    if (quick(Sb, k)) { n_pass++; int e = energy(Sb, k); if (e < ebest) ebest = e;
        if (e == 0) { report(etag, Sb, k); esols++; } }
}
static void rec_f(int need, int from, int at, int skipf) {
    if (ecapped) return;
    if (need == 0) { eval_set(at); return; }
    for (int i = from; i < nfl; i++) if (i != skipf) { Sb[at] = fl[i]; rec_f(need - 1, i + 1, at + 1, skipf); if (ecapped) return; }
}
static void rec_o(int need, int from, int at, int skipo) {
    if (ecapped) return;
    if (need == 0) { rec_f(enf, 0, at, -1); return; }
    for (int o = from; o < nol; o++) if (o != skipo) { Sb[at] = ol[o][0]; Sb[at + 1] = ol[o][1]; rec_o(need - 1, o + 1, at + 2, skipo); if (ecapped) return; }
}
static int ufind(int *uf, int x) { while (uf[x] != x) x = uf[x] = uf[uf[x]]; return x; }
static void ujoin(int *uf, int a, int b) { a = ufind(uf, a); b = ufind(uf, b); if (a != b) { if (a < b) uf[b] = a; else uf[a] = b; } }
/* factor-level automorphism candidates (as permutations of the factor) */
static int fauts(const factor *Q, int **out, int maxn) {
    int n = 0;
    if (Q->type == T_META) {
        int m = Q->m;
        for (int c = 2; c < m && n < maxn; c++) { if (gcd(c, m) != 1) continue;
            int *p = malloc(sizeof(int) * Q->size); for (int g = 0; g < Q->size; g++) p[g] = (int)((long long)c * Q->EI[g] % m) * Q->k + Q->EJ[g];
            out[n++] = p; }
    } else {
        const fld *F = Q->F;
        if (F->p != 2 && Q->type != T_PGL) { int h[4] = {1, 0, 0, F->nonsq}, hi[4]; minv(F, h, hi);
            int *p = malloc(sizeof(int) * Q->size);
            for (int x = 0; x < Q->size; x++) { int t1[4], t2[4]; mmul(F, h, Q->mat + 4 * x, t1); mmul(F, t1, hi, t2); p[x] = mindex(Q, t2); }
            out[n++] = p; }
        if (F->e > 1) { int *p = malloc(sizeof(int) * Q->size);
            for (int x = 0; x < Q->size; x++) { int t[4]; for (int i = 0; i < 4; i++) t[i] = fpowf(F, Q->mat[4 * x + i], F->p); p[x] = mindex(Q, t); }
            out[n++] = p; }
    }
    return n;
}
static void gamma_reps(int o1, int o2) {
    int *uf = malloc(sizeof(int) * N), *orbid = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) uf[g] = g;
    /* elements are joined when a generator maps one to the other; 2-orbits and fixed points are unions of these */
    int ngen = 0;
    int *img = malloc(sizeof(int) * N);
    /* inner: conj(g) commuting with psi; to keep the cost down use at most 64 random commuting g */
    int tried = 0;
    while (ngen < 64 && tried < 20 * N) {
        int g = tried < N ? tried : (int)(rnd() % N); tried++;
        if (g == 0) continue;
        int gi = ginvv[g], ok = 1;
        for (int x = 0; x < N && ok; x++) { img[x] = gm(gm(g, x), gi); }
        for (int x = 0; x < N && ok; x++) if (img[psi[x]] != psi[img[x]]) ok = 0;
        if (!ok) continue;
        for (int x = 0; x < N; x++) ujoin(uf, x, img[x]);
        ngen++;
        if (tried >= N && ngen >= 16) break;
    }
    /* factor-level */
    for (int side = 0; side < 2; side++) {
        const factor *Q = side ? Q2 : Q1; int *P[512]; int na = fauts(Q, P, 512);
        int *fp = side ? Q2->opt[o2] : Q1->opt[o1];
        for (int a = 0; a < na; a++) {
            int ok = 1; for (int x = 0; x < Q->size && ok; x++) if (P[a][fp[x]] != fp[P[a][x]]) ok = 0;
            if (ok) { for (int g = 0; g < N; g++) { int h = side ? E1[g] * n2 + P[a][E2[g]] : P[a][E1[g]] * n2 + E2[g]; ujoin(uf, g, h); } ngen++; }
            free(P[a]);
        }
    }
    /* representatives: a 2-orbit {x, psi x} is joined with {y, psi y} when x ~ y (the generators commute with psi) */
    norep = nfrep = 0; char *seen = calloc(N, 1);
    for (int o = 0; o < nol; o++) { int r = ufind(uf, ol[o][0]); int r2 = ufind(uf, ol[o][1]); int rr = r < r2 ? r : r2;
        if (!seen[rr]) { seen[rr] = 1; orep[norep++] = o; } }
    memset(seen, 0, N);
    for (int i = 0; i < nfl; i++) { int r = ufind(uf, fl[i]); if (!seen[r]) { seen[r] = 1; frep[nfrep++] = i; } }
    free(seen); free(uf); free(orbid); free(img);
    printf("GAMMA generators %d: %d of %d 2-orbits and %d of %d fixed points are representatives\n", ngen, norep, nol, nfrep, nfl); fflush(stdout);
}
static double binom(int n, int k) { if (k < 0 || k > n) return 0; double r = 1; for (int i = 0; i < k; i++) r = r * (n - i) / (i + 1); return r; }
static double enum_count(int f, int m) {
    if (f > nfl || m > nol) return 0;
    if (m >= 1) return norep * binom(nol - 1, m - 1) * binom(nfl, f);
    return nfrep * binom(nfl - 1, f - 1);
}
static void enumerate(const char *ptag, int f, int m) {
    if (f > nfl || m > nol || (f == 0 && m == 0)) return;
    snprintf(etag, sizeof etag, "%s_f%d_m%d_enum", ptag, f, m);
    double c0 = now(); n_enum = n_pass = 0; ecapped = 0; esols = 0; ebest = 1 << 30;
    if (m >= 1) {
        enf = f;
        for (int r = 0; r < norep && !ecapped; r++) { int o = orep[r]; Sb[0] = ol[o][0]; Sb[1] = ol[o][1]; rec_o(m - 1, 0, 2, o); }
    } else {
        for (int r = 0; r < nfrep && !ecapped; r++) { int i = frep[r]; Sb[0] = fl[i]; rec_f(f - 1, 0, 1, i); }
    }
    printf("ENUM %s sets %lld passed %lld best %d sols %d secs %.1f%s\n", etag, n_enum, n_pass, ebest == (1 << 30) ? -1 : ebest, esols, now() - c0, ecapped ? " CAPPED" : "");
    fflush(stdout);
}

static double deep_secs = 0; static int deep_thr = 0;
static void run(const char *ptag, int f, int m, double secs, int NB, int TEN, int STALL, int MAXSOL) {
    nf_ = f; nm_ = m;
    if (nf_ > nfl || nm_ > nol || (nf_ == 0 && nm_ == 0)) return;
    if (nf_ + nm_ > 64) return;
    char tag[160]; snprintf(tag, sizeof tag, "%s_f%d_m%d", ptag, f, m);
    tabu_until = calloc(nfl + nol, sizeof(long long)); step = 0;
    double c0 = now(); int best = 1 << 30, sols = 0, restarts = 0; long long evals = 0;
    randomize(); int k = build(); int e = energy(S, k), runbest = e; long long last_imp = 0; evals++;
    if (e < best) best = e;
    int extended = 0;
    for (;;) {
        double el = now() - c0;
        if (sols >= MAXSOL) break;
        if (el >= secs) { if (!extended && deep_secs > 0 && best <= deep_thr) { secs += deep_secs; extended = 1; } else break; }
        if (e == 0) {
            report(tag, S, k); sols++;
            randomize(); k = build(); e = energy(S, k); evals++; runbest = e; last_imp = step; restarts++; continue;
        }
        step++;
        int bi = -1, bx = -1, be = 1 << 30;
        for (int t = 0; t < NB; t++) {
            int i = (int)(rnd() % nit), isfix = it[i] < nfl; int x = rand_item(isfix); if (x < 0) continue;
            int old = it[i]; it[i] = x; int kk = build(); int e2 = energy(S, kk); evals++; it[i] = old;
            if (tabu_until[x] > step && e2 >= best) continue;
            if (e2 < be) { be = e2; bi = i; bx = x; }
        }
        if (bi < 0) continue;
        tabu_until[it[bi]] = step + TEN; it[bi] = bx; e = be; k = build();
        if (e < runbest) { runbest = e; last_imp = step; }
        if (e < best) best = e;
        if (e > 0 && step - last_imp > STALL) { randomize(); k = build(); e = energy(S, k); evals++; runbest = e; last_imp = step; restarts++; }
    }
    printf("TABU %s best %d sols %d steps %lld evals %lld restarts %d secs %.1f%s\n", tag, best, sols, step, evals, restarts,
           now() - c0, extended ? " DEEP" : "");
    fflush(stdout); free(tabu_until);
}
static void rands(const char *ptag, int f, int m, int cnt) {
    nf_ = f; nm_ = m;
    if (nf_ > nfl || nm_ > nol || (nf_ == 0 && nm_ == 0)) return;
    long long sum = 0; int mn = 1 << 30; double c0 = now();
    for (int t = 0; t < cnt; t++) { randomize(); int k = build(); int e = energy(S, k); sum += e; if (e < mn) mn = e;
        if (e == 0) { char tag[160]; snprintf(tag, sizeof tag, "%s_f%d_m%d_rand", ptag, f, m); report(tag, S, k); } }
    printf("RANDS %s_f%d_m%d n %d min %d mean %.1f secs %.2f\n", ptag, f, m, cnt, mn, (double)sum / cnt, now() - c0); fflush(stdout);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: sdhi K D FACTOR1 [FACTOR2]\n"); return 2; }
    K = atoi(argv[1]); D = atoi(argv[2]);
    int ai = 3; Q1 = parse_factor(argv, argc, &ai); Q2 = parse_factor(argv, argc, &ai);
    N = Q1->size * Q2->size; n2 = Q2->size;
    E1 = malloc(sizeof(int) * N); E2 = malloc(sizeof(int) * N); ginvv = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) { E1[g] = g / n2; E2[g] = g % n2; }
    for (int g = 0; g < N; g++) ginvv[g] = Q1->inv[E1[g]] * n2 + Q2->inv[E2[g]];
    for (int g = 0; g < N; g++) if (gm(g, ginvv[g]) != 0 || gm(0, g) != g) { fprintf(stderr, "group bug\n"); return 3; }
    mk = calloc(N, sizeof(uint32_t)); mk2 = calloc(N, sizeof(uint32_t)); buf = malloc(sizeof(int) * (N + 16));
    psi = malloc(sizeof(int) * N); fl = malloc(sizeof(int) * N); ol = malloc(sizeof(int) * 2 * N);
    orep = malloc(sizeof(int) * N); frep = malloc(sizeof(int) * N); ordA = malloc(sizeof(int) * N);
    for (int g = 0; g < N; g++) ordA[g] = g;
    if (getenv("ECAP")) ecap = atoll(getenv("ECAP"));
    printf("GROUP %s x %s N %d (Haar graph on %d vertices) K %d D %d", Q1->name, Q2->name, N, 2 * N, K, D);
    if (Q1->F && Q1->F->e > 1) printf(" field poly %d (base %d coefficients of x^0..x^%d, monic)", Q1->F->poly, Q1->F->p, Q1->F->e - 1);
    printf("\n");
    double secs = getenv("SECS") ? atof(getenv("SECS")) : 20;
    int NB = getenv("NB") ? atoi(getenv("NB")) : 48, TEN = getenv("TEN") ? atoi(getenv("TEN")) : 12;
    int STALL = getenv("STALL") ? atoi(getenv("STALL")) : 300, MAXSOL = getenv("MAXSOL") ? atoi(getenv("MAXSOL")) : 5;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd(); }
    edges_out = getenv("EDGES");
    if (getenv("DEEP")) sscanf(getenv("DEEP"), "%d,%lf", &deep_thr, &deep_secs);
    if (getenv("CHECK")) {
        const char *s = getenv("CHECK"); int SS[64], k = 0;
        while (*s) { while (*s == ' ') s++; if (!*s) break;
            int x1, x2; s = fparse(Q1, s, &x1); if (*s != '|') { fprintf(stderr, "expected |\n"); return 2; } s++;
            s = fparse(Q2, s, &x2); SS[k++] = x1 * n2 + x2; }
        int diam; int ok = fullcheck(SS, k, &diam);
        printf("CHECK k %d diam %d %s energy(sd side A) %d\n", k, diam, ok ? "VALID" : "INVALID", uncov_side(SS, k, 1));
        if (edges_out) write_edges(edges_out, SS, k);
        if (getenv("SDTEST")) {   /* is some b S a^-1 a union of psi-orbits, for one of the psi options? */
            int idx = 0;
            for (int o1 = 0; o1 < Q1->nopt; o1++) for (int o2 = 0; o2 < Q2->nopt; o2++, idx++) {
                setup_psi(o1, o2); long long hits = 0; int fa = -1, fb = -1;
                for (int a = 0; a < N; a++) { int ai = ginvv[a];
                    for (int b = 0; b < N; b++) { int T[64]; st1++;
                        for (int i = 0; i < k; i++) { T[i] = gm(gm(b, SS[i]), ai); mk[T[i]] = st1; }
                        int good = 1; for (int i = 0; i < k && good; i++) if (mk[psi[T[i]]] != st1) good = 0;
                        if (good) { hits++; if (fa < 0) { fa = a; fb = b; } } } }
                printf("SDTEST psi%d [%s] x [%s]: %lld pairs (a,b) with b S a^-1 psi-invariant", idx, Q1->optd[o1], Q2->optd[o2], hits);
                if (fa >= 0) { char b1[160], b2[160]; gdesc(fa, b1); gdesc(fb, b2); printf(", e.g. a = %s, b = %s", b1, b2); }
                printf("\n"); fflush(stdout);
            }
        }
        return ok ? 0 : 1;
    }
    int only = getenv("PSI") ? atoi(getenv("PSI")) : -1, idx = 0;
    const char *types = getenv("TYPES"); int nr = getenv("RANDS") ? atoi(getenv("RANDS")) : 0;
    if (getenv("PLAIN")) {
        sd = 0; setup_psi(-1, -1);
        printf("PSI plain fixed %d orbits %d\n", nfl, nol); fflush(stdout);
        if (!getenv("LIST")) { if (nr) rands("plain", K, 0, nr); else run("plain", K, 0, secs, NB, TEN, STALL, MAXSOL); }
        sd = 1;
        if (getenv("PLAINONLY")) { printf("DONE sols %d\n", nsol); return 0; }
    }
    for (int o1 = 0; o1 < Q1->nopt; o1++) for (int o2 = 0; o2 < Q2->nopt; o2++, idx++) {
        if (only >= 0 && idx != only) continue;
        setup_psi(o1, o2);
        printf("PSI %d [%s] x [%s] fixed %d orbits %d\n", idx, Q1->optd[o1], Q2->optd[o2], nfl, nol); fflush(stdout);
        if (getenv("LIST")) continue;
        if (getenv("ENUM")) gamma_reps(o1, o2);
        char ptag[64]; snprintf(ptag, sizeof ptag, "psi%d", idx);
        for (int f = K % 2; f <= K; f += 2) {
            if (types) { char b[4]; snprintf(b, sizeof b, "%d", f % 10); if (!strstr(types, b)) continue; }
            if (nr) rands(ptag, f, (K - f) / 2, nr);
            else if (getenv("ENUM")) {   /* enumerate when the type has at most ECAP sets, else tabu for SECS */
                double cnt = enum_count(f, (K - f) / 2);
                if (!ecap || cnt <= (double)ecap) enumerate(ptag, f, (K - f) / 2);
                else { printf("TYPE %s_f%d_m%d has %.3g sets > ECAP: tabu\n", ptag, f, (K - f) / 2, cnt); run(ptag, f, (K - f) / 2, secs, NB, TEN, STALL, MAXSOL); }
            }
            else run(ptag, f, (K - f) / 2, secs, NB, TEN, STALL, MAXSOL);
        }
    }
    printf("DONE sols %d\n", nsol);
    return 0;
}
