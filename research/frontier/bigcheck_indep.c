/*
 * bigcheck_indep.c -- independent low-memory checker for very large Haar graph records.
 *
 * Written from scratch (own element numbering, own matrix arithmetic, own projective normalisation); it shares no
 * code with the other checkers.  Only the solution-file format and the group families are taken from the files.
 *
 * Build:  gcc -O2 -fopenmp -o bigcheck_indep bigcheck_indep.c
 * Usage:  bigcheck_indep [--D <n>] [--degree full|sample|off] SOLUTION.txt
 *           --D n        use n instead of the D in the header (used to test that a smaller D is rejected)
 *           --degree m   how the "every vertex has d distinct neighbours" check is done (default full:
 *                        every vertex of both sides; sample: 4M random vertices; off: only the generator check)
 *
 * File format: header "d D <group> n NCYC N NTOT ...", then d lines "<idx> <element> z=<Z>".
 *   <group> := sl q [poly f] | psl q [poly f] | pgl q [poly f] | prod <simple> <simple>   (q = p or p^k, k>1 needs poly)
 *   <element> := mat(a,b,c,d)   or   prod[mat(a,b,c,d);mat(a,b,c,d)]       matrix [[a,b],[c,d]]
 *   G = <group> x Z_NCYC.  Field element of GF(p^k) = c0 + c1 p + ... + c_{k-1} p^{k-1} <-> c0 + c1 x + ... mod f.
 * Not supported (rejected with "RESULT UNSUPPORTED"): meta, agl1, cyc, csl, tpgl, nested prod, ...
 *
 * Graph: H(G,S) has vertices (g,A),(g,B) and edges (g,A) ~ (s*g,B), s in S.  Right multiplication by G is an
 * automorphism group transitive on each side, so BFS from (e,A) and (e,B) gives the diameter.
 * BFS state: four bitsets over G (visited A, visited B, frontier, next frontier) = N/2 bytes in total.
 *
 * Element numbering (index of g = (matrix rank)*NCYC + z; for prod: (r1*|M2| + r2)*NCYC + z):
 *   SL(2,q):   a != 0 : ((a-1)q + b) q + c            (d is forced: d = (1+bc)/a)
 *              a == 0 : (q-1)q^2 + (b-1) q + d         (b != 0, c = -1/b)
 *   PSL(2,q) (q odd): matrix is first multiplied by -1 if needed so that a (or b when a=0) is the chosen
 *              representative of {x,-x}; classes of nonzero elements numbered 0..(q-3)/2;
 *              a != 0 : (cls(a) q + b) q + c ;  a == 0 : h q^2 + cls(b) q + d ,   h = (q-1)/2
 *              (q even: PSL = SL, numbered as SL)
 *   PGL(2,q):  matrix scaled so that its first nonzero entry among (a,b) is 1;
 *              a == 1 : (b q + c)(q-1) + (d - bc - 1)  ;  a == 0, b == 1 : q^2 (q-1) + (c-1) q + d
 * The numbering is verified to be a bijection onto the group at start-up (rank(unrank(i)) == i for all i,
 * every unranked matrix has the right determinant, and scalar multiples get the same rank).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <time.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

#define MAXD 64
#define MAXLEV 4096

static double now(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + 1e-9 * t.tv_nsec;
}
static double T0;

static void unsupported(const char *fmt, ...)
{
    va_list ap;
    printf("RESULT UNSUPPORTED ");
    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);
    printf("\n");
    exit(2);
}
static void invalid(const char *fmt, ...)
{
    va_list ap;
    printf("RESULT INVALID ");
    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);
    printf("\n");
    exit(1);
}

/* ------------------------------------------------------------------ finite fields */
typedef struct {
    u32 q, p, k;
    int prime;        /* k == 1: arithmetic by formula */
    u64 M;            /* Lemire fastmod constant for q */
    u16 *add, *mul;   /* k > 1: q*q tables */
    u16 *neg, *inv;
} Field;

static inline u32 fmodq(const Field *F, u32 a)
{
    u64 low = F->M * a;
    return (u32)(((__uint128_t)low * F->q) >> 64);
}
static inline u32 fadd(const Field *F, u32 x, u32 y)
{
    if (F->prime) {
        u32 s = x + y;
        return s >= F->q ? s - F->q : s;
    }
    return F->add[x * F->q + y];
}
static inline u32 fneg(const Field *F, u32 x) { return F->neg[x]; }
static inline u32 fmul(const Field *F, u32 x, u32 y)
{
    if (F->prime) return fmodq(F, x * y);
    return F->mul[x * F->q + y];
}
/* x*y + z*w */
static inline u32 fmuladd(const Field *F, u32 x, u32 y, u32 z, u32 w)
{
    if (F->prime) return fmodq(F, x * y + z * w);
    return fadd(F, F->mul[x * F->q + y], F->mul[z * F->q + w]);
}
static inline u32 fsub(const Field *F, u32 x, u32 y) { return fadd(F, x, fneg(F, y)); }

static u64 splitmix(u64 *s)
{
    u64 z = (*s += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

static u32 powmod(u32 b, u32 e, u32 m)
{
    u64 r = 1, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (u32)r;
}

/* parse "x^3+2x+1" into coefficients c[0..k] (low to high), each reduced mod p; returns degree or -1 */
static int parse_poly(const char *s, u32 p, u32 *c)
{
    memset(c, 0, 65 * sizeof(u32));
    int deg = -1;
    const char *t = s;
    while (*t) {
        u32 coef = 0;
        int have_coef = 0, e = 0;
        while (*t >= '0' && *t <= '9') {
            coef = coef * 10 + (*t - '0');
            have_coef = 1;
            t++;
        }
        if (*t == 'x') {
            t++;
            e = 1;
            if (*t == '^') {
                t++;
                e = 0;
                if (!(*t >= '0' && *t <= '9')) return -1;
                while (*t >= '0' && *t <= '9') e = e * 10 + (*t++ - '0');
            }
            if (!have_coef) coef = 1;
        } else if (!have_coef)
            return -1;
        if (e > 64) return -1;
        c[e] = (c[e] + coef) % p;
        if (e > deg) deg = e;
        if (*t == '+')
            t++;
        else if (*t)
            return -1;
    }
    return deg;
}

static void field_init(Field *F, u32 q, const char *poly)
{
    memset(F, 0, sizeof *F);
    u32 p = 0, k = 0, t = q;
    for (u32 r = 2; r <= q; r++)
        if (q % r == 0) {
            p = r;
            break;
        }
    if (q < 2) unsupported("field order %u", q);
    while (t % p == 0) {
        t /= p;
        k++;
    }
    if (t != 1) unsupported("q=%u is not a prime power", q);
    F->q = q;
    F->p = p;
    F->k = k;
    F->M = UINT64_MAX / q + 1;
    F->prime = (k == 1);
    if (k == 1) {
        if (poly) unsupported("poly given for prime field q=%u", q);
        if (q >= 32768) unsupported("prime q=%u too large (limit 32767)", q);
        F->neg = malloc(q * sizeof(u16));
        F->inv = malloc(q * sizeof(u16));
        for (u32 x = 0; x < q; x++) {
            F->neg[x] = x ? q - x : 0;
            F->inv[x] = x ? powmod(x, q - 2, q) : 0;
        }
        for (u32 x = 1; x < q; x++)
            if ((u64)x * F->inv[x] % q != 1) invalid("field inverse table broken for q=%u", q);
        return;
    }
    if (!poly) unsupported("q=%u=%u^%u needs a 'poly' specification", q, p, k);
    if (q > 4096) unsupported("extension field q=%u too large (limit 4096)", q);
    u32 f[65];
    int deg = parse_poly(poly, p, f);
    if (deg != (int)k || f[k] != 1) unsupported("poly '%s' is not monic of degree %u over GF(%u)", poly, k, p);
    F->add = malloc((size_t)q * q * sizeof(u16));
    F->mul = malloc((size_t)q * q * sizeof(u16));
    F->neg = malloc(q * sizeof(u16));
    F->inv = malloc(q * sizeof(u16));
    u32 dig[4096][12], pw[13];
    if (k > 12) unsupported("extension degree %u too large", k);
    pw[0] = 1;
    for (u32 i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (u32 x = 0; x < q; x++)
        for (u32 i = 0; i < k; i++) dig[x][i] = (x / pw[i]) % p;
    for (u32 x = 0; x < q; x++)
        for (u32 y = 0; y < q; y++) {
            u32 s = 0;
            for (u32 i = 0; i < k; i++) s += ((dig[x][i] + dig[y][i]) % p) * pw[i];
            F->add[x * q + y] = s;
            u32 pr[24] = {0};
            for (u32 i = 0; i < k; i++)
                for (u32 j = 0; j < k; j++) pr[i + j] = (pr[i + j] + dig[x][i] * dig[y][j]) % p;
            for (int i = 2 * (int)k - 2; i >= (int)k; i--) { /* x^k = -(f_0 + ... + f_{k-1} x^{k-1}) */
                u32 co = pr[i];
                pr[i] = 0;
                for (u32 j = 0; j < k; j++) pr[i - k + j] = (pr[i - k + j] + (p - f[j]) * co) % p;
            }
            u32 m = 0;
            for (u32 i = 0; i < k; i++) m += pr[i] * pw[i];
            F->mul[x * q + y] = m;
        }
    for (u32 x = 0; x < q; x++) {
        int fn = 0, fi = 0;
        for (u32 y = 0; y < q; y++) {
            if (F->add[x * q + y] == 0) {
                F->neg[x] = y;
                fn = 1;
            }
            if (F->mul[x * q + y] == 1) {
                F->inv[x] = y;
                fi = 1;
            }
        }
        if (!fn) invalid("no additive inverse for %u", x);
        if (x && !fi) invalid("poly '%s' is not irreducible over GF(%u): %u has no inverse", poly, p, x);
    }
    /* distributivity / associativity: exhaustive for small q, else random */
    u64 seed = 12345;
    u64 trials = q <= 64 ? (u64)q * q * q : 2000000;
    for (u64 i = 0; i < trials; i++) {
        u32 x, y, z;
        if (q <= 64) {
            x = i / ((u64)q * q);
            y = (i / q) % q;
            z = i % q;
        } else {
            x = splitmix(&seed) % q;
            y = splitmix(&seed) % q;
            z = splitmix(&seed) % q;
        }
        if (F->mul[F->mul[x * q + y] * q + z] != F->mul[x * q + F->mul[y * q + z]] ||
            F->mul[x * q + F->add[y * q + z]] != F->add[F->mul[x * q + y] * q + F->mul[x * q + z]] ||
            F->add[F->add[x * q + y] * q + z] != F->add[x * q + F->add[y * q + z]])
            invalid("field axioms fail for GF(%u) with poly '%s'", q, poly);
    }
}

/* ------------------------------------------------------------------ 2x2 matrix factors */
enum { K_SL = 0, K_PSL = 1, K_PGL = 2 };
typedef struct {
    int kind;          /* K_SL (also PSL with q even), K_PSL (q odd), K_PGL */
    int req;           /* what the file asked for: 0 sl, 1 psl, 2 pgl */
    Field F;
    u32 q, h;
    u64 order;
    u16 *cls, *rep;    /* PSL: class number of x (x and -x share it), representative of class i */
    u8 *isrep;
} Fac;

static void fac_init(Fac *f, const char *kind, u32 q, const char *poly)
{
    memset(f, 0, sizeof *f);
    if (!strcmp(kind, "sl")) f->req = 0;
    else if (!strcmp(kind, "psl")) f->req = 1;
    else if (!strcmp(kind, "pgl")) f->req = 2;
    else unsupported("group family '%s'", kind);
    field_init(&f->F, q, poly);
    f->q = q;
    u64 sl = (u64)q * ((u64)q * q - 1);
    if (f->req == 0) { f->kind = K_SL; f->order = sl; }
    else if (f->req == 2) { f->kind = K_PGL; f->order = sl; }
    else if (q % 2 == 0) { f->kind = K_SL; f->order = sl; }
    else {
        f->kind = K_PSL;
        f->order = sl / 2;
        f->h = (q - 1) / 2;
        f->cls = calloc(q, sizeof(u16));
        f->rep = calloc(q, sizeof(u16));
        f->isrep = calloc(q, 1);
        u32 c = 0;
        for (u32 x = 1; x < q; x++)
            if (x < f->F.neg[x]) {
                f->isrep[x] = 1;
                f->rep[c] = x;
                f->cls[x] = f->cls[f->F.neg[x]] = c++;
            }
        if (c != f->h) invalid("PSL class count");
    }
}

static inline u64 fac_rank(const Fac *f, u32 a, u32 b, u32 c, u32 d)
{
    const Field *F = &f->F;
    u64 q = f->q;
    switch (f->kind) {
    case K_SL:
        if (a) return (((u64)(a - 1) * q + b) * q + c);
        return (q - 1) * q * q + (u64)(b - 1) * q + d;
    case K_PSL:
        if (a) {
            if (!f->isrep[a]) { a = fneg(F, a); b = fneg(F, b); c = fneg(F, c); d = fneg(F, d); }
            return ((u64)f->cls[a] * q + b) * q + c;
        }
        if (!f->isrep[b]) { b = fneg(F, b); c = fneg(F, c); d = fneg(F, d); }
        return (u64)f->h * q * q + (u64)f->cls[b] * q + d;
    default: /* K_PGL */
        if (a) {
            u32 ia = F->inv[a];
            b = fmul(F, b, ia); c = fmul(F, c, ia); d = fmul(F, d, ia);
            u32 delta = fsub(F, d, fmul(F, b, c)); /* nonzero */
            return ((u64)b * q + c) * (q - 1) + (delta - 1);
        } else {
            u32 ib = F->inv[b];
            c = fmul(F, c, ib); d = fmul(F, d, ib);
            return q * q * (q - 1) + (u64)(c - 1) * q + d;
        }
    }
}

static inline void fac_unrank(const Fac *f, u64 idx, u32 *e)
{
    const Field *F = &f->F;
    u64 q = f->q;
    u32 a, b, c, d;
    if (f->kind == K_PGL) {
        if (idx < q * q * (q - 1)) {
            u32 delta = (u32)(idx % (q - 1)) + 1;
            u64 t = idx / (q - 1);
            c = t % q;
            b = t / q;
            a = 1;
            d = fadd(F, delta, fmul(F, b, c));
        } else {
            u64 r = idx - q * q * (q - 1);
            d = r % q;
            c = r / q + 1;
            a = 0;
            b = 1;
        }
    } else {
        u64 lim = (f->kind == K_SL ? q - 1 : f->h) * q * q;
        if (idx < lim) {
            c = idx % q;
            u64 t = idx / q;
            b = t % q;
            a = f->kind == K_SL ? (u32)(t / q) + 1 : f->rep[t / q];
            u32 num = fadd(F, 1, fmul(F, b, c));
            d = fmul(F, F->inv[a], num);
        } else {
            u64 r = idx - lim;
            d = r % q;
            u64 j = r / q;
            b = f->kind == K_SL ? (u32)j + 1 : f->rep[j];
            a = 0;
            c = fneg(F, F->inv[b]);
        }
    }
    e[0] = a; e[1] = b; e[2] = c; e[3] = d;
}

/* o = s * (a,b,c,d) */
static inline void mmul(const Field *F, const u32 *s, const u32 *g, u32 *o)
{
    o[0] = fmuladd(F, s[0], g[0], s[1], g[2]);
    o[1] = fmuladd(F, s[0], g[1], s[1], g[3]);
    o[2] = fmuladd(F, s[2], g[0], s[3], g[2]);
    o[3] = fmuladd(F, s[2], g[1], s[3], g[3]);
}

static inline u32 det2(const Field *F, const u32 *m)
{
    return fsub(F, fmul(F, m[0], m[3]), fmul(F, m[1], m[2]));
}

/* exhaustive bijection test of the numbering of one factor + class-invariance of rank */
static void fac_selftest(const Fac *f)
{
    u64 bad = 0;
    const Field *F = &f->F;
#pragma omp parallel for reduction(+ : bad) schedule(static)
    for (long long i = 0; i < (long long)f->order; i++) {
        u32 e[4];
        fac_unrank(f, (u64)i, e);
        u32 dt = det2(F, e);
        if (f->kind == K_PGL ? dt == 0 : dt != 1) { bad++; continue; }
        if (fac_rank(f, e[0], e[1], e[2], e[3]) != (u64)i) { bad++; continue; }
        if (f->kind == K_PSL) {
            if (fac_rank(f, fneg(F, e[0]), fneg(F, e[1]), fneg(F, e[2]), fneg(F, e[3])) != (u64)i) bad++;
        } else if (f->kind == K_PGL) {
            u32 lam = 1 + (u32)(((u64)i * 2654435761u) % (f->q - 1));
            if (fac_rank(f, fmul(F, lam, e[0]), fmul(F, lam, e[1]), fmul(F, lam, e[2]), fmul(F, lam, e[3])) !=
                (u64)i)
                bad++;
        }
    }
    if (bad) invalid("numbering self-test failed for %s(2,%u): %llu bad indices",
                     f->req == 0 ? "SL" : f->req == 1 ? "PSL" : "PGL", f->q, (unsigned long long)bad);
    /* associativity of the matrix arithmetic on random triples */
    u64 seed = 777 + f->q;
    for (int t = 0; t < 20000; t++) {
        u32 x[4], y[4], z[4], xy[4], yz[4], l[4], r[4];
        fac_unrank(f, splitmix(&seed) % f->order, x);
        fac_unrank(f, splitmix(&seed) % f->order, y);
        fac_unrank(f, splitmix(&seed) % f->order, z);
        mmul(F, x, y, xy);
        mmul(F, xy, z, l);
        mmul(F, y, z, yz);
        mmul(F, x, yz, r);
        if (memcmp(l, r, sizeof l)) invalid("matrix multiplication not associative");
    }
}

/* ------------------------------------------------------------------ the group G = M1 [x M2] x Z_n */
typedef struct {
    int nf;
    Fac f[2];
    u64 n;          /* order of the cyclic factor */
    u64 mord;       /* |M| */
    u64 N;          /* |G| */
} Grp;

typedef struct {
    u32 m[2][4];
    u64 z;
} Gen;

/* indices of s*g for all generators in gs, g given by its index */
static inline void expand(const Grp *G, const Gen *gs, int d, u64 idx, u64 *out)
{
    u64 n = G->n;
    u64 z = idx % n, mi = idx / n;
    u32 e0[4], e1[4], o[4];
    if (G->nf == 1) {
        fac_unrank(&G->f[0], mi, e0);
        for (int t = 0; t < d; t++) {
            mmul(&G->f[0].F, gs[t].m[0], e0, o);
            u64 zt = z + gs[t].z;
            if (zt >= n) zt -= n;
            out[t] = fac_rank(&G->f[0], o[0], o[1], o[2], o[3]) * n + zt;
        }
    } else {
        u64 o1 = G->f[1].order;
        fac_unrank(&G->f[0], mi / o1, e0);
        fac_unrank(&G->f[1], mi % o1, e1);
        for (int t = 0; t < d; t++) {
            mmul(&G->f[0].F, gs[t].m[0], e0, o);
            u64 r0 = fac_rank(&G->f[0], o[0], o[1], o[2], o[3]);
            mmul(&G->f[1].F, gs[t].m[1], e1, o);
            u64 r1 = fac_rank(&G->f[1], o[0], o[1], o[2], o[3]);
            u64 zt = z + gs[t].z;
            if (zt >= n) zt -= n;
            out[t] = (r0 * o1 + r1) * n + zt;
        }
    }
}

/* ------------------------------------------------------------------ bitset BFS */
typedef struct {
    int nlev;
    u64 size[MAXLEV];
    u64 reached;
} BfsRes;

static void bfs(const Grp *G, const Gen *GF, const Gen *GB, int d, u64 src, int side, BfsRes *R)
{
    u64 N = G->N, nw = (N + 63) / 64;
    u64 *vis[2], *F, *NF;
    vis[0] = calloc(nw, 8);
    vis[1] = calloc(nw, 8);
    F = calloc(nw, 8);
    NF = calloc(nw, 8);
    if (!vis[0] || !vis[1] || !F || !NF) invalid("out of memory for bitsets (%llu words each)", (unsigned long long)nw);
    vis[side][src >> 6] |= 1ULL << (src & 63);
    F[src >> 6] |= 1ULL << (src & 63);
    R->nlev = 1;
    R->size[0] = 1;
    R->reached = 1;
    for (;;) {
        const Gen *gs = side == 0 ? GF : GB; /* (g,A) -> (s g,B); (h,B) -> (s^-1 h,A) */
        memset(NF, 0, nw * 8);
#pragma omp parallel
        {
            u64 out[MAXD];
#pragma omp for schedule(dynamic, 256)
            for (long long w = 0; w < (long long)nw; w++) {
                u64 x = F[w];
                while (x) {
                    int b = __builtin_ctzll(x);
                    x &= x - 1;
                    expand(G, gs, d, (u64)w * 64 + b, out);
                    for (int t = 0; t < d; t++)
                        __atomic_fetch_or(&NF[out[t] >> 6], 1ULL << (out[t] & 63), __ATOMIC_RELAXED);
                }
            }
        }
        u64 *V = vis[side ^ 1];
        u64 cnt = 0;
#pragma omp parallel for reduction(+ : cnt) schedule(static)
        for (long long w = 0; w < (long long)nw; w++) {
            u64 nwd = NF[w] & ~V[w];
            NF[w] = nwd;
            V[w] |= nwd;
            cnt += __builtin_popcountll(nwd);
        }
        if (!cnt) break;
        if (R->nlev >= MAXLEV) invalid("more than %d BFS levels", MAXLEV);
        R->size[R->nlev++] = cnt;
        R->reached += cnt;
        u64 *tmp = F; F = NF; NF = tmp;
        side ^= 1;
        fprintf(stderr, "  [%.0fs] level %d: %llu\n", now() - T0, R->nlev - 1, (unsigned long long)cnt);
    }
    free(vis[0]); free(vis[1]); free(F); free(NF);
}

/* ------------------------------------------------------------------ parsing */
static int parse_mat(const char *s, u32 *m, const char **end)
{
    unsigned a, b, c, d;
    int len = 0;
    if (sscanf(s, "mat(%u,%u,%u,%u)%n", &a, &b, &c, &d, &len) != 4 || !len) return 0;
    m[0] = a; m[1] = b; m[2] = c; m[3] = d;
    *end = s + len;
    return 1;
}

int main(int argc, char **argv)
{
    T0 = now();
    int Dover = -1;
    int degmode = 2; /* 0 off, 1 sample, 2 full */
    const char *path = NULL;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--D") && i + 1 < argc) Dover = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--degree") && i + 1 < argc) {
            i++;
            degmode = !strcmp(argv[i], "off") ? 0 : !strcmp(argv[i], "sample") ? 1 : 2;
        } else if (argv[i][0] != '-') path = argv[i];
        else { fprintf(stderr, "usage: %s [--D n] [--degree full|sample|off] FILE\n", argv[0]); return 64; }
    }
    if (!path) { fprintf(stderr, "usage: %s [--D n] [--degree full|sample|off] FILE\n", argv[0]); return 64; }
    FILE *fp = fopen(path, "r");
    if (!fp) { printf("RESULT INVALID cannot open %s\n", path); return 1; }
    static char line[1 << 16];
    if (!fgets(line, sizeof line, fp)) invalid("empty file");
    char hdr[1 << 16];
    strcpy(hdr, line);
    char *tok[128];
    int nt = 0;
    for (char *s = strtok(line, " \t\r\n"); s && nt < 128; s = strtok(NULL, " \t\r\n")) tok[nt++] = s;
    if (nt < 6) unsupported("header too short");
    int d = atoi(tok[0]), D = atoi(tok[1]);
    int pos = 2;
    Grp G;
    memset(&G, 0, sizeof G);
    {
        int nf = 1;
        if (!strcmp(tok[pos], "prod")) { nf = 2; pos++; }
        for (int i = 0; i < nf; i++) {
            if (pos + 1 >= nt) unsupported("bad group spec");
            const char *kind = tok[pos];
            if (strcmp(kind, "sl") && strcmp(kind, "psl") && strcmp(kind, "pgl"))
                unsupported("group family '%s' (supported: sl, psl, pgl, prod of two of them; times Z_n)", kind);
            u32 q = (u32)atoi(tok[pos + 1]);
            pos += 2;
            const char *poly = NULL;
            if (pos + 1 < nt && !strcmp(tok[pos], "poly")) { poly = tok[pos + 1]; pos += 2; }
            fac_init(&G.f[i], kind, q, poly);
        }
        G.nf = nf;
    }
    if (pos + 3 >= nt || strcmp(tok[pos], "n") || strcmp(tok[pos + 2], "N"))
        unsupported("header does not have the form '... n NCYC N NTOT' after the group");
    G.n = strtoull(tok[pos + 1], NULL, 10);
    u64 Ntot = strtoull(tok[pos + 3], NULL, 10);
    G.mord = G.f[0].order * (G.nf == 2 ? G.f[1].order : 1);
    G.N = G.mord * G.n;
    if (d < 1 || d > MAXD) unsupported("d=%d out of range 1..%d", d, MAXD);
    if (G.n < 1) invalid("NCYC=%llu", (unsigned long long)G.n);
    if (Dover >= 0) D = Dover;
    printf("file %s\n", path);
    printf("header: %s", hdr[strlen(hdr) - 1] == '\n' ? hdr : strcat(hdr, "\n"));
    printf("d=%d D=%d%s\n", d, D, Dover >= 0 ? " (overridden by --D)" : "");
    printf("group: ");
    for (int i = 0; i < G.nf; i++)
        printf("%s%s(2,%u) [order %llu]", i ? " x " : "", G.f[i].req == 0 ? "SL" : G.f[i].req == 1 ? "PSL" : "PGL",
               G.f[i].q, (unsigned long long)G.f[i].order);
    printf(" x Z_%llu; |G| = %llu, vertices 2|G| = %llu\n", (unsigned long long)G.n, (unsigned long long)G.N,
           (unsigned long long)(2 * G.N));
    if (Ntot != G.N) invalid("header N=%llu but |G|=%llu", (unsigned long long)Ntot, (unsigned long long)G.N);
    if (G.N >= (1ULL << 40)) unsupported("|G| too large");
#ifdef _OPENMP
    printf("threads: %d\n", omp_get_max_threads());
#endif
    fflush(stdout);
    for (int i = 0; i < G.nf; i++) fac_selftest(&G.f[i]);
    printf("numbering self-test passed (bijection onto the group, class invariance, associativity) [%.1fs]\n",
           now() - T0);

    /* generators */
    Gen GF[MAXD], GB[MAXD];
    u64 gid[MAXD];
    int ng = 0;
    while (fgets(line, sizeof line, fp)) {
        char *s = line;
        while (*s == ' ' || *s == '\t') s++;
        if (*s == '\n' || *s == '\r' || !*s) continue;
        if (ng >= d) invalid("more than d=%d generator lines", d);
        unsigned long idxcol;
        int off = 0;
        if (sscanf(s, "%lu %n", &idxcol, &off) < 1 || !off) invalid("generator line %d: bad index column", ng + 1);
        s += off;
        Gen *g = &GF[ng];
        memset(g, 0, sizeof *g);
        const char *e;
        if (G.nf == 1) {
            if (!parse_mat(s, g->m[0], &e)) invalid("generator line %d: expected mat(a,b,c,d)", ng + 1);
        } else {
            if (strncmp(s, "prod[", 5) || !parse_mat(s + 5, g->m[0], &e) || *e != ';' || !parse_mat(e + 1, g->m[1], &e) ||
                *e != ']')
                invalid("generator line %d: expected prod[mat(..);mat(..)]", ng + 1);
            e++; /* skip ']' */
        }
        while (*e == ' ') e++;
        unsigned long long zz;
        if (sscanf(e, "z=%llu", &zz) != 1) invalid("generator line %d: missing z=", ng + 1);
        if (zz >= G.n) invalid("generator line %d: z=%llu not in Z_%llu", ng + 1, zz, (unsigned long long)G.n);
        g->z = zz;
        u64 ranks = 0, rk[2];
        Gen *gb = &GB[ng];
        memset(gb, 0, sizeof *gb);
        for (int f = 0; f < G.nf; f++) {
            const Fac *fc = &G.f[f];
            const u32 *m = g->m[f];
            for (int k = 0; k < 4; k++)
                if (m[k] >= fc->q) invalid("generator %d: entry %u out of range for GF(%u)", ng + 1, m[k], fc->q);
            u32 dt = det2(&fc->F, m);
            if (fc->kind == K_PGL ? dt == 0 : dt != 1)
                invalid("generator %d: matrix (%u,%u,%u,%u) is not in %s(2,%u) (det=%u)", ng + 1, m[0], m[1], m[2], m[3],
                        fc->req == 0 ? "SL" : fc->req == 1 ? "PSL" : "PGL", fc->q, dt);
            rk[f] = fac_rank(fc, m[0], m[1], m[2], m[3]);
            /* inverse = adjugate (exact inverse when det = 1; inverse up to a scalar in PGL) */
            gb->m[f][0] = m[3]; gb->m[f][1] = fneg(&fc->F, m[1]); gb->m[f][2] = fneg(&fc->F, m[2]); gb->m[f][3] = m[0];
        }
        gb->z = g->z ? G.n - g->z : 0;
        ranks = G.nf == 1 ? rk[0] : rk[0] * G.f[1].order + rk[1];
        gid[ng] = ranks * G.n + g->z;
        ng++;
    }
    fclose(fp);
    if (ng < d) invalid("only %d generator lines for d=%d", ng, d);
    for (int i = 0; i < d; i++)
        for (int j = i + 1; j < d; j++)
            if (gid[i] == gid[j]) invalid("generators %d and %d are the same group element", i + 1, j + 1);
    printf("generators: %d distinct group elements, all in the group [%.1fs]\n", d, now() - T0);

    /* identity, and check that the stored inverses are inverses: s * s^-1 = e */
    u64 eidx;
    {
        u64 er[2] = {0, 0};
        for (int f = 0; f < G.nf; f++) er[f] = fac_rank(&G.f[f], 1, 0, 0, 1);
        eidx = (G.nf == 1 ? er[0] : er[0] * G.f[1].order + er[1]) * G.n;
        for (int t = 0; t < d; t++) {
            u64 prod_idx[2];
            for (int f = 0; f < G.nf; f++) {
                u32 o[4];
                mmul(&G.f[f].F, GF[t].m[f], GB[t].m[f], o);
                prod_idx[f] = fac_rank(&G.f[f], o[0], o[1], o[2], o[3]);
                if (prod_idx[f] != er[f]) invalid("generator %d: s * s^-1 is not the identity", t + 1);
            }
            if ((GF[t].z + GB[t].z) % G.n) invalid("generator %d: z part inverse wrong", t + 1);
        }
        /* unrank(identity index) must be the identity matrices */
        u32 e0[4];
        fac_unrank(&G.f[0], eidx / G.n / (G.nf == 2 ? G.f[1].order : 1), e0);
        if (e0[0] != 1 || e0[1] || e0[2] || e0[3] != 1) invalid("identity numbering broken");
    }

    /* neighbour checks */
    if (degmode) {
        u64 N = G.N, bad = 0, samples = degmode == 2 || N <= (1u << 22) ? N : (1u << 22);
        u64 consist = 0;
#pragma omp parallel reduction(+ : bad, consist)
        {
            u64 outf[MAXD], outb[MAXD], outr[MAXD];
            u64 seed = 99 + 7919ULL
#ifdef _OPENMP
                                    * omp_get_thread_num()
#endif
                ;
#pragma omp for schedule(static, 4096)
            for (long long i = 0; i < (long long)samples; i++) {
                u64 g = samples == N ? (u64)i : splitmix(&seed) % N;
                expand(&G, GF, d, g, outf); /* neighbours of (g,A) */
                expand(&G, GB, d, g, outb); /* neighbours of (g,B) */
                for (int a = 0; a < d; a++) {
                    if (outf[a] >= N || outb[a] >= N) bad++;
                    for (int b = a + 1; b < d; b++) {
                        if (outf[a] == outf[b]) bad++;
                        if (outb[a] == outb[b]) bad++;
                    }
                }
                /* adjacency symmetry on a subset: the B-neighbours of (s g, B) via inverses include (g, A) */
                if ((i & 63) == 0 || samples < (1u << 22)) {
                    expand(&G, GB, d, outf[0], outr);
                    int found = 0;
                    for (int a = 0; a < d; a++) found |= outr[a] == g;
                    if (!found || outr[0] != g) consist++;
                }
            }
        }
        printf("neighbour check (%s: %llu vertices per side): every vertex has %d distinct neighbours: %s\n",
               degmode == 2 ? "full" : "sample", (unsigned long long)samples, d, bad ? "NO" : "yes");
        printf("adjacency symmetry check (s^-1 (s g) = g): %s [%.1fs]\n", consist ? "FAILED" : "ok", now() - T0);
        if (bad) invalid("a vertex has repeated or out-of-range neighbours (%llu violations)", (unsigned long long)bad);
        if (consist) invalid("inverse generators do not invert (%llu violations)", (unsigned long long)consist);
    }

    /* the two BFS runs */
    static BfsRes R[2];
    int ecc[2];
    int ok = 1;
    char reason[256] = "";
    for (int side = 0; side < 2; side++) {
        fprintf(stderr, "BFS from (e,%c)\n", "AB"[side]);
        bfs(&G, GF, GB, d, eidx, side, &R[side]);
        ecc[side] = R[side].nlev - 1;
        u64 total = 2 * G.N;
        printf("BFS from %c: ecc=%d reached %llu of %llu (unreached %llu); level sizes [", "AB"[side], ecc[side],
               (unsigned long long)R[side].reached, (unsigned long long)total,
               (unsigned long long)(total - R[side].reached));
        for (int l = 0; l < R[side].nlev; l++) printf("%s%llu", l ? ", " : "", (unsigned long long)R[side].size[l]);
        printf("] [%.1fs]\n", now() - T0);
        fflush(stdout);
        if (R[side].reached != total && ok) {
            ok = 0;
            snprintf(reason, sizeof reason, "BFS from %c reaches only %llu of %llu vertices", "AB"[side],
                     (unsigned long long)R[side].reached, (unsigned long long)total);
        } else if (ecc[side] > D && ok) {
            ok = 0;
            snprintf(reason, sizeof reason, "ecc from %c is %d > D=%d", "AB"[side], ecc[side], D);
        }
    }
    printf("max degree = min degree = %d, no repeated edges (checked above)\n", d);
    printf("elapsed %.1fs\n", now() - T0);
    if (!ok) invalid("%s", reason);
    printf("RESULT VALID d=%d D=%d eccA=%d eccB=%d n=%llu\n", d, D, ecc[0], ecc[1], (unsigned long long)(2 * G.N));
    return 0;
}
