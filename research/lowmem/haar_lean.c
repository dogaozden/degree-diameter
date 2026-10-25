/* haar_lean: low-memory orbit-symmetric Haar graph search for big groups G = SL(2,p) x Z_n or PSL(2,p) x Z_n (p prime).
 *
 * Same search as research/structured/haar_sym.c in ORBIT mode: S = (f generators fixed by alpha, the first one e) +
 * m alpha-orbits of size k, alpha = conjugation by an element of order k on the matrix part times z -> r z on Z_n;
 * annealing moves replace a whole orbit (targeted: the new orbit is built from a word through a currently uncovered
 * element); energy = cost / k.  f = 0: S is m free orbits and nothing else; the solution is written as S s_0^-1
 * (an isomorphic Haar graph, (g,A) -> (s_0 g, A)) so that its first generator is e.
 *
 * What is new is the cost evaluation, which stores two bitsets of N bits (one per side) and nothing per element:
 * N ~ 1.2e9 needs ~0.3 GB per thread (haar_sym needs ~11-14 bytes per element).
 *   Rows are the left cosets x H of H = U x Z_n, U = {[[1,t],[0,1]]}; H is cyclic of order L = p n (gcd(p,n) = 1).
 *   The coset of M = [[a,b],[c,d]] is fixed by its first column u = (a,c) (up to sign for PSL).  Representative
 *   g_u = [u | v(u)] with v(u) = (0, 1/a) if a != 0, else (-1/c, 0); M = g_u U_t with t = b/a (a != 0) or d/c (a = 0).
 *   (M, z) is bit CRT(t, z) of row u.  s = (A, z_s): A g_u = g_{Au} U_t', so s (g_u U_t, z) = (g_{Au} U_{t'+t}, z + z_s),
 *   i.e. row u -> row Au and bit c -> c + CRT(t', z_s) mod L.  A dense BFS level is R x d rotated row-ORs
 *   (R = p^2 - 1 rows of L bits; (p^2-1)/2 for PSL), streaming through memory; the tables have R entries.
 *   Sparse levels push element lists through the same tables.
 *
 * Cost (as haar_gen3): D even: #B-side elements not within D-1 of (e,A); D odd: #A not within D-1 of (e,A) + #B not
 * within D-1 of (e,B).  Before writing a solution the full diameter (BFS to depth D from (e,A) and (e,B), both sides
 * fully reached) and distinct generators are checked.  Solution file: haar_gen3 format, header
 * "d D sl p n NCYC N N", lines "<index> mat(a,b,c,d) z=Z" (index = haar_gen3's element index for sl, 0 for psl);
 * check with ../frontier/haarcheck_sl.c, ../frontier/haarcheck2.c or ../structured/tools/haarcheck_psl.c.
 *
 * Usage: haar_lean d D seconds seed K outfile sl|psl p n
 * Env: ORBIT="k m f" (default "3 d/3 0" if 3 | d, else "3 (d-1)/3 1" or "3 (d-2)/3 2"), THREADS (candidates in
 *      parallel, one bitset pair each), TARGP (default 70), COOL (20), REHEAT (150), REHEATSTEPS (400), TMAX (1.5),
 *      TMIN (0.15), RESTART (0/1), ORBW (weight of an uncovered fixed element, default 1), UCAP (stored uncovered
 *      elements, 65536), DENSEF (frontier size above which a level is done densely, default N/2048),
 *      AR (r on Z_n), ATRACE (trace of the conjugating element), LEVELS=1 (print ball sizes),
 *      RANDORB=m (cost statistics of m random symmetric S, no search; "units" = uncovered free alpha-orbits + uncovered
 *      fixed points, the Poisson count that decides P(cost 0)), SOLFILE=f (cost + full check of a solution
 *      file's S, no search), BENCH=m (time m evaluations).
 * Build: gcc -O3 -march=native -fopenmp -o haar_lean haar_lean.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <signal.h>
#include <limits.h>
#include <sys/mman.h>
#ifdef _OPENMP
#include <omp.h>
#endif

#define MAXD 32
typedef struct { int a, b, c, d, z; } el;
typedef struct { uint32_t row, rot; } tent;

static int P, H, NC, PSL;          /* p, (p-1)/2, n, PSL flag */
static long long N, L;             /* |G|, row length p n */
static int R, WR;                  /* rows, 64-bit words per row */
static uint64_t TAILM;             /* valid bits of the last word of a row */
static int *INV;
static long long E1, E2;           /* CRT idempotents mod L: E1 = 1 mod p, 0 mod n; E2 = 0 mod p, 1 mod n */
static int d, D;
static el ID;

static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static void *xmalloc(size_t n) {   /* 64-byte aligned; big blocks 2 MB aligned with transparent huge pages (fewer TLB misses) */
    size_t al = n >= (8u << 20) ? (2u << 20) : 64; n = (n + al - 1) / al * al;
    void *p = aligned_alloc(al, n); if (!p) { fprintf(stderr, "out of memory (%zu bytes)\n", n); exit(2); }
    if (al > 64) madvise(p, n, MADV_HUGEPAGE);
    return p;
}

/* ---------------- group arithmetic ---------------- */
static inline int neg(int v) { return v ? P - v : 0; }
static inline void canon(el *x) {
    if (PSL && (x->a ? x->a > H : x->c > H)) { x->a = neg(x->a); x->b = neg(x->b); x->c = neg(x->c); x->d = neg(x->d); }
}
static inline el gmul(el x, el y) {
    el r = { (int)(((long long)x.a * y.a + (long long)x.b * y.c) % P), (int)(((long long)x.a * y.b + (long long)x.b * y.d) % P),
             (int)(((long long)x.c * y.a + (long long)x.d * y.c) % P), (int)(((long long)x.c * y.b + (long long)x.d * y.d) % P),
             (x.z + y.z) % NC };
    canon(&r); return r;
}
static inline el ginv(el x) { el r = { x.d, neg(x.b), neg(x.c), x.a, (NC - x.z) % NC }; canon(&r); return r; }
static inline int geq(el x, el y) { return x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d && x.z == y.z; }
static inline int row_of(int a, int c) { if (!PSL) return a * P + c - 1; return a ? (a - 1) * P + c : H * P + c - 1; }
static inline void el2rc(el x, int *r, long long *bit) {   /* x canonical */
    int t = x.a ? (int)((long long)x.b * INV[x.a] % P) : (int)((long long)x.d * INV[x.c] % P);
    *r = row_of(x.a, x.c);
    *bit = (int)(((long long)t * E1 + (long long)x.z * E2) % L);
}
static inline el rc2el(int r, long long bit) {
    int a, c;
    if (!PSL) { a = (r + 1) / P; c = (r + 1) % P; }
    else if (r < H * P) { a = r / P + 1; c = r % P; }
    else { a = 0; c = r - H * P + 1; }
    int t = (int)(bit % P), z = (int)(bit % NC), v1, v2;
    if (a) { v1 = 0; v2 = INV[a]; } else { v1 = P - INV[c]; v2 = 0; }
    el x = { a, (int)(((long long)t * a + v1) % P), c, (int)(((long long)t * c + v2) % P), z };
    return x;
}
static el rand_el(void) { int r = (int)(rnd() % (unsigned long long)R); long long b = (long long)(rnd() % (unsigned long long)L); return rc2el(r, b); }

/* table of x: T[r] = (row of x g_r, CRT(t', z_x)); inverse table TI[T[r].row] = (r, -rot) */
static void make_tables(el x, tent *T, tent *TI) {
    for (int r = 0; r < R; r++) {
        el g = rc2el(r, 0), y = gmul(x, g); int r2; long long b2; el2rc(y, &r2, &b2);
        T[r].row = (uint32_t)r2; T[r].rot = (uint32_t)b2;
        TI[r2].row = (uint32_t)r; TI[r2].rot = (uint32_t)(b2 ? L - b2 : 0);
    }
}

/* ---------------- bitset BFS ---------------- */
typedef struct {
    uint64_t *V[2];                 /* side bitsets, R x WR words (+ padding) */
    uint64_t *fl, *fln; long long nf, capf;   /* sparse frontier lists: codes r << 32 | c */
    uint64_t *acc;
    long long *unc; long long nunc, ucap;      /* uncovered elements of the last level (codes) */
    long long lev[64];
    double tlev[64];
} ctx;
static long long DENSEF;
static int UCAP = 65536;
static ctx *new_ctx(void) {
    ctx *c = calloc(1, sizeof *c);
    size_t words = (size_t)R * WR + 16;
    c->V[0] = xmalloc(8 * words); c->V[1] = xmalloc(8 * words);
    memset(c->V[0], 0, 8 * words); memset(c->V[1], 0, 8 * words);
    c->capf = DENSEF + 1024; c->fl = xmalloc(8 * c->capf); c->fln = xmalloc(8 * c->capf);
    c->acc = xmalloc(8 * (size_t)(WR + 16));
    c->ucap = UCAP; c->unc = xmalloc(8 * (size_t)c->ucap);
    return c;
}
/* acc |= src rotated: bit j of acc gets bit (j + rot) mod L of src.  Bits of acc at or above L are not cleaned here. */
static inline void or_rot(uint64_t *restrict acc, const uint64_t *restrict src, uint32_t rot) {
    long long n1 = L - rot;
    int q = (int)(rot >> 6), sh = (int)(rot & 63), w1 = (int)((n1 + 63) >> 6);
    const uint64_t *s = src + q;
    if (sh == 0) { for (int w = 0; w < w1 - 1; w++) acc[w] |= s[w]; }
    else { for (int w = 0; w < w1 - 1; w++) acc[w] |= (s[w] >> sh) | (s[w + 1] << (64 - sh)); }
    { int w = w1 - 1; uint64_t x = sh ? (s[w] >> sh) | (s[w + 1] << (64 - sh)) : s[w]; int nb = (int)(n1 - 64LL * w);
      acc[w] |= nb >= 64 ? x : x & ((1ULL << nb) - 1); }
    if (rot == 0) return;
    int W0 = (int)(n1 >> 6), sh2 = (int)(n1 & 63);
    if (sh2 == 0) { for (int k = 0; W0 + k < WR; k++) acc[W0 + k] |= src[k]; }
    else { acc[W0] |= src[0] << sh2; for (int k = 1; W0 + k < WR; k++) acc[W0 + k] |= (src[k] << sh2) | (src[k - 1] >> (64 - sh2)); }
}
static inline int row_full(const uint64_t *acc) {
    for (int k = 1; k < 8; k++) { int w = (int)((long long)k * (WR - 1) / 8); if (w < WR - 1 && acc[w] != ~0ULL) return 0; }   /* quick reject */
    uint64_t a = ~0ULL; for (int w = 0; w < WR - 1; w++) a &= acc[w];
    return a == ~0ULL && (acc[WR - 1] & TAILM) == TAILM;
}
static inline long long row_pop(const uint64_t *acc) { long long s = 0; for (int w = 0; w < WR; w++) s += __builtin_popcountll(acc[w]); return s; }
static const long long NOBOUND = LLONG_MAX / 4;
static int LEVELS = 0;

/* BFS from (e, startB) for depth steps.  tf[s] = table of s, ti[s] = table of s^-1.
 * A -> B: (g,A) ~ (s g, B) pushes through tf and pulls through ti; B -> A pushes through ti and pulls through tf.
 * count_last: the last level only counts the uncovered elements of its side (and records up to ucap of them),
 * giving up (return -1) once the count reaches bound.  Otherwise every level is written and the return value is the
 * number of elements missing on the final side.  cnt[side] = #reached. */
static long long bfs(ctx *cx, tent **tf, tent **ti, int startB, int depth, int count_last, long long bound, long long cnt[2]) {
    size_t words = (size_t)R * WR;
    memset(cx->V[0], 0, 8 * words); memset(cx->V[1], 0, 8 * words);
    int r0; long long b0; el2rc(ID, &r0, &b0);
    cx->V[startB][(size_t)r0 * WR + (b0 >> 6)] |= 1ULL << (b0 & 63);
    cx->fl[0] = ((uint64_t)r0 << 32) | (uint64_t)b0; cx->nf = 1;
    int dense = 0; cnt[0] = cnt[1] = 0; cnt[startB] = 1;
    int side = startB; long long unc = -1;
    for (int step = 0; step < depth; step++) {
        double tq = LEVELS ? now() : 0;
        int ns = side ^ 1, last = count_last && step == depth - 1;
        uint64_t *Vt = cx->V[ns]; const uint64_t *Vs = cx->V[side];
        tent **Tp = side == 0 ? tf : ti, **Tq = side == 0 ? ti : tf;   /* push / pull tables */
        if (!dense && !last && cx->nf <= DENSEF) {
            long long nn = 0, add = 0, cap = cx->capf; uint64_t *out = cx->fln; int ovf = 0;
            enum { BLK = 16 }; uint64_t tg[BLK * MAXD];   /* targets of a block of frontier elements, prefetched first */
            for (long long u0 = 0; u0 < cx->nf; u0 += BLK) {
                int nb = cx->nf - u0 < BLK ? (int)(cx->nf - u0) : BLK, nt = 0;
                for (int u = 0; u < nb; u++) {
                    uint32_t r = (uint32_t)(cx->fl[u0 + u] >> 32); long long c = (long long)(cx->fl[u0 + u] & 0xffffffffULL);
                    for (int s = 0; s < d; s++) {
                        tent t = Tp[s][r]; long long c2 = c + t.rot; if (c2 >= L) c2 -= L;
                        tg[nt++] = ((uint64_t)t.row << 32) | (uint64_t)c2;
                        __builtin_prefetch(Vt + (size_t)t.row * WR + (c2 >> 6), 1);
                    }
                }
                for (int i = 0; i < nt; i++) {
                    uint32_t r2 = (uint32_t)(tg[i] >> 32); long long c2 = (long long)(tg[i] & 0xffffffffULL);
                    uint64_t *w = Vt + (size_t)r2 * WR + (c2 >> 6), m = 1ULL << (c2 & 63);
                    if (!(*w & m)) { *w |= m; add++; if (nn < cap) out[nn++] = tg[i]; else ovf = 1; }
                }
            }
            cnt[ns] += add;
            uint64_t *tt = cx->fl; cx->fl = cx->fln; cx->fln = tt; cx->nf = ovf ? cap + 1 : nn;
        } else {
            dense = 1;
            uint64_t *acc = cx->acc; long long add = 0, u0 = 0, nrec = cx->nunc, tag = (long long)startB << 62;
            for (int r = 0; r < R; r++) {
                uint64_t *vt = Vt + (size_t)r * WR;
                memcpy(acc, vt, 8 * (size_t)WR);
                if (row_full(acc)) continue;
                long long before = last ? 0 : row_pop(acc);
                for (int s = 0; s < d; s++) {
                    tent t = Tq[s][r];
                    if (s + 1 < d) __builtin_prefetch(Vs + (size_t)Tq[s + 1][r].row * WR + (Tq[s + 1][r].rot >> 6));
                    or_rot(acc, Vs + (size_t)t.row * WR, t.rot);
                    if (last && s >= 4 && row_full(acc)) break;
                }
                acc[WR - 1] &= TAILM;
                if (last) {
                    long long m = L - row_pop(acc);
                    if (m) {
                        u0 += m;
                        if (u0 >= bound) { cx->nunc = nrec; return -1; }
                        for (int w = 0; w < WR && nrec < cx->ucap; w++) {
                            uint64_t z = ~acc[w] & (w == WR - 1 ? TAILM : ~0ULL);
                            while (z && nrec < cx->ucap) { int b = __builtin_ctzll(z); z &= z - 1; cx->unc[nrec++] = tag | ((long long)r << 32) | (64LL * w + b); }
                        }
                    }
                } else { memcpy(vt, acc, 8 * (size_t)WR); add += row_pop(acc) - before; }
            }
            if (last) { unc = u0; cx->nunc = nrec; cnt[ns] = N - u0; }
            else cnt[ns] += add;
        }
        if (step < 64) { cx->lev[step] = cnt[ns]; if (LEVELS) cx->tlev[step] += now() - tq; }
        side = ns;
    }
    if (unc >= 0) return unc;
    return N - cnt[side];
}
/* cost of the generator tables (tf, ti); bound: give up (return -1) as soon as the cost reaches it.
 * The uncovered elements are recorded in cx->unc (codes r << 32 | c, bit 62 set for the list of the BFS from (e,B)). */
static long long cost(ctx *cx, tent **tf, tent **ti, long long bound) {
    long long cnt[2]; cx->nunc = 0;
    if (D % 2 == 0) return bfs(cx, tf, ti, 0, D - 1, 1, bound, cnt);
    long long u1 = bfs(cx, tf, ti, 0, D - 1, 1, bound, cnt); if (u1 < 0) return -1;
    long long u2 = bfs(cx, tf, ti, 1, D - 1, 1, bound == NOBOUND ? NOBOUND : bound - u1, cnt); if (u2 < 0) return -1;
    return u1 + u2;
}
static int full_check(ctx *cx, tent **tf, tent **ti) {
    long long cnt[2];
    for (int st = 0; st < 2; st++) {
        bfs(cx, tf, ti, st, D, 0, NOBOUND, cnt);
        long long a = 0, b = 0; size_t words = (size_t)R * WR;
        for (size_t w = 0; w < words; w++) { a += __builtin_popcountll(cx->V[0][w]); b += __builtin_popcountll(cx->V[1][w]); }
        printf("full check from (e,%c): reached A %lld/%lld, B %lld/%lld within %d\n", st ? 'B' : 'A', a, N, b, N, D);
        if (a != N || b != N) return 0;
    }
    return 1;
}

/* ---------------- alpha and orbits ---------------- */
static int OK_ = 3, OM = 5, OF = 0, AR = 1;
static el AG, AGI;                  /* conjugating element and its inverse */
static el *FIXL; static long long NFIX;
static el S[MAXD], SI[MAXD];
static tent *TF[MAXD], *TI[MAXD];
static inline el alpha(el x) { el y = gmul(gmul(AG, x), AGI); y.z = (int)((long long)AR * x.z % NC); return y; }
static int orbit_of(el x, el *o) {
    o[0] = x; for (int i = 1; i < OK_; i++) { o[i] = alpha(o[i - 1]); if (geq(o[i], x)) return 0; }
    return geq(alpha(o[OK_ - 1]), x);
}
static inline int ostart(int j) { return OF + j * OK_; }
static int orbit_free(const el *o, int j) {
    for (int i = 0; i < OK_; i++) for (int u = 0; u < d; u++) {
        if (j >= 0 && u >= ostart(j) && u < ostart(j) + OK_) continue;
        if (geq(S[u], o[i])) return 0;
    }
    return 1;
}
static int random_orbit(int j, el *o) {
    for (int tries = 0; tries < 100000; tries++) { el x = rand_el(); if (orbit_of(x, o) && orbit_free(o, j)) return 1; }
    return 0;
}
static long long ipow_mod(long long b, long long e, long long m) { long long r = 1 % m; b %= m; while (e) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; } return r; }
static int gcdi(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a < 0 ? -a : a; }
static int order_mod_pm(el g) {     /* order of the matrix part of g modulo +-I (conjugation order) */
    el x = g; x.z = 0; el y = x;
    for (int o = 1; o <= 2 * P + 4; o++) {
        if (y.b == 0 && y.c == 0 && y.a == y.d && (y.a == 1 || y.a == P - 1)) return o;
        y = gmul(y, x);
    }
    return -1;
}
static int choose_alpha(void) {
    int k = OK_;
    if (getenv("AR")) AR = atoi(getenv("AR"));
    else if (NC > 1) {
        int best = -1, bfix = 1 << 30;
        for (int r = 2; r < NC; r++) {
            if (gcdi(r, NC) != 1 || ipow_mod(r, k, NC) != 1) continue;
            int fx = gcdi(r - 1, NC); if (fx < bfix) { bfix = fx; best = r; }
        }
        AR = best < 0 ? 1 : best;
    } else AR = 0;
    /* companion matrix [[0,-1],[1,t]] (det 1, trace t) whose class mod +-I has order k */
    int t0 = getenv("ATRACE") ? atoi(getenv("ATRACE")) : -1, found = 0;
    for (int t = 0; t < P && !found; t++) {
        if (t0 >= 0 && t != t0) continue;
        el g = { 0, P - 1, 1, t, 0 }; canon(&g);
        if (order_mod_pm(g) == k) { AG = g; found = 1; }
    }
    if (!found) { fprintf(stderr, "no conjugating element of order %d\n", k); return 0; }
    AGI = ginv(AG);
    fprintf(stderr, "alpha: conj by mat(%d,%d,%d,%d), z -> %d z on Z_%d\n", AG.a, AG.b, AG.c, AG.d, AR, NC);
    return 1;
}
static void find_fix(void) {   /* Fix(alpha) \ {e}: torus {x I + y g} with det 1, times {z : (r-1) z = 0} */
    long long cap = 4 * (long long)P + 16, nz = 0; int *zs = malloc(sizeof(int) * NC);
    for (int z = 0; z < NC; z++) if ((long long)(AR - 1 + NC) * z % NC == 0) zs[nz++] = z;
    el *tor = malloc(sizeof(el) * cap); long long nt = 0;
    for (int x = 0; x < P; x++) for (int y = 0; y < P; y++) {
        el m = { (int)((x + (long long)y * AG.a) % P), (int)((long long)y * AG.b % P), (int)((long long)y * AG.c % P), (int)((x + (long long)y * AG.d) % P), 0 };
        if (((long long)m.a * m.d - (long long)m.b * m.c) % P != 1 % P && (((long long)m.a * m.d - (long long)m.b * m.c) % P + P) % P != 1) continue;
        canon(&m); int dup = 0; for (long long i = 0; i < nt; i++) if (geq(tor[i], m)) { dup = 1; break; }
        if (!dup && nt < cap) tor[nt++] = m;
    }
    FIXL = malloc(sizeof(el) * (nt * nz + 1)); NFIX = 0;
    for (long long i = 0; i < nt; i++) for (long long j = 0; j < nz; j++) { el x = tor[i]; x.z = zs[j]; if (geq(x, ID)) continue; if (!geq(alpha(x), x)) { fprintf(stderr, "fixed-point error\n"); exit(2); } FIXL[NFIX++] = x; }
    free(tor); free(zs);
}
static double Wwords(int dd, int DD) {
    double w = 0;
    if (DD % 2) { int k = (DD - 1) / 2; w = 1; for (int i = 1; i <= k; i++) w += dd * pow(dd - 1, 2 * i - 1); }
    else { int k = DD / 2; for (int i = 0; i < k; i++) w += dd * pow(dd - 1, 2 * i); }
    return w;
}

/* ---------------- targeted moves ---------------- */
static long long *CUNC; static long long CNUNC, CTRUE;   /* current S: stored uncovered codes, true count */
static inline el code2el(long long code) { return rc2el((int)((code >> 32) & 0x3fffffff), code & 0xffffffffLL); }
static uint32_t AVOIDMASK = 0;
static el walk(el g, int *side, int len) {
    for (int s = 0; s < len; s++) {
        int j; do j = (int)(rnd() % d); while ((AVOIDMASK >> j) & 1);
        g = (*side == 0) ? gmul(S[j], g) : gmul(SI[j], g);
        *side ^= 1;
    }
    return g;
}
static int targeted(el *out) {
    if (CNUNC == 0) return 0;
    long long code = CUNC[rnd() % CNUNC]; int tagB = (int)((code >> 62) & 1);
    el u = code2el(code);
    for (int tries = 0; tries < 20; tries++) {
        int a = (int)(rnd() % (D - 1)), b = (int)(rnd() % (D - 1 - a));
        /* D even: the list is side B of the BFS from (e,A); D odd: side A from (e,A) (tag 0) or side B from (e,B) */
        int sp = D % 2 ? tagB : 0, sq = D % 2 ? tagB : 1;
        el Pw = walk(ID, &sp, a), Qw = walk(u, &sq, b);
        if (sp == sq) continue;
        el gA = sp == 0 ? Pw : Qw, hB = sp == 0 ? Qw : Pw;
        *out = gmul(hB, ginv(gA)); return 1;
    }
    return 0;
}

static volatile int stop_flag = 0;
static void on_term(int s) { (void)s; stop_flag = 1; }
static long long sl_index(el x) {   /* haar_gen3's element index for SL(2,p) x Z_n (build_matrix enumeration order) */
    long long q = P, k;
    if (x.a) k = (q - 1) * q + (long long)(x.a - 1) * q * q + (long long)x.b * q + x.c;
    else k = (long long)(x.b - 1) * q + x.d;
    return k * NC + x.z;
}
static int write_solution(ctx *c0, const char *out) {
    for (int i = 0; i < d; i++) for (int j = 0; j < i; j++) if (geq(S[i], S[j])) { printf("repeated generator\n"); return 0; }
    int ok = full_check(c0, TF, TI); printf("full diameter check: %s\n", ok ? "OK" : "FAIL"); if (!ok) return 0;
    if (!geq(S[0], ID)) {
        el a0 = ginv(S[0]); for (int i = 0; i < d; i++) S[i] = gmul(S[i], a0);
        for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); make_tables(S[u], TF[u], TI[u]); }
        int ok2 = full_check(c0, TF, TI); printf("full diameter check after normalising s_0 = e: %s\n", ok2 ? "OK" : "FAIL"); if (!ok2) return 0;
    }
    FILE *f = fopen(out, "w"); if (!f) { perror(out); return 0; }
    fprintf(f, "%d %d %s %d n %d N %lld\n", d, D, PSL ? "psl" : "sl", P, NC, N);
    for (int i = 0; i < d; i++) fprintf(f, "%lld mat(%d,%d,%d,%d) z=%d\n", PSL ? 0LL : sl_index(S[i]), S[i].a, S[i].b, S[i].c, S[i].d, S[i].z);
    fclose(f); printf("wrote %s\n", out);
    return 1;
}
static int read_solution(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); return 0; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 0;
    int k = 0;
    while (fgets(line, sizeof line, f) && k < MAXD) {
        char *m = strstr(line, "mat("), *zz = strstr(line, "z=");
        if (!m || !zz) continue;
        el x; if (sscanf(m, "mat(%d,%d,%d,%d)", &x.a, &x.b, &x.c, &x.d) != 4 || sscanf(zz, "z=%d", &x.z) != 1) return 0;
        canon(&x); S[k++] = x;
    }
    fclose(f);
    if (k != d) { fprintf(stderr, "read %d generators, expected %d\n", k, d); return 0; }
    return 1;
}
static long long fixmiss(ctx *cx) {   /* uncovered alpha-fixed elements among the recorded uncovered list */
    long long m = 0;
    for (long long i = 0; i < cx->nunc; i++) { el x = code2el(cx->unc[i]); if (geq(alpha(x), x)) m++; }
    return m;
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: haar_lean d D seconds seed K outfile sl|psl p n\n"); return 2; }
    setvbuf(stdout, NULL, _IOLBF, 0); setvbuf(stderr, NULL, _IOLBF, 0);
    d = atoi(argv[1]); D = atoi(argv[2]); double secs = atof(argv[3]); unsigned long long seed = strtoull(argv[4], 0, 10);
    int K = atoi(argv[5]); const char *out = argv[6];
    PSL = !strcmp(argv[7], "psl"); if (!PSL && strcmp(argv[7], "sl")) { fprintf(stderr, "group must be sl or psl\n"); return 2; }
    P = atoi(argv[8]); NC = atoi(argv[9]);
    if (d > MAXD || d < 2 || K < 1 || K > 64) { fprintf(stderr, "bad d or K\n"); return 2; }
    if (P < 5) { fprintf(stderr, "p >= 5\n"); return 2; }
    for (int t = 2; t * t <= P; t++) if (P % t == 0) { fprintf(stderr, "p must be prime\n"); return 2; }
    if (NC < 1 || NC % P == 0) { fprintf(stderr, "need n >= 1 and gcd(p, n) = 1\n"); return 2; }
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    signal(SIGTERM, on_term); signal(SIGINT, on_term);
    H = (P - 1) / 2;
    INV = malloc(sizeof(int) * P); INV[0] = 0; for (int x = 1; x < P; x++) INV[x] = (int)ipow_mod(x, P - 2, P);
    L = (long long)P * NC; R = PSL ? (P * P - 1) / 2 : P * P - 1; WR = (int)((L + 63) / 64);
    N = (long long)R * L; TAILM = (L % 64) ? (1ULL << (L % 64)) - 1 : ~0ULL;
    { long long ip = ipow_mod(NC % P, P - 2, P);   /* n^-1 mod p */
      E1 = (long long)NC * ip % L; E2 = (1 - E1 + L) % L; if (NC == 1) { E1 = 1 % L; E2 = 0; } }
    ID = (el){1, 0, 0, 1, 0};
    DENSEF = getenv("DENSEF") ? atoll(getenv("DENSEF")) : N / 256 + 1024;
    if (getenv("UCAP")) UCAP = atoi(getenv("UCAP"));
    LEVELS = getenv("LEVELS") ? atoi(getenv("LEVELS")) : 0;
    /* self-test of the indexing */
    for (int t = 0; t < 2000; t++) { int r = (int)(rnd() % R); long long b = (long long)(rnd() % L); el x = rc2el(r, b); int r2; long long b2; el2rc(x, &r2, &b2);
        if (r2 != r || b2 != b || (((long long)x.a * x.d - (long long)x.b * x.c) % P + P) % P != 1) { fprintf(stderr, "index self-test failed\n"); return 2; }
        el y = rand_el(), xy = gmul(x, y); int rx, ry, rxy; long long bx, by, bxy; el2rc(x, &rx, &bx); el2rc(y, &ry, &by); el2rc(xy, &rxy, &bxy);
        (void)rx; (void)bx; (void)rxy; (void)bxy; (void)ry; (void)by; }
    int nth = getenv("THREADS") ? atoi(getenv("THREADS")) : 1; if (nth < 1) nth = 1; if (nth > K) nth = K;
#ifdef _OPENMP
    omp_set_num_threads(nth);
#endif
    if (getenv("ORBIT")) { if (sscanf(getenv("ORBIT"), "%d %d %d", &OK_, &OM, &OF) != 3) { fprintf(stderr, "ORBIT=\"k m f\"\n"); return 2; } }
    else { OK_ = 3; OF = d % 3 == 0 ? 0 : d % 3; OM = (d - OF) / 3; }
    if (OK_ < 2 || OM < 1 || OF < 0 || OF + OK_ * OM != d) { fprintf(stderr, "ORBIT: f + k m = d\n"); return 2; }
    double t00 = now();
    ctx **C = malloc(sizeof(ctx *) * nth); for (int t = 0; t < nth; t++) C[t] = new_ctx();
    for (int i = 0; i < d; i++) { TF[i] = xmalloc(sizeof(tent) * (size_t)R); TI[i] = xmalloc(sizeof(tent) * (size_t)R); }
    fprintf(stderr, "group %s %d x Z_%d, N=%lld, rows %d of %lld bits (%d words), memory %.2f GB per thread, threads %d, setup %.2fs\n",
            PSL ? "psl" : "sl", P, NC, N, R, L, WR, 2.0 * 8 * R * (double)WR / 1e9, nth, now() - t00);
    double Ww = Wwords(d, D), lam = Ww / N, mu = N * exp(-lam);

    if (getenv("SOLFILE")) {   /* cost and full check of a given S (validation) */
        if (!read_solution(getenv("SOLFILE"))) return 2;
        for (int i = 0; i < d; i++) { SI[i] = ginv(S[i]); make_tables(S[i], TF[i], TI[i]); }
        double t1 = now(); long long c = cost(C[0], TF, TI, NOBOUND);
        printf("SOLFILE cost=%lld (%.2fs) mu=%.2f levels:", c, now() - t1, mu); for (int h = 0; h < D - 1; h++) printf(" %lld", C[0]->lev[h]); printf("\n");
        if (c == 0) { int ok = full_check(C[0], TF, TI); printf("SOLFILE full check: %s\n", ok ? "VALID" : "INVALID"); }
        return 0;
    }
    if (!choose_alpha()) return 2;
    { for (int u = 0; u < 6; u++) { el x = rand_el(), y = rand_el();
        if (!geq(alpha(gmul(x, y)), gmul(alpha(x), alpha(y)))) { fprintf(stderr, "alpha is not an automorphism\n"); return 2; }
        el w = x; for (int i = 0; i < OK_; i++) w = alpha(w); if (!geq(w, x)) { fprintf(stderr, "alpha^k != 1\n"); return 2; } } }
    find_fix();
    double nb = D % 2 ? 2 : 1;
    fprintf(stderr, "ORBIT k=%d m=%d f=%d: |Fix(alpha)| = %lld (+e); mu = %.2f, mu/k = %.2f, fixed-point misses ~ %.2f\n",
            OK_, OM, OF, NFIX, mu, mu / OK_, nb * (NFIX + 1) * exp(-lam / OK_));
    /* initial S */
    if (OF) S[0] = ID;
    for (int u = 1; u < OF; u++) { int ok; el x; do { x = FIXL[rnd() % NFIX]; ok = 1; for (int v = 0; v < u; v++) if (geq(S[v], x)) ok = 0; } while (!ok); S[u] = x; }
    for (int u = OF; u < d; u++) S[u] = (el){-1, -1, -1, -1 - u, -1};
    for (int j = 0; j < OM; j++) { el o[MAXD]; if (!random_orbit(j, o)) { fprintf(stderr, "no orbit found\n"); return 2; } for (int i = 0; i < OK_; i++) S[ostart(j) + i] = o[i]; }
    for (int i = 0; i < d; i++) { SI[i] = ginv(S[i]); make_tables(S[i], TF[i], TI[i]); }
    if (getenv("BENCH")) {
        int m = atoi(getenv("BENCH")); LEVELS = 1; double t1 = now(); long long c = 0;
        for (int t = 0; t < m; t++) c = cost(C[0], TF, TI, NOBOUND);
        double tt = now() - t1; double tb = now(); make_tables(S[0], TF[0], TI[0]); double tm = now() - tb;
        printf("BENCH %d evals: %.3f s/eval (last cost %lld), make_tables %.4f s; per level:", m, tt / m, c, tm);
        for (int h = 0; h < D - 1; h++) printf(" %.3f", C[0]->tlev[h] / m); printf("\nlevels:");
        for (int h = 0; h < D - 1; h++) printf(" %lld", C[0]->lev[h]); printf("\n");
        return 0;
    }
    if (getenv("RANDORB")) {
        int m = atoi(getenv("RANDORB")), saved = 0; long long *v = malloc(sizeof(long long) * m); double sm = 0, t1 = now();
        double *u = malloc(sizeof(double) * m), su = 0;   /* units = uncovered free alpha-orbits + uncovered fixed points */
        for (int t = 0; t < m; t++) {
            for (int j = 0; j < OM; j++) for (int i = 0; i < OK_; i++) S[ostart(j) + i] = (el){-1, -1, -1, -1 - ostart(j) - i, -1};
            for (int j = 0; j < OM; j++) { el o[MAXD]; random_orbit(j, o); for (int i = 0; i < OK_; i++) { int u = ostart(j) + i; S[u] = o[i]; SI[u] = ginv(o[i]); make_tables(o[i], TF[u], TI[u]); } }
            v[t] = cost(C[0], TF, TI, NOBOUND); sm += v[t];
            { long long fm = fixmiss(C[0]); u[t] = (double)(v[t] - fm) / OK_ + fm; su += u[t]; }
            if (LEVELS) { fprintf(stderr, "levels:"); for (int h = 0; h < D - 1; h++) fprintf(stderr, " %lld", C[0]->lev[h]); fprintf(stderr, " cost %lld units %.1f\n", v[t], u[t]); }
            if (v[t] == 0 && !saved && strcmp(out, "/dev/null")) saved = write_solution(C[0], out);
        }
        for (int i = 1; i < m; i++) { long long x = v[i]; int j = i - 1; while (j >= 0 && v[j] > x) { v[j + 1] = v[j]; j--; } v[j + 1] = x; }
        for (int i = 1; i < m; i++) { double x = u[i]; int j = i - 1; while (j >= 0 && u[j] > x) { u[j + 1] = u[j]; j--; } u[j + 1] = x; }
        printf("RANDORB d=%d D=%d group=%s %d x Z_%d N=%lld k=%d m=%d f=%d fix=%lld samples=%d min=%lld p10=%lld median=%lld mean=%.2f mu=%.2f time=%.1f"
               " units: min=%.1f p10=%.1f median=%.1f mean=%.2f\n",
               d, D, PSL ? "psl" : "sl", P, NC, N, OK_, OM, OF, NFIX, m, v[0], v[m / 10], v[m / 2], sm / m, mu, now() - t1,
               u[0], u[m / 10], u[m / 2], su / m);
        return 0;
    }

    /* ---------------- annealing over orbits ---------------- */
    double COOL = getenv("COOL") ? atof(getenv("COOL")) : 20.0, REHEAT = getenv("REHEAT") ? atof(getenv("REHEAT")) : 150.0;
    double TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 1.5, TMIN = getenv("TMIN") ? atof(getenv("TMIN")) : 0.15;
    int TARGP = getenv("TARGP") ? atoi(getenv("TARGP")) : 70, ORBW = getenv("ORBW") ? atoi(getenv("ORBW")) : 1;
    long long REHEATSTEPS = getenv("REHEATSTEPS") ? atoll(getenv("REHEATSTEPS")) : 400;
    int ORESTART = getenv("RESTART") ? atoi(getenv("RESTART")) : 0;
    tent *OTF[64][MAXD], *OTI[64][MAXD];
    for (int t = 0; t < K; t++) for (int i = 0; i < OK_; i++) { OTF[t][i] = xmalloc(sizeof(tent) * (size_t)R); OTI[t][i] = xmalloc(sizeof(tent) * (size_t)R); }
    long long *UNCS[64]; long long NUNCS[64]; for (int t = 0; t < K; t++) UNCS[t] = xmalloc(8 * (size_t)UCAP);
    CUNC = xmalloc(8 * (size_t)UCAP);
    el cand[64][MAXD]; long long cs[64], craw[64]; el bestS[MAXD];
    double te = now(); long long c = cost(C[0], TF, TI, NOBOUND), ce = c + (ORBW > 1 ? (ORBW - 1) * fixmiss(C[0]) : 0); te = now() - te;
    CNUNC = C[0]->nunc; memcpy(CUNC, C[0]->unc, 8 * CNUNC); CTRUE = c;
    long long best = c, bestE = ce; memcpy(bestS, S, sizeof(el) * d);
    double cE = (double)ce / OK_, t0 = now(), T = TMAX, lastimp = t0, lastprint = t0, lastheat = t0;
    long long evals = 1, steps = 0, lastimpstep = 0;
    fprintf(stderr, "start cost=%lld (first eval %.2fs)\n", c, te);
    int nslots = OM + (OF > 1 ? OF - 1 : 0);
    while (!stop_flag && now() - t0 < secs && best > 0) {
        int slot = (int)(rnd() % nslots), isorb = slot < OM, j = slot, fs = isorb ? -1 : 1 + (slot - OM);
        for (int t = 0; t < K; t++) {
            if (isorb) {
                el x, o[MAXD]; int ok = 0;
                AVOIDMASK = 0; for (int i = 0; i < OK_; i++) AVOIDMASK |= 1u << (ostart(j) + i);
                if ((int)(rnd() % 100) < TARGP && targeted(&x) && !geq(x, ID) && orbit_of(x, o) && orbit_free(o, j)) ok = 1;
                AVOIDMASK = 0;
                if (!ok) random_orbit(j, o);
                memcpy(cand[t], o, sizeof(el) * OK_);
            } else { int ok; el x; do { x = FIXL[rnd() % NFIX]; ok = 1; for (int v = 0; v < d; v++) if (v != fs && geq(S[v], x)) ok = 0; } while (!ok); cand[t][0] = x; }
        }
        long long bound = NOBOUND;
        #pragma omp parallel for schedule(dynamic, 1) if (nth > 1)
        for (int t = 0; t < K; t++) {
            int me = 0;
#ifdef _OPENMP
            me = omp_get_thread_num();
#endif
            ctx *cx = C[me]; tent *tf[MAXD], *ti[MAXD]; memcpy(tf, TF, sizeof(tent *) * d); memcpy(ti, TI, sizeof(tent *) * d);
            if (isorb) for (int i = 0; i < OK_; i++) { make_tables(cand[t][i], OTF[t][i], OTI[t][i]); tf[ostart(j) + i] = OTF[t][i]; ti[ostart(j) + i] = OTI[t][i]; }
            else { make_tables(cand[t][0], OTF[t][0], OTI[t][0]); tf[fs] = OTF[t][0]; ti[fs] = OTI[t][0]; }
            long long bv = __atomic_load_n(&bound, __ATOMIC_RELAXED);
            long long r = cost(cx, tf, ti, bv == NOBOUND ? NOBOUND : bv + (nth > 1));
            if (r >= 0) { NUNCS[t] = cx->nunc; memcpy(UNCS[t], cx->unc, 8 * cx->nunc); craw[t] = r; if (ORBW > 1) r += (ORBW - 1) * fixmiss(cx); }
            if (r < 0) cs[t] = NOBOUND;
            else { cs[t] = r; long long b2 = __atomic_load_n(&bound, __ATOMIC_RELAXED);
                while (r < b2 && !__atomic_compare_exchange_n(&bound, &b2, r, 0, __ATOMIC_RELAXED, __ATOMIC_RELAXED)) ; }
        }
        evals += K;
        int bt = 0; for (int t = 1; t < K; t++) if (cs[t] < cs[bt]) bt = t;
        double bE = (double)cs[bt] / OK_;
        if (cs[bt] < NOBOUND && (bE <= cE || exp((cE - bE) / T) > (rnd() % 1000000) / 1e6)) {
            if (isorb) for (int i = 0; i < OK_; i++) { int u = ostart(j) + i; S[u] = cand[bt][i]; SI[u] = ginv(S[u]); tent *a = TF[u], *b = TI[u]; TF[u] = OTF[bt][i]; TI[u] = OTI[bt][i]; OTF[bt][i] = a; OTI[bt][i] = b; }
            else { S[fs] = cand[bt][0]; SI[fs] = ginv(S[fs]); tent *a = TF[fs], *b = TI[fs]; TF[fs] = OTF[bt][0]; TI[fs] = OTI[bt][0]; OTF[bt][0] = a; OTI[bt][0] = b; }
            c = craw[bt]; ce = cs[bt]; cE = bE; CNUNC = NUNCS[bt]; memcpy(CUNC, UNCS[bt], 8 * CNUNC); CTRUE = c;
        }
        steps++;
        if (ce < bestE) { best = c; bestE = ce; memcpy(bestS, S, sizeof(el) * d); lastimp = now(); lastimpstep = steps; }
        T = TMAX * pow(0.5, (now() - lastheat) / COOL); if (T < TMIN) T = TMIN;
        if (now() - lastimp > REHEAT && steps - lastimpstep > REHEATSTEPS) {
            lastheat = now(); T = TMAX; memcpy(S, bestS, sizeof(el) * d);
            if (ORESTART) {
                for (int jj = 0; jj < OM; jj++) for (int i = 0; i < OK_; i++) S[ostart(jj) + i] = (el){-1, -1, -1, -1 - ostart(jj) - i, -1};
                for (int jj = 0; jj < OM; jj++) { el o[MAXD]; random_orbit(jj, o); for (int i = 0; i < OK_; i++) S[ostart(jj) + i] = o[i]; }
            }
            for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); make_tables(S[u], TF[u], TI[u]); }
            c = cost(C[0], TF, TI, NOBOUND); ce = c + (ORBW > 1 ? (ORBW - 1) * fixmiss(C[0]) : 0); cE = (double)ce / OK_;
            CNUNC = C[0]->nunc; memcpy(CUNC, C[0]->unc, 8 * CNUNC); CTRUE = c; lastimp = now(); lastimpstep = steps;
        }
        if (now() - lastprint > 30) { fprintf(stderr, "t=%.0f steps=%lld evals=%lld cost=%lld best=%lld T=%.2f%s\n", now() - t0, steps, evals, c, best, T,
                                              ORBW > 1 ? " (energy counts fixed points)" : ""); lastprint = now(); }
    }
    memcpy(S, bestS, sizeof(el) * d);
    for (int u = 0; u < d; u++) { SI[u] = ginv(S[u]); make_tables(S[u], TF[u], TI[u]); }
    printf("RESULT d=%d D=%d group=%s %d x Z_%d N=%lld best=%lld evals=%lld time=%.1f orbit k=%d m=%d f=%d fix=%lld\n",
           d, D, PSL ? "psl" : "sl", P, NC, N, best, evals, now() - t0, OK_, OM, OF, NFIX);
    if (best == 0) { long long c2 = cost(C[0], TF, TI, NOBOUND); printf("recomputed cost of best S: %lld\n", c2); if (c2 != 0 || !write_solution(C[0], out)) return 1; }
    return best == 0 ? 0 : 1;
}
