/* haar_sd (c12, beyond-d11 round 1): haar_big0.c plus SD=1 self-dual symmetric S for odd D (section SD below).
 * Usage: SDSIZES="6 6" haar_sd d D seconds seed K outfile sl|psl p n   (d = 1 + sum of SDSIZES; e is slot 0).
 * Cost = 2 x one-sided hole count (valid when tau(S)=S, checked by EVAL), one BFS per evaluation.
 * Build: gcc -O3 -march=native -fopenmp -o haar_sd haar_sd.c -lm */
/* haar_big: orbit-symmetric Haar graph search for very large groups, G = SL(2,p) x Z_n or PSL(2,p) x Z_n
 * (p an odd prime >= 5, gcd(p, n) = 1), |G| up to ~3e10.  Job cell-16-10 (2026-10-24); odd D added by job
 * new-cells-beyond (2026-10-26): for odd D the last level is X_(D-1) = S^-1 Y_(D-2) (side A); cost = #A-side elements
 * not within D-1 of (e,A) plus the same count for H(G, S^-1) (= B-side elements not within D-1 of (e,B)); cost 0 gives
 * diameter <= D (same side <= D-1, other side one step more).  ZQ/FIXF: even D only.
 *
 * Haar graph H(G,S): vertices (g,A), (g,B); edges (g,A) ~ (s g, B), s in S, |S| = d, s_0 = e.  Right multiplication
 * by G preserves edges and is transitive on each side.  Cost = #B-side elements not within D-1 of (e,A).  For even D,
 * cost 0 implies diameter <= D: every A-vertex is then within D-1 of every B-vertex, and two vertices on the same side
 * are within D (step to a neighbour of one of them first).  With e in S the BFS level sets are nested,
 * X_0 = {e} c Y_1 = S X_0 c X_2 = S^-1 Y_1 c ... c Y_(D-1), and cost = N - |Y_(D-1)|.
 *
 * Layout.  Rows are the left cosets of C = U x Z_n, U = {u(t) = [[1,t],[0,1]]}; C is cyclic of order L = p n.
 *   SL : row <-> first column v = (a,c) != 0, R = p^2 - 1 rows; rep(v) = [[a,0],[c,1/a]] (a != 0), [[0,-1/c],[c,0]].
 *   PSL: v up to sign (first nonzero coordinate in 1..(p-1)/2), R = (p^2-1)/2; matrices are kept with that sign.
 *   (rep(v) u(t), z) is bit i of row v, i = CRT(t mod p, z mod n) in [0, L).
 *   s = (M, w): s rep(v) = rep(v') u(k) (v' = M v, up to sign for PSL), so s maps row v to row v' rotated by
 *   c(s,v) = CRT(k, w): bit i -> bit i + c (mod L).
 * Each row is stored twice in a row (2L bits) so that a rotation is one window read.  A dense BFS level is a pull,
 * T[w] = OR_s rot(C[src_s(w)], c), over all target rows w; sparse levels push from an element list instead.  The last
 * level only counts zeros (512-bit chunks stop as soon as they are full) and lists the uncovered elements.
 * Memory: two bitsets of 2N bits (N/2 bytes) plus small tables, about 1.1 GB at N = 2.2e9.
 *
 * Search: the ORBIT mode of research/structured/haar_sym.c.  alpha = (conjugation by g = [[0,-1],[1,-1]], order 3)
 * x (z -> r z, r of order 3 mod n with the fewest fixed points); S = {e} + (f-1) alpha-fixed generators + m alpha-orbits
 * of size 3 (d = f + 3m).  Annealing over orbit slots: each step proposes K candidate orbits for one slot (TARGP % of
 * them targeted at a random uncovered element: a random walk from (e,A) and one from the uncovered vertex, joined by
 * the new generator), evaluates them with the exact best-of-K abort, and accepts the best by Metropolis on energy
 * cost/3.  Schedules count steps, not seconds (one step costs K evaluations of ~1 s at N = 2e9).
 *
 * Usage: haar_big d D seconds seed K outfile sl|psl p n
 * Env: ORBIT="k m f" (default "3 m 1" with m = (d-1)/3), THREADS (OpenMP threads, default 1), TARGP (70),
 *      TMAX (1.5), TMIN (0.15), COOLSTEPS (steps per halving of T, 4), REHEATSTEPS (steps without gain before a reheat
 *      from the best S, 60), PUSHMAX (push a level iff |list| * d <= PUSHMAX, default min(2^24, N d / 512)), UCAP (65536),
 *      RANDORB=m (cost statistics of m random symmetric S, no search), EVAL=file (cost of the S in a solution file),
 *      START=file (start the search from the S in a solution file; it must have the orbit structure), BENCH=1 (timings),
 *      ORBIT f > 1: the f - 1 alpha-fixed generators are drawn at random once and never moved (new-cells-beyond).
 *      UNCPRINT=1 (with EVAL: list up to 200 uncovered elements), FIXF=1 (D = 10 only: screen each candidate on the
 *      alpha-fixed elements by meet in the middle, ~0.1 s, and fully evaluate only candidates with at most FIXMAX (0)
 *      fixed holes, trying up to FIXTRY (200) per candidate slot; with EVAL it compares the screen with the full count),
 *      BOUNDCUR=1 (once T is at TMIN, abort every candidate as soon as it is worse than the current S), FIX2=1 (the
 *      faster screen: s^-1 v x in X_4 instead of building Y_5).
 * Output: solution file in haar_gen3 format: "d D sl p n NCYC N NTOT" then d lines "<index> mat(a,b,c,d) z=Z",
 *      first generator e; checked independently by research/frontier/haarcheck_sl.c, haarcheck2.c (SL) and
 *      research/structured/tools/haarcheck_psl.c (PSL).  The current best S is also written to outfile.best after
 *      every improvement.
 * f = 0 (job beyond-d11, 2026-11-01, haar_big0.c): ORBIT="k m 0" searches S = m free alpha-orbits without e (the right
 *      choice for 3 | d, research/structured/STRUCTURE.md 8); every evaluation uses T = S s_0^-1, which contains e and
 *      gives an isomorphic Haar graph; solution files hold T (first generator e), <out>.orb the orbit form (for START).
 * Build: gcc -O3 -march=native -fopenmp -o haar_big haar_big.c -lm
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <signal.h>
#include <immintrin.h>
#include <omp.h>

typedef uint64_t u64; typedef int64_t i64; typedef uint32_t u32;
#define MAXD 64

static int P, PSL, HALF;      /* p, PSL flag, (p-1)/2 */
static i64 NC = 1;            /* n */
static i64 L, R, NG;          /* row length p n, rows, |G| */
static i64 LW, LW8, RW;       /* words per row copy, LW rounded up to 8, words per stored (doubled) row */
static i64 CP, CN;            /* CRT: i = (t CP + z CN) mod L */
static int *INV;
static int d, D;
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static u64 rs = 88172645463325252ULL;
static inline u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int md(i64 x) { x %= P; return (int)(x < 0 ? x + P : x); }

/* ---------------- group elements ---------------- */
typedef struct { int a, b, c, d; i64 z; } el;
static el E_ID;
static inline el canon(el x) {   /* PSL: sign with the first nonzero of (a,c) in 1..(p-1)/2 */
    if (PSL) { int f = x.a ? x.a : x.c; if (f > HALF) { x.a = md(-x.a); x.b = md(-x.b); x.c = md(-x.c); x.d = md(-x.d); } }
    return x;
}
static inline el emul(el x, el y) {
    el r; r.a = md((i64)x.a * y.a + (i64)x.b * y.c); r.b = md((i64)x.a * y.b + (i64)x.b * y.d);
    r.c = md((i64)x.c * y.a + (i64)x.d * y.c); r.d = md((i64)x.c * y.b + (i64)x.d * y.d); r.z = (x.z + y.z) % NC;
    return canon(r);
}
static inline el einv(el x) { el r = {x.d, md(-x.b), md(-x.c), x.a, (NC - x.z) % NC}; return canon(r); }
static inline int eeq(el x, el y) { return x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d && x.z == y.z; }
static inline i64 vrow(int a, int c) {      /* row of the (canonical) first column (a,c) */
    if (!PSL) return (i64)a * P + c - 1;
    return a ? (i64)(a - 1) * P + c : (i64)HALF * P + c - 1;
}
static inline void rowv(i64 r, int *a, int *c) {
    if (!PSL) { i64 x = r + 1; *a = (int)(x / P); *c = (int)(x % P); return; }
    if (r < (i64)HALF * P) { *a = (int)(r / P) + 1; *c = (int)(r % P); } else { *a = 0; *c = (int)(r - (i64)HALF * P) + 1; }
}
static inline int tco(el x) { return x.a ? md((i64)x.b * INV[x.a]) : md((i64)x.d * INV[x.c]); }   /* x = rep(v) u(t) */
static inline i64 crt(i64 t, i64 z) { return (i64)(((__int128)t * CP + (__int128)z * CN) % L); }
static inline i64 eidx(el x) { return vrow(x.a, x.c) * L + crt(tco(x), x.z); }
static el eofidx(i64 g) {
    i64 r = g / L, i = g % L; int a, c; rowv(r, &a, &c);
    int t = (int)(i % P); el x; x.a = a; x.c = c; x.z = i % NC;
    if (a) { x.b = md((i64)a * t); x.d = md((i64)c * t + INV[a]); }
    else { x.b = md(-(i64)INV[c]); x.d = md((i64)c * t); }
    return x;
}
static void edesc(el x, char *buf) { sprintf(buf, "%lld mat(%d,%d,%d,%d) z=%lld", (long long)eidx(x), x.a, x.b, x.c, x.d, (long long)x.z); }

/* ---------------- generator tables ---------------- */
/* per generator j: FR[j][v] = row of s_j rep(v), FC[j][v] = its rotation c(s_j, v);
 * pull tables: PS[j][w] = (src << 32) | offset for S levels, PI[j][w] for S^-1 levels (window offset in (0, L]) */
static u32 *FR[MAXD], *FC[MAXD];
static u64 *PS[MAXD], *PI[MAXD];
static el S[MAXD];
static el TT[MAXD];   /* the evaluated generators: TT = S, or S s_0^-1 when f = 0 (beyond-d11, 2026-11-01) */
static int OF0 = 0;   /* f = 0: S is m free alpha-orbits without e; H(G,S) = H(G, S s_0^-1) up to isomorphism */
static void make_tables(int j) {
    el s = S[j];
    if (OF0) s = j == 0 ? E_ID : emul(S[j], einv(S[0]));
    TT[j] = s;
    for (i64 v = 0; v < R; v++) {
        int a, c; rowv(v, &a, &c);
        el rep; rep.a = a; rep.c = c; rep.z = 0;
        if (a) { rep.b = 0; rep.d = INV[a]; } else { rep.b = md(-(i64)INV[c]); rep.d = 0; }
        el m = emul(s, rep);                       /* = rep(v') u(k), z = s.z */
        i64 v2 = vrow(m.a, m.c); i64 cr = crt(tco(m), s.z);
        FR[j][v] = (u32)v2; FC[j][v] = (u32)cr;
        PS[j][v2] = ((u64)v << 32) | (u64)(L - cr);             /* S: T[v2] |= rot(C[v], cr): window offset L - cr */
        PI[j][v] = ((u64)v2 << 32) | (u64)(cr ? cr : L);        /* S^-1: T[v] |= rot(C[v2], -cr): offset cr */
    }
}

/* ---------------- BFS / cost ---------------- */
static u64 *BUF[2];
static i64 *LIST; static i64 LISTCAP, PUSHMAX = 1 << 24;
static int NTH = 1;
static u64 **ACC;                 /* per-thread accumulators, LW8 + 8 words */
static int UCAP = 65536;
static double TLEV[64]; static int BENCH = 0;
static inline void setbit2(u64 *B, i64 r, i64 i) {
    u64 *row = B + r * RW; i64 j = i + L;
    row[i >> 6] |= 1ULL << (i & 63); row[j >> 6] |= 1ULL << (j & 63);
}
static inline int getbit(const u64 *B, i64 r, i64 i) { return (B[r * RW + (i >> 6)] >> (i & 63)) & 1; }
static u64 LASTMASK;              /* valid bits of word LW-1 */

static inline __m512i win8(const u64 *row, i64 q, __m128i sh, __m128i sh2) {
    __m512i lo = _mm512_loadu_si512((const void *)(row + q)), hi = _mm512_loadu_si512((const void *)(row + q + 1));
    return _mm512_or_si512(_mm512_srl_epi64(lo, sh), _mm512_sll_epi64(hi, sh2));
}
static u64 **RB;                  /* per-thread doubled-row buffers, RW words */
static int PFD = 2;               /* rows ahead whose source windows are prefetched */
static inline void prefetch_row(const u64 *C, u64 **tab, i64 w) {
    for (int j = 0; j < d; j++) { u64 e = tab[j][w]; const u64 *s = C + (i64)(e >> 32) * RW + (((u32)e) >> 6);
        _mm_prefetch((const char *)s, _MM_HINT_T0); _mm_prefetch((const char *)(s + 8), _MM_HINT_T0); }
}
/* one dense level: T = (S or S^-1) . C over all rows.  Per 512-bit chunk the d source windows are ORed in a register;
 * the doubled target row is built in a thread buffer and streamed out with non-temporal stores. */
static int LEVPOP, CURLEV; static i64 POPC[64];   /* LEVPOP=1: count the elements of every pulled level */
static void pull_level(const u64 *C, u64 *T, u64 **tab) {
    #pragma omp parallel num_threads(NTH)
    {
        u64 *acc = ACC[omp_get_thread_num()], *rb = RB[omp_get_thread_num()];
        const u64 *src[MAXD]; i64 q[MAXD]; __m128i sh[MAXD], sh2[MAXD];
        i64 base = L >> 6; int r = L & 63; __m128i s1 = _mm_cvtsi32_si128(r), s2 = _mm_cvtsi32_si128(64 - r);
        #pragma omp for schedule(dynamic, 16)
        for (i64 w = 0; w < R; w++) {
            for (int j = 0; j < d; j++) { u64 e = tab[j][w]; src[j] = C + (i64)(e >> 32) * RW; u32 o = (u32)e; q[j] = o >> 6;
                sh[j] = _mm_cvtsi32_si128(o & 63); sh2[j] = _mm_cvtsi32_si128(64 - (o & 63)); }
            if (w + PFD < R) prefetch_row(C, tab, w + PFD);
            for (i64 h = 0; h < LW8; h += 8) {
                __m512i a = _mm512_setzero_si512();
                for (int j = 0; j < d; j++) a = _mm512_or_si512(a, win8(src[j], q[j] + h, sh[j], sh2[j]));
                _mm512_store_si512((void *)(acc + h), a);
            }
            acc[LW - 1] &= LASTMASK; for (i64 u = LW; u < LW8 + 8; u++) acc[u] = 0;
            if (LEVPOP) { i64 pc = 0; for (i64 u = 0; u < LW; u++) pc += __builtin_popcountll(acc[u]);
                #pragma omp atomic
                POPC[CURLEV] += pc; }
            memcpy(rb, acc, 8 * LW); memset(rb + LW, 0, 8 * (RW - LW));
            if (!r) memcpy(rb + base, acc, 8 * LW);
            else {   /* second copy at bit L: word base + u = acc[u] << r | acc[u-1] >> (64 - r) */
                rb[base] |= acc[0] << r;
                for (i64 u = 1; u <= LW; u += 8)
                    _mm512_storeu_si512((void *)(rb + base + u), _mm512_or_si512(_mm512_sll_epi64(_mm512_loadu_si512((const void *)(acc + u)), s1),
                                                                                 _mm512_srl_epi64(_mm512_loadu_si512((const void *)(acc + u - 1)), s2)));
            }
            u64 *dst = T + w * RW;
            for (i64 u = 0; u < RW; u += 8) _mm512_stream_si512((void *)(dst + u), _mm512_load_si512((const void *)(rb + u)));
        }
        _mm_sfence();
    }
}
/* last level: count B-side zeros of S . C; abort (return -1) once the count reaches *bound.  Uncovered elements go
 * to unc[0..ucap) (first ucap of them, *nunc = count stored). */
static i64 last_level(const u64 *C, u64 **tab, i64 bound, i64 *unc, int ucap, int *nunc) {
    volatile int abort_ = 0; i64 tot = 0; i64 nu = 0;   /* 64-bit: a candidate can leave > 2^31 elements uncovered */
    __m512i ones = _mm512_set1_epi64(-1);
    /* mask of the last chunk: words >= LW invalid, word LW-1 partial */
    u64 lm[8]; i64 hl = (LW - 1) / 8 * 8;
    for (int u = 0; u < 8; u++) { i64 wi = hl + u; lm[u] = wi < LW - 1 ? ~0ULL : wi == LW - 1 ? LASTMASK : 0; }
    __m512i lastm = _mm512_loadu_si512((const void *)lm);
    #pragma omp parallel num_threads(NTH)
    {
        #pragma omp for schedule(dynamic, 16)
        for (i64 w = 0; w < R; w++) {
            if (abort_) continue;
            const u64 *src[MAXD]; i64 q[MAXD]; __m128i sh[MAXD], sh2[MAXD];
            for (int j = 0; j < d; j++) { u64 e = tab[j][w]; src[j] = C + (i64)(e >> 32) * RW; u32 o = (u32)e; q[j] = o >> 6;
                sh[j] = _mm_cvtsi32_si128(o & 63); sh2[j] = _mm_cvtsi32_si128(64 - (o & 63)); }
            if (w + PFD < R) prefetch_row(C, tab, w + PFD);
            i64 zr = 0;
            for (i64 h = 0; h < LW8; h += 8) {
                __m512i m = h == hl ? lastm : ones, nm = _mm512_xor_si512(m, ones), acc = nm;
                for (int j = 0; j < d; j++) {
                    acc = _mm512_or_si512(acc, win8(src[j], q[j] + h, sh[j], sh2[j]));
                    if (_mm512_cmpneq_epi64_mask(acc, ones) == 0) break;
                }
                __m512i zz = _mm512_andnot_si512(acc, ones);
                if (_mm512_test_epi64_mask(zz, zz)) {
                    u64 zw[8]; _mm512_storeu_si512((void *)zw, zz);
                    for (int u = 0; u < 8; u++) { u64 x = zw[u];
                        while (x) { int b = __builtin_ctzll(x); x &= x - 1; zr++;
                            i64 k;
                            #pragma omp atomic capture
                            k = nu++;
                            if (k < ucap) unc[k] = w * L + (h + u) * 64 + b; } }
                }
            }
            if (zr) { i64 t;
                #pragma omp atomic capture
                t = tot += zr;
                if (t >= bound) abort_ = 1; }
        }
    }
    *nunc = nu < ucap ? (int)nu : ucap;
    return abort_ ? -1 : tot;
}
static const i64 NOBOUND = (i64)1 << 62;
static i64 LEV[64];
/* cost of the current tables (S[0] must be e) */
static int INVS = 0;   /* odd D: 1 = BFS of H(G, S^-1), whose A-side coverage is the B-side coverage of H(G, S) */
static i64 cost1(i64 bound, i64 *unc, int ucap, int *nunc) {
    double t0 = now();
    memset(BUF[0], 0, (size_t)(R * RW * 8));
    i64 n = 0; i64 e = eidx(E_ID); LIST[n++] = e; setbit2(BUF[0], e / L, e % L);
    int cur = 0, listmode = 1;
    if (BENCH) TLEV[0] = now() - t0;
    for (int lev = 1; lev <= D - 1; lev++) {
        double tl = now();
        int sideS = (lev & 1) ^ INVS; /* odd levels: S (A -> B), even: S^-1; swapped for H(G, S^-1) */
        if (lev == D - 1) {
            i64 c = last_level(BUF[cur], sideS ? PS : PI, bound, unc, ucap, nunc);   /* odd D: last level is S^-1 (A side) */
            if (BENCH) { TLEV[lev] = now() - tl; }
            return c;
        }
        if (listmode && n * (i64)d <= PUSHMAX && n * (i64)d * d > PUSHMAX && lev + 1 < D - 1) {
            /* last push level (the next one is a pull): no list, no test; targets of a batch are prefetched while the
             * previous batch is written */
            u64 *B = BUF[cur]; enum { BT = 16 };
            #pragma omp parallel num_threads(NTH)
            {
                u64 *addr[2][2 * BT * MAXD]; u64 bitv[2][2 * BT * MAXD];
                int nth = omp_get_num_threads(), me = omp_get_thread_num();
                i64 lo = n * me / nth, hi = n * (me + 1) / nth;
                int nb = 0, cb = 0;
                for (i64 x0 = lo; x0 <= hi; x0 += BT) {
                    int na = 0; u64 **ad = addr[cb]; u64 *bv = bitv[cb];
                    for (i64 x = x0; x < x0 + BT && x < hi; x++) {
                        i64 g = LIST[x], r = g / L, i = g % L;
                        for (int j = 1; j < d; j++) {
                            i64 r2, i2;
                            if (sideS) { r2 = FR[j][r]; i2 = i + FC[j][r]; if (i2 >= L) i2 -= L; }
                            else { u64 pe = PS[j][r]; r2 = (i64)(pe >> 32); i64 c = L - (i64)(u32)pe; i2 = i - c; if (i2 < 0) i2 += L; }
                            u64 *row = B + r2 * RW; i64 i3 = i2 + L;
                            ad[na] = row + (i2 >> 6); bv[na++] = 1ULL << (i2 & 63); _mm_prefetch((const char *)(row + (i2 >> 6)), _MM_HINT_T0);
                            ad[na] = row + (i3 >> 6); bv[na++] = 1ULL << (i3 & 63); _mm_prefetch((const char *)(row + (i3 >> 6)), _MM_HINT_T0);
                        }
                    }
                    { u64 **pa = addr[cb ^ 1]; u64 *pb = bitv[cb ^ 1];
                      if (nth > 1) for (int u = 0; u < nb; u++) __atomic_fetch_or(pa[u], pb[u], __ATOMIC_RELAXED);
                      else for (int u = 0; u < nb; u++) *pa[u] |= pb[u]; }
                    nb = na; cb ^= 1;
                }
                { u64 **pa = addr[cb ^ 1]; u64 *pb = bitv[cb ^ 1];
                  if (nth > 1) for (int u = 0; u < nb; u++) __atomic_fetch_or(pa[u], pb[u], __ATOMIC_RELAXED);
                  else for (int u = 0; u < nb; u++) *pa[u] |= pb[u]; }
            }
            listmode = 0; LEV[lev] = -2;
        } else if (listmode && n * (i64)d <= PUSHMAX && n * (i64)d <= LISTCAP) {
            i64 m = n; u64 *B = BUF[cur];
            for (i64 x = 0; x < m; x++) {
                i64 g = LIST[x], r = g / L, i = g % L;
                for (int j = 1; j < d; j++) {
                    i64 r2, i2;
                    if (sideS) { r2 = FR[j][r]; i2 = i + FC[j][r]; if (i2 >= L) i2 -= L; }
                    else { u64 pe = PS[j][r]; r2 = (i64)(pe >> 32); i64 c = L - (i64)(u32)pe; i2 = i - c; if (i2 < 0) i2 += L; }
                    if (!getbit(B, r2, i2)) { setbit2(B, r2, i2); LIST[n++] = r2 * L + i2; }
                }
            }
            LEV[lev] = n;
        } else {
            listmode = 0;
            CURLEV = lev; POPC[lev] = 0;
            pull_level(BUF[cur], BUF[cur ^ 1], sideS ? PS : PI);
            cur ^= 1; LEV[lev] = -1;
        }
        if (BENCH) TLEV[lev] = now() - tl;
    }
    return -2;   /* not reached for D >= 2 */
}

/* For even D, cost1 from (e,A) decides the diameter (odd words from B are the inverses of odd words from A).  For odd D
 * the same-side sets differ: from (e,A) they are (S^-1 S)^k, from (e,B) (S S^-1)^k = the A-side words of H(G, S^-1).
 * So for odd D, cost = holes of H(G,S) + holes of H(G,S^-1) (both from (e,A)); holes of the second kind are stored
 * with bit 62 set.  (new-cells-beyond, 2026-10-26) */
#define BHOLE ((i64)1 << 62)
/* ---------------- orbit structure ---------------- */
static int OK_ = 3, OM, OF = 1;
static el AG, AGI; static i64 AR = 0;
static inline el alpha(el x) { el y = emul(emul(AG, x), AGI); y.z = NC > 1 ? (i64)((__int128)AR * x.z % NC) : 0; return y; }
static el randel(void) { return eofidx((i64)(rnd() % (u64)NG)); }
static int orbit_of(el x, el *o) {
    o[0] = x; for (int i = 1; i < OK_; i++) { o[i] = alpha(o[i - 1]); if (eeq(o[i], x)) return 0; }
    return eeq(alpha(o[OK_ - 1]), x);
}
static inline int ostart(int j) { return OF + j * OK_; }
static int orbit_free(const el *o, int j) {
    for (int i = 0; i < OK_; i++) for (int u = 0; u < d; u++) {
        if (j >= 0 && u >= ostart(j) && u < ostart(j) + OK_) continue;
        if (eeq(S[u], o[i])) return 0;
    }
    return 1;
}
static int random_orbit(int j, el *o) {
    for (int t = 0; t < 100000; t++) { el x = randel(); if (orbit_of(x, o) && orbit_free(o, j)) return 1; }
    return 0;
}
static i64 ipow_mod(i64 b, i64 e, i64 m) { i64 r = 1 % m; b %= m; while (e) { if (e & 1) r = (i64)((__int128)r * b % m); b = (i64)((__int128)b * b % m); e >>= 1; } return r; }
static i64 gcdl(i64 a, i64 b) { while (b) { i64 t = a % b; a = b; b = t; } return a < 0 ? -a : a; }
static void choose_alpha(void) {   /* g = [[0,-1],[1,t]] with g^k = +-I (projective order k; k = 3: t = -1 first) */
    int tsel = -1;
    for (int tt = 0; tt < P && tsel < 0; tt++) {
        int t = (tt == 0) ? P - 1 : tt - 1; if (tt > 0 && t == P - 1) continue;
        el g = (el){0, P - 1, 1, t, 0}, y = E_ID; int ispm = 0;
        for (int i = 0; i < OK_; i++) y = emul(y, g);       /* emul canonicalises for PSL; compare up to sign */
        if ((y.a == 1 && y.d == 1 && !y.b && !y.c) || (y.a == P - 1 && y.d == P - 1 && !y.b && !y.c)) ispm = 1;
        if (ispm) tsel = t;
    }
    if (getenv("AT")) tsel = atoi(getenv("AT"));
    if (tsel < 0) { fprintf(stderr, "no element of projective order %d in SL(2,%d)\n", OK_, P); exit(2); }
    AG = (el){0, P - 1, 1, tsel, 0}; AG = canon(AG); AGI = einv(AG);
    if (NC > 1) { i64 best = -1, bfix = (i64)1 << 60;
        for (i64 r = 2; r < NC; r++) { if (gcdl(r, NC) != 1 || ipow_mod(r, OK_, NC) != 1) continue;
            i64 fx = gcdl(r - 1, NC); if (fx < bfix) { bfix = fx; best = r; } }
        AR = best < 0 ? 1 : best;
        if (getenv("AR")) AR = atoll(getenv("AR"));
    }
}

/* ---------------- targeted moves ---------------- */
static i64 *UNC; static int NUNC;  /* uncovered list of the current S */
static u64 AVOID;                  /* generator slots the walks must not use */
static int WINV = 0;   /* walks in H(G, S^-1) (targeting a hole of the second kind, odd D) */
static el walk(el g, int *side, int len) {
    for (int s = 0; s < len; s++) {
        int j; do j = (int)(rnd() % d); while ((AVOID >> j) & 1);
        g = (*side == 0) != WINV ? emul(TT[j], g) : emul(einv(TT[j]), g);
        *side ^= 1;
    }
    return g;
}
static int targeted(el *x) {
    if (NUNC == 0) return 0;
    i64 hidx = UNC[rnd() % NUNC]; WINV = (hidx & BHOLE) != 0;
    el u = eofidx(hidx & ~BHOLE);
    for (int tries = 0; tries < 20; tries++) {
        int a = (int)(rnd() % (D - 1)), b = (int)(rnd() % (D - 1 - a));
        int sp = 0, sq = (D % 2 == 0);   /* uncovered elements are on side B for even D, side A for odd D */
        el Pp = walk(E_ID, &sp, a), Qv = walk(u, &sq, b);
        if (sp == sq) continue;
        el gA = sp == 0 ? Pp : Qv, hB = sp == 0 ? Qv : Pp;
        *x = emul(hB, einv(gA)); if (WINV) *x = einv(*x);
        if (OF0) *x = emul(*x, S[0]);   /* back from T = S s_0^-1 to S */
        WINV = 0; return 1;
    }
    WINV = 0; return 0;
}

/* ---------------- SD (c12): self-dual symmetric S for odd D ----------------
 * tau(M,z) = (M^T, z) is an anti-automorphism of G.  alpha = conjugation by g with g^T g = s I (s = +-1, so
 * alpha tau = tau alpha) times z -> r z.  If tau(S) = S then gamma(x) = tau(x)^-1 is an automorphism with
 * gamma(S) = S^-1, so H(G,S^-1) = H(G,S) (same sides, (e,A) fixed) and the odd-D cost is 2 x the one-sided cost.
 * S = {e} + H-orbits, H = <alpha, tau>; slot k is one H-orbit of size SDSIZES[k] (1, 2, 3 or 6). */
static int NSLOT;                       /* slot 0 = {e} (position 0), slots 1.. = H-orbits */
static int SLOTPOS[MAXD], SLOTSZ[MAXD];
static i64 NLIST[4]; static el *SZLIST[4];   /* all elements whose H-orbit has size 1, 2, 3 */
#define LCAP (1 << 21)
static inline el tau(el x) { el t = {x.a, x.c, x.b, x.d, x.z}; return canon(t); }
static int horbit(el x, el *o) {   /* H-orbit of x (size <= 6, 7 if the orbit is larger) */
    int n = 1; o[0] = x;
    for (int i = 0; i < n; i++) {
        el c[2] = {alpha(o[i]), tau(o[i])};
        for (int k = 0; k < 2; k++) { int f = 0;
            for (int u = 0; u < n && !f; u++) f = eeq(o[u], c[k]);
            if (!f) { if (n == 6) return 7; o[n++] = c[k]; } }
    }
    return n;
}
static int hfree(const el *o, int sz, int k) {   /* the H-orbit o (size sz) avoids every generator outside slot k */
    for (int i = 0; i < sz; i++) for (int u = 0; u < d; u++) {
        if (u >= SLOTPOS[k] && u < SLOTPOS[k] + SLOTSZ[k]) continue;
        if (eeq(S[u], o[i])) return 0;
    }
    return 1;
}
static void build_lists(void) {
    for (int s = 1; s <= 3; s++) { NLIST[s] = 0; SZLIST[s] = NULL; }
    for (int s = 1; s <= 3; s++) for (int k = 1; k < NSLOT; k++) if (SLOTSZ[k] == s && !SZLIST[s]) SZLIST[s] = malloc(sizeof(el) * LCAP);
    el o[8];
    for (i64 g = 0; g < NG; g++) {
        el x = canon(eofidx(g)); if (eeq(x, E_ID)) continue;
        int n = horbit(x, o);
        if (n <= 3 && SZLIST[n] && NLIST[n] < LCAP) SZLIST[n][NLIST[n]++] = x;
    }
}
static int random_hslot(int k, el *o) {   /* random H-orbit of the slot's size, avoiding the other generators */
    int sz = SLOTSZ[k];
    for (int t = 0; t < 4000000; t++) {
        el x;
        if (sz == 6) x = randel();
        else { if (!NLIST[sz]) return 0; x = SZLIST[sz][rnd() % (u64)NLIST[sz]]; }
        if (horbit(x, o) == sz && hfree(o, sz, k)) return 1;
    }
    return 0;
}
static void choose_alpha_sd(void) {   /* g in SL(2,p) of trace +-1 with g^T g = +-I (so tau alpha = alpha tau) */
    int *rt = malloc(sizeof(int) * P);
    for (int i = 0; i < P; i++) rt[i] = -1;
    for (int x = 0; x < P; x++) rt[(i64)x * x % P] = x;
    el *LA = malloc(sizeof(el) * 4 * P + 8), *LB = malloc(sizeof(el) * 4 * P + 8);
    for (int si = 0; si < 2; si++) {
        int s = si ? P - 1 : 1, na = 0, nb = 0;
        for (int a = 0; a < P; a++) { int t = md((i64)s - (i64)a * a); if (rt[t] < 0) continue;
            LA[na++] = (el){a, 0, rt[t], 0, 0}; if (rt[t]) LA[na++] = (el){a, 0, P - rt[t], 0, 0}; }
        for (int b = 0; b < P; b++) { int t = md((i64)s - (i64)b * b); if (rt[t] < 0) continue;
            LB[nb++] = (el){0, b, 0, rt[t], 0}; if (rt[t]) LB[nb++] = (el){0, b, 0, P - rt[t], 0}; }
        for (int i = 0; i < na; i++) for (int j = 0; j < nb; j++) {
            int a = LA[i].a, c = LA[i].c, b = LB[j].b, dd = LB[j].d;
            if (md((i64)a * b + (i64)c * dd) != 0) continue;
            if (md((i64)a * dd - (i64)b * c) != 1) continue;
            int tr = (a + dd) % P;
            if (tr != 1 && tr != P - 1) continue;
            AG = canon((el){a, b, c, dd, 0}); AGI = einv(AG);
            fprintf(stderr, "alpha: g=(%d,%d,%d,%d) trace %d, g^T g = %s I\n", a, b, c, dd, tr, si ? "-" : "+");
            free(rt); free(LA); free(LB); return;
        }
    }
    fprintf(stderr, "no orthogonal-type g of trace +-1 in SL(2,%d)\n", P); exit(2);
}
/* cost of the current S (odd D): the one-sided count, doubled.  bound is in doubled units. */
static i64 cost_sd(i64 bound, i64 *unc, int ucap, int *nunc) {
    INVS = 0;
    i64 b1 = bound == NOBOUND ? NOBOUND : (bound + 1) / 2;
    i64 c = cost1(b1, unc, ucap, nunc);
    return c < 0 ? -1 : 2 * c;
}
static void retab_slot(int k) { for (int i = 0; i < SLOTSZ[k]; i++) make_tables(SLOTPOS[k] + i); }
static void retab(int j) { retab_slot(j); }

/* ---------------- I/O ---------------- */
static char SPEC[64];
static void write_sol1(const char *out, el *SS) {
    FILE *f = fopen(out, "w"); if (!f) { perror(out); return; }
    fprintf(f, "%d %d %s n %lld N %lld\n", d, D, SPEC, (long long)NC, (long long)NG);
    for (int i = 0; i < d; i++) { char b[200]; edesc(SS[i], b); fprintf(f, "%s\n", b); }
    fclose(f);
}
static void write_sol(const char *out, el *SS) {
    if (!OF0) { write_sol1(out, SS); return; }
    el T[MAXD], a0 = einv(SS[0]); for (int i = 0; i < d; i++) T[i] = i ? emul(SS[i], a0) : E_ID;
    write_sol1(out, T); char b[1100]; snprintf(b, sizeof b, "%s.orb", out); write_sol1(b, SS);
}
static void retab(int j);
static int read_sol(const char *fn, el *SS) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); return 0; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 0;
    int k = 0;
    while (fgets(line, sizeof line, f) && k < d) {
        char *m = strstr(line, "mat("), *zz = strstr(line, "z="); if (!m || !zz) continue;
        el x; long long z; if (sscanf(m, "mat(%d,%d,%d,%d)", &x.a, &x.b, &x.c, &x.d) != 4 || sscanf(zz, "z=%lld", &z) != 1) return 0;
        x.z = z % NC; x.a = md(x.a); x.b = md(x.b); x.c = md(x.c); x.d = md(x.d);
        if (md((i64)x.a * x.d - (i64)x.b * x.c) != 1) { fprintf(stderr, "det != 1: %s", line); return 0; }
        SS[k++] = canon(x);
    }
    fclose(f);
    return k == d;
}
static volatile int stop_flag = 0;
static void on_term(int s) { (void)s; stop_flag = 1; }
static int cmpll(const void *a, const void *b) { i64 x = *(const i64 *)a, y = *(const i64 *)b; return (x > y) - (x < y); }

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: haar_sd d D seconds seed K outfile sl|psl p n   (env SD=1 SDSIZES=\"6 6\")\n"); return 2; }
    d = atoi(argv[1]); D = atoi(argv[2]); double secs = atof(argv[3]); u64 seed = strtoull(argv[4], 0, 10);
    int K = atoi(argv[5]); const char *out = argv[6];
    PSL = !strcmp(argv[7], "psl"); if (!PSL && strcmp(argv[7], "sl")) { fprintf(stderr, "family sl or psl\n"); return 2; }
    P = atoi(argv[8]); NC = atoll(argv[9]);
    if (D < 3 || d < 2 || d > MAXD || K < 1 || K > 64) { fprintf(stderr, "need D >= 3, 2 <= d <= %d, 1 <= K <= 64\n", MAXD); return 2; }
    if (D % 2 == 0) { fprintf(stderr, "SD mode is for odd D\n"); return 2; }
    for (int t = 2; t * t <= P; t++) if (P % t == 0) { fprintf(stderr, "p must be prime\n"); return 2; }
    if (P < 5) { fprintf(stderr, "p >= 5\n"); return 2; }
    if (gcdl(P, NC) != 1) { fprintf(stderr, "gcd(p, n) must be 1\n"); return 2; }
    HALF = (P - 1) / 2;
    sprintf(SPEC, "%s %d", PSL ? "psl" : "sl", P);
    rs ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd();
    INV = malloc(sizeof(int) * P); INV[0] = 0;
    for (int x = 1; x < P; x++) INV[x] = (int)ipow_mod(x, P - 2, P);
    L = (i64)P * NC; R = PSL ? ((i64)P * P - 1) / 2 : (i64)P * P - 1; NG = R * L;
    LW = (L + 63) / 64; LW8 = (LW + 7) / 8 * 8; RW = (2 * LW + 17 + 7) / 8 * 8;
    LASTMASK = (L & 63) ? (1ULL << (L & 63)) - 1 : ~0ULL;
    CP = (i64)((__int128)NC * ipow_mod(NC % P, P - 2, P) % L);
    CN = 0;
    if (NC > 1) {
        i64 t = 0, nt = 1, r = NC, nr = P % NC;
        while (nr) { i64 qq = r / nr, x = t - qq * nt; t = nt; nt = x; x = r - qq * nr; r = nr; nr = x; }
        if (t < 0) t += NC; CN = (i64)((__int128)P * t % L);
    }
    if (crt(1, 0) % P != 1 || (NC > 1 && crt(1, 0) % NC != 0) || crt(0, 1) % P != 0 || (NC > 1 && crt(0, 1) % NC != 1)) { fprintf(stderr, "CRT setup failed\n"); return 2; }
    E_ID = (el){1, 0, 0, 1, 0};
    for (int t = 0; t < 200000; t++) { i64 g = (i64)(rnd() % (u64)NG); el x = eofidx(g);
        if (md((i64)x.a * x.d - (i64)x.b * x.c) != 1 || eidx(x) != g || !eeq(canon(x), x)) { fprintf(stderr, "index self-test failed at %lld\n", (long long)g); return 2; } }
    NTH = getenv("THREADS") ? atoi(getenv("THREADS")) : 1; if (NTH < 1) NTH = 1;
    PUSHMAX = (i64)1 << 24; if (NG * (i64)d / 512 < PUSHMAX) PUSHMAX = NG * (i64)d / 512;
    if (getenv("PUSHMAX")) PUSHMAX = atoll(getenv("PUSHMAX"));
    if (getenv("UCAP")) UCAP = atoi(getenv("UCAP"));
    BENCH = getenv("BENCH") ? atoi(getenv("BENCH")) : 0; LEVPOP = 0;
    for (int b = 0; b < 2; b++) { BUF[b] = aligned_alloc(64, (size_t)(R * RW * 8)); if (!BUF[b]) { fprintf(stderr, "out of memory\n"); return 2; } }
    LISTCAP = PUSHMAX + 64; LIST = malloc(sizeof(i64) * LISTCAP);
    ACC = malloc(sizeof(u64 *) * NTH); RB = malloc(sizeof(u64 *) * NTH);
    for (int t = 0; t < NTH; t++) { ACC[t] = aligned_alloc(64, 8 * (LW8 + 16)); RB[t] = aligned_alloc(64, 8 * (RW + 16)); }
    for (int j = 0; j < d; j++) { FR[j] = malloc(4 * R); FC[j] = malloc(4 * R); PS[j] = malloc(8 * R); PI[j] = malloc(8 * R); }
    fprintf(stderr, "group %s x Z_%lld, N=%lld (2N=%lld), memory %.2f GB\n", SPEC, (long long)NC, (long long)NG, (long long)(2 * NG),
            2.0 * R * RW * 8 / 1e9 + (double)LISTCAP * 8 / 1e9 + 24.0 * d * R / 1e9);
    signal(SIGTERM, on_term); signal(SIGINT, on_term);
    i64 *ULIST[64]; int UN[64];
    for (int t = 0; t < K; t++) ULIST[t] = malloc(sizeof(i64) * UCAP);
    UNC = malloc(sizeof(i64) * UCAP);
    double W = 1; for (int i = 1; i <= (D - 1) / 2; i++) W += d * pow(d - 1, 2 * i - 1);   /* even words <= D-1 */
    double mu = NG * exp(-W / NG);
    choose_alpha_sd();
    if (NC > 1) { i64 best = -1, bfix = (i64)1 << 60;
        for (i64 r = 2; r < NC; r++) { if (gcdl(r, NC) != 1 || ipow_mod(r, 3, NC) != 1) continue;
            i64 fx = gcdl(r - 1, NC); if (fx < bfix) { bfix = fx; best = r; } }
        AR = best < 0 ? 1 : best; }
    for (int t = 0; t < 1000; t++) { el x = randel(), y = randel();
        if (!eeq(tau(alpha(x)), alpha(tau(x))) || !eeq(alpha(alpha(alpha(x))), x) || !eeq(tau(tau(x)), x) || !eeq(alpha(emul(x, y)), emul(alpha(x), alpha(y)))) {
            fprintf(stderr, "alpha/tau self-test failed\n"); return 2; } }
    NSLOT = 1; SLOTPOS[0] = 0; SLOTSZ[0] = 1;
    if (getenv("SDSIZES")) { char buf[256]; snprintf(buf, sizeof buf, "%s", getenv("SDSIZES")); int pos = 1;
        for (char *tok = strtok(buf, " ,"); tok; tok = strtok(NULL, " ,")) { int s = atoi(tok);
            if (s != 1 && s != 2 && s != 3 && s != 6) { fprintf(stderr, "slot size must be 1,2,3 or 6\n"); return 2; }
            if (NSLOT >= MAXD) return 2; SLOTPOS[NSLOT] = pos; SLOTSZ[NSLOT] = s; pos += s; NSLOT++; }
        if (pos != d) { fprintf(stderr, "SDSIZES must sum to d-1 = %d\n", d - 1); return 2; } }
    else if (!getenv("EVAL")) { fprintf(stderr, "SDSIZES=\"s1 s2 ...\" needed (sizes 1,2,3,6 summing to d-1)\n"); return 2; }
    S[0] = E_ID;
    for (int u = 1; u < d; u++) S[u] = (el){0, 0, 0, 0, -1};
    { int need_lists = 0; for (int k = 1; k < NSLOT; k++) if (SLOTSZ[k] != 6) need_lists = 1;
      if (need_lists) { double tl = now(); build_lists(); fprintf(stderr, "lists: %lld/%lld/%lld elements with H-orbit size 1/2/3 (%.1fs)\n",
          (long long)NLIST[1], (long long)NLIST[2], (long long)NLIST[3], now() - tl); } }
    fprintf(stderr, "alpha: order 3, tau-commuting; z -> %lld z on Z_%lld; slots %d; W=%.6g mu=%.2f\n",
            (long long)AR, (long long)NC, NSLOT - 1, W, mu);
    if (getenv("EVAL")) {
        if (!read_sol(getenv("EVAL"), S)) { fprintf(stderr, "cannot read %s\n", getenv("EVAL")); return 2; }
        if (!eeq(S[0], E_ID)) { el a0 = einv(S[0]); for (int i = 0; i < d; i++) S[i] = emul(S[i], a0); }
        int selfdual = 1;
        for (int i = 0; i < d; i++) { el t = tau(S[i]); int f = 0; for (int u = 0; u < d; u++) f |= eeq(S[u], t); selfdual &= f; }
        for (int j = 0; j < d; j++) make_tables(j);
        int nu; double t0 = now(); i64 c1 = cost1(NOBOUND, ULIST[0], UCAP, &nu);
        printf("EVAL %s selfdual=%d onesided=%lld sd_cost=%lld time=%.3f mu=%.2f\n", getenv("EVAL"), selfdual, (long long)c1, (long long)(2 * c1), now() - t0, mu);
        return c1 == 0 ? 0 : 1;
    }
    if (getenv("START")) {
        if (!read_sol(getenv("START"), S)) { fprintf(stderr, "cannot read START\n"); return 2; }
        for (int k = 1; k < NSLOT; k++) { el o[8]; int n = horbit(S[SLOTPOS[k]], o);
            if (n != SLOTSZ[k]) { fprintf(stderr, "START: slot %d has H-orbit size %d, want %d\n", k, n, SLOTSZ[k]); return 2; }
            for (int i = 0; i < SLOTSZ[k]; i++) { int f = 0; for (int u = 0; u < n; u++) f |= eeq(o[u], S[SLOTPOS[k] + i]); if (!f) { fprintf(stderr, "START: slot %d not an H-orbit\n", k); return 2; } } }
    } else for (int k = 1; k < NSLOT; k++) { el o[8]; if (!random_hslot(k, o)) { fprintf(stderr, "no H-orbit for slot %d\n", k); return 2; }
        for (int i = 0; i < SLOTSZ[k]; i++) S[SLOTPOS[k] + i] = o[i]; }
    for (int j = 0; j < d; j++) make_tables(j);
    int TARGP = getenv("TARGP") ? atoi(getenv("TARGP")) : 70;
    double TMAX = getenv("TMAX") ? atof(getenv("TMAX")) : 1.5, TMIN = getenv("TMIN") ? atof(getenv("TMIN")) : 0.15;
    double COOLSTEPS = getenv("COOLSTEPS") ? atof(getenv("COOLSTEPS")) : 4;
    i64 REHEATSTEPS = getenv("REHEATSTEPS") ? atoll(getenv("REHEATSTEPS")) : 60;
    double t0 = now();
    i64 c = cost_sd(NOBOUND, UNC, UCAP, &NUNC), best = c; el bestS[MAXD]; memcpy(bestS, S, sizeof(el) * d);
    i64 evals = 1, steps = 0, lastimp = 0, heat = 0;
    double T = TMAX, cE = (double)c / 2.0;
    fprintf(stderr, "start sd_cost=%lld (%.2fs)\n", (long long)c, now() - t0);
    char bestfile[1024]; snprintf(bestfile, sizeof bestfile, "%s.best", out);
    el cand[64][6];
    while (!stop_flag && now() - t0 < secs && best > 0) {
        int k = 1 + (int)(rnd() % (u64)(NSLOT - 1)); int sz = SLOTSZ[k], pos = SLOTPOS[k];
        AVOID = 0; for (int i = 0; i < sz; i++) AVOID |= 1ULL << (pos + i);
        int bad = 0;
        for (int t = 0; t < K; t++) {
            el x, o[8]; int ok = 0;
            if ((int)(rnd() % 100) < TARGP && targeted(&x)) ok = !eeq(x, E_ID) && horbit(x, o) == sz && hfree(o, sz, k);
            if (!ok) ok = random_hslot(k, o);
            if (!ok) { bad = 1; break; }
            memcpy(cand[t], o, sizeof(el) * sz);
        }
        AVOID = 0;
        if (bad) { steps++; continue; }
        el keep[6]; memcpy(keep, S + pos, sizeof(el) * sz);
        i64 bound = NOBOUND, cs[64]; int bt = -1;
        for (int t = 0; t < K && !stop_flag; t++) {
            for (int i = 0; i < sz; i++) S[pos + i] = cand[t][i];
            retab_slot(k);
            i64 r = cost_sd(bound, ULIST[t], UCAP, &UN[t]); evals++;
            cs[t] = r < 0 ? NOBOUND : r;
            if (r >= 0 && r < bound) { bound = r; bt = t; }
        }
        if (bt < 0) { for (int i = 0; i < sz; i++) S[pos + i] = keep[i]; retab_slot(k); steps++; continue; }
        double bE = (double)cs[bt] / 2.0;
        int acc = bE <= cE || exp((cE - bE) / T) > (double)(rnd() % 1000000) / 1e6;
        if (acc) { for (int i = 0; i < sz; i++) S[pos + i] = cand[bt][i]; retab_slot(k);
            c = cs[bt]; cE = bE; memcpy(UNC, ULIST[bt], sizeof(i64) * UN[bt]); NUNC = UN[bt]; }
        else { for (int i = 0; i < sz; i++) S[pos + i] = keep[i]; retab_slot(k); }
        steps++;
        if (c < best) { best = c; memcpy(bestS, S, sizeof(el) * d); lastimp = steps; write_sol(bestfile, bestS); }
        T = TMAX * pow(0.5, (steps - heat) / COOLSTEPS); if (T < TMIN) T = TMIN;
        if (steps - lastimp > REHEATSTEPS) {
            heat = steps; T = TMAX; memcpy(S, bestS, sizeof(el) * d); for (int u = 0; u < d; u++) make_tables(u);
            c = cost_sd(NOBOUND, UNC, UCAP, &NUNC); evals++; cE = (double)c / 2.0; lastimp = steps;
            fprintf(stderr, "reheat at step %lld: back to best S, cost %lld\n", (long long)steps, (long long)c);
        }
        if (steps % 200 == 0) fprintf(stderr, "t=%.0f step=%lld evals=%lld slot=%d cur=%lld best=%lld T=%.2f\n", now() - t0,
            (long long)steps, (long long)evals, k, (long long)c, (long long)best, T);
    }
    printf("RESULT SD d=%d D=%d group=%s x Z_%lld N=%lld vertices=%lld best=%lld evals=%lld steps=%lld time=%.1f slots=%d mu=%.2f\n",
           d, D, SPEC, (long long)NC, (long long)NG, (long long)(2 * NG), (long long)best, (long long)evals, (long long)steps, now() - t0, NSLOT - 1, mu);
    if (best == 0) {
        memcpy(S, bestS, sizeof(el) * d); for (int u = 0; u < d; u++) make_tables(u);
        int nu; i64 c2 = cost_sd(NOBOUND, UNC, UCAP, &nu);
        printf("re-evaluation of the best S: sd_cost %lld\n", (long long)c2);
        if (c2 == 0) { write_sol(out, bestS); printf("wrote %s\n", out); }
        return c2 == 0 ? 0 : 1;
    }
    return 1;
}
