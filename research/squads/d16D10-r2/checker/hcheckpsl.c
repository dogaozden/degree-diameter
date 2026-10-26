/* hcheckpsl.c -- independent diameter checker for Haar graphs H(G,S), G = PSL(2,p) x Z_n.
 * Written from the definitions on the card only.
 *
 * build : gcc -O3 -fopenmp -Wall -o hcheckpsl hcheckpsl.c
 * usage : THREADS=k ./hcheckpsl FILE   prints VALID/INVALID and an ecc line; exit 0 iff VALID
 *         ./hcheckpsl --selftest       index, reduction and BFS self-tests; exit 0 iff all pass
 *
 * Group: elements (M,z), M in PSL(2,p) = SL(2,p)/{+-I}, z in Z_n.  P = p(p^2-1)/2,  N = n P.
 * psl_index(M) in [0,P): the canonical M has a in [1,H] (H=(p-1)/2), or a = 0 and c in [1,H].
 *   a != 0 :  (a-1) p^2 + c p + b          (d follows from ad-bc = 1)
 *   a == 0 :  H p^2 + (c-1) p + d          (b = -1/c)
 * Element index = psl_index(M) * n + z.
 *
 * Vertices (g,A), (g,B). Edges (g,A) ~ (s g,B) for s in S, i.e. (h,B) ~ (s^-1 h,A), with
 *   s g = (M_s M, z_s + z),   s^-1 = (adj M_s, -z_s),   adj[[a,b],[c,d]] = [[d,-b],[-c,a]].
 * Right multiplication is an automorphism, so the diameter is max(ecc(e,A), ecc(e,B)).
 *
 * Storage: the field of vertex (pidx, X, z) is (2 pidx + X) n + z, two bits:
 *   0 = unseen, 1 + (level mod 3) otherwise.  4 bits per group element.
 *   The 2n fields of one PSL element are contiguous: one matrix product per (block, generator).
 * BFS step t: side X = source side XOR (t mod 2) is scanned for fields equal to 1 + (t mod 3) and
 *   each such vertex pushes to the other side with label 1 + ((t+1) mod 3).  The scan also meets
 *   older vertices with the same label (levels t-6, t-12, ...).  Their neighbours have level <= t-5,
 *   are already labelled and set nothing, so they cost time only.
 *   A new label is set by a plain test of the field followed by an atomic OR (no label is overwritten).
 */
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>

typedef uint64_t u64;
typedef uint32_t u32;
typedef unsigned __int128 u128;

#define MAXGEN 256

static u64 P_, H_, PP_, MU_;        /* p, (p-1)/2, p^2, floor((2^64-1)/p) */
static u64 NPSL_, NZ_, NF_, NW_;    /* P = |PSL(2,p)|, n, fields = 2N, 64-bit words */
static int NGEN_;
static u32 *INV_;                   /* INV_[x] = x^-1 mod p */
static u64 G_[2][MAXGEN][4];        /* [0]: M_s ;  [1]: adj(M_s) */
static u64 GZ_[2][MAXGEN];          /* [0]: z_s ;  [1]: -z_s mod n */
static u64 *W_;                     /* 2-bit fields */

/* x mod p for any 64-bit x (Barrett with two correction steps) */
static inline u64 bred(u64 x) {
    u64 q = (u64)(((u128)x * MU_) >> 64);
    u64 r = x - q * P_;
    if (r >= P_) r -= P_;
    if (r >= P_) r -= P_;
    return r;
}

static void set_modulus(u64 p) {
    P_ = p;
    H_ = (p - 1) / 2;
    PP_ = p * p;
    MU_ = (~0ULL) / p;
}

static void build_inverses(void) {
    free(INV_);
    INV_ = calloc(P_, sizeof(u32));
    INV_[1] = 1;
    for (u64 x = 2; x < P_; x++) INV_[x] = (u32)((P_ - (P_ / x) * INV_[P_ % x] % P_) % P_);
}

/* canonical PSL index of det-1 matrix [[a,b],[c,d]] with entries in [0,p) */
static inline u64 psl_index(u64 a, u64 b, u64 c, u64 d) {
    if (a) {
        if (a > H_) { a = P_ - a; b = b ? P_ - b : 0; c = c ? P_ - c : 0; d = d ? P_ - d : 0; }
        return (a - 1) * PP_ + c * P_ + b;
    }
    if (c > H_) { c = P_ - c; d = d ? P_ - d : 0; }
    return H_ * PP_ + (c - 1) * P_ + d;
}

/* inverse of psl_index: canonical matrix of index idx */
static inline void psl_decode(u64 idx, u64 m[4]) {
    if (idx < H_ * PP_) {
        u64 a = idx / PP_ + 1, r = idx - (a - 1) * PP_;
        u64 c = r / P_, b = r - c * P_;
        m[0] = a; m[1] = b; m[2] = c;
        m[3] = bred(bred(1 + b * c) * INV_[a]);
    } else {
        u64 j = idx - H_ * PP_;
        u64 c = j / P_ + 1, d = j - (c - 1) * P_;
        m[0] = 0; m[1] = P_ - INV_[c]; m[2] = c; m[3] = d;
    }
}

static inline u64 lowmask(unsigned k) { return k >= 32 ? ~0ULL : ((1ULL << (2 * k)) - 1); }

/* fields in [lo,hi) with value v: out[k] = field - lo; returns the count */
static unsigned scan_hits(u64 lo, u64 hi, unsigned v, u32 *out) {
    const u64 L = 0x5555555555555555ULL;
    unsigned cnt = 0;
    u64 f = lo;
    while (f < hi) {
        u64 wi = f >> 5, ws = wi << 5;
        u64 seg = hi < ws + 32 ? hi : ws + 32;
        unsigned j0 = (unsigned)(f - ws), j1 = (unsigned)(seg - ws);
        u64 w = __atomic_load_n(&W_[wi], __ATOMIC_RELAXED);
        u64 b0 = w & L, b1 = (w >> 1) & L;
        u64 m = ((v & 1) ? b0 : (~b0 & L)) & ((v & 2) ? b1 : (~b1 & L));
        m &= lowmask(j1) & ~lowmask(j0);
        while (m) {
            unsigned pos = (unsigned)__builtin_ctzll(m) >> 1;
            out[cnt++] = (u32)(ws + pos - lo);
            m &= m - 1;
        }
        f = seg;
    }
    return cnt;
}

/* set field f from 0 to vn (1..3); returns 1 iff this call set it */
static inline u64 set_if_zero(u64 f, u64 vn) {
    u64 *wp = &W_[f >> 5];
    unsigned sh = (unsigned)(f & 31) << 1;
    if ((__atomic_load_n(wp, __ATOMIC_RELAXED) >> sh) & 3) return 0;
    u64 old = __atomic_fetch_or(wp, vn << sh, __ATOMIC_RELAXED);
    return ((old >> sh) & 3) ? 0 : 1;
}

/* one BFS step: expand side X fields equal to vcur into the other side with label vnext.
 * Returns the number of newly labelled vertices. */
static u64 bfs_step(int X, unsigned vcur, unsigned vnext) {
    const int Y = 1 - X;
    u64 added = 0;
    #pragma omp parallel reduction(+ : added)
    {
        u32 *hits = malloc((size_t)NZ_ * sizeof(u32));
        u64 tb[MAXGEN];
        #pragma omp for schedule(dynamic, 256)
        for (long long pl = 0; pl < (long long)NPSL_; pl++) {
            u64 lo = ((u64)pl * 2 + (u64)X) * NZ_;
            unsigned nh = scan_hits(lo, lo + NZ_, vcur, hits);
            if (!nh) continue;
            u64 m[4];
            psl_decode((u64)pl, m);
            for (int j = 0; j < NGEN_; j++) {
                const u64 *g = G_[X][j];
                u64 a2 = bred(g[0] * m[0] + g[1] * m[2]);
                u64 b2 = bred(g[0] * m[1] + g[1] * m[3]);
                u64 c2 = bred(g[2] * m[0] + g[3] * m[2]);
                u64 d2 = bred(g[2] * m[1] + g[3] * m[3]);
                u64 base = (psl_index(a2, b2, c2, d2) * 2 + (u64)Y) * NZ_;
                tb[j] = base;
                for (u64 f = base; f < base + NZ_; f += 256) __builtin_prefetch(&W_[f >> 5], 1, 3);
            }
            for (int j = 0; j < NGEN_; j++) {
                u64 base = tb[j], zs = GZ_[X][j];
                for (unsigned i = 0; i < nh; i++) {
                    u64 zt = (u64)hits[i] + zs;
                    if (zt >= NZ_) zt -= NZ_;
                    added += set_if_zero(base + zt, vnext);
                }
            }
        }
        free(hits);
    }
    return added;
}

/* BFS from field src (side side0) until the frontier empties. Returns the eccentricity;
 * *reached = number of labelled vertices (2N iff connected). */
static int g_verbose = 0;           /* VERBOSE=1: per-step timing on stderr only */

static unsigned bfs_ecc(u64 src, int side0, u64 *reached) {
    memset(W_, 0, NW_ * sizeof(u64));
    W_[src >> 5] |= 1ULL << ((src & 31) << 1);      /* label 1 = level 0 */
    u64 count = 1;
    unsigned t = 0;
    for (;;) {
        int X = side0 ^ (int)(t & 1);
        double ts = omp_get_wtime();
        u64 added = bfs_step(X, t % 3 + 1, (t + 1) % 3 + 1);
        if (g_verbose)
            fprintf(stderr, "  bfs(side0=%d) step %u: side %s -> new %llu, %.3f s\n", side0, t, X ? "B" : "A",
                    (unsigned long long)added, omp_get_wtime() - ts);
        if (!added) break;
        count += added;
        t++;
    }
    *reached = count;
    return t;
}

static void alloc_fields(void) {
    size_t al = (size_t)1 << 21;
    size_t bytes = (size_t)NW_ * sizeof(u64);
    bytes = (bytes + al - 1) / al * al;
    if (posix_memalign((void **)&W_, al, bytes)) {
        fprintf(stderr, "out of memory (%.2f GB requested)\n", bytes / 1e9);
        exit(2);
    }
    (void)madvise(W_, bytes, MADV_HUGEPAGE);
}

static int is_prime(u64 x) {
    if (x < 2) return 0;
    for (u64 q = 2; q * q <= x; q++) if (x % q == 0) return 0;
    return 1;
}

static u64 modp(long long x, u64 m) {
    long long r = x % (long long)m;
    if (r < 0) r += (long long)m;
    return (u64)r;
}

static int is_blank(const char *s) { return strspn(s, " \t\r\n") == strlen(s); }

/* "idx mat(a,b,c,d) z=Z": parse the matrix entries and z (signed integers allowed) */
static int parse_gen(const char *s, long long m[4], long long *z) {
    const char *q = strstr(s, "mat(");
    char *e;
    if (!q) return 0;
    q += 4;
    for (int k = 0; k < 4; k++) {
        while (*q == ' ' || *q == '\t') q++;
        m[k] = strtoll(q, &e, 10);
        if (e == q) return 0;
        q = e;
        while (*q == ' ' || *q == '\t') q++;
        if (k < 3) {
            if (*q != ',') return 0;
            q++;
        }
    }
    while (*q == ' ' || *q == '\t') q++;
    if (*q != ')') return 0;
    q = strstr(q, "z=");
    if (!q) return 0;
    *z = strtoll(q + 2, &e, 10);
    return e != q + 2;
}

static void invalid_exit(const char *why) {
    printf("INVALID reason=%s\n", why);
    exit(1);
}

/* ---------------------------------------------------------------- self-test ---- */

static u64 rng_s = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) {
    rng_s ^= rng_s << 13;
    rng_s ^= rng_s >> 7;
    rng_s ^= rng_s << 17;
    return rng_s;
}

static int st_reduction(void) {
    static const u64 ps[] = {3, 5, 389, 1009, 2147483647ULL};
    int bad = 0;
    for (int k = 0; k < 5; k++) {
        set_modulus(ps[k]);
        for (int it = 0; it < 1000000; it++) {
            u64 x = rnd();
            if (bred(x) != x % ps[k]) bad++;
        }
        u64 p = ps[k];
        u64 edge[] = {0, 1, p - 1, p, 2 * p - 1, 2 * p, ~0ULL, ~0ULL - 1};
        for (int i = 0; i < 8; i++) if (bred(edge[i]) != edge[i] % p) bad++;
    }
    printf("selftest reduction (Barrett mod p, p=3,5,389,1009,2^31-1): %s\n", bad ? "FAIL" : "ok");
    return bad;
}

/* every det-1 matrix maps to an index in [0,P); every index is hit by exactly the two matrices +-M;
 * decode/encode round trip; decoded matrices have det 1 */
static int st_index_exhaustive(u64 p) {
    set_modulus(p);
    build_inverses();
    u64 Pn = p * (p * p - 1) / 2;
    u32 *cnt = calloc(Pn, sizeof(u32));
    int bad = 0;
    for (u64 a = 0; a < p; a++)
        for (u64 b = 0; b < p; b++)
            for (u64 c = 0; c < p; c++)
                for (u64 d = 0; d < p; d++) {
                    if ((a * d % p + p - b * c % p) % p != 1) continue;
                    u64 idx = psl_index(a, b, c, d);
                    if (idx >= Pn) bad++;
                    else cnt[idx]++;
                }
    for (u64 i = 0; i < Pn; i++) {
        if (cnt[i] != 2) bad++;
        u64 m[4];
        psl_decode(i, m);
        if ((m[0] * m[3] % p + p - m[1] * m[2] % p) % p != 1) bad++;
        if (psl_index(m[0], m[1], m[2], m[3]) != i) bad++;
        u64 n0 = m[0] ? p - m[0] : 0, n1 = m[1] ? p - m[1] : 0, n2 = m[2] ? p - m[2] : 0, n3 = m[3] ? p - m[3] : 0;
        if (psl_index(n0, n1, n2, n3) != i) bad++;
    }
    free(cnt);
    printf("selftest index bijection, exhaustive p=%llu (P=%llu): %s\n", (unsigned long long)p,
           (unsigned long long)Pn, bad ? "FAIL" : "ok");
    return bad;
}

/* random indices and random det-1 matrices (both a != 0 and a == 0 branches) for larger p */
static int st_index_random(u64 p, int iters) {
    set_modulus(p);
    build_inverses();
    u64 Pn = p * (p * p - 1) / 2;
    int bad = 0;
    for (int it = 0; it < iters; it++) {
        u64 idx = rnd() % Pn, m[4];
        psl_decode(idx, m);
        if ((m[0] * m[3] % p + p - m[1] * m[2] % p) % p != 1) bad++;
        if (psl_index(m[0], m[1], m[2], m[3]) != idx) bad++;
        /* random matrix with a != 0 */
        u64 a = rnd() % (p - 1) + 1, b = rnd() % p, c = rnd() % p;
        u64 d = bred(bred(1 + b * c) * INV_[a]);
        u64 k = psl_index(a, b, c, d);
        u64 na = p - a, nb = (p - b) % p, nc = (p - c) % p, nd = (p - d) % p;
        if (k >= Pn || psl_index(na, nb, nc, nd) != k) bad++;
        u64 cm[4];
        psl_decode(k, cm);
        if (a <= H_) { if (cm[0] != a || cm[1] != b || cm[2] != c || cm[3] != d) bad++; }
        else if (cm[0] != na || cm[1] != nb || cm[2] != nc || cm[3] != nd) bad++;
        /* random matrix with a == 0 */
        u64 c0 = rnd() % (p - 1) + 1, d0 = rnd() % p;
        u64 b0 = (p - INV_[c0]) % p;               /* -b c = 1 */
        u64 k0 = psl_index(0, b0, c0, d0);
        if (k0 >= Pn || psl_index(0, (p - b0) % p, (p - c0) % p, (p - d0) % p) != k0) bad++;
    }
    printf("selftest index random, p=%llu (%d draws): %s\n", (unsigned long long)p, iters, bad ? "FAIL" : "ok");
    return bad;
}

/* naive reference for small p: explicit sorted list of canonical matrices, explicit adjacency */
static u64 *NC_ = NULL;
static u64 NNP_ = 0;

static u64 code4(u64 p, const u64 m[4]) { return ((m[0] * p + m[1]) * p + m[2]) * p + m[3]; }

static u64 canon_code(u64 p, const u64 m[4]) {
    u64 neg[4] = {(p - m[0]) % p, (p - m[1]) % p, (p - m[2]) % p, (p - m[3]) % p};
    u64 c1 = code4(p, m), c2 = code4(p, neg);
    return c1 < c2 ? c1 : c2;
}

static int cmp_u64(const void *x, const void *y) {
    u64 a = *(const u64 *)x, b = *(const u64 *)y;
    return (a > b) - (a < b);
}

static void build_naive(u64 p) {
    free(NC_);
    u64 *t = malloc(p * p * p * p * sizeof(u64));
    u64 k = 0;
    for (u64 a = 0; a < p; a++)
        for (u64 b = 0; b < p; b++)
            for (u64 c = 0; c < p; c++)
                for (u64 d = 0; d < p; d++) {
                    if ((a * d % p + p - b * c % p) % p != 1) continue;
                    u64 m[4] = {a, b, c, d};
                    t[k++] = canon_code(p, m);
                }
    qsort(t, k, sizeof(u64), cmp_u64);
    u64 u = 0;
    for (u64 i = 0; i < k; i++) if (i == 0 || t[i] != t[i - 1]) t[u++] = t[i];
    NC_ = t;
    NNP_ = u;
}

static u64 naive_rank(u64 code) {
    u64 lo = 0, hi = NNP_;
    while (lo < hi) {
        u64 mid = (lo + hi) / 2;
        if (NC_[mid] < code) lo = mid + 1; else hi = mid;
    }
    return lo;
}

static void naive_mat(u64 p, u64 r, u64 m[4]) {
    u64 code = NC_[r];
    m[3] = code % p; code /= p;
    m[2] = code % p; code /= p;
    m[1] = code % p; code /= p;
    m[0] = code;
}

/* eccentricity and reached count of source (e, side0) by a plain queue BFS */
static void naive_ecc(u64 p, u64 n, int d, u64 gm[][4], const u64 *gz, int side0, unsigned *ecc, u64 *reached) {
    u64 Pn = NNP_, NV = 2 * Pn * n;
    int *dist = malloc(NV * sizeof(int));
    u64 *q = malloc(NV * sizeof(u64));
    for (u64 i = 0; i < NV; i++) dist[i] = -1;
    u64 idm[4] = {1, 0, 0, 1};
    u64 r0 = naive_rank(canon_code(p, idm));
    u64 src = ((u64)side0 * Pn + r0) * n;
    u64 head = 0, tail = 0;
    q[tail++] = src;
    dist[src] = 0;
    while (head < tail) {
        u64 v = q[head++];
        u64 z = v % n, rest = v / n, r = rest % Pn;
        int X = (int)(rest / Pn);
        u64 M[4];
        naive_mat(p, r, M);
        for (int j = 0; j < d; j++) {
            u64 S[4] = {gm[j][0], gm[j][1], gm[j][2], gm[j][3]};
            u64 zs = gz[j];
            if (X == 1) {                                /* s^-1 = (adj S, -z_s) */
                u64 adj[4] = {S[3], (p - S[1]) % p, (p - S[2]) % p, S[0]};
                memcpy(S, adj, sizeof S);
                zs = (n - gz[j]) % n;
            }
            u64 T[4];
            T[0] = (S[0] * M[0] + S[1] * M[2]) % p;
            T[1] = (S[0] * M[1] + S[1] * M[3]) % p;
            T[2] = (S[2] * M[0] + S[3] * M[2]) % p;
            T[3] = (S[2] * M[1] + S[3] * M[3]) % p;
            u64 r2 = naive_rank(canon_code(p, T));
            u64 w = ((u64)(1 - X) * Pn + r2) * n + (z + zs) % n;
            if (dist[w] < 0) {
                dist[w] = dist[v] + 1;
                q[tail++] = w;
            }
        }
    }
    *reached = tail;
    *ecc = (unsigned)dist[q[tail - 1]];
    free(dist);
    free(q);
}

static int st_bfs_vs_naive(int trials) {
    static const u64 PR[] = {3, 5, 7, 11, 13, 17, 19, 23};
    static const u64 NR[] = {1, 2, 3, 4, 5, 6, 8, 12};
    int bad = 0, done = 0;
    unsigned maxecc = 0;
    u64 naive_p = 0;
    for (int tr = 0; tr < trials; tr++) {
        u64 p = PR[rnd() % 8], n = NR[rnd() % 8];
        int d = 1 + (int)(rnd() % 6);
        if (p != naive_p) { build_naive(p); naive_p = p; }
        u64 Pn = NNP_;
        if (Pn != p * (p * p - 1) / 2) { bad++; continue; }
        u64 gr[MAXGEN], gz[MAXGEN], gm[MAXGEN][4];
        int k = 0;
        while (k < d) {
            u64 r = rnd() % Pn, z = rnd() % n;
            int dup = 0;
            for (int i = 0; i < k; i++) if (gr[i] == r && gz[i] == z) dup = 1;
            if (dup) continue;
            gr[k] = r; gz[k] = z;
            naive_mat(p, r, gm[k]);
            k++;
        }
        set_modulus(p);
        build_inverses();
        NZ_ = n; NPSL_ = Pn; NF_ = 2 * Pn * n; NGEN_ = d;
        for (int j = 0; j < d; j++) {
            for (int t = 0; t < 4; t++) G_[0][j][t] = gm[j][t];
            GZ_[0][j] = gz[j];
            G_[1][j][0] = gm[j][3];
            G_[1][j][1] = (p - gm[j][1]) % p;
            G_[1][j][2] = (p - gm[j][2]) % p;
            G_[1][j][3] = gm[j][0];
            GZ_[1][j] = (n - gz[j]) % n;
        }
        NW_ = (NF_ + 31) / 32 + 1;
        alloc_fields();
        u64 rA = 0, rB = 0;
        unsigned eA = bfs_ecc(0, 0, &rA);
        unsigned eB = bfs_ecc(NZ_, 1, &rB);
        free(W_);
        unsigned nA = 0, nB = 0;
        u64 mA = 0, mB = 0;
        naive_ecc(p, n, d, gm, gz, 0, &nA, &mA);
        naive_ecc(p, n, d, gm, gz, 1, &nB, &mB);
        if (eA > maxecc) maxecc = eA;
        if (eB > maxecc) maxecc = eB;
        if (eA != nA || rA != mA || eB != nB || rB != mB) {
            bad++;
            printf("  MISMATCH p=%llu n=%llu d=%d: fast ecc(A,B)=(%u,%u) reached=(%llu,%llu) naive=(%u,%u) reached=(%llu,%llu)\n",
                   (unsigned long long)p, (unsigned long long)n, d, eA, eB, (unsigned long long)rA,
                   (unsigned long long)rB, nA, nB, (unsigned long long)mA, (unsigned long long)mB);
        }
        done++;
    }
    printf("selftest BFS vs naive reference: %d/%d instances agree (largest ecc seen %u)\n", done - bad, done, maxecc);
    return bad;
}

static int selftest(void) {
    int bad = 0;
    bad += st_reduction();
    for (u64 p = 3; p <= 13; p += 2) if (is_prime(p)) bad += st_index_exhaustive(p);
    bad += st_index_exhaustive(17);
    bad += st_index_exhaustive(19);
    bad += st_index_exhaustive(23);
    bad += st_index_random(151, 200000);
    bad += st_index_random(389, 200000);
    bad += st_index_random(1009, 200000);
    bad += st_bfs_vs_naive(400);
    printf("SELFTEST %s (failures=%d, threads=%d)\n", bad ? "FAILED" : "PASSED", bad, omp_get_max_threads());
    return bad ? 1 : 0;
}

/* ---------------------------------------------------------------- main ---- */

int main(int argc, char **argv) {
    const char *env = getenv("THREADS");
    int th = env ? atoi(env) : 1;
    if (th < 1) th = 1;
    omp_set_num_threads(th);
    g_verbose = getenv("VERBOSE") != NULL;
    if (argc == 2 && !strcmp(argv[1], "--selftest")) return selftest();
    if (argc != 2) {
        fprintf(stderr, "usage: THREADS=k %s FILE   |   %s --selftest\n", argv[0], argv[0]);
        return 2;
    }
    FILE *fp = fopen(argv[1], "r");
    if (!fp) { perror(argv[1]); return 2; }
    static char line[1 << 16];
    do {
        if (!fgets(line, sizeof line, fp)) invalid_exit("empty file");
    } while (is_blank(line));

    unsigned long long hd, hD, hp, hn, hN;
    char w1[32], w2[32], w3[32];
    if (sscanf(line, "%llu %llu %31s %llu %31s %llu %31s %llu", &hd, &hD, w1, &hp, w2, &hn, w3, &hN) != 8 ||
        strcmp(w1, "psl") || strcmp(w2, "n") || strcmp(w3, "N"))
        invalid_exit("header must read 'd D psl p n n N N'");
    if (hd < 1 || hd > MAXGEN) invalid_exit("d out of range");
    if (hp < 3 || hp % 2 == 0 || hp > (1ULL << 21) || !is_prime(hp)) invalid_exit("p is not an odd prime <= 2^21");
    if (hn < 1 || hn >= (1ULL << 32)) invalid_exit("n out of range");
    u64 p = hp, n = hn;
    u128 Nexp = (u128)n * (u128)(p * (p * p - 1) / 2);
    if (Nexp >> 40) invalid_exit("N too large for this checker");
    if ((u128)hN != Nexp) invalid_exit("header N differs from n*p(p^2-1)/2");

    static long long raw[MAXGEN][4], rawz[MAXGEN];
    int cnt = 0;
    while (fgets(line, sizeof line, fp)) {
        if (is_blank(line)) continue;
        if (cnt >= (int)hd) invalid_exit("more generator lines than d");
        if (!parse_gen(line, raw[cnt], &rawz[cnt])) invalid_exit("cannot parse a generator line");
        cnt++;
    }
    fclose(fp);
    if (cnt != (int)hd) invalid_exit("number of generator lines differs from d");

    set_modulus(p);
    build_inverses();
    NZ_ = n;
    NPSL_ = p * (p * p - 1) / 2;
    NF_ = 2 * NPSL_ * n;
    NGEN_ = (int)hd;
    static u64 gidx[MAXGEN];
    for (int j = 0; j < NGEN_; j++) {
        u64 a = modp(raw[j][0], p), b = modp(raw[j][1], p), c = modp(raw[j][2], p), d = modp(raw[j][3], p);
        u64 z = modp(rawz[j], n);
        if ((bred(a * d) + P_ - bred(b * c)) % P_ != 1) invalid_exit("a generator matrix has det != 1 mod p");
        G_[0][j][0] = a; G_[0][j][1] = b; G_[0][j][2] = c; G_[0][j][3] = d;
        GZ_[0][j] = z;
        G_[1][j][0] = d; G_[1][j][1] = (P_ - b) % P_; G_[1][j][2] = (P_ - c) % P_; G_[1][j][3] = a;
        GZ_[1][j] = (n - z) % n;
        gidx[j] = psl_index(a, b, c, d) * n + z;
    }
    for (int i = 0; i < NGEN_; i++)
        for (int j = i + 1; j < NGEN_; j++)
            if (gidx[i] == gidx[j]) invalid_exit("two generators coincide as PSL(2,p) x Z_n elements");

    NW_ = (NF_ + 31) / 32 + 1;
    alloc_fields();
    double t0 = omp_get_wtime();
    u64 rA = 0, rB = 0;
    unsigned eA = bfs_ecc(0, 0, &rA);          /* (e,A): field 0 */
    double t1 = omp_get_wtime();
    unsigned eB = bfs_ecc(NZ_, 1, &rB);        /* (e,B): field n */
    double t2 = omp_get_wtime();
    free(W_);

    int connA = (rA == NF_), connB = (rB == NF_);
    unsigned long long D = hD;
    int ok = connA && connB && eA <= D && eB <= D;
    char sa[96], sb[96];
    if (connA) snprintf(sa, sizeof sa, "%u", eA);
    else snprintf(sa, sizeof sa, "inf(reached %llu of %llu)", (unsigned long long)rA, (unsigned long long)NF_);
    if (connB) snprintf(sb, sizeof sb, "%u", eB);
    else snprintf(sb, sizeof sb, "inf(reached %llu of %llu)", (unsigned long long)rB, (unsigned long long)NF_);
    if (ok) {
        printf("VALID d=%llu D=%llu group=psl %llu x Z_%llu N=%llu vertices=%llu\n", hd, D,
               (unsigned long long)p, (unsigned long long)n, (unsigned long long)Nexp, (unsigned long long)NF_);
    } else {
        printf("INVALID d=%llu D=%llu group=psl %llu x Z_%llu N=%llu vertices=%llu reason=%s\n", hd, D,
               (unsigned long long)p, (unsigned long long)n, (unsigned long long)Nexp, (unsigned long long)NF_,
               (!connA || !connB) ? "not connected" : "diameter > D");
    }
    printf("ecc(e,A)=%s ecc(e,B)=%s\n", sa, sb);
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    fprintf(stderr, "# threads=%d bfsA=%.3fs bfsB=%.3fs total=%.3fs maxrss=%ldMB\n", th, t1 - t0, t2 - t1,
            t2 - t0, ru.ru_maxrss / 1024);
    return ok ? 0 : 1;
}
