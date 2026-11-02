/* haarcheck_rows: the same independent diameter check as haarcheck_gen (read its header for the graph, the header
 * format and the definitions), but a BFS layer is moved one row at a time, with no atomics per edge.
 *
 * Index.  Element (m, z) with m in the matrix part M = M1 x M2 and z in Z_n has bit index g = r*n + z, where r is the
 * compact index of m (exactly as haarcheck_gen computes it).  So row r is the n bits [r*n, r*n+n) of a bitset, rows
 * packed with no padding.  Bitsets hold N bits, same as haarcheck_gen.
 *
 * Why it is correct.  g -> g^-1 fixes e and maps the Haar edges (g,A)~(s g,B) to  x ~ x s^-1  (x on side A, x s^-1 on B),
 * i.e. right multiplication.  The sides keep their names, so the BFS levels from (e,A) and (e,B) are the same sets of
 * sizes as before.  Pull form: an element y on side B has neighbours y s on side A (s in S), an element y on side A has
 * neighbours y s^-1 on side B.  Right multiplication by u = (m_u, z_u) is (r, z) -> (r m_u, z + z_u mod n), so the
 * new layer on the destination side is: for each generator u, take the source row r m_u, rotate it so that destination
 * bit z reads source bit (z + z_u) mod n, OR all of them, and AND with NOT visited.  The result is the exact set of
 * vertices with a neighbour in the frontier, so the level sizes match haarcheck_gen.
 *
 * Speed.  Destination rows that are already full are skipped, source rows that are empty are skipped, and the rest is
 * done in 64-bit chunks of the rotated row.  Threads (pthreads) take blocks of destination rows.  A row's new bits are
 * written only by the thread that owns the row, but neighbouring rows share a 64-bit word at their ends, so bit writes
 * use an atomic OR.  Reads of the source frontier never race with writes (it is a different bitset in the same step).
 *
 * Memory.  4 bitsets of N bits (visited and frontier, one each per side), i.e. N/2 bytes, plus O(q^2) field tables.
 * N = 1.5e9 gives about 0.75 GB.
 * Selftests: haarcheck_gen's, plus the row rule (row and z of x*u) checked against the group multiplication.
 *
 * Build: cc -O3 -pthread -o haarcheck_rows haarcheck_rows.c
 * Run:   ./haarcheck_rows SOL.txt [--full] [A|B]
 *        A or B runs only the BFS from (e,A) or (e,B); its last line is HALF-VALID or HALF-INVALID, and the graph is
 *        VALID only when both halves pass.  --full: as in haarcheck_gen.
 * Threads: env HAAR_THREADS, default = online cores.  Exit 0 iff VALID (or HALF-VALID).  Meta groups are rejected. */
#include <ctype.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static void die(const char *m, const char *x) { fprintf(stderr, "ERROR: %s%s%s\n", m, x ? ": " : "", x ? x : ""); exit(2); }

/* ------------------------------------------------------------------ the field and the matrix group */
typedef struct { u32 a, b, c, d; } Mat;
typedef struct {
    int q, p, k, psl;
    u16 *add, *mul, *neg, *inv;   /* add[x*q+y], mul[x*q+y] */
    int *rank;                    /* rank[x] = rank among allowed leading values, or -1 */
    u16 *unrank;                  /* unrank[r] = x */
    u64 na, q2, order;            /* na = number of allowed leading values; order = |M| */
    char spec[128];               /* e.g. "psl 243 poly x^5+2x+1" */
} MG;

static int is_prime(int x) { if (x < 2) return 0; for (int t = 2; t * t <= x; t++) if (x % t == 0) return 0; return 1; }

static void build_field(MG *G, const char *poly) {
    int q = G->q, p = 0, k = 0, x = q;
    for (int t = 2; t <= q; t++) if (q % t == 0) { p = t; break; }
    while (x % p == 0) { x /= p; k++; }
    if (x != 1 || !is_prime(p)) die("q is not a prime power", NULL);
    if (q > 4096) die("q too large for table-based field", NULL);
    G->p = p; G->k = k;
    int f[16] = {0};   /* f[0..k], f[k] = 1 */
    if (k == 1) { if (poly) die("poly given for a prime field", NULL); f[1] = 1; }
    else {
        if (!poly) die("q = p^k with k > 1 needs 'poly f'", NULL);
        const char *s = poly;
        while (*s) {                                  /* terms  [coef]['x'['^'e]]  separated by '+' */
            long coef = 1; int e = 0, has_c = 0;
            if (isdigit((unsigned char)*s)) { char *end; coef = strtol(s, &end, 10); s = end; has_c = 1; }
            if (*s == 'x') { s++; e = 1; if (*s == '^') { s++; char *end; e = (int)strtol(s, &end, 10); s = end; } }
            else if (!has_c) die("bad polynomial", poly);
            if (e < 0 || e > k) die("polynomial degree exceeds k", poly);
            f[e] = (int)((f[e] + coef) % p);
            if (*s == '+') s++; else if (*s) die("bad polynomial", poly);
        }
        if (f[k] != 1) die("polynomial must be monic of degree k", poly);
    }
    u16 *add = malloc(sizeof(u16) * (size_t)q * q), *mul = malloc(sizeof(u16) * (size_t)q * q);
    u16 *neg = malloc(sizeof(u16) * q), *inv = malloc(sizeof(u16) * q);
    int dg[2][16];
    for (int x1 = 0; x1 < q; x1++) {
        for (int y1 = 0; y1 < q; y1++) {
            int xa = x1, ya = y1, s_ = 0, mult = 1;
            for (int i = 0; i < k; i++) { dg[0][i] = xa % p; xa /= p; dg[1][i] = ya % p; ya /= p; }
            for (int i = 0; i < k; i++) { s_ += ((dg[0][i] + dg[1][i]) % p) * mult; mult *= p; }
            add[(size_t)x1 * q + y1] = (u16)s_;
            int pr[32] = {0};
            for (int i = 0; i < k; i++) for (int j = 0; j < k; j++) pr[i + j] = (pr[i + j] + dg[0][i] * dg[1][j]) % p;
            for (int i = 2 * k - 2; i >= k; i--) {    /* reduce x^i using x^k = -(f[0] + ... + f[k-1] x^(k-1)) */
                int t = pr[i]; pr[i] = 0;
                for (int j = 0; j < k; j++) pr[i - k + j] = ((pr[i - k + j] - t * f[j]) % p + p) % p;
            }
            int r = 0; mult = 1;
            for (int i = 0; i < k; i++) { r += pr[i] * mult; mult *= p; }
            mul[(size_t)x1 * q + y1] = (u16)r;
        }
    }
    for (int x1 = 0; x1 < q; x1++) {
        neg[x1] = inv[x1] = 0;
        for (int y1 = 0; y1 < q; y1++) {
            if (add[(size_t)x1 * q + y1] == 0) neg[x1] = (u16)y1;
            if (mul[(size_t)x1 * q + y1] == 1) inv[x1] = (u16)y1;
        }
        if (x1 && inv[x1] == 0) die("field: element without inverse (polynomial reducible?)", poly);
    }
    G->add = add; G->mul = mul; G->neg = neg; G->inv = inv;
    /* axioms */
    u64 trip = (u64)q * q * q;
    u64 seed = 0x9E3779B97F4A7C15ULL, lim = trip <= 30000000ULL ? trip : 30000000ULL;
    for (u64 t = 0; t < lim; t++) {
        u32 a, b, c;
        if (trip <= 30000000ULL) { a = (u32)(t / ((u64)q * q)); b = (u32)(t / q % q); c = (u32)(t % q); }
        else { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; a = seed % q; b = (seed >> 20) % q; c = (seed >> 40) % q; }
        if (mul[mul[a * q + b] * q + c] != mul[a * q + mul[b * q + c]] || add[add[a * q + b] * q + c] != add[a * q + add[b * q + c]] ||
            mul[a * q + add[b * q + c]] != add[mul[a * q + b] * q + mul[a * q + c]] || mul[a * q + b] != mul[b * q + a] ||
            add[a * q + b] != add[b * q + a])
            die("field axiom failure", poly);
    }
    for (int x1 = 0; x1 < q; x1++) if (add[(size_t)x1 * q + neg[x1]] != 0 || add[(size_t)x1 * q + 0] != x1 || mul[(size_t)x1 * q + 1] != x1) die("field identity failure", NULL);
}

static void build_group(MG *G, int psl) {
    int q = G->q;
    G->psl = psl && (q % 2 == 1);
    G->rank = malloc(sizeof(int) * q); G->unrank = malloc(sizeof(u16) * q);
    int r = 0;
    for (int x = 0; x < q; x++) {
        int ok = x != 0 && (!G->psl || x < G->neg[x]);
        G->rank[x] = ok ? r : -1;
        if (ok) G->unrank[r++] = (u16)x;
    }
    G->na = r; G->q2 = (u64)q * q;
    G->order = G->na * G->q2 + G->na * q;
    u64 expect = (u64)q * ((u64)q * q - 1) / (G->psl ? 2 : 1);
    if (G->order != expect) die("group order formula mismatch", NULL);
}

static inline Mat mdec(const MG *G, u64 i) {
    Mat m; u32 q = G->q;
    if (i < G->na * G->q2) {
        u64 r = i % G->q2;
        m.a = G->unrank[i / G->q2]; m.b = (u32)(r / q); m.c = (u32)(r % q);
        u32 t = G->add[1 * q + G->mul[m.b * q + m.c]];
        m.d = G->mul[t * q + G->inv[m.a]];
    } else {
        u64 j = i - G->na * G->q2;
        m.a = 0; m.b = G->unrank[j / q]; m.d = (u32)(j % q); m.c = G->neg[G->inv[m.b]];
    }
    return m;
}
static inline u64 menc(const MG *G, Mat m) {
    u32 q = G->q;
    if (G->psl) {
        u32 lead = m.a ? m.a : m.b;
        if (G->rank[lead] < 0) { m.a = G->neg[m.a]; m.b = G->neg[m.b]; m.c = G->neg[m.c]; m.d = G->neg[m.d]; }
    }
    if (m.a) return (u64)G->rank[m.a] * G->q2 + (u64)m.b * q + m.c;
    return G->na * G->q2 + (u64)G->rank[m.b] * q + m.d;
}
static inline Mat mmul(const MG *G, Mat s, Mat g) {
    u32 q = G->q; const u16 *A = G->add, *M = G->mul; Mat r;
    r.a = A[M[s.a * q + g.a] * q + M[s.b * q + g.c]];
    r.b = A[M[s.a * q + g.b] * q + M[s.b * q + g.d]];
    r.c = A[M[s.c * q + g.a] * q + M[s.d * q + g.c]];
    r.d = A[M[s.c * q + g.b] * q + M[s.d * q + g.d]];
    return r;
}
static inline int mdet1(const MG *G, Mat m) {
    u32 q = G->q;
    return G->add[G->mul[m.a * q + m.d] * q + G->neg[G->mul[m.b * q + m.c]]] == 1;
}

/* ------------------------------------------------------------------ header and generators */
#define MAXF 2
static MG F[MAXF]; static int nf = 0;
static u64 NG, NZ;       /* |G| = prod |Fi| * n ; n */
static char group_spec[512];
typedef struct { Mat m[MAXF]; u32 z; } El;

static char *tok[64]; static int ntok = 0;
static int parse_mg(int i, MG *G) {   /* returns next token index */
    if (i + 1 >= ntok) die("header: truncated group spec", NULL);
    int psl = 0;
    if (!strcmp(tok[i], "sl")) psl = 0; else if (!strcmp(tok[i], "psl")) psl = 1;
    else die("unsupported group in header (only sl, psl and prod of two)", tok[i]);
    G->q = atoi(tok[i + 1]); i += 2;
    const char *poly = NULL;
    if (i < ntok && !strcmp(tok[i], "poly")) { if (i + 1 >= ntok) die("header: poly without value", NULL); poly = tok[i + 1]; i += 2; }
    build_field(G, poly); build_group(G, psl);
    snprintf(G->spec, sizeof G->spec, "%s %d%s%s", psl ? "psl" : "sl", G->q, poly ? " poly " : "", poly ? poly : "");
    return i;
}

static El parse_el(const char *line, u32 n) {
    El e; memset(&e, 0, sizeof e);
    const char *s = line; int cnt = 0;
    const char *zz = strstr(line, "z=");
    if (!zz) die("generator line without z=", line);
    if (nf == 2 && !strstr(line, "prod[")) die("generator line without prod[...]", line);
    while ((s = strstr(s, "mat(")) != NULL && s < zz) {
        long v[4]; char *end; const char *t = s + 4;
        for (int i = 0; i < 4; i++) { v[i] = strtol(t, &end, 10); if (end == t) die("bad mat()", line); t = end; if (*t == ',' || (i == 3 && *t == ')')) t++; else die("bad mat()", line); }
        if (cnt >= nf) die("too many mat() in line", line);
        for (int i = 0; i < 4; i++) if (v[i] < 0 || v[i] >= F[cnt].q) die("matrix entry out of range", line);
        e.m[cnt] = (Mat){(u32)v[0], (u32)v[1], (u32)v[2], (u32)v[3]};
        if (!mdet1(&F[cnt], e.m[cnt])) die("matrix does not have det 1", line);
        cnt++; s = t;
    }
    if (cnt != nf) die("wrong number of mat() in line", line);
    long z = strtol(zz + 2, NULL, 10);
    if (z < 0 || z >= (long)n) die("z out of range", line);
    e.z = (u32)z; return e;
}
static inline u64 enc_el(const El *e) {
    u64 r = 0;
    for (int i = 0; i < nf; i++) r = r * F[i].order + menc(&F[i], e->m[i]);
    return r * NZ + e->z;
}
static El inv_el(const El *e) {
    El r; memset(&r, 0, sizeof r);
    for (int i = 0; i < nf; i++) { const Mat *m = &e->m[i]; r.m[i] = (Mat){m->d, F[i].neg[m->b], F[i].neg[m->c], m->a}; }
    r.z = (NZ - e->z) % NZ; return r;
}
static inline El dec_el(u64 g) {
    El e; e.z = (u32)(g % NZ); u64 r = g / NZ;
    for (int i = nf - 1; i >= 0; i--) { e.m[i] = mdec(&F[i], r % F[i].order); r /= F[i].order; }
    return e;
}
static inline u64 lmul_idx(const El *s, const El *g) {   /* index of s*g */
    u64 r = 0;
    for (int i = 0; i < nf; i++) r = r * F[i].order + menc(&F[i], mmul(&F[i], s->m[i], g->m[i]));
    u32 z = s->z + g->z; if (z >= NZ) z -= NZ;
    return r * NZ + z;
}

static u64 rng_s = 88172645463325252ULL;
static u64 rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }

static void selftests(const El *S, int d) {
    for (int i = 0; i < nf; i++) {
        MG *G = &F[i]; u64 cnt = 0;
        for (u64 x = 0; x < G->order; x++) {
            Mat m = mdec(G, x);
            if (!mdet1(G, m) || menc(G, m) != x) die("index round trip failed", G->spec);
        }
        if (G->q <= 81) {   /* brute-force count of det-1 matrices */
            for (u32 a = 0; a < (u32)G->q; a++) for (u32 b = 0; b < (u32)G->q; b++) for (u32 c = 0; c < (u32)G->q; c++) for (u32 dd = 0; dd < (u32)G->q; dd++)
                if (mdet1(G, (Mat){a, b, c, dd})) cnt++;
            u64 want = G->order * (G->psl ? 2 : 1);
            if (cnt != want) die("brute-force det-1 count mismatch", G->spec);
            printf("selftest %s: |M| = %llu, det-1 matrices %llu\n", G->spec, (unsigned long long)G->order, (unsigned long long)cnt);
        } else printf("selftest %s: |M| = %llu, index round trip over all elements ok\n", G->spec, (unsigned long long)G->order);
    }
    for (int t = 0; t < 20000; t++) {   /* associativity, identity, inverse on random elements */
        El x = dec_el(rnd() % NG), y = dec_el(rnd() % NG), z = dec_el(rnd() % NG);
        u64 yz = lmul_idx(&y, &z); El yzE = dec_el(yz);
        u64 xyz1 = lmul_idx(&x, &yzE);
        u64 xy = lmul_idx(&x, &y); El xyE = dec_el(xy);
        u64 xyz2 = lmul_idx(&xyE, &z);
        if (xyz1 != xyz2) die("associativity test failed", NULL);
        El id; memset(&id, 0, sizeof id); for (int i = 0; i < nf; i++) id.m[i] = (Mat){1, 0, 0, 1};
        if (lmul_idx(&id, &x) != enc_el(&x) || lmul_idx(&x, &id) != enc_el(&x)) die("identity test failed", NULL);
        El xi = inv_el(&x);
        if (lmul_idx(&x, &xi) != enc_el(&id)) die("inverse test failed", NULL);
    }
    puts("selftest group multiplication: associativity, identity, inverse on 20000 random triples ok");
    for (int i = 0; i < d; i++) {
        El id; memset(&id, 0, sizeof id); for (int j = 0; j < nf; j++) id.m[j] = (Mat){1, 0, 0, 1};
        El si = inv_el(&S[i]);
        if (lmul_idx(&S[i], &si) != enc_el(&id)) die("generator times its inverse is not e", NULL);
    }
}

/* ------------------------------------------------------------------ bit rows */
static El *Sg, *SIg;     /* generators and their inverses (set in main) */
static u64 NR;           /* number of rows = |M| */

static inline u64 lowmask(int L) { return L >= 64 ? ~0ULL : (1ULL << L) - 1; }
static inline int chunk_len(u64 z0) { u64 rem = NZ - z0; return rem < 64 ? (int)rem : 64; }

/* L (1..64) bits of a bitset starting at bit pos; the bitset has one spare word at the end */
static inline u64 get_bits(const u64 *bs, u64 pos, int L) {
    u64 w = pos >> 6; int o = (int)(pos & 63);
    u64 v = __atomic_load_n(&bs[w], __ATOMIC_RELAXED) >> o;
    if (o && o + L > 64) v |= __atomic_load_n(&bs[w + 1], __ATOMIC_RELAXED) << (64 - o);
    return v & lowmask(L);
}
/* OR the L low bits of val into a bitset at bit pos (atomic: the word may be shared with a neighbouring row) */
static inline void or_bits(u64 *bs, u64 pos, u64 val, int L) {
    u64 w = pos >> 6; int o = (int)(pos & 63);
    __atomic_fetch_or(&bs[w], val << o, __ATOMIC_RELAXED);
    if (o && o + L > 64) __atomic_fetch_or(&bs[w + 1], val >> (64 - o), __ATOMIC_RELAXED);
}
/* L cyclic bits of the n-bit row at bit base, starting at offset p (0 <= p < n): bit j is row bit (p + j) mod n */
static inline u64 get_cyc(const u64 *bs, u64 base, u64 p, int L) {
    u64 a = NZ - p;                                   /* bits from p to the end of the row */
    if ((u64)L <= a) return get_bits(bs, base + p, L);
    return get_bits(bs, base + p, (int)a) | (get_bits(bs, base, L - (int)a) << a);
}
static int row_nonzero(const u64 *bs, u64 base) {
    for (u64 z0 = 0; z0 < NZ; z0 += 64) if (get_bits(bs, base + z0, chunk_len(z0))) return 1;
    return 0;
}
static int row_full(const u64 *bs, u64 base) {
    for (u64 z0 = 0; z0 < NZ; z0 += 64) { int L = chunk_len(z0); if (get_bits(bs, base + z0, L) != lowmask(L)) return 0; }
    return 1;
}
/* matrix part of row r, one matrix per factor (decoding is the slow part, so it is done once per row) */
static inline void row_decode(u64 r, Mat *y) {
    for (int i = nf - 1; i >= 0; i--) { y[i] = mdec(&F[i], r % F[i].order); r /= F[i].order; }
}
/* row index of (row y) * u, where u is given by its matrix part (the z part is not used here) */
static inline u64 row_times(const Mat *y, const El *u) {
    u64 out = 0;
    for (int i = 0; i < nf; i++) out = out * F[i].order + menc(&F[i], mmul(&F[i], y[i], u->m[i]));
    return out;
}

static void row_selftest(void) {   /* the row rule against the full group multiplication */
    for (int t = 0; t < 20000; t++) {
        El x = dec_el(rnd() % NG), u = dec_el(rnd() % NG);
        El xu = dec_el(lmul_idx(&x, &u));
        if (xu.z != (x.z + u.z) % NZ) die("row test: z part of x*u is not z + z_u", NULL);
        Mat y[MAXF]; row_decode(enc_el(&x) / NZ, y);
        if (enc_el(&xu) / NZ != row_times(y, &u)) die("row test: matrix row of x*u is not row(x) * u", NULL);
    }
    puts("selftest row rule: row and z of x*u agree with the group multiplication on 20000 random pairs ok");
}

/* ------------------------------------------------------------------ one BFS layer, by threads over destination rows */
typedef struct {
    const u64 *src;     /* frontier of the source side (read only in this step) */
    u64 *dst, *vis;     /* frontier and visited of the destination side */
    const El *u;        /* pull generators: source = destination * u */
    int d;
    u64 nextrow, added; /* shared counters, used atomically */
} Step;

static u64 do_row(Step *st, u64 r) {
    u64 base = r * NZ;
    if (row_full(st->vis, base)) return 0;
    Mat y[MAXF]; row_decode(r, y);
    u64 srow[st->d], zs[st->d]; int live = 0;
    for (int a = 0; a < st->d; a++) {
        u64 sb = row_times(y, &st->u[a]) * NZ;
        if (row_nonzero(st->src, sb)) { srow[live] = sb; zs[live] = st->u[a].z; live++; }
    }
    u64 add = 0;
    for (u64 z0 = 0; z0 < NZ && live; z0 += 64) {
        int L = chunk_len(z0);
        u64 acc = 0;
        for (int i = 0; i < live; i++) acc |= get_cyc(st->src, srow[i], (z0 + zs[i]) % NZ, L);
        if (!acc) continue;
        u64 nw = acc & ~get_bits(st->vis, base + z0, L) & lowmask(L);   /* only this row's bits; others may change under us */
        if (nw) { or_bits(st->vis, base + z0, nw, L); or_bits(st->dst, base + z0, nw, L); add += (u64)__builtin_popcountll(nw); }
    }
    return add;
}

#define ROWCHUNK 1024
static void *worker(void *arg) {
    Step *st = arg; u64 add = 0;
    for (;;) {
        u64 r0 = __atomic_fetch_add(&st->nextrow, ROWCHUNK, __ATOMIC_RELAXED);
        if (r0 >= NR) break;
        u64 r1 = r0 + ROWCHUNK < NR ? r0 + ROWCHUNK : NR;
        for (u64 r = r0; r < r1; r++) add += do_row(st, r);
    }
    __atomic_fetch_add(&st->added, add, __ATOMIC_RELAXED);
    return NULL;
}
static u64 run_step(Step *st, int T) {
    pthread_t *th = malloc(sizeof(pthread_t) * T);
    st->nextrow = 0; st->added = 0;
    for (int t = 0; t < T; t++) if (pthread_create(&th[t], NULL, worker, st) != 0) die("pthread_create failed", NULL);
    for (int t = 0; t < T; t++) pthread_join(th[t], NULL);
    free(th);
    return st->added;
}
static int nthreads(void) {
    const char *e = getenv("HAAR_THREADS");
    if (e && atoi(e) > 0) return atoi(e);
    long c = sysconf(_SC_NPROCESSORS_ONLN);
    return c > 0 ? (int)c : 1;
}

/* ------------------------------------------------------------------ main */
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haarcheck_rows SOL.txt [--full] [A|B]\n"); return 2; }
    int full = 0, only = -1;   /* only: -1 both starts, 0 = (e,A) only, 1 = (e,B) only */
    for (int j = 2; j < argc; j++) {
        if (!strcmp(argv[j], "--full")) full = 1;
        else if (!strcmp(argv[j], "A") || !strcmp(argv[j], "B")) only = argv[j][0] == 'B';
        else die("unknown argument (use --full, A or B)", argv[j]);
    }
    double t0 = now();
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    static char line[8192];
    if (!fgets(line, sizeof line, f)) die("empty file", NULL);
    char hdr[8192]; snprintf(hdr, sizeof hdr, "%s", line); hdr[strcspn(hdr, "\r\n")] = 0;
    for (char *t = strtok(line, " \t\r\n"); t && ntok < 64; t = strtok(NULL, " \t\r\n")) tok[ntok++] = strdup(t);
    if (ntok < 6) die("short header", hdr);
    for (int j = 0; j < ntok; j++) if (!strcmp(tok[j], "meta")) die("meta groups are not supported by haarcheck_rows (use haarcheck_gen)", hdr);
    int d = atoi(tok[0]), D = atoi(tok[1]), i = 2;
    if (!strcmp(tok[i], "prod")) { i = parse_mg(i + 1, &F[0]); i = parse_mg(i, &F[1]); nf = 2; }
    else { i = parse_mg(i, &F[0]); nf = 1; }
    if (i >= ntok || strcmp(tok[i], "n")) die("header: expected 'n' after the group spec (unsupported group?)", hdr);
    long long n = atoll(tok[i + 1]); i += 2;
    if (n < 1) die("bad n", hdr);
    NZ = (u64)n; NG = NZ; for (int j = 0; j < nf; j++) NG *= F[j].order;
    NR = NG / NZ;
    if (i < ntok && !strcmp(tok[i], "N")) { if (i + 1 >= ntok || (u64)atoll(tok[i + 1]) != NG) die("header N does not match the group order", hdr); i += 2; }
    if (nf == 1) snprintf(group_spec, sizeof group_spec, "%s x Z_%lld", F[0].spec, n);
    else snprintf(group_spec, sizeof group_spec, "prod %s %s x Z_%lld", F[0].spec, F[1].spec, n);
    if (D < 1 || d < 1) die("bad d or D", hdr);
    El *S = malloc(sizeof(El) * d), *SI = malloc(sizeof(El) * d); int k = 0;
    while (k < d && fgets(line, sizeof line, f)) {
        if (!strstr(line, "z=")) continue;
        S[k] = parse_el(line, (u32)n); SI[k] = inv_el(&S[k]); k++;
    }
    if (k != d) die("fewer generator lines than d", NULL);
    Sg = S; SIg = SI;
    selftests(S, d);
    row_selftest();
    u64 *gi = malloc(sizeof(u64) * d);
    for (int a = 0; a < d; a++) { gi[a] = enc_el(&S[a]); for (int b = 0; b < a; b++) if (gi[a] == gi[b]) die("repeated generator (as a group element)", NULL); }
    printf("file %s\nheader: %s\ngroup %s, |G| = %llu = N, vertices 2N = %llu; %d distinct generators\n", argv[1], hdr, group_spec,
           (unsigned long long)NG, (unsigned long long)(2 * NG), d);
    int T = nthreads();
    printf("engine: row bitsets (row = %llu bits), %d threads\n", (unsigned long long)NZ, T);
    fflush(stdout);

    u64 N = NG, W = (N + 63) / 64 + 1;   /* one spare word for the unaligned reads and writes at the end */
    u64 *vis[2], *fr[2];
    for (int s = 0; s < 2; s++) { vis[s] = calloc(W, 8); fr[s] = calloc(W, 8); if (!vis[s] || !fr[s]) die("out of memory", NULL); }
    El id; memset(&id, 0, sizeof id); for (int j = 0; j < nf; j++) id.m[j] = (Mat){1, 0, 0, 1};
    u64 e = enc_el(&id);
    int bad = 0, eccmax = 0; u64 unreached_max = 0;
    for (int start = 0; start < 2; start++) {
        if (only >= 0 && start != only) continue;
        for (int s = 0; s < 2; s++) { memset(vis[s], 0, W * 8); memset(fr[s], 0, W * 8); }
        vis[start][e >> 6] |= 1ULL << (e & 63); fr[start][e >> 6] |= 1ULL << (e & 63);
        u64 reached[2] = {0, 0}; reached[start] = 1;
        int side = start, ecc = 0; u64 level[64]; int nlev = 1; level[0] = 1;
        u64 snap[2] = {reached[0], reached[1]};   /* reached counts after exactly D steps */
        for (int step = 1; step <= (full ? 60 : D); step++) {
            int ns = side ^ 1;
            /* side A -> B pulls with S (y = x s^-1 in the transformed graph), side B -> A pulls with S^-1 */
            Step st = {.src = fr[side], .dst = fr[ns], .vis = vis[ns], .u = side == 0 ? S : SI, .d = d};
            u64 add = run_step(&st, T);
            memset(fr[side], 0, W * 8);          /* the consumed frontier; fr[ns] now holds the new one */
            reached[ns] += add; level[nlev++] = add; if (add) ecc = step; side = ns;
            if (step == D) { snap[0] = reached[0]; snap[1] = reached[1]; }
            if (!add) { nlev--; if (step < D) { snap[0] = reached[0]; snap[1] = reached[1]; } break; }
        }
        printf("from (e,%c): reached A %llu/%llu, B %llu/%llu within %d", start ? 'B' : 'A', (unsigned long long)snap[0],
               (unsigned long long)N, (unsigned long long)snap[1], (unsigned long long)N, D);
        if (full) printf("; true ecc %d", ecc); else if (snap[0] == N && snap[1] == N) printf("; ecc %d", ecc);
        printf("; level sizes [");
        for (int j = 0; j < nlev; j++) printf("%s%llu", j ? ", " : "", (unsigned long long)level[j]);
        printf("]  (%.0fs)\n", now() - t0); fflush(stdout);
        if (snap[0] != N || snap[1] != N) bad = 1;
        { u64 un = 2 * N - snap[0] - snap[1]; if (un > unreached_max) unreached_max = un; }
        if (ecc > eccmax) eccmax = ecc;
    }
    if (only >= 0) {
        printf("%s from (e,%c) d=%d D=%d group=%s N=%llu vertices=%llu\n", bad ? "HALF-INVALID" : "HALF-VALID", only ? 'B' : 'A', d, D,
               group_spec, (unsigned long long)N, (unsigned long long)(2 * N));
        return bad;
    }
    printf("%s d=%d D=%d group=%s N=%llu vertices=%llu (distinct generators, %d-regular simple; ", bad ? "INVALID" : "VALID", d, D,
           group_spec, (unsigned long long)N, (unsigned long long)(2 * N), d);
    if (bad) printf("%llu vertices unreached within D from the worse start", (unsigned long long)unreached_max);
    else printf("every vertex within %d of both (e,A) and (e,B); ecc %d", D, eccmax);
    if (full && bad) printf("; true ecc %d", eccmax);
    printf("; %.0fs)\n", now() - t0);
    return bad;
}
