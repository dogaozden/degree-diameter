/* haarcheck_gen: independent, low-memory diameter check of a Haar graph H(G,S) for the families
 *     G = M x Z_n            M = sl q | psl q            (q = p^k, optional "poly f" for k > 1)
 *     G = (M1 x M2) x Z_n    header "prod M1 M2", each Mi as above
 * Header (one line):  d D <group spec> n NCYC [N NTOT]      e.g.
 *     11 10 psl 243 poly x^5+2x+1 n 11 N 78917652
 *     15 9 prod sl 5 sl 19 n 127 N 104241600
 * Then d lines "<idx> mat(a,b,c,d) z=Z"  or  "<idx> prod[mat(..);mat(..)] z=Z"  (the <idx> is ignored).
 * Field elements are integers 0..q-1 written as sum c_i p^i, c_i the coefficient of x^i of the field GF(p)[x]/(f).
 * Graph: vertices (g,A),(g,B), g in G, edges (g,A) ~ (s g,B), s in S.  Right multiplication by G is an automorphism group
 * transitive on each side, so BFS from (e,A) and from (e,B), each reaching every vertex within D steps, is exactly
 * diameter <= D.  Distinct generators give a simple d-regular graph.
 *
 * Own code, not shared with build_haar2.py / check_haar_indep.py / haarcheck2.c:
 *   - GF(q) multiplication/addition tables from the header polynomial (schoolbook product, reduction by monic f);
 *     checked: every nonzero element invertible, associativity/distributivity (exhaustive for q^3 <= 3e7, else random).
 *   - Matrix group M: elements with det 1 (psl: modulo +-I, q odd; psl of even q is sl).  Compact index of a matrix:
 *       a != 0 (and a canonical):  idx = rank(a) q^2 + b q + c        (d = (1 + bc)/a)
 *       a == 0:                    idx = na q^2 + rank(b) q + d       (c = -1/b)
 *     where for sl rank(x) = x-1 on x != 0 and for psl the canonical representative of {X,-X} is the one whose first
 *     nonzero entry among (a,b) is the smaller of x, -x as an integer, rank counts canonical values in increasing order.
 *     Product elements: idx = (idx1 * |M2| + idx2) * n + z.
 *   - Neighbours (s g) are computed on the fly by 2x2 products with the lookup tables; inverse generators by the
 *     adjugate [[d,-b],[-c,a]] and -z.
 * Memory: 6 bitsets of N bits + O(q^2) tables, ~ 0.75 N bytes (about 80 MB at N = 104M).
 * Startup self-tests (all must pass, else exit 2): field axioms, index bijection over every matrix of each factor
 * (decode lands on det 1, encode inverts), brute-force count of det-1 matrices for q <= 81, random associativity and
 * identity of the group multiplication, s * s^-1 = e for every generator, generators det 1 and pairwise distinct.
 * Build: cc -O3 -fopenmp -o haarcheck_gen haarcheck_gen.c      Run: ./haarcheck_gen SOL.txt
 * Exit 0 iff VALID.  Output line "VALID d=.. D=.. group=<spec> x Z_<n> N=.. vertices=.." on success, "INVALID ..." else. */
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef _OPENMP
#include <omp.h>
#endif

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
    int psl;
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

/* ------------------------------------------------------------------ main */
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haarcheck_gen SOL.txt [--full]\n"); return 2; }
    int full = argc > 2 && !strcmp(argv[2], "--full");   /* --full: keep going past D to report the true eccentricity (verdict is still about D) */
    double t0 = now();
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    static char line[8192];
    if (!fgets(line, sizeof line, f)) die("empty file", NULL);
    char hdr[8192]; snprintf(hdr, sizeof hdr, "%s", line); hdr[strcspn(hdr, "\r\n")] = 0;
    for (char *t = strtok(line, " \t\r\n"); t && ntok < 64; t = strtok(NULL, " \t\r\n")) tok[ntok++] = strdup(t);
    if (ntok < 6) die("short header", hdr);
    int d = atoi(tok[0]), D = atoi(tok[1]), i = 2;
    if (!strcmp(tok[i], "prod")) { i = parse_mg(i + 1, &F[0]); i = parse_mg(i, &F[1]); nf = 2; }
    else { i = parse_mg(i, &F[0]); nf = 1; }
    if (i >= ntok || strcmp(tok[i], "n")) die("header: expected 'n' after the group spec (unsupported group?)", hdr);
    long long n = atoll(tok[i + 1]); i += 2;
    if (n < 1) die("bad n", hdr);
    NZ = (u64)n; NG = NZ; for (int j = 0; j < nf; j++) NG *= F[j].order;
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
    selftests(S, d);
    u64 *gi = malloc(sizeof(u64) * d);
    for (int a = 0; a < d; a++) { gi[a] = enc_el(&S[a]); for (int b = 0; b < a; b++) if (gi[a] == gi[b]) die("repeated generator (as a group element)", NULL); }
    printf("file %s\nheader: %s\ngroup %s, |G| = %llu = N, vertices 2N = %llu; %d distinct generators\n", argv[1], hdr, group_spec,
           (unsigned long long)NG, (unsigned long long)(2 * NG), d);
    fflush(stdout);

    u64 N = NG, W = (N + 63) / 64;
    u64 *vis[2], *cur[2], *nxt[2];
    for (int s = 0; s < 2; s++) { vis[s] = calloc(W, 8); cur[s] = calloc(W, 8); nxt[s] = calloc(W, 8); if (!vis[s] || !cur[s] || !nxt[s]) die("out of memory", NULL); }
    El id; memset(&id, 0, sizeof id); for (int j = 0; j < nf; j++) id.m[j] = (Mat){1, 0, 0, 1};
    u64 e = enc_el(&id);
    int bad = 0, eccmax = 0; u64 unreached_max = 0;
    for (int start = 0; start < 2; start++) {
        for (int s = 0; s < 2; s++) { memset(vis[s], 0, W * 8); memset(cur[s], 0, W * 8); }
        vis[start][e >> 6] |= 1ULL << (e & 63); cur[start][e >> 6] |= 1ULL << (e & 63);
        u64 reached[2] = {0, 0}; reached[start] = 1;
        int side = start, ecc = 0; u64 level[64]; int nlev = 1; level[0] = 1;
        u64 snap[2] = {reached[0], reached[1]};   /* reached counts after exactly D steps */
        for (int step = 1; step <= (full ? 60 : D); step++) {
            int ns = side ^ 1; u64 add = 0;
            memset(nxt[ns], 0, W * 8);
            const El *T = side == 0 ? S : SI;       /* (g,A) -> (s g, B);  (h,B) -> (s^-1 h, A) */
            u64 *cs = cur[side], *vs = vis[ns], *nx = nxt[ns];
#pragma omp parallel for schedule(dynamic, 256) reduction(+ : add)
            for (u64 w = 0; w < W; w++) {
                u64 bits = cs[w];
                while (bits) {
                    int bt = __builtin_ctzll(bits); bits &= bits - 1;
                    El g = dec_el(w * 64 + bt);
                    for (int a = 0; a < d; a++) {
                        u64 h = lmul_idx(&T[a], &g);
                        u64 m1 = 1ULL << (h & 63);
                        if (!(__atomic_load_n(&vs[h >> 6], __ATOMIC_RELAXED) & m1)) {
                            if (!(__atomic_fetch_or(&vs[h >> 6], m1, __ATOMIC_RELAXED) & m1)) { __atomic_fetch_or(&nx[h >> 6], m1, __ATOMIC_RELAXED); add++; }
                        }
                    }
                }
            }
            memset(cur[side], 0, W * 8); u64 *t = cur[ns]; cur[ns] = nxt[ns]; nxt[ns] = t;
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
    printf("%s d=%d D=%d group=%s N=%llu vertices=%llu (distinct generators, %d-regular simple; ", bad ? "INVALID" : "VALID", d, D,
           group_spec, (unsigned long long)N, (unsigned long long)(2 * N), d);
    if (bad) printf("%llu vertices unreached within D from the worse start", (unsigned long long)unreached_max);
    else printf("every vertex within %d of both (e,A) and (e,B); ecc %d", D, eccmax);
    if (full && bad) printf("; true ecc %d", eccmax);
    printf("; %.0fs)\n", now() - t0);
    return bad;
}
