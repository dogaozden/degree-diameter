/* bcd.c: bigcheck-dist, a checker whose BFS sources can be split into parts that run on different machines.
 *
 * Two kinds of input.
 *   explicit  an edge list (apsp.c text format "n" then "u v" lines, or the binary format below) plus optional
 *             automorphism generators (permutations, or "shift L B" level shifts as in apsp_orb.c). Each generator
 *             is checked edge by edge: a bijection of V that maps every edge to an edge is an automorphism.
 *   lift      a cyclic voltage lift: a base multigraph on NB vertices, each edge "u v a" giving the lift edges
 *             (u, g) ~ (v, g + a mod M) for all g in Z_M. Also "group sl P N" / "group psl P N": voltages in
 *             SL(2,P) x Z_N or PSL(2,P) x Z_N, edges "u v a b c d z" giving (u, g) ~ (v, s g), s = (mat(a,b,c,d), z)
 *             (a Haar graph H(G,S) is the lift of the dipole: base vertices 0 = A, 1 = B, one edge 0 1 s per s in S). Translations g -> g + h are automorphisms by definition.
 *             Optional base automorphisms "aut u pi(0..NB-1) c(0..NB-1)" stand for (v, g) -> (pi v, u g + c(v));
 *             each is checked on the base: for every base edge v -> w with voltage a there must be a base edge
 *             pi v -> pi w with voltage u a + c(w) - c(v), and degrees must match. The lift is never written out.
 *
 * The checker computes the orbits of the generated group on vertices (explicit) or on base vertices (lift),
 * takes the smallest vertex of each orbit as its representative (lift: (rep, 0)), sorts the representatives, and
 * runs a bit-parallel BFS (64 sources per pass, OpenMP over vertices inside each level) from the representatives
 * of one part: part i of K is the index range [floor(iR/K), floor((i+1)R/K)). Eccentricity is constant on
 * orbits, so the largest eccentricity over all representatives is the diameter. Each run writes a certificate
 * (sha256 of the inputs, graph statistics, orbit count, sha256 of the representative list, one line per source
 * with its eccentricity and number of unreached vertices). bcd_merge.py checks that a set of certificates covers
 * every representative exactly once, that all of them describe the same input, and prints the verdict.
 *
 * Checks done in every run: ids in range, no self-loops, no repeated edges (lift: no two base edges v -> w with the
 * same voltage), maximum degree, bipartite (explicit: 2-colouring of the graph; lift: 2-colouring of the base,
 * which colours the lift), automorphisms as above. Connectivity follows from the BFS reaching every vertex.
 *
 * Binary edge format: 8 bytes "BCDE1\0\0\0", uint64 n, uint64 m, then m pairs of uint32.
 * Binary automorphism format: 8 bytes "BCDA1\0\0\0", uint64 n, uint64 K, then K permutations of n uint32.
 * Text automorphism format: lines "perm x0 x1 ... x_{n-1}" or "shift L B".
 *
 * Usage:
 *   bcd explicit EDGES d D [--aut FILE] [--part i/K] [--threads T] [--cert FILE] [--reps FILE] [--count]
 *   bcd lift SPEC d D [--part i/K] [--threads T] [--cert FILE] [--reps FILE] [--count]
 * --cost stops every BFS after D levels, so "unreached" counts the vertices at distance > D (a search score; the
 * certificate is then marked by "cost_mode 1" and bcd_merge.py refuses it).
 * --count stops after the orbit computation (prints the number of representatives); --reps writes the sorted
 * representative list (one per line; its sha256 is the reps_sha256 in every certificate).
 * Build: cc -O3 -march=native -fopenmp -o bcd bcd.c
 */
#include <inttypes.h>
#include <omp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define VERSION "bcd 1.0"

static void die(const char *msg) { fprintf(stderr, "bcd: %s\n", msg); printf("RESULT ERROR %s\n", msg); exit(2); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* ------------------------------------------------------------------ sha256 */
typedef struct { uint32_t h[8]; uint64_t len; uint8_t buf[64]; int nb; } sha_t;
static const uint32_t K256[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5, 0xd807aa98,
    0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8,
    0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819,
    0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
    0xc67178f2};
#define ROR(x, n) (((x) >> (n)) | ((x) << (32 - (n))))
static void sha_block(sha_t *s, const uint8_t *p) {
    uint32_t w[64], a, b, c, d, e, f, g, h;
    for (int i = 0; i < 16; i++) w[i] = (uint32_t)p[4 * i] << 24 | (uint32_t)p[4 * i + 1] << 16 | (uint32_t)p[4 * i + 2] << 8 | p[4 * i + 3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = ROR(w[i - 15], 7) ^ ROR(w[i - 15], 18) ^ (w[i - 15] >> 3), s1 = ROR(w[i - 2], 17) ^ ROR(w[i - 2], 19) ^ (w[i - 2] >> 10);
        w[i] = w[i - 16] + s0 + w[i - 7] + s1;
    }
    a = s->h[0]; b = s->h[1]; c = s->h[2]; d = s->h[3]; e = s->h[4]; f = s->h[5]; g = s->h[6]; h = s->h[7];
    for (int i = 0; i < 64; i++) {
        uint32_t t1 = h + (ROR(e, 6) ^ ROR(e, 11) ^ ROR(e, 25)) + ((e & f) ^ (~e & g)) + K256[i] + w[i];
        uint32_t t2 = (ROR(a, 2) ^ ROR(a, 13) ^ ROR(a, 22)) + ((a & b) ^ (a & c) ^ (b & c));
        h = g; g = f; f = e; e = d + t1; d = c; c = b; b = a; a = t1 + t2;
    }
    s->h[0] += a; s->h[1] += b; s->h[2] += c; s->h[3] += d; s->h[4] += e; s->h[5] += f; s->h[6] += g; s->h[7] += h;
}
static void sha_init(sha_t *s) {
    static const uint32_t h0[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
    memcpy(s->h, h0, sizeof h0); s->len = 0; s->nb = 0;
}
static void sha_update(sha_t *s, const void *data, size_t n) {
    const uint8_t *p = data; s->len += n;
    if (s->nb) { while (n && s->nb < 64) { s->buf[s->nb++] = *p++; n--; } if (s->nb == 64) { sha_block(s, s->buf); s->nb = 0; } }
    while (n >= 64) { sha_block(s, p); p += 64; n -= 64; }
    while (n) { s->buf[s->nb++] = *p++; n--; }
}
static void sha_final(sha_t *s, char hex[65]) {
    uint64_t bits = s->len * 8; uint8_t pad = 0x80, z = 0, L[8];
    sha_update(s, &pad, 1); while (s->nb != 56) sha_update(s, &z, 1);
    for (int i = 0; i < 8; i++) L[i] = (uint8_t)(bits >> (56 - 8 * i));
    sha_update(s, L, 8);
    for (int i = 0; i < 8; i++) sprintf(hex + 8 * i, "%08x", s->h[i]);
    hex[64] = 0;
}

/* ------------------------------------------------------------------ token reader that hashes everything it reads */
typedef struct { FILE *f; uint8_t *buf; size_t n, i; sha_t sha; int eof; } rd_t;
#define RDBUF (1 << 22)
static void rd_open(rd_t *r, const char *path) {
    r->f = fopen(path, "rb"); if (!r->f) { fprintf(stderr, "cannot open %s\n", path); die("cannot open input"); }
    r->buf = malloc(RDBUF); r->n = r->i = 0; r->eof = 0; sha_init(&r->sha);
}
static int rd_fill(rd_t *r) {
    if (r->eof) return 0;
    r->n = fread(r->buf, 1, RDBUF, r->f); r->i = 0;
    if (r->n == 0) { r->eof = 1; return 0; }
    sha_update(&r->sha, r->buf, r->n); return 1;
}
static int rd_byte(rd_t *r) { if (r->i == r->n && !rd_fill(r)) return -1; return r->buf[r->i++]; }
static int rd_bytes(rd_t *r, void *dst, size_t n) {
    uint8_t *d = dst;
    while (n) { if (r->i == r->n && !rd_fill(r)) return 0; size_t k = r->n - r->i; if (k > n) k = n; memcpy(d, r->buf + r->i, k); r->i += k; d += k; n -= k; }
    return 1;
}
/* next whitespace-separated word into w (max len); returns length, 0 at end of file */
static int rd_word(rd_t *r, char *w, int max) {
    int c; do c = rd_byte(r); while (c == ' ' || c == '\n' || c == '\r' || c == '\t');
    if (c < 0) return 0;
    int k = 0; while (c >= 0 && c != ' ' && c != '\n' && c != '\r' && c != '\t') { if (k < max - 1) w[k++] = (char)c; c = rd_byte(r); }
    w[k] = 0; return k;
}
static int rd_long(rd_t *r, long long *x) {
    char w[64]; if (!rd_word(r, w, sizeof w)) return 0;
    char *e; *x = strtoll(w, &e, 10); if (*e) { fprintf(stderr, "not an integer: %s\n", w); die("bad integer in input"); }
    return 1;
}
static void rd_drain(rd_t *r) { while (rd_fill(r)) ; }
static void rd_close(rd_t *r, char hex[65]) { rd_drain(r); sha_final(&r->sha, hex); fclose(r->f); free(r->buf); }

/* ------------------------------------------------------------------ graph state */
static int MODE;            /* 0 explicit, 1 lift */
static int64_t n;           /* number of vertices (lift: NB * M) */
static int64_t m_edges;     /* number of edges */
/* explicit: CSR */
static int64_t *st; static uint32_t *adj;
/* lift: base CSR with voltages; lift neighbour of (v,g) along (w,a) is (w, g+a mod M) */
static int64_t NB, M; static int64_t *bst; static uint32_t *bw; static int64_t *ba;
/* matrix voltage groups: GK = 1 for SL(2,P) x Z_NC, 2 for PSL(2,P) x Z_NC (P an odd prime for PSL); elements are
   indexed as in research/frontier/haarcheck_sl.c (c-keyed), lift edge (u, g) ~ (v, s g) for a base edge u -> v with
   voltage s (left multiplication), so right multiplications are automorphisms and one source per base vertex suffices */
static int GK = 0; static int64_t GP, GNC, GPP; static int64_t *GINV;
typedef struct { int64_t a, b, c, d, z; } gel;
static int64_t gmd(int64_t x) { x %= GP; return x < 0 ? x + GP : x; }
static gel gcanon(gel e) {
    if (GK == 2) { int neg = e.c ? (e.c > (GP - 1) / 2) : (e.a > (GP - 1) / 2);
        if (neg) { e.a = gmd(-e.a); e.b = gmd(-e.b); e.c = gmd(-e.c); e.d = gmd(-e.d); } }
    return e;
}
static int64_t genc(gel e) {
    e = gcanon(e); int64_t k;
    int64_t cmax = GK == 2 ? (GP - 1) / 2 : GP - 1;
    if (e.c) k = ((e.c - 1) * GP + e.a) * GP + e.d; else k = cmax * GPP + (e.a - 1) * GP + e.b;
    return k * GNC + e.z;
}
static gel gdec(int64_t g) {
    gel e; e.z = g % GNC; int64_t k = g / GNC, cmax = GK == 2 ? (GP - 1) / 2 : GP - 1;
    if (k < cmax * GPP) { e.c = k / GPP + 1; e.a = k / GP % GP; e.d = k % GP; e.b = gmd(gmd(e.a * e.d - 1) * GINV[e.c]); }
    else { k -= cmax * GPP; e.c = 0; e.a = k / GP + 1; e.b = k % GP; e.d = GINV[e.a]; }
    return e;
}
static gel gmul(gel s, gel g) {
    gel r = {gmd(s.a * g.a + s.b * g.c), gmd(s.a * g.b + s.b * g.d), gmd(s.c * g.a + s.d * g.c), gmd(s.c * g.b + s.d * g.d), (s.z + g.z) % GNC};
    return r;
}
static gel ginv(gel e) { gel r = {e.d, gmd(-e.b), gmd(-e.c), e.a, (GNC - e.z) % GNC}; return r; }
static gel *bsel; /* voltage of each base adjacency slot as a matrix (matrix groups) */

static int cmp_u32(const void *a, const void *b) { uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b; return x < y ? -1 : x > y; }
static int cmp_u64(const void *a, const void *b) { uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y; }
static int has_edge(int64_t u, uint32_t v) {
    int64_t lo = st[u], hi = st[u + 1] - 1;
    while (lo <= hi) { int64_t mid = (lo + hi) / 2; if (adj[mid] == v) return 1; if (adj[mid] < v) lo = mid + 1; else hi = mid - 1; }
    return 0;
}

static int64_t maxdeg, mindeg; static int bip;

static void load_explicit(const char *path, char hex[65]) {
    rd_t r; rd_open(&r, path);
    uint8_t mg[8]; uint32_t *U, *W;
    int c0 = rd_byte(&r);
    if (c0 == 'B') {
        mg[0] = 'B'; if (!rd_bytes(&r, mg + 1, 7) || memcmp(mg, "BCDE1\0\0\0", 8)) die("bad binary edge header");
        uint64_t nn, mm; if (!rd_bytes(&r, &nn, 8) || !rd_bytes(&r, &mm, 8)) die("short binary header");
        n = (int64_t)nn; m_edges = (int64_t)mm;
        U = malloc(sizeof(uint32_t) * m_edges); W = malloc(sizeof(uint32_t) * m_edges);
        uint32_t pr[2];
        for (int64_t i = 0; i < m_edges; i++) { if (!rd_bytes(&r, pr, 8)) die("short binary edge list"); U[i] = pr[0]; W[i] = pr[1]; }
        if (rd_byte(&r) >= 0) die("trailing bytes after binary edge list");
    } else {
        r.i--; /* unread */
        long long nn; if (!rd_long(&r, &nn)) die("empty edge file"); n = nn;
        int64_t cap = 1 << 20; m_edges = 0; U = malloc(4 * cap); W = malloc(4 * cap);
        long long a, b;
        while (rd_long(&r, &a)) {
            if (!rd_long(&r, &b)) die("odd number of endpoints");
            if (a < 0 || b < 0 || a >= n || b >= n) die("vertex id out of range");
            if (m_edges == cap) { cap *= 2; U = realloc(U, 4 * cap); W = realloc(W, 4 * cap); }
            U[m_edges] = (uint32_t)a; W[m_edges] = (uint32_t)b; m_edges++;
        }
    }
    rd_close(&r, hex);
    if (n <= 0 || n > 4000000000LL) die("n out of range (1 .. 4e9)");
    int64_t *deg = calloc(n + 1, 8);
    for (int64_t i = 0; i < m_edges; i++) {
        if (U[i] >= n || W[i] >= n) die("vertex id out of range");
        if (U[i] == W[i]) die("self-loop");
        deg[U[i]]++; deg[W[i]]++;
    }
    st = malloc(8 * (n + 1)); st[0] = 0; for (int64_t i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    adj = malloc(sizeof(uint32_t) * 2 * m_edges);
    memset(deg, 0, 8 * (n + 1));
    for (int64_t i = 0; i < m_edges; i++) { adj[st[U[i]] + deg[U[i]]++] = W[i]; adj[st[W[i]] + deg[W[i]]++] = U[i]; }
    free(U); free(W); free(deg);
    maxdeg = 0; mindeg = INT64_MAX; int dup = 0;
#pragma omp parallel for schedule(dynamic, 4096) reduction(max : maxdeg) reduction(min : mindeg) reduction(| : dup)
    for (int64_t x = 0; x < n; x++) {
        int64_t k = st[x + 1] - st[x]; if (k > maxdeg) maxdeg = k; if (k < mindeg) mindeg = k;
        qsort(adj + st[x], k, sizeof(uint32_t), cmp_u32);
        for (int64_t i = st[x] + 1; i < st[x + 1]; i++) if (adj[i] == adj[i - 1]) dup = 1;
    }
    if (dup) die("repeated edge");
    /* bipartite: 2-colour every component */
    int8_t *col = malloc(n); memset(col, -1, n); uint32_t *qq = malloc(sizeof(uint32_t) * n); bip = 1;
    for (int64_t s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        int64_t h = 0, t = 0; col[s] = 0; qq[t++] = (uint32_t)s;
        while (h < t) { uint32_t x = qq[h++]; for (int64_t i = st[x]; i < st[x + 1]; i++) { uint32_t y = adj[i]; if (col[y] < 0) { col[y] = 1 - col[x]; qq[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    }
    free(col); free(qq);
}

/* ------------------------------------------------------------------ automorphisms and orbits */
static uint32_t *uf;
static uint32_t uf_find(uint32_t x) { while (uf[x] != x) { uf[x] = uf[uf[x]]; x = uf[x]; } return x; }
static void uf_union(uint32_t a, uint32_t b) { a = uf_find(a); b = uf_find(b); if (a == b) return; if (a < b) uf[b] = a; else uf[a] = b; }
static int nauts;

static void check_perm_bijection(const uint32_t *p, int64_t len) {
    uint8_t *seen = calloc(len, 1);
    for (int64_t i = 0; i < len; i++) { if (p[i] >= len || seen[p[i]]) die("automorphism is not a permutation"); seen[p[i]] = 1; }
    free(seen);
}
/* explicit: check that p maps every edge to an edge, then merge orbits */
static void use_perm_explicit(const uint32_t *p) {
    check_perm_bijection(p, n);
    int bad = 0;
#pragma omp parallel for schedule(dynamic, 4096) reduction(| : bad)
    for (int64_t x = 0; x < n; x++)
        for (int64_t i = st[x]; i < st[x + 1]; i++) if (adj[i] > x && !has_edge(p[x], p[adj[i]])) bad = 1;
    if (bad) die("a generator is not an automorphism");
    for (int64_t x = 0; x < n; x++) uf_union((uint32_t)x, p[x]);
    nauts++;
}
static void load_auts_explicit(const char *path, char hex[65]) {
    rd_t r; rd_open(&r, path);
    uint32_t *p = malloc(sizeof(uint32_t) * n);
    int c0 = rd_byte(&r);
    if (c0 == 'B') {
        uint8_t mg[8]; mg[0] = 'B'; if (!rd_bytes(&r, mg + 1, 7) || memcmp(mg, "BCDA1\0\0\0", 8)) die("bad binary automorphism header");
        uint64_t nn, kk; if (!rd_bytes(&r, &nn, 8) || !rd_bytes(&r, &kk, 8)) die("short automorphism header");
        if ((int64_t)nn != n) die("automorphism file has the wrong n");
        for (uint64_t k = 0; k < kk; k++) { if (!rd_bytes(&r, p, sizeof(uint32_t) * n)) die("short automorphism file"); use_perm_explicit(p); }
        if (rd_byte(&r) >= 0) die("trailing bytes after automorphisms");
    } else {
        r.i--; char w[64];
        while (rd_word(&r, w, sizeof w)) {
            if (!strcmp(w, "perm")) {
                for (int64_t i = 0; i < n; i++) { long long x; if (!rd_long(&r, &x)) die("short perm"); if (x < 0 || x >= n) die("perm entry out of range"); p[i] = (uint32_t)x; }
            } else if (!strcmp(w, "shift")) {
                long long L, B; if (!rd_long(&r, &L) || !rd_long(&r, &B)) die("shift needs L B");
                if (L < 1 || B < 1 || L * B > n) die("bad shift layout");
                for (int64_t i = 0; i < n; i++) p[i] = (uint32_t)(i < L * B ? (i + B) % (L * B) : i);
            } else die("automorphism lines start with perm or shift");
            use_perm_explicit(p);
        }
    }
    free(p); rd_close(&r, hex);
}

static void load_lift(const char *path, char hex[65]) {
    rd_t r; rd_open(&r, path); char w[64]; long long x;
    if (!rd_word(&r, w, sizeof w) || strcmp(w, "bcd-lift")) die("lift spec must start with bcd-lift 1");
    if (!rd_long(&r, &x) || x != 1) die("lift spec version must be 1");
    if (!rd_word(&r, w, sizeof w) || strcmp(w, "group")) die("expected: group cyclic M | group sl P N | group psl P N");
    if (!rd_word(&r, w, sizeof w)) die("missing group kind");
    if (!strcmp(w, "cyclic")) { if (!rd_long(&r, &x) || x < 1) die("bad M"); M = x; }
    else if (!strcmp(w, "sl") || !strcmp(w, "psl")) {
        GK = strcmp(w, "sl") ? 2 : 1;
        if (!rd_long(&r, &x) || x < 2) die("bad P"); GP = x;
        for (int64_t t = 2; t * t <= GP; t++) if (GP % t == 0) die("P must be prime");
        if (GK == 2 && GP == 2) die("psl needs an odd prime");
        if (!rd_long(&r, &x) || x < 1) die("bad N"); GNC = x;
        GPP = GP * GP; M = GP * (GPP - 1) / (GK == 2 ? 2 : 1) * GNC;
        GINV = malloc(8 * GP); GINV[0] = 0;
        for (int64_t a = 1; a < GP; a++) { int64_t rr = 1, e = GP - 2, bb = a; while (e) { if (e & 1) rr = rr * bb % GP; bb = bb * bb % GP; e >>= 1; } GINV[a] = rr; }
        for (int64_t g = 0; g < M; g += M / 4096 + 1) { gel e = gdec(g); if (gmd(e.a * e.d - e.b * e.c) != 1 || genc(e) != g) die("group index self-test failed"); }
    } else die("group kind must be cyclic, sl or psl");
    if (!rd_word(&r, w, sizeof w) || strcmp(w, "vertices")) die("expected: vertices NB");
    if (!rd_long(&r, &x) || x < 1) die("bad NB");
    NB = x;
    if (!rd_word(&r, w, sizeof w) || strcmp(w, "edges")) die("expected: edges E");
    long long E; if (!rd_long(&r, &E) || E < 0) die("bad E");
    if ((double)NB * (double)M > 4.0e9) die("lift too large for 32-bit vertex ids in this version");
    n = NB * M; m_edges = E * M;
    int64_t *eu = malloc(8 * E), *ev = malloc(8 * E), *ea = malloc(8 * E), *eia = malloc(8 * E);
    for (long long i = 0; i < E; i++) {
        long long u, v, a;
        if (!rd_long(&r, &u) || !rd_long(&r, &v)) die("short edge list");
        if (GK == 0) { if (!rd_long(&r, &a)) die("short edge list"); }
        else {
            long long m4[5]; for (int t = 0; t < 5; t++) if (!rd_long(&r, &m4[t])) die("short edge list (u v a b c d z)");
            gel e = {gmd(m4[0]), gmd(m4[1]), gmd(m4[2]), gmd(m4[3]), ((m4[4] % GNC) + GNC) % GNC};
            if (gmd(e.a * e.d - e.b * e.c) != 1) die("voltage matrix does not have determinant 1");
            a = genc(e); eia[i] = genc(ginv(e));
        }
        if (u < 0 || v < 0 || u >= NB || v >= NB) die("base vertex out of range");
        if (u == v) die("base loop (the lift would not be bipartite)");
        eu[i] = u; ev[i] = v; ea[i] = GK ? a : ((a % M) + M) % M;
    }
    int64_t *deg = calloc(NB + 1, 8);
    for (long long i = 0; i < E; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    bst = malloc(8 * (NB + 1)); bst[0] = 0; for (int64_t i = 0; i < NB; i++) bst[i + 1] = bst[i] + deg[i];
    bw = malloc(sizeof(uint32_t) * 2 * E); ba = malloc(8 * 2 * E); memset(deg, 0, 8 * (NB + 1));
    for (long long i = 0; i < E; i++) {
        int64_t u = eu[i], v = ev[i];
        bw[bst[u] + deg[u]] = (uint32_t)v; ba[bst[u] + deg[u]++] = ea[i];
        bw[bst[v] + deg[v]] = (uint32_t)u; ba[bst[v] + deg[v]++] = GK ? eia[i] : (M - ea[i]) % M;
    }
    free(eu); free(ev); free(ea); free(eia); free(deg);
    /* sort each base adjacency by (w, a); repeated (w, a) = repeated lift edge */
    uint64_t *key = malloc(8 * 2 * (E ? E : 1));
    maxdeg = 0; mindeg = INT64_MAX;
    for (int64_t v = 0; v < NB; v++) {
        int64_t k = bst[v + 1] - bst[v]; if (k > maxdeg) maxdeg = k; if (k < mindeg) mindeg = k;
        for (int64_t i = 0; i < k; i++) key[i] = (uint64_t)bw[bst[v] + i] * (uint64_t)M + (uint64_t)ba[bst[v] + i];
        qsort(key, k, 8, cmp_u64);
        for (int64_t i = 0; i < k; i++) { bw[bst[v] + i] = (uint32_t)(key[i] / M); ba[bst[v] + i] = (int64_t)(key[i] % M); if (i && key[i] == key[i - 1]) die("repeated lift edge (two base edges with the same ends and voltage)"); }
    }
    if (GK) { bsel = malloc(sizeof(gel) * (2 * E ? 2 * E : 1)); for (int64_t i = 0; i < 2 * E; i++) bsel[i] = gdec(ba[i]); }
    /* bipartite base */
    int8_t *col = malloc(NB); memset(col, -1, NB); uint32_t *qq = malloc(sizeof(uint32_t) * NB); bip = 1;
    for (int64_t s = 0; s < NB; s++) {
        if (col[s] >= 0) continue;
        int64_t h = 0, t = 0; col[s] = 0; qq[t++] = (uint32_t)s;
        while (h < t) { uint32_t y0 = qq[h++]; for (int64_t i = bst[y0]; i < bst[y0 + 1]; i++) { uint32_t y = bw[i]; if (col[y] < 0) { col[y] = 1 - col[y0]; qq[t++] = y; } else if (col[y] == col[y0]) bip = 0; } }
    }
    free(col); free(qq);
    /* base automorphisms */
    uf = malloc(sizeof(uint32_t) * NB); for (int64_t i = 0; i < NB; i++) uf[i] = (uint32_t)i;
    uint32_t *p = malloc(sizeof(uint32_t) * NB); int64_t *c = malloc(8 * NB);
    while (rd_word(&r, w, sizeof w)) {
        if (!strcmp(w, "end")) break;
        if (strcmp(w, "aut")) die("expected aut or end after the edges");
        if (GK) die("base automorphisms are only supported for cyclic groups");
        long long u; if (!rd_long(&r, &u)) die("aut needs a unit");
        u = ((u % M) + M) % M;
        { long long a = u, b = M; while (b) { long long t = a % b; a = b; b = t; } if (a != 1) die("aut multiplier is not a unit mod M"); }
        for (int64_t i = 0; i < NB; i++) { if (!rd_long(&r, &x) || x < 0 || x >= NB) die("bad aut permutation"); p[i] = (uint32_t)x; }
        for (int64_t i = 0; i < NB; i++) { if (!rd_long(&r, &x)) die("bad aut offsets"); c[i] = ((x % M) + M) % M; }
        check_perm_bijection(p, NB);
        for (int64_t v = 0; v < NB; v++) {
            int64_t pv = p[v];
            if (bst[pv + 1] - bst[pv] != bst[v + 1] - bst[v]) die("lifted automorphism check failed (degree)");
            for (int64_t i = bst[v]; i < bst[v + 1]; i++) {
                uint32_t wv = bw[i]; int64_t img_a = (int64_t)(((__int128)u * ba[i] + c[wv] - c[v]) % M); img_a = (img_a + M) % M;
                uint32_t pw = p[wv]; int64_t lo = bst[pv], hi = bst[pv + 1] - 1, found = 0;
                uint64_t want = (uint64_t)pw * (uint64_t)M + (uint64_t)img_a;
                while (lo <= hi) { int64_t mid = (lo + hi) / 2; uint64_t kk = (uint64_t)bw[mid] * (uint64_t)M + (uint64_t)ba[mid]; if (kk == want) { found = 1; break; } if (kk < want) lo = mid + 1; else hi = mid - 1; }
                if (!found) die("lifted automorphism check failed (edge not mapped to an edge)");
            }
        }
        for (int64_t v = 0; v < NB; v++) uf_union((uint32_t)v, p[v]);
        nauts++;
    }
    free(p); free(c); free(key);
    rd_close(&r, hex);
}

/* ------------------------------------------------------------------ BFS (WB sources per pass)
 * Compile with -DWB=8, 16 or 32 to use narrower words: 3·WB/8 bytes per vertex instead of 24, WB sources per pass.
 * The certificates do not depend on WB. */
#ifndef WB
#define WB 64
#endif
#if WB == 64
typedef uint64_t W_T;
#elif WB == 32
typedef uint32_t W_T;
#elif WB == 16
typedef uint16_t W_T;
#elif WB == 8
typedef uint8_t W_T;
#else
#error "WB must be 8, 16, 32 or 64"
#endif
static W_T *VIS, *FR, *NX;
static void pull_explicit(uint64_t *anyp) {
    uint64_t any = 0;
#pragma omp parallel for schedule(dynamic, 8192) reduction(| : any)
    for (int64_t x = 0; x < n; x++) {
        W_T acc = 0; for (int64_t i = st[x]; i < st[x + 1]; i++) acc |= FR[adj[i]];
        acc &= (W_T)~VIS[x]; NX[x] = acc; any |= acc;
    }
    *anyp = any;
}
static void pull_lift_mat(uint64_t *anyp) {
    uint64_t any = 0;
    const int64_t CH = 4096; int64_t nch = (M + CH - 1) / CH, tasks = NB * nch;
#pragma omp parallel for schedule(dynamic, 1) reduction(| : any)
    for (int64_t t = 0; t < tasks; t++) {
        int64_t v = t / nch, g0 = (t % nch) * CH, g1 = g0 + CH < M ? g0 + CH : M;
        W_T *out = NX + v * M; const W_T *vis = VIS + v * M;
        for (int64_t g = g0; g < g1; g++) {
            gel e = gdec(g); W_T acc = 0;
            for (int64_t i = bst[v]; i < bst[v + 1]; i++) acc |= FR[(int64_t)bw[i] * M + genc(gmul(bsel[i], e))];
            acc &= (W_T)~vis[g]; out[g] = acc; any |= acc;
        }
    }
    *anyp = any;
}
static void pull_lift(uint64_t *anyp) {
    if (GK) { pull_lift_mat(anyp); return; }
    uint64_t any = 0;
    const int64_t CH = 16384; int64_t nch = (M + CH - 1) / CH, tasks = NB * nch;
#pragma omp parallel for schedule(dynamic, 1) reduction(| : any)
    for (int64_t t = 0; t < tasks; t++) {
        int64_t v = t / nch, g0 = (t % nch) * CH, g1 = g0 + CH < M ? g0 + CH : M;
        W_T *out = NX + v * M;
        for (int64_t g = g0; g < g1; g++) out[g] = 0;
        for (int64_t i = bst[v]; i < bst[v + 1]; i++) {
            const W_T *src = FR + (int64_t)bw[i] * M; int64_t a = ba[i];
            /* out[g] |= src[(g + a) mod M] for g in [g0, g1) */
            int64_t split = M - a; /* g < split: g + a; else g + a - M */
            int64_t e1 = g1 < split ? g1 : split;
            for (int64_t g = g0; g < e1; g++) out[g] |= src[g + a];
            for (int64_t g = (g0 > split ? g0 : split); g < g1; g++) out[g] |= src[g + a - M];
        }
        const W_T *vis = VIS + v * M;
        for (int64_t g = g0; g < g1; g++) { out[g] &= (W_T)~vis[g]; any |= out[g]; }
    }
    *anyp = any;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: bcd explicit EDGES d D [--aut FILE] [--part i/K] [--threads T] [--cert FILE] [--reps FILE] [--count]\n"
                        "       bcd lift SPEC d D [--part i/K] [--threads T] [--cert FILE] [--reps FILE] [--count]\n");
        return 2;
    }
    double t0 = now();
    if (!strcmp(argv[1], "explicit")) MODE = 0; else if (!strcmp(argv[1], "lift")) MODE = 1; else die("mode must be explicit or lift");
    const char *inpath = argv[2]; int dmax = atoi(argv[3]), DD = atoi(argv[4]);
    const char *autpath = NULL, *certpath = NULL, *repspath = NULL; int64_t part = 0, K = 1; int count_only = 0, cost_mode = 0;
    for (int i = 5; i < argc; i++) {
        if (!strcmp(argv[i], "--aut") && i + 1 < argc) autpath = argv[++i];
        else if (!strcmp(argv[i], "--part") && i + 1 < argc) { if (sscanf(argv[++i], "%" SCNd64 "/%" SCNd64, &part, &K) != 2 || K < 1 || part < 0 || part >= K) die("bad --part i/K"); }
        else if (!strcmp(argv[i], "--threads") && i + 1 < argc) omp_set_num_threads(atoi(argv[++i]));
        else if (!strcmp(argv[i], "--cert") && i + 1 < argc) certpath = argv[++i];
        else if (!strcmp(argv[i], "--reps") && i + 1 < argc) repspath = argv[++i];
        else if (!strcmp(argv[i], "--count")) count_only = 1;
        else if (!strcmp(argv[i], "--cost")) cost_mode = 1;
        else die("unknown option");
    }
    if (MODE == 1 && autpath) die("--aut is for explicit mode; lift automorphisms go in the spec");
    char inhex[65], authex[65] = "none";
    if (MODE == 0) {
        load_explicit(inpath, inhex);
        uf = malloc(sizeof(uint32_t) * n); for (int64_t i = 0; i < n; i++) uf[i] = (uint32_t)i;
        if (autpath) load_auts_explicit(autpath, authex);
    } else load_lift(inpath, inhex);
    double t1 = now();
    /* representatives */
    int64_t nb = MODE ? NB : n, R = 0;
    for (int64_t i = 0; i < nb; i++) if (uf_find((uint32_t)i) == i) R++;
    uint32_t *reps = malloc(sizeof(uint32_t) * (R ? R : 1)); R = 0;
    for (int64_t i = 0; i < nb; i++) if (uf_find((uint32_t)i) == i) reps[R++] = (uint32_t)i;
    sha_t rs; sha_init(&rs); char line[64], repshex[65];
    FILE *rf = repspath ? fopen(repspath, "w") : NULL;
    for (int64_t i = 0; i < R; i++) { int l = sprintf(line, "%u\n", reps[i]); sha_update(&rs, line, l); if (rf) fputs(line, rf); }
    if (rf) fclose(rf);
    sha_final(&rs, repshex);
    int64_t lo = part * R / K, hi = (part + 1) * R / K;
    printf("%s mode %s input %s sha256 %s\n", VERSION, MODE ? "lift" : "explicit", inpath, inhex);
    if (MODE == 0) printf("automorphisms %s sha256 %s (%d generators, each checked edge by edge)\n", autpath ? autpath : "none", authex, nauts);
    else if (GK) printf("lift: group %s(2,%" PRId64 ") x Z_%" PRId64 " (order %" PRId64 ", left multiplication), base %" PRId64 " vertices\n", GK == 1 ? "SL" : "PSL", GP, GNC, M, NB);
    else printf("lift: group Z_%" PRId64 ", base %" PRId64 " vertices, %d base automorphisms checked on the base\n", M, NB, nauts);
    printf("n=%" PRId64 " edges=%" PRId64 " degree min=%" PRId64 " max=%" PRId64 " bipartite=%s\n", n, m_edges, mindeg, maxdeg, bip ? "yes" : "no");
    printf("orbits %" PRId64 " (representatives sha256 %s); part %" PRId64 "/%" PRId64 " = representatives [%" PRId64 ", %" PRId64 ")  [%.1fs]\n", R, repshex, part, K, lo, hi, t1 - t0);
    fflush(stdout);
    if (count_only) return 0;
    FILE *cf = certpath ? fopen(certpath, "w") : NULL;
    if (certpath && !cf) die("cannot write certificate");
    if (cf) {
        fprintf(cf, "bcd-cert 1\nversion %s\nmode %s\ninput_sha256 %s\naut_sha256 %s\nnauts %d\n", VERSION, MODE ? "lift" : "explicit", inhex, authex, nauts);
        if (MODE) fprintf(cf, "lift M %" PRId64 " NB %" PRId64 "%s\n", M, NB, GK == 1 ? " sl" : GK == 2 ? " psl" : "");
        fprintf(cf, "n %" PRId64 "\nedges %" PRId64 "\nmindeg %" PRId64 "\nmaxdeg %" PRId64 "\nbipartite %s\nd %d\nD %d\n", n, m_edges, mindeg, maxdeg, bip ? "yes" : "no", dmax, DD);
        if (cost_mode) fprintf(cf, "cost_mode 1\n");
        fprintf(cf, "orbits %" PRId64 "\nreps_sha256 %s\npart %" PRId64 " %" PRId64 " %" PRId64 " %" PRId64 "\n", R, repshex, part, K, lo, hi);
        fflush(cf);
    }
    VIS = malloc(sizeof(W_T) * n); FR = malloc(sizeof(W_T) * n); NX = malloc(sizeof(W_T) * n);
    if (!VIS || !FR || !NX) die("out of memory for the BFS arrays (3 words per vertex)");
    int part_max = 0; int64_t part_unreached = 0;
    for (int64_t b0 = lo; b0 < hi; b0 += WB) {
        int ns = hi - b0 < WB ? (int)(hi - b0) : WB; W_T full = ns == WB ? (W_T)~(W_T)0 : (W_T)((1ULL << ns) - 1);
        double tb = now();
        memset(VIS, 0, sizeof(W_T) * n); memset(FR, 0, sizeof(W_T) * n);
        for (int k = 0; k < ns; k++) { int64_t s = MODE ? (int64_t)reps[b0 + k] * M : (int64_t)reps[b0 + k]; VIS[s] |= (W_T)1 << k; FR[s] |= (W_T)1 << k; }
        int ecc[64] = {0}, lev = 0;
        for (;;) {
            uint64_t any; if (MODE) pull_lift(&any); else pull_explicit(&any);
            if (!any) break;
            lev++; for (int k = 0; k < ns; k++) if (any >> k & 1) ecc[k] = lev;
#pragma omp parallel for schedule(static)
            for (int64_t x = 0; x < n; x++) VIS[x] |= NX[x];
            W_T *tmp = FR; FR = NX; NX = tmp;
            if (cost_mode && lev == DD) break; /* --cost: unreached = vertices at distance > D */
            if (lev > DD + 2) break; /* already too far; the unreached count below is then a lower bound */
        }
        int64_t un[64] = {0}; int anyun = 0;
#pragma omp parallel for schedule(static) reduction(| : anyun)
        for (int64_t x = 0; x < n; x++) if (VIS[x] != full) anyun = 1;
        if (anyun) for (int64_t x = 0; x < n; x++) { uint64_t z = (uint64_t)(W_T)(~VIS[x] & full); while (z) { un[__builtin_ctzll(z)]++; z &= z - 1; } }
        for (int k = 0; k < ns; k++) {
            if (ecc[k] > part_max) part_max = ecc[k];
            part_unreached += un[k];
            if (cf) fprintf(cf, "src %u ecc %d unreached %" PRId64 "\n", reps[b0 + k], ecc[k], un[k]);
        }
        if (cf) fflush(cf);
        fprintf(stderr, "batch %" PRId64 "-%" PRId64 " of [%" PRId64 ",%" PRId64 "): levels %d, max ecc so far %d, unreached %" PRId64 " [%.1fs]\n", b0, b0 + ns, lo, hi, lev, part_max, part_unreached, now() - tb);
    }
    int ok = part_unreached == 0 && part_max <= DD;
    if (cf) { fprintf(cf, "part_max_ecc %d\npart_unreached %" PRId64 "\npart_status %s\nend\n", part_max, part_unreached, ok ? "OK" : "FAIL"); fclose(cf); }
    printf("part %" PRId64 "/%" PRId64 ": %" PRId64 " sources, max eccentricity %d, unreached %" PRId64 "  [%.1fs]\n", part, K, hi - lo, part_max, part_unreached, now() - t0);
    if (cost_mode) { printf("COST %" PRId64 " (pairs (source, vertex) at distance > %d, summed over the %" PRId64 " sources of this part)\n", part_unreached, DD, hi - lo); return 0; }
    if (K == 1) {
        int valid = ok && bip && maxdeg <= dmax;
        printf("diameter=%d (all %" PRId64 " orbit representatives)\n", part_unreached ? -1 : part_max, R);
        printf(valid ? "RESULT VALID d=%d D=%d n=%" PRId64 "\n" : "RESULT INVALID d=%d D=%d n=%" PRId64 "\n", dmax, DD, n);
        return valid ? 0 : 1;
    }
    printf("PART %s (merge all %" PRId64 " parts with bcd_merge.py for the verdict)\n", ok ? "OK" : "FAIL", K);
    return ok ? 0 : 1;
}
