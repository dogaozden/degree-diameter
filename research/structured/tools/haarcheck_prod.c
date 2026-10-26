/* haarcheck_prod: independent low-memory diameter check of a Haar graph H(G,S), G = SL(2,p1) x SL(2,p2) x Z_n,
 * p1, p2 prime (the product case that haarcheck_sl and haarcheck_psl do not cover).
 * Reads a haar_sym / haar_gen3 solution file with header "d D prod sl p1 sl p2 n n N NN" and d lines
 * "<idx> prod[mat(a,b,c,d);mat(a,b,c,d)] z=Z" (only the matrices and z are used).
 * Vertices (g,A),(g,B); edges (g,A) ~ (s g,B) for s in S. Right multiplication by G is transitive on each side, so
 * BFS from (e,A) and from (e,B) gives the exact diameter. Own element indexing: a dense table over all p^4 integer
 * quadruples per factor (no closed-form index), element index = (k1 * |SL(p2)| + k2) * n + z.
 * Memory: 4 bitsets of N bits plus the tables. Build: cc -O3 -march=native -o haarcheck_prod haarcheck_prod.c
 * Usage: haarcheck_prod SOL.txt */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { long long a, b, c, d; } M;
typedef struct { M x, y; long long z; } El;          /* one element of SL x SL x Z_n */

static long long P[2], K[2], n, N;
static int *IDX[2];                                  /* IDX[t][code(M)] = index of M in SL(2,P[t]), or -1 */
static M *MAT[2];                                    /* MAT[t][k] = the matrix with index k */

static long long md(long long x, long long p) { x %= p; return x < 0 ? x + p : x; }
static long long code(int t, M m) {
    long long p = P[t];
    return ((m.a * p + m.b) * p + m.c) * p + m.d;
}
static M mul(M x, M y, long long p) {
    M r = { md(x.a * y.a + x.b * y.c, p), md(x.a * y.b + x.b * y.d, p),
            md(x.c * y.a + x.d * y.c, p), md(x.c * y.b + x.d * y.d, p) };
    return r;
}
static M inv(M x, long long p) {                     /* inverse of a det-1 matrix */
    M r = { x.d, md(-x.b, p), md(-x.c, p), x.a };
    (void)p;
    return r;
}
static void build(int t) {
    long long p = P[t], cells = p * p * p * p, cnt = p * (p * p - 1), k = 0;
    IDX[t] = malloc(sizeof(int) * cells);
    MAT[t] = malloc(sizeof(M) * cnt);
    for (long long i = 0; i < cells; i++) IDX[t][i] = -1;
    for (long long a = 0; a < p; a++) for (long long b = 0; b < p; b++)
        for (long long c = 0; c < p; c++) for (long long d = 0; d < p; d++)
            if (md(a * d - b * c, p) == 1) {
                M m = { a, b, c, d };
                IDX[t][code(t, m)] = (int)k; MAT[t][k] = m; k++;
            }
    if (k != cnt) { fprintf(stderr, "|SL(2,%lld)| = %lld, expected %lld\n", p, k, cnt); exit(2); }
    K[t] = cnt;
}
static long long encode(M x, M y, long long z) {    /* index of (x, y, z); x, y must lie in the groups */
    long long k1 = IDX[0][code(0, x)], k2 = IDX[1][code(1, y)];
    if (k1 < 0 || k2 < 0 || z < 0 || z >= n) { fprintf(stderr, "product left the group\n"); exit(3); }
    return (k1 * K[1] + k2) * n + z;
}
static El decode(long long g) {
    El e;
    e.z = g % n;
    long long r = g / n;
    e.y = MAT[1][r % K[1]];
    e.x = MAT[0][r / K[1]];
    return e;
}
static int parse_mat(const char *s, M *m, long long p) {
    if (sscanf(s, "mat(%lld,%lld,%lld,%lld)", &m->a, &m->b, &m->c, &m->d) != 4) return 0;
    if (m->a < 0 || m->a >= p || m->b < 0 || m->b >= p || m->c < 0 || m->c >= p || m->d < 0 || m->d >= p) return 0;
    return md(m->a * m->d - m->b * m->c, p) == 1;
}
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haarcheck_prod SOL.txt\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    int dg, D; long long NN;
    if (sscanf(line, "%d %d prod sl %lld sl %lld n %lld N %lld", &dg, &D, &P[0], &P[1], &n, &NN) != 6) {
        fprintf(stderr, "only 'prod sl p1 sl p2 n n N' headers: %s", line); return 2; }
    for (int t = 0; t < 2; t++)
        for (long long q = 2; q * q <= P[t]; q++) if (P[t] % q == 0) { fprintf(stderr, "p not prime\n"); return 2; }
    build(0); build(1);
    N = K[0] * K[1] * n;
    if (N != NN) { fprintf(stderr, "header N %lld != |G| = %lld\n", NN, N); return 2; }
    El S[64]; int k = 0;
    while (fgets(line, sizeof line, f) && k < 64) {
        char *m = strstr(line, "prod[mat("), *zz = strstr(line, "z=");
        if (!m || !zz) continue;
        char *m2 = strstr(m, ";mat(");
        if (!m2) { fprintf(stderr, "bad element: %s", line); return 2; }
        *m2 = 0; m2 += 1;                          /* m -> "prod[mat(...)", m2 -> "mat(...)] z=..." */
        El e;
        if (!parse_mat(m + 5, &e.x, P[0]) || !parse_mat(m2, &e.y, P[1]) || sscanf(zz, "z=%lld", &e.z) != 1
            || e.z < 0 || e.z >= n) { fprintf(stderr, "bad element: %s", line); return 2; }
        S[k++] = e;
    }
    if (k != dg) { fprintf(stderr, "read %d elements, expected %d\n", k, dg); return 2; }
    for (int i = 0; i < k; i++) for (int j = 0; j < i; j++)
        if (!memcmp(&S[i], &S[j], sizeof(El))) { fprintf(stderr, "repeated generator %d %d\n", i, j); return 2; }
    /* generator sets for the two sides: (g,A) -> (s g, B) uses S; (h,B) -> (s^-1 h, A) uses S^-1 */
    El T[2][64];
    for (int i = 0; i < k; i++) {
        T[0][i] = S[i];
        T[1][i].x = inv(S[i].x, P[0]); T[1][i].y = inv(S[i].y, P[1]); T[1][i].z = (n - S[i].z) % n;
    }
    /* self-test: decode/encode round trip on a sample of indices */
    for (long long g = 0; g < N; g += N / 1000 + 1) {
        El e = decode(g);
        if (encode(e.x, e.y, e.z) != g) { fprintf(stderr, "index self-test failed\n"); return 2; }
    }
    long long W = (N + 63) / 64;
    uint64_t *vis[2], *cur[2], *nxt[2];
    for (int s = 0; s < 2; s++) { vis[s] = calloc(W, 8); cur[s] = calloc(W, 8); nxt[s] = calloc(W, 8); }
    M I0 = { 1, 0, 0, 1 }, I1 = { 1, 0, 0, 1 };
    int bad = 0;
    for (int start = 0; start < 2; start++) {
        for (int s = 0; s < 2; s++) { memset(vis[s], 0, W * 8); memset(cur[s], 0, W * 8); }
        long long e0 = encode(I0, I1, 0);
        vis[start][e0 >> 6] |= 1ULL << (e0 & 63); cur[start][e0 >> 6] |= 1ULL << (e0 & 63);
        long long reached[2] = { 0, 0 }; reached[start] = 1;
        int side = start, ecc = 0;
        for (int step = 1; step <= D; step++) {
            int ns = side ^ 1; long long add = 0;
            memset(nxt[ns], 0, W * 8);
            for (long long w = 0; w < W; w++) {
                uint64_t bits = cur[side][w];
                while (bits) {
                    int bt = __builtin_ctzll(bits); bits &= bits - 1;
                    El g = decode(w * 64 + bt);
                    for (int i = 0; i < k; i++) {
                        const El *s = &T[side][i];
                        long long h = encode(mul(s->x, g.x, P[0]), mul(s->y, g.y, P[1]), (s->z + g.z) % n);
                        uint64_t m1 = 1ULL << (h & 63);
                        if (!(vis[ns][h >> 6] & m1)) { vis[ns][h >> 6] |= m1; nxt[ns][h >> 6] |= m1; add++; }
                    }
                }
            }
            memset(cur[side], 0, W * 8);
            uint64_t *t = cur[ns]; cur[ns] = nxt[ns]; nxt[ns] = t;
            reached[ns] += add;
            if (add) ecc = step;
            side = ns;
        }
        printf("from (e,%c): reached A %lld/%lld, B %lld/%lld within %d, ecc %d\n",
               start ? 'B' : 'A', reached[0], N, reached[1], N, D, ecc);
        if (reached[0] != N || reached[1] != N) bad = 1;
    }
    printf("%s d=%d D=%d group=sl %lld x sl %lld x Z_%lld N=%lld vertices=%lld (distinct generators, %d-regular simple)\n",
           bad ? "INVALID" : "VALID", dg, D, P[0], P[1], n, N, 2 * N, dg);
    return bad;
}
