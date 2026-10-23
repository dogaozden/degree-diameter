/* haarcheck_sl: independent, low-memory diameter check of a Haar graph H(G,S), G = SL(2,p) x Z_n, p prime.
 * Reads a haar_gen3 solution file (header "d D sl p n NCYC N NTOT", then d lines "<idx> mat(a,b,c,d) z=Z"; only the
 * mat/z descriptions are used).  Vertices (g,A),(g,B); edges (g,A) ~ (s g, B).  Right multiplication by G is
 * transitive on each side, so BFS from (e,A) and from (e,B) give the exact diameter.
 * Own element indexing (keyed on c, unlike haar_gen3's a-keyed one): c != 0: (c,a,d) -> b = (ad-1)/c;
 * c = 0: a != 0, d = 1/a, b free.  Neighbours are computed by explicit 2x2 matrix products mod p.
 * Memory: 4 bitsets of N bits per BFS.  Usage: haarcheck_sl SOL.txt */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static long long p, n, N;
static long long *INV;
static long long md(long long x) { x %= p; return x < 0 ? x + p : x; }
static long long enc(long long a, long long b, long long c, long long d, long long z) {
    long long k;
    if (c) k = ((c - 1) * p + a) * p + d;
    else k = (p - 1) * p * p + (a - 1) * p + b;
    return k * n + z;
}
static void dec(long long g, long long *a, long long *b, long long *c, long long *d, long long *z) {
    *z = g % n; long long k = g / n;
    if (k < (p - 1) * p * p) { *c = k / (p * p) + 1; *a = k / p % p; *d = k % p; *b = md((*a * *d - 1) % p * INV[*c]); }
    else { k -= (p - 1) * p * p; *c = 0; *a = k / p + 1; *b = k % p; *d = INV[*a]; }
}
typedef struct { long long a, b, c, d, z; } el;
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haarcheck_sl SOL.txt\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; if (!fgets(line, sizeof line, f)) return 2;
    int dg, D; char fam[64]; long long NN;
    if (sscanf(line, "%d %d %63s %lld n %lld N %lld", &dg, &D, fam, &p, &n, &NN) != 6 || strcmp(fam, "sl")) {
        fprintf(stderr, "only 'sl p' (p prime) headers: %s", line); return 2; }
    for (long long t = 2; t * t <= p; t++) if (p % t == 0) { fprintf(stderr, "p not prime\n"); return 2; }
    N = p * (p * p - 1) * n;
    if (N != NN) { fprintf(stderr, "header N %lld != p(p^2-1)n = %lld\n", NN, N); return 2; }
    INV = malloc(sizeof(long long) * p); INV[0] = 0;
    for (long long x = 1; x < p; x++) { long long r = 1, e = p - 2, bb = x; while (e) { if (e & 1) r = r * bb % p; bb = bb * bb % p; e >>= 1; } INV[x] = r; }
    el S[64], SI[64]; int k = 0;
    while (fgets(line, sizeof line, f) && k < 64) {
        char *m = strstr(line, "mat("), *zz = strstr(line, "z=");
        if (!m || !zz) continue;
        long long a, b, c, d, z; if (sscanf(m, "mat(%lld,%lld,%lld,%lld)", &a, &b, &c, &d) != 4 || sscanf(zz, "z=%lld", &z) != 1) return 2;
        if (md(a * d - b * c) != 1 || a < 0 || a >= p || b < 0 || b >= p || c < 0 || c >= p || d < 0 || d >= p || z < 0 || z >= n) { fprintf(stderr, "bad element: %s", line); return 2; }
        S[k] = (el){a, b, c, d, z}; SI[k] = (el){d, md(-b), md(-c), a, md(0) + (n - z) % n}; k++;
    }
    if (k != dg) { fprintf(stderr, "read %d elements, expected %d\n", k, dg); return 2; }
    for (int i = 0; i < k; i++) for (int j = 0; j < i; j++)
        if (!memcmp(&S[i], &S[j], sizeof(el))) { fprintf(stderr, "repeated generator %d %d\n", i, j); return 2; }
    /* self-test of enc/dec */
    for (long long g = 0; g < N; g += N / 1000 + 1) { long long a, b, c, d, z; dec(g, &a, &b, &c, &d, &z);
        if (md(a * d - b * c) != 1 || enc(a, b, c, d, z) != g) { fprintf(stderr, "index self-test failed\n"); return 2; } }
    long long W = (N + 63) / 64;
    uint64_t *vis[2], *cur[2], *nxt[2];
    for (int s = 0; s < 2; s++) { vis[s] = calloc(W, 8); cur[s] = calloc(W, 8); nxt[s] = calloc(W, 8); }
    int bad = 0;
    for (int start = 0; start < 2; start++) {
        for (int s = 0; s < 2; s++) { memset(vis[s], 0, W * 8); memset(cur[s], 0, W * 8); }
        long long e = enc(1, 0, 0, 1, 0); vis[start][e >> 6] |= 1ULL << (e & 63); cur[start][e >> 6] |= 1ULL << (e & 63);
        long long reached[2] = {0, 0}; reached[start] = 1; int side = start, ecc = 0;
        for (int step = 1; step <= D; step++) {
            int ns = side ^ 1; long long add = 0; memset(nxt[ns], 0, W * 8);
            el *T = side == 0 ? S : SI;          /* (g,A) -> (s g, B);  (h,B) -> (s^-1 h, A) */
            for (long long w = 0; w < W; w++) { uint64_t bits = cur[side][w];
                while (bits) { int bt = __builtin_ctzll(bits); bits &= bits - 1; long long g = w * 64 + bt;
                    long long a, b, c, d, z; dec(g, &a, &b, &c, &d, &z);
                    for (int i = 0; i < k; i++) { const el *s = &T[i];
                        long long h = enc((s->a * a + s->b * c) % p, (s->a * b + s->b * d) % p, (s->c * a + s->d * c) % p, (s->c * b + s->d * d) % p, (s->z + z) % n);
                        uint64_t m1 = 1ULL << (h & 63);
                        if (!(vis[ns][h >> 6] & m1)) { vis[ns][h >> 6] |= m1; nxt[ns][h >> 6] |= m1; add++; } } } }
            memset(cur[side], 0, W * 8); uint64_t *t = cur[ns]; cur[ns] = nxt[ns]; nxt[ns] = t;
            reached[ns] += add; if (add) ecc = step; side = ns;
        }
        printf("from (e,%c): reached A %lld/%lld, B %lld/%lld within %d, ecc %d\n", start ? 'B' : 'A', reached[0], N, reached[1], N, D, ecc);
        if (reached[0] != N || reached[1] != N) bad = 1;
    }
    printf("%s d=%d D=%d group=sl %lld x Z_%lld N=%lld vertices=%lld (distinct generators, %d-regular simple)\n", bad ? "INVALID" : "VALID", dg, D, p, n, N, 2 * N, dg);
    return bad;
}
