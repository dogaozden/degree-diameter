/* hcheck: independent BFS check of the Haar graph H(G,S), G = Z_m x|_r Z_k (no extra factor), from a hmeta solution file.
 * Vertices (g,A) = index g, (g,B) = N + g. Edges (g,A) ~ (s g,B) for s in S. Since right multiplication by G is an
 * automorphism transitive on each side, BFS from (e,A) and from (e,B) reaching all 2N vertices within D = diameter check.
 * Own code: plain queue BFS over an explicit adjacency rule (no bit-parallelism).
 * Usage: hcheck SOLFILE */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef int64_t i64;
static i64 m, k, r, N;
static i64 rpow(i64 e) { i64 x = 1 % m; for (i64 i = 0; i < e; i++) x = x * r % m; return x; }
static i64 *RP;
/* index g = a*k + j */
static i64 mulidx(i64 s, i64 g) {
    i64 sa = s / k, sj = s % k, ga = g / k, gj = g % k;
    i64 a = (sa + RP[sj] * ga) % m; i64 j = (sj + gj) % k;
    return a * k + j;
}
static i64 invidx(i64 s) {
    i64 sa = s / k, sj = s % k;
    i64 lj = (k - sj) % k;
    i64 x = (m - (RP[lj] * sa) % m) % m;
    return x * k + lj;
}
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: hcheck SOL\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    int d, D; char tag[16]; char nn[4]; char NS[4]; i64 nfac, one, NN;
    if (fscanf(f, "%d %d %15s %lld %lld %lld %3s %lld %3s %lld", &d, &D, tag, (long long *)&m, (long long *)&k,
               (long long *)&r, nn, (long long *)&one, NS, (long long *)&NN) != 10) { fprintf(stderr, "bad header\n"); return 2; }
    nfac = one;
    if (strcmp(tag, "meta") || strcmp(nn, "n") || nfac != 1 || strcmp(NS, "N")) { fprintf(stderr, "unexpected header format\n"); return 2; }
    N = m * k;
    if (N != NN) { fprintf(stderr, "N mismatch %lld %lld\n", (long long)N, (long long)NN); return 2; }
    RP = malloc(sizeof(i64) * k);
    for (i64 j = 0; j < k; j++) RP[j] = rpow(j);
    if (rpow(k) != 1 % m) { fprintf(stderr, "r^k != 1 mod m\n"); return 2; }
    i64 *S = malloc(sizeof(i64) * d), *Si = malloc(sizeof(i64) * d);
    char line[512];
    fgets(line, sizeof line, f);  /* rest of header line */
    for (int i = 0; i < d; i++) {
        if (!fgets(line, sizeof line, f)) { fprintf(stderr, "short file\n"); return 2; }
        long long idx, a, j;
        if (sscanf(line, "%lld meta(a=%lld,j=%lld)", &idx, &a, &j) != 3) { fprintf(stderr, "bad gen line %d\n", i); return 2; }
        S[i] = (a % m) * k + (j % k);
    }
    fclose(f);
    if (S[0] != 0) { fprintf(stderr, "first generator must be e\n"); return 2; }
    for (int i = 0; i < d; i++) { Si[i] = invidx(S[i]); for (int l = 0; l < i; l++) if (S[l] == S[i]) { printf("INVALID: repeated generator\n"); return 1; } }
    /* sanity: s * s^-1 = e */
    for (int i = 0; i < d; i++) if (mulidx(S[i], Si[i]) != 0) { printf("INVALID: inverse failure\n"); return 1; }
    /* sanity: associativity on random triples */
    srand(7);
    for (int t = 0; t < 100000; t++) {
        i64 x = ((i64)rand() * RAND_MAX + rand()) % N, y = ((i64)rand() * RAND_MAX + rand()) % N, z = ((i64)rand() * RAND_MAX + rand()) % N;
        if (mulidx(mulidx(x, y), z) != mulidx(x, mulidx(y, z))) { printf("INVALID: associativity\n"); return 1; }
    }
    uint64_t V = 2 * (uint64_t)N;
    uint8_t *dist = malloc(V);
    uint32_t *q = malloc(sizeof(uint32_t) * V);
    int allok = 1;
    for (int side = 0; side < 2; side++) {
        memset(dist, 0xff, V);
        uint64_t head = 0, tail = 0;
        uint64_t src = side ? (uint64_t)N + 0 : 0;   /* (e,A) = 0, (e,B) = N */
        dist[src] = 0; q[tail++] = (uint32_t)src;
        uint64_t reached = 0; int maxd = 0;
        while (head < tail) {
            uint64_t v = q[head++]; int dv = dist[v];
            if (dv > maxd) maxd = dv;
            reached++;
            i64 g = (v >= (uint64_t)N) ? (i64)(v - N) : (i64)v;
            int isA = (v < (uint64_t)N);
            if (isA) {
                for (int i = 0; i < d; i++) { uint64_t w = (uint64_t)N + mulidx(S[i], g);
                    if (dist[w] == 0xff) { dist[w] = dv + 1; q[tail++] = (uint32_t)w; } }
            } else {
                for (int i = 0; i < d; i++) { uint64_t w = (uint64_t)mulidx(Si[i], g);
                    if (dist[w] == 0xff) { dist[w] = dv + 1; q[tail++] = (uint32_t)w; } }
            }
        }
        printf("from (e,%c): reached %llu of %llu, eccentricity %d (need <= %d)\n", side ? 'B' : 'A',
               (unsigned long long)reached, (unsigned long long)V, maxd, D);
        if (reached != V || maxd > D) allok = 0;
    }
    printf("%s d=%d D=%d meta %lld %lld %lld N=%lld vertices=%llu\n", allok ? "VALID" : "INVALID", d, D,
           (long long)m, (long long)k, (long long)r, (long long)N, (unsigned long long)V);
    return allok ? 0 : 1;
}
