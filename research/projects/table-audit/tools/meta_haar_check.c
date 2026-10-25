/* meta_haar_check.c (table-audit): independent check of a Haar graph of a metacyclic group, written from the
   definitions (not from haar_gen3 or build_haar2.py).
   G = Z_m x|_r Z_k, element (a, j), product (a, j)(b, l) = (a + r^j b mod m, j + l mod k), r^k = 1 mod m.
   Haar graph H(G, S): vertices (g, A), (g, B); (g, A) ~ (s g, B) for s in S.  Right multiplication by G is an
   automorphism group transitive on each side, so BFS from (e, A) and (e, B) gives the exact diameter.
   Checks: r^k = 1 mod m, the d elements of S are distinct (simple graph, degree exactly d), every vertex reached,
   and the largest distance from (e,A) and (e,B).  Prints "RESULT VALID d D n" iff diameter <= D.
   Input: a haar_gen3 solution file (header "d D meta m k r n NCYC ...", then d lines "<idx> meta(a=A,j=J) z=0").
   Usage: meta_haar_check SOL */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    int d, D; long m, k, r, ncyc; char word[64];
    if (fscanf(f, "%d %d %63s %ld %ld %ld %*s %ld", &d, &D, word, &m, &k, &r, &ncyc) != 7 || strcmp(word, "meta") || ncyc != 1) {
        printf("RESULT INVALID unsupported header\n"); return 1;
    }
    char line[512]; long *sa = malloc(sizeof(long) * d), *sj = malloc(sizeof(long) * d); int ns = 0;
    while (fgets(line, sizeof line, f)) {
        char *p = strstr(line, "meta(a="); if (!p) continue;
        long a, j; if (sscanf(p, "meta(a=%ld,j=%ld)", &a, &j) == 2) { sa[ns] = a % m; sj[ns] = j % k; ns++; }
    }
    if (ns != d) { printf("RESULT INVALID read %d elements, expected %d\n", ns, d); return 1; }
    long *rp = malloc(sizeof(long) * (k + 1)); rp[0] = 1;
    for (long i = 1; i <= k; i++) rp[i] = rp[i - 1] * r % m;
    if (rp[k] != 1) { printf("RESULT INVALID r^k != 1 mod m\n"); return 1; }
    for (int x = 0; x < d; x++) for (int y = x + 1; y < d; y++) if (sa[x] == sa[y] && sj[x] == sj[y]) { printf("RESULT INVALID repeated element\n"); return 1; }
    long N = m * k, n = 2 * N;
    /* inverses: (a,j)^-1 = (-r^{-j} a, -j); r^{-j} = r^{k-j} */
    long *ia = malloc(sizeof(long) * d), *ij = malloc(sizeof(long) * d);
    for (int x = 0; x < d; x++) { long jj = (k - sj[x]) % k; ij[x] = jj; ia[x] = (m - rp[jj] * sa[x] % m) % m; }
    int8_t *dist = malloc(n); long *q = malloc(sizeof(long) * n); int diam = 0;
    for (int side = 0; side < 2; side++) {
        memset(dist, -1, n); long h = 0, t = 0; long s0 = side * N; dist[s0] = 0; q[t++] = s0;
        while (h < t) {
            long v = q[h++]; int sv = v >= N; long g = v - sv * N, ga = g / k, gj = g % k;
            for (int x = 0; x < d; x++) {
                long na, nj;
                if (!sv) { na = (sa[x] + rp[sj[x]] * ga) % m; nj = (sj[x] + gj) % k; }      /* (g,A) -> (s g, B) */
                else { na = (ia[x] + rp[ij[x]] * ga) % m; nj = (ij[x] + gj) % k; }          /* (h,B) -> (s^-1 h, A) */
                long w = (1 - sv) * N + na * k + nj;
                if (dist[w] < 0) { dist[w] = dist[v] + 1; q[t++] = w; }
            }
        }
        if (t != n) { printf("RESULT INVALID unreached %ld\n", n - t); return 1; }
        int e = dist[q[t - 1]]; if (e > diam) diam = e;
        printf("ecc(e,%c) = %d\n", side ? 'B' : 'A', e);
    }
    printf("n=%ld degree=%d diameter=%d group=Z%ld x|_%ld Z%ld\n", n, d, diam, m, r, k);
    if (diam <= D) printf("RESULT VALID d=%d D=%d n=%ld\n", d, D, n); else printf("RESULT INVALID\n");
    return 0;
}
