/* metacheck: independent diameter check of a Haar graph H(G,S), G = Z_m x|_r Z_c (haar_sym "meta m c r" family, n = 1).
 * Vertices (g,side), side 0 = A, 1 = B.  Edges (g,A) ~ (s g, B) for s in S (|S| = d).  Multiplication as in haar_sym:
 * (a,j)(b,l) = (a + r^j b mod m, j + l mod c).  Right multiplication by G is an automorphism group, transitive on each
 * side, so diam = max(ecc(e,A), ecc(e,B)).  Plain BFS, one byte of distance per vertex.
 * usage: metacheck FILE   (FILE: haar_sym solution file "d D meta m c r n 1 N ..." + d lines "idx meta(a=A,j=J) z=0")
 * prints VALID d=.. D=.. group=meta m c r vertices=.. if diameter <= D and the set has d distinct elements, else INVALID. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: metacheck FILE\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    char line[4096]; int d = 0, D = 0; long long m = 0, c = 0, r = 0; long long N = 0;
    if (!fgets(line, sizeof line, f)) return 2;
    { char g[64]; int n1 = 0; if (sscanf(line, "%d %d meta %lld %lld %lld", &d, &D, &m, &c, &r) != 5) { fprintf(stderr, "header is not meta: %s", line); return 2; }
      (void)n1; (void)g; }
    if (strstr(line, " n 1 ") == NULL) { fprintf(stderr, "only n = 1 handled\n"); }
    long long *Sa = malloc(sizeof(long long) * d), *Sj = malloc(sizeof(long long) * d);
    for (int i = 0; i < d; i++) {
        if (!fgets(line, sizeof line, f)) { fprintf(stderr, "short file\n"); return 2; }
        long long a, j; char *p = strstr(line, "meta(a=");
        if (!p || sscanf(p, "meta(a=%lld,j=%lld)", &a, &j) != 2) { fprintf(stderr, "element %d not meta: %s", i, line); return 2; }
        Sa[i] = a; Sj[i] = j;
    }
    fclose(f);
    for (int i = 0; i < d; i++) for (int k = 0; k < i; k++) if (Sa[i] == Sa[k] && Sj[i] == Sj[k]) { printf("INVALID repeated generator %d\n", i); return 1; }
    N = m * c;
    long long *R = malloc(sizeof(long long) * c); R[0] = 1 % m;
    for (long long j = 1; j < c; j++) R[j] = R[j - 1] * r % m;
    if (R[c - 1] * r % m != 1 % m) { printf("INVALID r^c != 1\n"); return 1; }
    /* element index g = a*c + j */
    uint64_t V = 2 * (uint64_t)N;
    uint8_t *dist = malloc(V); uint32_t *q = malloc(sizeof(uint32_t) * V);
    if (!dist || !q) { fprintf(stderr, "out of memory\n"); return 2; }
    int worst = 0;
    for (int src = 0; src < 2; src++) {
        memset(dist, 0xff, V);
        uint64_t qh = 0, qt = 0; uint64_t s0 = (uint64_t)src * N + 0;   /* identity index is (0,0) = 0 */
        dist[s0] = 0; q[qt++] = (uint32_t)s0; int ecc = 0; uint64_t seen = 1;
        while (qh < qt) {
            uint32_t x = q[qh++]; int dx = dist[x];
            int side = x >= (uint64_t)N; uint64_t g = side ? x - N : x;
            long long a = g / c, j = g % c;
            /* from (g, side): neighbours (s g, 1-side) if side==0 ; (s^-1 g, 0) if side==1 */
            for (int i = 0; i < d; i++) {
                long long ga, gj; uint64_t y;
                if (side == 0) {                 /* (s g, B) */
                    ga = (Sa[i] + R[Sj[i]] * a) % m; gj = (Sj[i] + j) % c;
                    y = (uint64_t)N + (uint64_t)(ga * c + gj);
                } else {                         /* (s^-1 g, A) with s^-1 = (a', j') inverse */
                    /* inverse of (s,t): (-R[-t] s, -t) */
                    long long t = Sj[i], s = Sa[i];
                    long long ti = (c - t) % c; long long si = ((m - (R[ti] * s) % m) % m);
                    ga = (si + R[ti] * a) % m; gj = (ti + j) % c;
                    y = (uint64_t)(ga * c + gj);
                }
                if (dist[y] == 0xff) { dist[y] = (uint8_t)(dx + 1); q[qt++] = (uint32_t)y; seen++; if (dx + 1 > ecc) ecc = dx + 1; }
            }
        }
        if (seen != V / 2 && seen != V) { /* only one side reached is impossible for connected graphs */ }
        if (seen < V) { printf("INVALID disconnected from %s (reached %llu of %llu)\n", src ? "B" : "A", (unsigned long long)seen, (unsigned long long)V); return 1; }
        if (ecc > worst) worst = ecc;
        fprintf(stderr, "ecc from %s = %d\n", src ? "(e,B)" : "(e,A)", ecc);
    }
    if (worst <= D) { printf("VALID d=%d D=%d group=meta %lld %lld %lld x Z_1 N=%lld vertices=%llu diameter=%d\n", d, D, m, c, r, (long long)N, (unsigned long long)V, worst); return 0; }
    printf("INVALID diameter %d > %d\n", worst, D); return 1;
}
