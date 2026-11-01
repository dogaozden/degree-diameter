/* Independent check of a Haar graph H(G,S), G = (Z_m x|_r Z_k) x (Z_m2 x|_r2 Z_k2), from a haar_gen3 solution file.
 * Group law copied from the meta definition: (a,j)(b,l) = (a + r^j b mod m, j+l mod k). Vertices (g,A)=g, (g,B)=N+g,
 * edges (g,A) ~ (s g,B). Diameter = max(ecc(e,A), ecc(e,B)) (right multiplication is transitive on each side). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int m1,k1,m2,k2; static int64_t R1[64], R2[64]; static long long o2, N;
static long long mul(long long x, long long y) {
    long long x1 = x / o2, x2 = x % o2, y1 = y / o2, y2 = y % o2;
    int a = x1 / k1, j = x1 % k1, b = y1 / k1, l = y1 % k1;
    long long c1 = (a + R1[j] * b) % m1; int j3 = (j + l) % k1;
    int a2 = x2 / k2, j2 = x2 % k2, b2 = y2 / k2, l2 = y2 % k2;
    long long c2 = (a2 + R2[j2] * b2) % m2; int j4 = (j2 + l2) % k2;
    return (c1 * k1 + j3) * o2 + (c2 * k2 + j4);
}
static long long inv(long long x) { /* brute-free inverse: (a,j)^-1 = (-r^{-j} a, -j) */
    long long x1 = x / o2, x2 = x % o2;
    int a = x1 / k1, j = x1 % k1, jj = (k1 - j) % k1; long long b = (m1 - (R1[jj] * a) % m1) % m1; long long c1 = b * k1 + jj;
    int a2 = x2 / k2, j2 = x2 % k2, jj2 = (k2 - j2) % k2; long long b2 = (m2 - (R2[jj2] * a2) % m2) % m2; long long c2 = b2 * k2 + jj2;
    return c1 * o2 + c2;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); char line[512]; int d, D; long long n_unused;
    fgets(line, sizeof line, f); /* header: d D prod meta m k r meta m k r n 1 N N */
    long long Nhdr; char *p = line; sscanf(line, "%d %d", &d, &D);
    /* header fields */
    char tmp[512]; strcpy(tmp, line); int mm1, kk1, rr1, mm2, kk2, rr2;
    char *tok = strtok(tmp, " \n"); int ti = 0; int vals[16]; int nv = 0; char *toks[32]; int nt=0;
    while (tok) { toks[nt++] = tok; tok = strtok(NULL, " \n"); }
    /* toks: d D prod meta m k r meta m k r n 1 N N */
    mm1 = atoi(toks[4]); kk1 = atoi(toks[5]); rr1 = atoi(toks[6]); mm2 = atoi(toks[8]); kk2 = atoi(toks[9]); rr2 = atoi(toks[10]);
    m1 = mm1; k1 = kk1; m2 = mm2; k2 = kk2; o2 = (long long)m2 * k2; N = (long long)m1 * k1 * o2;
    R1[0] = 1 % m1; for (int j = 1; j < k1; j++) R1[j] = R1[j-1] * rr1 % m1;
    R2[0] = 1 % m2; for (int j = 1; j < k2; j++) R2[j] = R2[j-1] * rr2 % m2;
    if (R1[k1-1] * rr1 % m1 != 1 % m1 || R2[k2-1] * rr2 % m2 != 1 % m2) { printf("bad r\n"); return 1; }
    long long S[64]; int ns = 0;
    while (fgets(line, sizeof line, f)) {
        if (!strstr(line, "prod[")) continue;
        int a1, j1, a2, j2; if (sscanf(line, "%*d prod[meta(a=%d,j=%d);meta(a=%d,j=%d)]", &a1, &j1, &a2, &j2) != 4) continue;
        S[ns++] = (long long)(a1 * k1 + j1) * o2 + (long long)(a2 * k2 + j2);
    }
    /* group identity must be index 0 */
    printf("N=%lld |S|=%d (d=%d)\n", N, ns, d);
    for (int i = 0; i < ns; i++) for (int j = i+1; j < ns; j++) if (S[i] == S[j]) { printf("duplicate\n"); return 1; }
    /* closure sanity: associativity on random triples */
    srand(1); for (int t = 0; t < 2000; t++) { long long x = ((long long)rand()*RAND_MAX+rand()) % N, y = ((long long)rand()*RAND_MAX+rand()) % N, z = ((long long)rand()*RAND_MAX+rand()) % N;
        if (mul(mul(x,y),z) != mul(x,mul(y,z))) { printf("assoc fail\n"); return 1; } if (mul(x, inv(x)) != 0) { printf("inv fail\n"); return 1; } }
    long long V = 2 * N; long long *sinv = malloc(sizeof(long long) * ns);
    for (int i = 0; i < ns; i++) sinv[i] = inv(S[i]);
    unsigned char *dist = malloc(V); long long *q = malloc(sizeof(long long) * V);
    int ecc[2] = {0, 0}; int start[2] = {0, (int)0};
    for (int side = 0; side < 2; side++) {
        memset(dist, 255, V); long long head = 0, tail = 0; long long src = side == 0 ? 0 : N; dist[src] = 0; q[tail++] = src; int mx = 0;
        while (head < tail) {
            long long v = q[head++]; int dv = dist[v]; if (dv > mx) mx = dv;
            long long g = v >= N ? v - N : v;
            if (v < N) { for (int i = 0; i < ns; i++) { long long w = N + mul(S[i], g); if (dist[w] == 255) { dist[w] = dv + 1; q[tail++] = w; } } }
            else { for (int i = 0; i < ns; i++) { long long w = mul(sinv[i], g); if (dist[w] == 255) { dist[w] = dv + 1; q[tail++] = w; } } }
        }
        if (tail != V) { printf("disconnected: reached %lld of %lld from side %d\n", tail, V, side); return 1; }
        ecc[side] = mx; printf("ecc from %s(e) = %d\n", side ? "B" : "A", mx);
    }
    int diam = ecc[0] > ecc[1] ? ecc[0] : ecc[1];
    printf("vertices=%lld diameter=%d regular_degree=%d verdict=%s\n", V, diam, ns, diam <= D ? "OK (diameter <= D)" : "FAIL");
    return 0;
}
