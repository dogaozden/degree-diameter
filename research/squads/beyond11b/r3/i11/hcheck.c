/* independent check: Haar graph H(G,S), G = Z_m x|_r Z_k (n=1), (a,j)(b,l) = (a + r^j b, j + l).
   usage: hcheck m k r D a1 j1 ... a5 j5  (S as list of (a,j); first must be identity (0,0)) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv) {
    long m = atol(argv[1]), k = atol(argv[2]), r = atol(argv[3]); int D = atoi(argv[4]);
    int d = (argc - 5) / 2; long S[64][2];
    for (int i = 0; i < d; i++) { S[i][0] = atol(argv[5 + 2*i]); S[i][1] = atol(argv[6 + 2*i]); }
    long N = m * k;
    /* rk[j] = r^j mod m */
    long *rk = malloc(sizeof(long) * k); rk[0] = 1 % m;
    for (long j = 1; j < k; j++) rk[j] = rk[j-1] * r % m;
    if (rk[0] * 1 != 1 || (rk[k-1] * r) % m != 1 % m) { printf("r^k != 1\n"); }
    /* inverse of s: (x,y) with (a,j)(x,y) = (0,0): y = -j, x = -r^{-j} a = -r^{k-j} a */
    long IS[64][2];
    for (int i = 0; i < d; i++) {
        long a = S[i][0], j = S[i][1];
        long y = (k - j) % k;
        long rr = rk[y];                       /* r^{-j} = r^{k-j} */
        long x = ((m - (rr * a) % m)) % m;
        IS[i][0] = x; IS[i][1] = y;
        /* verify */
        long ta = (a + rk[j] * x) % m, tj = (j + y) % k;
        if (ta != 0 || tj != 0) { printf("inverse wrong\n"); return 1; }
    }
    /* distinctness */
    for (int i = 0; i < d; i++) for (int l = i+1; l < d; l++) if (S[i][0]==S[l][0] && S[i][1]==S[l][1]) { printf("dup S\n"); return 1; }
    /* vertex ids: A-side g -> g (idx = a*k + j), B-side g -> N + g */
    long V = 2 * N;
    unsigned char *dist[2];
    long *q = malloc(sizeof(long) * V);
    long maxecc = 0; int ok = 1;
    for (int src = 0; src < 2; src++) {        /* src 0: (e,A), src 1: (e,B) */
        unsigned char *dd = malloc(V); memset(dd, 255, V);
        long head = 0, tail = 0; long s0 = src * N + 0; dd[s0] = 0; q[tail++] = s0;
        long reached = 1;
        while (head < tail) {
            long u = q[head++]; long du = dd[u];
            long g = (u >= N) ? u - N : u; long a = g / k, j = g % k;
            int side = (u >= N);   /* 0 = A, 1 = B */
            for (int i = 0; i < d; i++) {
                long v;
                if (!side) {               /* (g,A) ~ (s g, B) */
                    long na = (S[i][0] + rk[S[i][1]] * a) % m; long nj = (S[i][1] + j) % k;
                    v = N + na * k + nj;
                } else {                    /* (h,B) ~ (s^-1 h, A) */
                    long x = IS[i][0], y = IS[i][1];
                    long na = (x + rk[y] * a) % m; long nj = (y + j) % k;
                    v = na * k + nj;
                }
                if (dd[v] == 255) { dd[v] = du + 1; q[tail++] = v; reached++; if (du + 1 > maxecc) maxecc = du + 1; }
            }
        }
        /* ecc from this source */
        long ecc = 0; for (long v = 0; v < V; v++) { if (dd[v] == 255) { ok = 0; } else if (dd[v] > ecc) ecc = dd[v]; }
        printf("src %s: ecc=%ld reached=%ld of %ld\n", src ? "(e,B)" : "(e,A)", ecc, reached, V);
        if (ecc > D) ok = 0;
        free(dd);
    }
    printf("N=%ld n_vertices=%ld edges=%ld d=%d D=%d diameter_ok=%d\n", N, V, N * (long)d, d, D, ok);
    return 0;
}
