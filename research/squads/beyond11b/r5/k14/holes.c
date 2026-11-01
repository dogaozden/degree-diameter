/* holes.c: BFS anatomy of a Haar graph H(G,S), G = Z_m x|_r Z_k (n = 1), from a solution/state file.
 * Usage: holes FILE
 * Header "d D meta m k r n 1 N N ..."; d generator lines (first token = index x = a*k + j).
 * (a,j)(b,l) = (a + R[j] b, j + l), R[j] = r^j mod m; inverse of (a,j) = (-R[-j] a, -j).
 * Vertices: side 0 = A, side 1 = B; (g,A) ~ (s g, B); (h,B) ~ (s^-1 h, A).
 * Prints the odd-D cost (A from (e,A) + B from (e,B)), the even-D cost (B from (e,A)), and every hole
 * (same-side element not within D-1 of the base vertex) with coset j, inverse and whether the inverse is a hole.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static long long M, K, R_[4096];
static int N, d, D;
static int *S, *SI;

static int mul(int x, int y) {
    long long a = x / K, j = x % K, b = y / K, l = y % K;
    long long c = (a + R_[j] * b) % M;
    return (int)(c * K + (j + l) % K);
}
static int inv(int x) {
    long long a = x / K, j = x % K, jj = (K - j) % K;
    long long b = (M - (R_[jj] * a) % M) % M;
    return (int)(b * K + jj);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: holes FILE\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 1; }
    char line[4096], kind[16];
    if (!fgets(line, sizeof line, f)) return 1;
    int dd, DD, nn, Nn; long long m, k, r;
    int cnt = sscanf(line, "%d %d %15s %lld %lld %lld n %d N %d", &dd, &DD, kind, &m, &k, &r, &nn, &Nn);
    if (cnt < 8 || strcmp(kind, "meta") != 0) { fprintf(stderr, "only meta groups with n=1: %s\n", line); return 1; }
    d = dd; D = DD; M = m; K = k; N = Nn;
    R_[0] = 1 % M;
    for (long long j = 1; j < K; j++) R_[j] = R_[j - 1] * r % M;
    S = malloc(sizeof(int) * d); SI = malloc(sizeof(int) * d);
    for (int i = 0; i < d; i++) {
        if (!fgets(line, sizeof line, f)) { fprintf(stderr, "too few generators\n"); return 1; }
        S[i] = atoi(line);
    }
    fclose(f);
    for (int i = 0; i < d; i++) SI[i] = inv(S[i]);

    int *dist[2];
    int *qq = malloc(sizeof(int) * 2 * N);
    int reach[2];
    for (int base = 0; base < 2; base++) {        /* base 0: (e,A), base 1: (e,B) */
        dist[base] = malloc(sizeof(int) * 2 * N);
        int *dd_ = dist[base];
        for (int i = 0; i < 2 * N; i++) dd_[i] = -1;
        int h = 0, t = 0; int s0 = base * N;      /* identity is index 0 */
        dd_[s0] = 0; qq[t++] = s0;
        while (h < t) {
            int v = qq[h++]; int side = v / N, g = v % N; int dv = dd_[v];
            for (int i = 0; i < d; i++) {
                int w = (side == 0) ? N + mul(S[i], g) : mul(SI[i], g);
                if (dd_[w] < 0) { dd_[w] = dv + 1; qq[t++] = w; }
            }
        }
        reach[base] = t;
    }
    free(qq);
    int ecc[2] = {0, 0};
    for (int v = 0; v < 2 * N; v++) {
        if (dist[0][v] > ecc[0]) ecc[0] = dist[0][v];
        if (dist[1][v] > ecc[1]) ecc[1] = dist[1][v];
    }
    long long A_eA = 0, B_eB = 0, B_eA = 0, A_eB = 0;
    for (int g = 0; g < N; g++) {
        if (dist[0][g] < 0 || dist[0][g] > D - 1) A_eA++;
        if (dist[1][N + g] < 0 || dist[1][N + g] > D - 1) B_eB++;
        if (dist[0][N + g] < 0 || dist[0][N + g] > D - 1) B_eA++;
        if (dist[1][g] < 0 || dist[1][g] > D - 1) A_eB++;
    }
    printf("file %s d=%d D=%d m=%lld k=%lld r=%lld N=%d\n", argv[1], d, D, M, K, r, N);
    printf("reach (e,A)=%d (e,B)=%d of %d; ecc(e,A)=%d ecc(e,B)=%d (diam %s)\n", reach[0], reach[1], 2 * N,
           ecc[0], ecc[1], (reach[0] == 2 * N && reach[1] == 2 * N && ((D % 2) ? (ecc[0] <= D && ecc[1] <= D) : (ecc[0] <= D && ecc[1] <= D))) ? "<= D" : "> D or disconnected");
    printf("odd-D cost = A_from_eA %lld + B_from_eB %lld = %lld\n", A_eA, B_eB, A_eA + B_eB);
    printf("even-D cost = B_from_eA %lld ; (cross: A_from_eB %lld)\n", B_eA, A_eB);
    /* holes for odd-D cost: side A from (e,A), side B from (e,B) */
    printf("HOLES odd-D terms: side a j inv_a inv_j inv_is_hole dist\n");
    for (int side = 0; side < 2; side++) {
        for (int g = 0; g < N; g++) {
            int dv = dist[side][side * N + g];
            if (dv >= 0 && dv <= D - 1) continue;
            int ig = inv(g);
            int dinv = dist[side][side * N + ig];
            int invhole = (dinv < 0 || dinv > D - 1);
            printf("H %c %lld %lld %lld %lld %d %d\n", side ? 'B' : 'A', (long long)(g / K), (long long)(g % K),
                   (long long)(ig / K), (long long)(ig % K), invhole, dv);
        }
    }
    printf("HOLES even-D term (B from eA): side a j inv_a inv_j inv_is_hole dist\n");
    for (int g = 0; g < N; g++) {
        int dv = dist[0][N + g];
        if (dv >= 0 && dv <= D - 1) continue;
        int ig = inv(g);
        int dinv = dist[0][N + ig];
        int invhole = (dinv < 0 || dinv > D - 1);
        printf("E B %lld %lld %lld %lld %d %d\n", (long long)(g / K), (long long)(g % K),
               (long long)(ig / K), (long long)(ig % K), invhole, dv);
    }
    for (int b = 0; b < 2; b++) free(dist[b]);
    free(S); free(SI);
    return 0;
}
