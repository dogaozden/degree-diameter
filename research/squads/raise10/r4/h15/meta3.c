/* Exhaustive cubic Haar graphs H(G,{e,a,b}) over metacyclic groups G = Z_m x|_r Z_k (r^k = 1 mod m), |G| = N.
   Elements (a,j): (a,j)(b,l) = (a + r^j b mod m, j + l mod k). Edges (g,0) ~ (s g,1), s in S.
   Left translation of S gives an isomorphic graph, so e in S WLOG. Both sides are checked (BFS from (e,0), (e,1)).
   Usage: meta3 Nlo Nhi D first_group max_seconds ; groups enumerated in order (N, k, r); prints group index for resume. */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
int main(int argc, char **argv) {
    int Nlo = atoi(argv[1]), Nhi = atoi(argv[2]), D = atoi(argv[3]);
    long first = atol(argv[4]); double maxsec = atof(argv[5]); long thr = argc > 6 ? atol(argv[6]) : 1000000000L;
    long gi = 0; clock_t t0 = clock();
    int *dist = malloc(sizeof(int) * 2 * Nhi), *q = malloc(sizeof(int) * 2 * Nhi);
    for (int N = Nlo; N <= Nhi; N++)
    for (int k = 2; k <= N; k++) {
        if (N % k) continue;
        int m = N / k;
        for (int r = 1; r < m || (m == 1 && r == 1); r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            long p = 1 % m; for (int i = 0; i < k; i++) p = (p * r) % m;
            if (p != 1 % m) continue;
            gi++;
            if (gi - 1 < first) continue;
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > maxsec) { printf("STOP next_group %ld\n", gi - 1); return 0; }
            int *rp = malloc(sizeof(int) * k); rp[0] = 1 % m;
            for (int j = 1; j < k; j++) rp[j] = (int)(((long)rp[j - 1] * r) % m);
            int V = 2 * N;
            int *iv = malloc(sizeof(int) * N); /* inverse id; element id = a*k + j */
            for (int a = 0; a < m; a++) for (int j = 0; j < k; j++) {
                int l = (k - j) % k;
                long c = (-(long)rp[l] * a) % m; if (c < 0) c += m;
                iv[a * k + j] = (int)c * k + l;
            }
            long best = thr; int bA = -1, bB = -1, solved = 0;
            for (int A = 1; A < N && !solved; A++) for (int B = A + 1; B < N; B++) {
                int ids[3] = {0, A, B};
                int worst = 0;
                for (int src = 0; src < 2; src++) {
                    int s0 = src == 0 ? 0 : N;
                    for (int v = 0; v < V; v++) dist[v] = -1;
                    int h = 0, t = 0; q[t++] = s0; dist[s0] = 0;
                    while (h < t) {
                        int v = q[h++]; int dv = dist[v];
                        if (dv >= D) continue;
                        int side = v >= N; int g = side ? v - N : v;
                        int b = g / k, l = g % k;
                        for (int c = 0; c < 3; c++) {
                            int sid = ids[c];
                            int id2 = side ? iv[sid] : sid;   /* s^{-1} when moving from side 1 */
                            int a = id2 / k, j = id2 % k;
                            int ng = (int)((a + (long)rp[j] * b) % m) * k + (j + l) % k;
                            int w = side ? ng : N + ng;
                            if (dist[w] < 0) { dist[w] = dv + 1; q[t++] = w; }
                        }
                    }
                    int holes = V - t; if (holes > worst) worst = holes;
                    if (worst >= best) break;
                }
                if (worst < best) { best = worst; bA = A; bB = B; }
                if (best == 0) { solved = 1; break; }
            }
            printf("group %ld N %d m %d k %d r %d minholes %ld S {e,%d,%d}%s\n", gi - 1, N, m, k, r, best,
                   bA, bB, best == 0 ? " SOLVED" : "");
            fflush(stdout);
            free(rp); free(iv);
        }
    }
    printf("DONE groups %ld\n", gi);
    return 0;
}
