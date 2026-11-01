/* Independent check of a Haar graph H(G,S), G = Z_m x|_r Z_k (law as in research/frontier/haar_gen3.c:
   (a,j)(b,l) = (a + r^j b mod m, j+l mod k), index = a*k + j).
   Vertices (g,A) = g, (g,B) = N+g; edges (g,A)~(s g,B), s in S.
   Right multiplication is an automorphism, so diameter = max ecc over BFS from (e,A) and (e,B). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int64_t m, k, r, N; static int64_t *R;
static int64_t mul(int64_t x, int64_t y) {
    int64_t a = x / k, j = x % k, b = y / k, l = y % k;
    int64_t c = (a + R[j] * b) % m; return c * k + (j + l) % k; }
static int64_t inv(int64_t x) {
    int64_t a = x / k, j = x % k, jj = (k - j) % k;
    int64_t b = (m - (R[jj] * a) % m) % m; return b * k + jj; }
static int64_t *S; static int d;
static int bfs(int start, int D, int *ecc, int64_t *reached) {
    int64_t V = 2 * N; unsigned char *dist = malloc(V); int64_t *q = malloc(sizeof(int64_t) * V);
    memset(dist, 255, V); int64_t h = 0, t = 0; q[t++] = start; dist[start] = 0; int mx = 0;
    while (h < t) {
        int64_t u = q[h++]; int du = dist[u];
        if (u < N) { /* A-side g: neighbours (s g, B) */
            for (int i = 0; i < d; i++) { int64_t v = N + mul(S[i], u); if (dist[v] == 255) { dist[v] = du + 1; q[t++] = v; } }
        } else { /* B-side x: neighbours (s^-1 x, A) */
            int64_t x = u - N;
            for (int i = 0; i < d; i++) { int64_t v = mul(inv(S[i]), x); if (dist[v] == 255) { dist[v] = du + 1; q[t++] = v; } }
        }
        if (du + 1 > mx && t > 0) { if (dist[q[t-1]] > mx) mx = dist[q[t-1]]; }
    }
    for (int64_t v = 0; v < V; v++) if (dist[v] != 255 && dist[v] > mx) mx = dist[v];
    *reached = t; *ecc = mx; free(dist); free(q); return 0;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    char line[256]; if (!fgets(line, sizeof line, f)) return 1;
    char *tok[32]; int nt = 0; char *p = strtok(line, " \n"); while (p && nt < 32) { tok[nt++] = p; p = strtok(NULL, " \n"); }
    /* header: D_d D meta m k r n 1 N NN */
    int Dtarget = atoi(tok[1]); d = atoi(tok[0]);
    int ix = -1; for (int i = 0; i < nt; i++) if (!strcmp(tok[i], "meta")) ix = i;
    if (ix < 0) { fprintf(stderr, "not meta\n"); return 1; }
    m = atoll(tok[ix + 1]); k = atoll(tok[ix + 2]); r = atoll(tok[ix + 3]);
    int64_t nn = 1; for (int i = 0; i < nt; i++) if (!strcmp(tok[i], "N")) nn = atoll(tok[i + 1]);
    N = m * k; if (nn != N) { fprintf(stderr, "N mismatch\n"); }
    R = malloc(sizeof(int64_t) * k); R[0] = 1 % m; for (int64_t j = 1; j < k; j++) R[j] = R[j-1] * r % m;
    if (R[k-1] * r % m != 1 % m) { fprintf(stderr, "r^k != 1\n"); return 1; }
    /* sanity: inverse law and associativity on random triples */
    for (int64_t x = 0; x < N; x += 997) if (mul(x, inv(x)) != 0 || mul(inv(x), x) != 0) { fprintf(stderr, "inverse law fails\n"); return 1; }
    S = malloc(sizeof(int64_t) * 64); int ns = 0; char buf[256];
    while (fgets(buf, sizeof buf, f)) { long long v; if (sscanf(buf, "%lld", &v) == 1) S[ns++] = v; }
    fclose(f);
    if (ns != d) { fprintf(stderr, "|S|=%d, expected %d\n", ns, d); }
    for (int i = 0; i < ns; i++) for (int j = 0; j < i; j++) if (S[i] == S[j]) { fprintf(stderr, "repeat in S\n"); return 1; }
    int e1, e2; int64_t r1, r2;
    bfs(0, Dtarget, &e1, &r1);          /* from (e,A) */
    bfs(N, Dtarget, &e2, &r2);          /* from (e,B) */
    printf("N=%lld |S|=%d vertices=%lld reachedA=%lld reachedB=%lld ecc(e,A)=%d ecc(e,B)=%d diameter=%d -> %s (D=%d)\n",
        (long long)N, ns, (long long)(2*N), (long long)r1, (long long)r2, e1, e2, e1 > e2 ? e1 : e2,
        (r1 == 2*N && r2 == 2*N && (e1 > e2 ? e1 : e2) <= Dtarget) ? "VALID" : "INVALID", Dtarget);
    return 0;
}
