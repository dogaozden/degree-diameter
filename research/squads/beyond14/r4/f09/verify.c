/* f09 independent check: plain BFS (no bit tricks) on the Haar graph H(G,S), G = Z_m x|_r Z_k, from (e,A) and (e,B).
 * Group written from its definition: (a,j)(b,l) = (a + r^j b mod m, j + l mod k); element index a*k + j.
 * Vertices: A-index g (0..N-1), B-index N+g; edges (g,A) ~ (s g, B) for s in S. Neighbours computed on the fly.
 * Usage: verify SOLFILE D.  Solution file: "d D meta m k r n 1 N n" then d lines "idx meta(a=A,j=J) z=0".
 * Prints ecc from (e,A), (e,B), counts reached, and VALID iff both eccentricities <= D and all 2N vertices reached
 * and the d generators are distinct. Build: gcc -O2 -o verify verify.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef long long ll;
static ll M, K, R, N; static int d; static ll SA[16], SJ[16], SIA[16], SIJ[16];
static ll *RP;
static void mul(ll a, ll j, ll b, ll l, ll *oa, ll *oj) { *oa = (a + (__int128)RP[j] * b) % M; *oj = (j + l) % K; }
static void inv(ll a, ll j, ll *oa, ll *oj) { ll jj = (K - j) % K; *oa = (M - (__int128)RP[jj] * a % M) % M; *oj = jj; }
static ll idx(ll a, ll j) { return a * K + j; }
static uint8_t *dist; static int32_t *q;
static int bfs(ll src) {  /* returns eccentricity; -1 if not all 2N reached */
    memset(dist, 0xff, 2 * N); ll head = 0, tail = 0; q[tail++] = (int32_t)src; dist[src] = 0; ll reached = 1, ecc = 0;
    while (head < tail) { ll v = q[head++]; int dv = dist[v];
        ll g = v < N ? v : v - N; ll ga = g / K, gj = g % K;
        for (int t = 0; t < d; t++) {
            ll w;
            if (v < N) { ll ra, rj; mul(SA[t], SJ[t], ga, gj, &ra, &rj); w = N + idx(ra, rj); }   /* (g,A) -> (s g, B) */
            else { ll ia, ij; ll ta, tj; inv(SA[t], SJ[t], &ia, &ij); mul(ia, ij, ga, gj, &ta, &tj); w = idx(ta, tj); } /* (g,B) -> (s^-1 g, A) */
            if (dist[w] == 0xff) { dist[w] = dv + 1; if (dv + 1 > ecc) ecc = dv + 1; reached++; q[tail++] = (int32_t)w; }
        } }
    return reached == 2 * N ? (int)ecc : -(int)reached;
}
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: verify SOL D\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]); char line[512];
    if (!f || !fgets(line, sizeof line, f)) { fprintf(stderr, "cannot read\n"); return 2; }
    char gname[32]; int dd, DD; ll Nh;
    if (sscanf(line, "%d %d %31s %lld %lld %lld", &dd, &DD, gname, &M, &K, &R) != 6 || strcmp(gname, "meta")) { fprintf(stderr, "not a meta file\n"); return 2; }
    d = dd; N = M * K; RP = malloc(sizeof(ll) * K); RP[0] = 1 % M; for (ll j = 1; j < K; j++) RP[j] = (__int128)RP[j - 1] * (R % M) % M;
    if ((__int128)RP[K - 1] * (R % M) % M != 1 % M) { printf("INVALID r^k != 1 mod m\n"); return 1; }
    int n = 0; while (n < d && fgets(line, sizeof line, f)) { char *p = strstr(line, "meta(a="); if (!p) continue;
        ll a, j; if (sscanf(p, "meta(a=%lld,j=%lld)", &a, &j) == 2) { SA[n] = a % M; SJ[n] = j % K; n++; } }
    fclose(f);
    if (n != d) { printf("INVALID only %d generators\n", n); return 1; }
    for (int i = 0; i < d; i++) for (int t = 0; t < i; t++) if (SA[i] == SA[t] && SJ[i] == SJ[t]) { printf("INVALID repeated generator\n"); return 1; }
    /* the identity (0,0) must not be in S (no loops) */
    for (int i = 0; i < d; i++) if (SA[i] == 0 && SJ[i] == 0) printf("note: identity in S\n");
    dist = malloc(2 * N); q = malloc(sizeof(int32_t) * 2 * N);
    if (!dist || !q) { printf("out of memory\n"); return 2; }
    int eA = bfs(0), eB = bfs(N);
    printf("n=%lld (vertices %lld) d=%d m=%lld k=%lld r=%lld\necc(e,A)=%d ecc(e,B)=%d (negative = reached count)\n", N, 2 * N, d, M, K, R, eA, eB);
    int ok = eA >= 0 && eB >= 0 && eA <= D && eB <= D;
    printf("%s D=%d N=%lld vertices=%lld\n", ok ? "VALID" : "INVALID", D, (ll)N, 2 * N);
    return ok ? 0 : 1;
}
