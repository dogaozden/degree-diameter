/* haarcheck_prod: independent low-memory diameter check of a Haar graph H(G,S), G = A x B x Z_n with A, B = SL(2,q)
 * (any prime power q), written for round 2 of the (14,9) raise job from the definitions only.  Input is the table file
 * written by haarcheck_prod.py (group sizes, n, the d generators' left-multiplication tables, and their inverses).
 * Vertices (g,A),(g,B) with g = (ia,ib,z), index g = (ia*NB+ib)*n+z; edges (g,A) ~ (s g,B) for s in S.
 * BFS from (e,A) and from (e,B) (right multiplication by G is transitive on each side), so the diameter is the max of the
 * two eccentricities.  One byte per vertex.   Usage: haarcheck_prod TABLE.txt      Build: cc -O3 -o haarcheck_prod haarcheck_prod.c */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static long long NA, NB, n, d, D, N, V;
static int *LA, *LAi, *LB, *LBi;     /* [j*NA + x], [j*NB + y] */
static long long *SZ;                 /* z-part of generator j */
static long long ia0, ib0;

static unsigned char *dist;

static long long bfs(long long src, long long *ecc) {
    memset(dist, 255, V);
    dist[src] = 0;
    long long reached = 1, lev;
    for (lev = 0; lev < D; lev++) {
        long long added = 0;
        for (long long v = 0; v < V; v++) {
            if (dist[v] != lev) continue;
            long long z, ia, ib, u;
            if (v < N) {                                /* (g,A) -> (s g, B) */
                long long g = v; z = g % n; g /= n; ib = g % NB; ia = g / NB;
                for (long long j = 0; j < d; j++) {
                    long long zz = (SZ[j] + z) % n;
                    u = N + ((long long)LA[j*NA+ia] * NB + LB[j*NB+ib]) * n + zz;
                    if (dist[u] == 255) { dist[u] = lev + 1; added++; }
                }
            } else {                                    /* (h,B) -> (s^-1 h, A) */
                long long g = v - N; z = g % n; g /= n; ib = g % NB; ia = g / NB;
                for (long long j = 0; j < d; j++) {
                    long long zz = ((z - SZ[j]) % n + n) % n;
                    u = ((long long)LAi[j*NA+ia] * NB + LBi[j*NB+ib]) * n + zz;
                    if (dist[u] == 255) { dist[u] = lev + 1; added++; }
                }
            }
        }
        reached += added;
        if (!added) break;
    }
    long long mx = 0, cnt = 0;
    for (long long v = 0; v < V; v++) if (dist[v] != 255) { cnt++; if (dist[v] > mx) mx = dist[v]; }
    *ecc = mx;
    return cnt;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: haarcheck_prod TABLE.txt\n"); return 2; }
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("table"); return 2; }
    if (fscanf(f, "%lld %lld %lld %lld %lld", &NA, &NB, &n, &d, &D) != 5) return 2;
    N = NA * NB * n; V = 2 * N;
    LA = malloc(sizeof(int) * d * NA); LAi = malloc(sizeof(int) * d * NA);
    LB = malloc(sizeof(int) * d * NB); LBi = malloc(sizeof(int) * d * NB);
    SZ = malloc(sizeof(long long) * d);
    for (long long j = 0; j < d; j++) {
        if (fscanf(f, "%lld", &SZ[j]) != 1) return 2;
        for (long long x = 0; x < NA; x++) if (fscanf(f, "%d", &LA[j*NA+x]) != 1) return 2;
        for (long long x = 0; x < NA; x++) if (fscanf(f, "%d", &LAi[j*NA+x]) != 1) return 2;
        for (long long y = 0; y < NB; y++) if (fscanf(f, "%d", &LB[j*NB+y]) != 1) return 2;
        for (long long y = 0; y < NB; y++) if (fscanf(f, "%d", &LBi[j*NB+y]) != 1) return 2;
    }
    if (fscanf(f, "%lld %lld", &ia0, &ib0) != 2) return 2;
    fclose(f);
    dist = malloc(V);
    if (!dist) { fprintf(stderr, "out of memory\n"); return 3; }
    long long eA, eB, cA, cB;
    cA = bfs(((ia0 * NB + ib0) * n + 0), &eA);              /* (e,A) */
    cB = bfs(N + ((ia0 * NB + ib0) * n + 0), &eB);          /* (e,B) */
    printf("N=%lld vertices=%lld ecc(e,A)=%lld ecc(e,B)=%lld reached A=%lld B=%lld of %lld\n",
           N, V, eA, eB, cA, cB, N);
    int ok = cA == V && cB == V && eA <= D && eB <= D;
    printf("%s d=%lld D=%lld vertices=%lld (haarcheck_prod)\n", ok ? "VALID" : "INVALID", d, D, V);
    return ok ? 0 : 1;
}
