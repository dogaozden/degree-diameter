/* Bit-parallel count of ordered pairs at distance > D (D<=5). Usage: cnt5 edges D
   Prints n, m, maxdeg, mindeg, number of unordered pairs at distance > D (missing), and diameter-ok flag. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int D = atoi(argv[2]);
    int n; if (fscanf(f, "%d", &n) != 1) return 1;
    int cap = 1 << 22; int *eu = malloc(sizeof(int) * cap), *ev = malloc(sizeof(int) * cap); long m = 0;
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) {
        if (m >= cap) { cap *= 2; eu = realloc(eu, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        eu[m] = a; ev[m] = b; m++;
    }
    fclose(f);
    int *deg = calloc(n, sizeof(int));
    for (long i = 0; i < m; i++) { deg[eu[i]]++; deg[ev[i]]++; }
    int maxd = 0, mind = 1 << 30; for (int v = 0; v < n; v++) { if (deg[v] > maxd) maxd = deg[v]; if (deg[v] < mind) mind = deg[v]; }
    long *off = calloc(n + 1, sizeof(long)); for (int v = 0; v < n; v++) off[v + 1] = off[v] + deg[v];
    int *adj = malloc(sizeof(int) * off[n]); long *pos = malloc(sizeof(long) * n);
    for (int v = 0; v < n; v++) pos[v] = off[v];
    for (long i = 0; i < m; i++) { adj[pos[eu[i]]++] = ev[i]; adj[pos[ev[i]]++] = eu[i]; }
    uint64_t *R = malloc(sizeof(uint64_t) * n), *N = malloc(sizeof(uint64_t) * n);
    long long missing = 0; /* ordered pairs (s,v) with dist > D */
    for (int base = 0; base < n; base += 64) {
        int cnt = (n - base < 64) ? (n - base) : 64;
        uint64_t valid = (cnt == 64) ? ~0ULL : ((1ULL << cnt) - 1);
        for (int v = 0; v < n; v++) R[v] = 0;
        for (int i = 0; i < cnt; i++) R[base + i] |= 1ULL << i;
        for (int k = 0; k < D; k++) {
            for (int v = 0; v < n; v++) {
                uint64_t x = R[v];
                for (long j = off[v]; j < off[v + 1]; j++) x |= R[adj[j]];
                N[v] = x;
            }
            uint64_t *t = R; R = N; N = t;
        }
        for (int v = 0; v < n; v++) missing += __builtin_popcountll(~R[v] & valid);
    }
    /* missing counts ordered pairs (s,v) incl. none self (self always reached) */
    printf("RESULT n=%d m=%ld mindeg=%d maxdeg=%d D=%d missing_ordered=%lld missing_unordered=%lld %s\n",
           n, m, mind, maxd, D, missing, missing / 2, missing == 0 ? "DIAMETER_OK" : "FAIL");
    return 0;
}
