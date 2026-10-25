/* Card c7: exact count of unreached pairs at distance > 5.
   usage: badcount EDGES NPOINT STEP
   EDGES: "n" then "a b" lines (lift, vertex = 6*b + h; base b < NPOINT is a point, else a line).
   For every base source b (every STEP-th one), BFS from (b,0) to depth 5 and count vertices not reached.
   Prints counts split by (source side, target side). Sides: 0 = point, 1 = line. */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    long npoint = atol(argv[2]), step = argc > 3 ? atol(argv[3]) : 1;
    long n, a, b, m = 0, cap = 1 << 16;
    if (!f || fscanf(f, "%ld", &n) != 1) return 2;
    long *U = malloc(cap * sizeof(long)), *W = malloc(cap * sizeof(long));
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (m == cap) { cap *= 2; U = realloc(U, cap * sizeof(long)); W = realloc(W, cap * sizeof(long)); }
        U[m] = a; W[m] = b; m++;
    }
    long *deg = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { deg[U[i]]++; deg[W[i]]++; }
    long *st = calloc(n + 1, sizeof(long));
    for (long i = 0; i < n; i++) st[i + 1] = st[i] + deg[i];
    long *adj = malloc(2 * m * sizeof(long) + 8), *pos = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) {
        adj[st[U[i]] + pos[U[i]]++] = W[i];
        adj[st[W[i]] + pos[W[i]]++] = U[i];
    }
    int *dist = malloc(n * sizeof(int));
    long *q = malloc(n * sizeof(long));
    long bad[2][2] = {{0, 0}, {0, 0}}, badc[2][2][2] = {{{0,0},{0,0}},{{0,0},{0,0}}}, nsrc = 0, reach_sum[2] = {0, 0}, nsrc_t[2] = {0, 0};
    long nbase = n / 6;
    for (long s = 0; s < nbase; s += step) {
        for (long x = 0; x < n; x++) dist[x] = -1;
        long src = 6 * s, h = 0, t = 0;
        dist[src] = 0; q[t++] = src;
        while (h < t) {
            long x = q[h++];
            if (dist[x] == 5) continue;
            for (long i = st[x]; i < st[x + 1]; i++) {
                long y = adj[i];
                if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; }
            }
        }
        int ss = (s >= npoint);
        long reached = t;
        reach_sum[ss] += reached; nsrc_t[ss]++;
        for (long x = 0; x < n; x++)
            if (dist[x] < 0) {
                int tside = ((x / 6) >= npoint);
                int col = (tside + ((x % 6) & 1)) & 1;   /* colour: side + Z2 part of sheet */
                bad[ss][tside]++; badc[ss][tside][col]++;
            }
        nsrc++;
    }
    long total = bad[0][0] + bad[0][1] + bad[1][0] + bad[1][1];
    printf("sources=%ld (points %ld, lines %ld) n=%ld\n", nsrc, nsrc_t[0], nsrc_t[1], n);
    printf("bad (src point -> tgt point)=%ld  (src point -> tgt line)=%ld\n", bad[0][0], bad[0][1]);
    printf("bad (src line  -> tgt point)=%ld  (src line  -> tgt line)=%ld\n", bad[1][0], bad[1][1]);
    printf("by target colour (src side, tgt side, colour): P->P c0=%ld c1=%ld | P->L c0=%ld c1=%ld | L->P c0=%ld c1=%ld | L->L c0=%ld c1=%ld\n",
           badc[0][0][0], badc[0][0][1], badc[0][1][0], badc[0][1][1], badc[1][0][0], badc[1][0][1], badc[1][1][0], badc[1][1][1]);
    printf("TOTAL bad (source,target) lift pairs at distance > 5 = %ld\n", total);
    if (nsrc_t[0]) printf("avg reached within 5 from a point source = %.1f of %ld\n", (double)reach_sum[0] / nsrc_t[0], n);
    if (nsrc_t[1]) printf("avg reached within 5 from a line source  = %.1f of %ld\n", (double)reach_sum[1] / nsrc_t[1], n);
    return 0;
}
