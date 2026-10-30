/* brute.c: independent check of sdk.c.  Every K-valent bipartite Cayley graph Cay(H, T) of a group H of order 2n
 * with T = T^-1 inside the coset H \ G of an index-2 subgroup G (export_hat.g), no normalisation at all:
 * T = f involutions + m inverse pairs of the coset.  Diameter by BFS from the identity (Cayley graphs are
 * vertex-transitive).  Prints "HIT f m t_1 .. t_K" for every T of diameter <= 5 and writes each graph as an edge list
 * (x ~ t x) to OUTDIR/hit_<count>.edges if OUTDIR is set.  usage: brute FILE.hat SUBINDEX K  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int N, K, *mul, *inG, I[4096], nI, P[4096][2], nP, T[32], *dist, *q; static long long cnt = 0, nsets = 0;
static const char *outdir;
static int bfs_ok(void) {
    for (int i = 0; i < N; i++) dist[i] = -1;
    int h = 0, t = 0; dist[0] = 0; q[t++] = 0;
    while (h < t) { int x = q[h++]; if (dist[x] == 5) continue;
        for (int i = 0; i < K; i++) { int y = mul[T[i] * N + x]; if (dist[y] < 0) { dist[y] = dist[x] + 1; q[t++] = y; } } }
    return t == N;
}
static void hit(int f, int m) {
    cnt++; printf("HIT %d %d", f, m); for (int i = 0; i < K; i++) printf(" %d", T[i]); printf("\n");
    if (outdir) { char p[512]; snprintf(p, sizeof p, "%s/hit_%lld.edges", outdir, cnt); FILE *o = fopen(p, "w");
        fprintf(o, "%d\n", N); for (int x = 0; x < N; x++) if (inG[x]) for (int i = 0; i < K; i++) fprintf(o, "%d %d\n", x, mul[T[i] * N + x]); fclose(o); }
}
static int F, Mm;
static void recP(int need, int from, int at) {
    if (need == 0) { nsets++; if (bfs_ok()) hit(F, Mm); return; }
    for (int i = from; i < nP; i++) { T[at] = P[i][0]; T[at + 1] = P[i][1]; recP(need - 1, i + 1, at + 2); }
}
static void recI(int need, int from, int at) {
    if (need == 0) { recP(Mm, 0, at); return; }
    for (int i = from; i < nI; i++) { T[at] = I[i]; recI(need - 1, i + 1, at + 1); }
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int sub = atoi(argv[2]); K = atoi(argv[3]); outdir = getenv("OUTDIR");
    if (fscanf(f, "%d", &N) != 1) return 1;
    mul = malloc(sizeof(int) * N * N); for (int i = 0; i < N * N; i++) if (fscanf(f, "%d", &mul[i]) != 1) return 1;
    inG = malloc(sizeof(int) * N); char w[16]; int s = -1;
    while (fscanf(f, "%15s", w) == 1) { s++; for (int i = 0; i < N; i++) if (fscanf(f, "%d", &inG[i]) != 1) return 1; if (s == sub) break; }
    if (s != sub) { fprintf(stderr, "no SUB %d\n", sub); return 1; }
    int *inv = malloc(sizeof(int) * N), *seen = calloc(N, sizeof(int));
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv[a] = b;
    for (int x = 0; x < N; x++) if (!inG[x] && !seen[x]) { seen[x] = seen[inv[x]] = 1;
        if (inv[x] == x) I[nI++] = x; else { P[nP][0] = x; P[nP][1] = inv[x]; nP++; } }
    dist = malloc(sizeof(int) * N); q = malloc(sizeof(int) * N);
    fprintf(stderr, "N %d coset involutions %d pairs %d\n", N, nI, nP);
    for (F = K % 2; F <= K; F += 2) { Mm = (K - F) / 2; long long c0 = cnt, s0 = nsets; recI(F, 0, 0);
        printf("TYPE f %d m %d sets %lld hits %lld\n", F, Mm, nsets - s0, cnt - c0); fflush(stdout); }
    printf("DONE hits %lld\n", cnt);
    return 0;
}
