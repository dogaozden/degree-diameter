/* tabucol-style search: proper k-colouring of the collinearity graph of H(5) (points), with class sizes pulled to
   target T = N/k. cost = conflicts + sum_c |n_c - T|. usage: ./tabu coll.txt k seed maxiters out.txt */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define MAXN 4000
#define DEG 30
int N, K, T;
int adj[MAXN][DEG];
int col[MAXN], cnt[MAXN][16], nc[16];
long tabu_until[MAXN][16];
static unsigned long long rs;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    K = atoi(argv[2]);
    rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[3]) * 2654435761ULL;
    long maxit = atol(argv[4]);
    fscanf(f, "%d", &N);
    for (int p = 0; p < N; p++) for (int j = 0; j < DEG; j++) fscanf(f, "%d", &adj[p][j]);
    fclose(f);
    T = N / K;
    /* balanced random start */
    int perm[MAXN];
    for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    memset(nc, 0, sizeof nc);
    for (int i = 0; i < N; i++) { col[perm[i]] = i % K; nc[i % K]++; }
    memset(cnt, 0, sizeof cnt);
    for (int p = 0; p < N; p++) for (int j = 0; j < DEG; j++) cnt[p][col[adj[p][j]]]++;
    long conf = 0;
    for (int p = 0; p < N; p++) conf += cnt[p][col[p]];
    conf /= 2;
    long imb = 0; for (int c = 0; c < K; c++) imb += abs(nc[c] - T);
    long cost = conf + (getenv("NOIMB") ? 0 : imb), best = cost;
    fprintf(stderr, "start conf %ld imb %ld\n", conf, imb);
    for (long it = 0; it < maxit && cost > 0; it++) {
        long bd = 1L << 60; int bv = -1, bb = -1, nties = 0;
        for (int v = 0; v < N; v++) {
            int a = col[v];
            if (cnt[v][a] == 0 && nc[a] <= T && nc[a] >= T) { /* quick skip only when balanced and no conflict */ }
            for (int b = 0; b < K; b++) {
                if (b == a) continue;
                long d = (long)cnt[v][b] - cnt[v][a];
                int na = nc[a], nb = nc[b];
                if (getenv("NOIMB") == NULL) d += abs(na - 1 - T) - abs(na - T) + abs(nb + 1 - T) - abs(nb - T);
                int istabu = tabu_until[v][b] > it;
                if (istabu && cost + d >= best) continue;
                if (d < bd) { bd = d; bv = v; bb = b; nties = 1; }
                else if (d == bd) { nties++; if (rnd() % nties == 0) { bv = v; bb = b; } }
            }
        }
        if (bv < 0) continue;
        int a = col[bv], b = bb;
        tabu_until[bv][a] = it + 10 + (rnd() % 10) + (conf > 0 ? conf / 2 : 0);
        col[bv] = b; nc[a]--; nc[b]++;
        for (int j = 0; j < DEG; j++) { int u = adj[bv][j]; cnt[u][a]--; cnt[u][b]++; }
        conf = 0; for (int p = 0; p < N; p++) conf += cnt[p][col[p]];
        conf /= 2;
        imb = 0; for (int c = 0; c < K; c++) imb += abs(nc[c] - T);
        cost = conf + (getenv("NOIMB") ? 0 : imb);
        if (cost < best) { best = cost; }
        if (it % 20000 == 0) fprintf(stderr, "it %ld conf %ld imb %ld best %ld\n", it, conf, imb, best);
    }
    fprintf(stderr, "final conf %ld imb %ld\n", conf, imb);
    if (cost == 0) {
        FILE *o = fopen(argv[5], "w");
        for (int p = 0; p < N; p++) fprintf(o, "%d\n", col[p]);
        fclose(o);
        printf("FOUND\n");
    } else printf("NOTFOUND cost %ld\n", cost);
    return 0;
}
