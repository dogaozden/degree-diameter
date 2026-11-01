/* c7odd: odd-order route to n = 169 (wildcard card c7, squad deep-37 round 1).
   ins : base cubic bipartite graph on n0 vertices (n0 = 168). One new vertex x joins side s; x is adjacent to three
         distinct vertices b1,b2,b3 of the other side t; each b_i loses one neighbour a_i (choice among its 3), so the
         a_i have degree 2. Exhaustive over all such choices up to Aut(base) when REPS=file gives colour-preserving
         orbit representatives r of side t: every object is equivalent to one containing some representative r.
   del : base on n0 = 170 vertices; delete one vertex (every choice), far at n = n0 - 1.
   far = unordered vertex pairs at distance > 7 (bit-parallel BFS, 7 steps).
   usage: c7odd BASE ins|del OUTPREFIX [keep]     env: SIDE=s (side of x; default 0), REPS=file (ins only)
   Writes OUTPREFIX_<k>.edges for the keep best graphs and prints the far histogram (low end) and the best. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define MAXN 200
#define NW 4
typedef uint64_t u64;
static int n0, bn[MAXN][3], bd[MAXN], col[MAXN];
static int nb[MAXN][3], dg[MAXN];

static long far_count(int N) {
    static u64 R[MAXN][NW], F[MAXN][NW], G[MAXN][NW];
    int nw = (N + 63) / 64;
    for (int v = 0; v < N; v++) for (int w = 0; w < nw; w++) { R[v][w] = 0; F[v][w] = 0; }
    for (int v = 0; v < N; v++) { R[v][v >> 6] |= 1ULL << (v & 63); F[v][v >> 6] |= 1ULL << (v & 63); }
    for (int step = 0; step < 7; step++) {
        for (int v = 0; v < N; v++) {
            for (int w = 0; w < nw; w++) G[v][w] = 0;
            for (int j = 0; j < dg[v]; j++) { int u = nb[v][j]; for (int w = 0; w < nw; w++) G[v][w] |= F[u][w]; }
            for (int w = 0; w < nw; w++) G[v][w] &= ~R[v][w];
        }
        for (int v = 0; v < N; v++) for (int w = 0; w < nw; w++) { F[v][w] = G[v][w]; R[v][w] |= G[v][w]; }
    }
    long reached = 0;
    for (int v = 0; v < N; v++) for (int w = 0; w < nw; w++) reached += __builtin_popcountll(R[v][w]);
    long ordered_far = (long)N * (N - 1) - (reached - N);
    return ordered_far / 2;
}

static int remove_from(int v, int u) { for (int j = 0; j < dg[v]; j++) if (nb[v][j] == u) { nb[v][j] = nb[v][--dg[v]]; return 1; } return 0; }
static void replace_in(int v, int old, int neu) { for (int j = 0; j < dg[v]; j++) if (nb[v][j] == old) { nb[v][j] = neu; return; } }

#define KEEP 16
static long hist[1000];
static long bestfar[KEEP]; static int bestN[KEEP], nbest = 0, keep = 5;
static int snb[KEEP][MAXN][3], sdg[KEEP][MAXN];
static long evals = 0;

static void offer(long f, int N) {
    evals++;
    if (f < 1000) hist[f]++;
    if (nbest == keep && f >= bestfar[nbest - 1]) return;
    int pos = (nbest < keep) ? nbest++ : nbest - 1;
    while (pos > 0 && bestfar[pos - 1] > f) {
        bestfar[pos] = bestfar[pos - 1]; bestN[pos] = bestN[pos - 1];
        memcpy(snb[pos], snb[pos - 1], sizeof snb[0]); memcpy(sdg[pos], sdg[pos - 1], sizeof sdg[0]); pos--;
    }
    bestfar[pos] = f; bestN[pos] = N;
    memcpy(snb[pos], nb, sizeof nb); memcpy(sdg[pos], dg, sizeof dg);
}

static void load_base(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(2); }
    static int ea[2000], eb[2000]; int m = 0, a, b;
    if (fscanf(f, "%d", &n0) != 1) exit(2);
    while (fscanf(f, "%d %d", &a, &b) == 2) { ea[m] = a; eb[m] = b; m++; }
    fclose(f);
    memset(bd, 0, sizeof bd);
    for (int i = 0; i < m; i++) { bn[ea[i]][bd[ea[i]]++] = eb[i]; bn[eb[i]][bd[eb[i]]++] = ea[i]; }
    for (int v = 0; v < n0; v++) col[v] = -1;
    static int q[MAXN]; int h = 0, t = 0; col[0] = 0; q[t++] = 0;
    while (h < t) { int v = q[h++]; for (int j = 0; j < bd[v]; j++) { int u = bn[v][j]; if (col[u] < 0) { col[u] = 1 - col[v]; q[t++] = u; } } }
    fprintf(stderr, "base n=%d edges=%d\n", n0, m);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: c7odd BASE ins|del OUTPREFIX [keep]\n"); return 2; }
    load_base(argv[1]);
    const char *mode = argv[2];
    if (argc > 4) keep = atoi(argv[4]);
    if (keep > KEEP) keep = KEEP;
    int side = getenv("SIDE") ? atoi(getenv("SIDE")) : 0;
    int t = 1 - side;
    if (strcmp(mode, "ins") == 0) {
        int N = n0 + 1, x = n0;
        int reps[MAXN], nr = 0;
        if (getenv("REPS")) {
            FILE *f = fopen(getenv("REPS"), "r"); int r, c, k;
            while (fscanf(f, "%d %d %d", &r, &c, &k) == 3) if (c == t) reps[nr++] = r;
            fclose(f);
        } else { for (int v = 0; v < n0; v++) if (col[v] == t) reps[nr++] = v; }
        int cand[MAXN], nc = 0;
        for (int v = 0; v < n0; v++) if (col[v] == t) cand[nc++] = v;
        fprintf(stderr, "side(x)=%d endpoints side=%d reps=%d cand=%d\n", side, t, nr, nc);
        for (int ri = 0; ri < nr; ri++) {
            int r = reps[ri];
            for (int i = 0; i < nc; i++) { if (cand[i] == r) continue;
              for (int j = i + 1; j < nc; j++) { if (cand[j] == r) continue;
                for (int c = 0; c < 27; c++) {
                    int ch[3] = { c % 3, (c / 3) % 3, c / 9 };
                    int bs[3] = { r, cand[i], cand[j] };
                    memcpy(nb, bn, sizeof bn); memcpy(dg, bd, sizeof bd);
                    for (int q = 0; q < 3; q++) {
                        int b = bs[q]; int a = bn[b][ch[q]];
                        replace_in(b, a, x);
                        remove_from(a, b);
                    }
                    dg[x] = 3; nb[x][0] = bs[0]; nb[x][1] = bs[1]; nb[x][2] = bs[2];
                    offer(far_count(N), N);
                }
              }
            }
        }
    } else if (strcmp(mode, "del") == 0) {
        for (int x = 0; x < n0; x++) {
            int map[MAXN]; int N = 0;
            for (int v = 0; v < n0; v++) map[v] = (v == x) ? -1 : N++;
            for (int v = 0; v < n0; v++) { if (v == x) continue; int w = map[v]; dg[w] = 0;
                for (int j = 0; j < bd[v]; j++) { int u = bn[v][j]; if (u == x) continue; nb[w][dg[w]++] = map[u]; } }
            offer(far_count(N), N);
            printf("del %d far %ld\n", x, far_count(N));
        }
    } else { fprintf(stderr, "unknown mode\n"); return 2; }
    fprintf(stderr, "evaluated %ld\n", evals);
    for (long f = 0; f < 1000; f++) if (hist[f] && f <= 150) printf("hist far %ld count %ld\n", f, hist[f]);
    for (int k = 0; k < nbest; k++) {
        char fn[600]; snprintf(fn, sizeof fn, "%s_%d.edges", argv[3], k);
        FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", bestN[k]);
        for (int v = 0; v < bestN[k]; v++) for (int j = 0; j < sdg[k][v]; j++) if (snb[k][v][j] > v) fprintf(f, "%d %d\n", v, snb[k][v][j]);
        fclose(f);
        printf("best %d far %ld file %s\n", k, bestfar[k], fn);
    }
    return 0;
}
