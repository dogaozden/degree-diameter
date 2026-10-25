/* pack2.c (card c7 variant of pack.c: clustered distance-2 forced insertions + maximality refill):  iterated local search for large partial distance-2 ovoids of H(q) (point sets with at most one point on
   every line = non-collinear sets, R_H of the typed construction) or, in mode L, the dual (line sets with at most one
   line through every point = non-concurrent sets, R_L).  ARW-style ILS for maximum independent sets in the
   collinearity graph.  Elements = points (mode P) or lines (mode L); cells = lines (P) or points (L).
   Swap move at a chosen x: drop x and add one 1-tight element from each cell of x that has one (elements on different
   cells of x are never adjacent: the hexagon has no triangles), gain = (#such cells) - 1.  Perturbation: force-insert
   a random element (dropping its <= q+1 conflicting chosen elements), then swaps on the affected region; the best set
   is kept and restored when the current one falls behind.
   usage: pack HEXBIN P|L SEED SECONDS [START.txt] OUT.txt  (OUT rewritten at each improvement; ids one per line) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

static int q, N, Q1;
static int *EC, *CE;     /* element -> cells, cell -> elements (Q1 each) */
static int *owner, *tight, *sol, *pos, ns;
static char *in;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int *queue, nq, *qmark, qstamp = 1;
static inline void push(int e) { if (qmark[e] != qstamp) { qmark[e] = qstamp; queue[nq++] = e; } }

static void add(int e) {
    in[e] = 1; pos[e] = ns; sol[ns++] = e;
    for (int i = 0; i < Q1; i++) {
        int c = EC[e * Q1 + i]; owner[c] = e;
        for (int t = 0; t < Q1; t++) { int f = CE[c * Q1 + t]; if (f != e) tight[f]++; }
    }
}
static void rem(int e) {   /* also queues the chosen elements near the elements whose tightness drops */
    in[e] = 0; int p = pos[e]; sol[p] = sol[--ns]; pos[sol[p]] = p;
    for (int i = 0; i < Q1; i++) {
        int c = EC[e * Q1 + i]; owner[c] = -1;
        for (int t = 0; t < Q1; t++) {
            int f = CE[c * Q1 + t]; if (f == e) continue;
            if (--tight[f] <= 1) for (int i2 = 0; i2 < Q1; i2++) { int o = owner[EC[f * Q1 + i2]]; if (o >= 0) push(o); }
        }
    }
}
static int fill_near(int e) {   /* add free elements on the cells of e */
    int got = 0;
    for (int i = 0; i < Q1; i++) {
        int c = EC[e * Q1 + i];
        for (int t = 0; t < Q1; t++) { int f = CE[c * Q1 + t]; if (!in[f] && tight[f] == 0) { add(f); got++; } }
    }
    return got;
}
static int pick[64];
static int rl[1 << 16], nrl;   /* elements removed by the current perturbation */
static int try_swap(int x, int allow_zero) {
    int ncell = 0;
    for (int i = 0; i < Q1; i++) {
        int c = EC[x * Q1 + i], k = 0, chosen = -1;
        for (int t = 0; t < Q1; t++) {
            int f = CE[c * Q1 + t];
            if (f != x && !in[f] && tight[f] == 1) { k++; if (rnd() % k == 0) chosen = f; }
        }
        if (chosen >= 0) pick[ncell++] = chosen;
    }
    if (ncell >= 2 || (allow_zero && ncell == 1)) {
        rem(x);
        for (int i = 0; i < ncell; i++) add(pick[i]);
        fill_near(x);
        for (int i = 0; i < ncell; i++) push(pick[i]);
        return ncell - 1;
    }
    return -1;
}
static void run_queue(void) {
    while (nq) {
        int x = queue[--nq]; qmark[x] = 0;
        if (in[x]) try_swap(x, 0);
    }
}
int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: pack HEXBIN P|L SEED SECONDS [START] OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int hdr[3];
    if (fread(hdr, 4, 3, f) != 3) return 1;
    q = hdr[0]; N = hdr[1]; Q1 = q + 1;
    int *LP = malloc(sizeof(int) * N * Q1);
    if (fread(LP, 4, (size_t)N * Q1, f) != (size_t)N * Q1) return 1;
    fclose(f);
    int *PL = malloc(sizeof(int) * N * Q1); int *cnt = calloc(N, sizeof(int));
    for (int l = 0; l < N; l++) for (int i = 0; i < Q1; i++) { int p = LP[l * Q1 + i]; PL[p * Q1 + cnt[p]++] = l; }
    int modeL = argv[2][0] == 'L';
    EC = modeL ? LP : PL; CE = modeL ? PL : LP;
    rs = 0x9E3779B97F4A7C15ULL ^ (uint64_t)atoll(argv[3]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[4]);
    const char *outfn = argv[argc - 1];
    owner = malloc(sizeof(int) * N); memset(owner, -1, sizeof(int) * N);
    tight = calloc(N, sizeof(int)); in = calloc(N, 1); sol = malloc(sizeof(int) * N); pos = malloc(sizeof(int) * N);
    queue = malloc(sizeof(int) * N); qmark = calloc(N, sizeof(int));
    if (argc == 7) {
        FILE *g = fopen(argv[5], "r"); int e;
        while (fscanf(g, "%d", &e) == 1) { if (!in[e] && tight[e] == 0) add(e); else fprintf(stderr, "start conflict %d\n", e); }
        fclose(g);
    }
    int *perm = malloc(sizeof(int) * N); for (int i = 0; i < N; i++) perm[i] = i;
    for (int i = N - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    for (int i = 0; i < N; i++) if (!in[perm[i]] && tight[perm[i]] == 0) add(perm[i]);
    fprintf(stderr, "start %d\n", ns);
    nq = 0; for (int i = 0; i < ns; i++) push(sol[i]);
    run_queue();
    fprintf(stderr, "after LS %d\n", ns);
    int best = ns; int *bestsol = malloc(sizeof(int) * N); memcpy(bestsol, sol, sizeof(int) * ns);
    clock_t t0 = clock(); long it = 0; double lastprint = 0, lastsave = 0; int saved = best;
    while (1) {
        it++;
        if ((it & 1023) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > secs) break;
            if (el - lastprint > 60) { lastprint = el; fprintf(stderr, "t=%.0f it=%ld cur=%d best=%d\n", el, it, ns, best); }
            if (best > saved && el - lastsave > 20) {
                FILE *o = fopen(outfn, "w"); for (int i = 0; i < best; i++) fprintf(o, "%d\n", bestsol[i]); fclose(o);
                saved = best; lastsave = el;
            }
        }
        /* perturbation v2: force-insert a base element (low tightness); with prob 1/2 the forced set is a cluster of
           2-3 elements, each at collinearity distance 2 from the previous one (so the forced region is local); then
           refill every element freed by the removals (maximality repair: pack v1 never re-added freed free elements) */
        nrl = 0;
        int clustered = (rnd() % 2 == 0);
        int kk = clustered ? 2 + (int)(rnd() % 2) : ((rnd() % 8 == 0) ? 2 : 1);
        int prev = -1;
        for (int r = 0; r < kk; r++) {
            int x = -1;
            if (r > 0 && clustered) {
                int L = EC[prev * Q1 + rnd() % Q1];
                int z = CE[L * Q1 + rnd() % Q1];
                int M = (z == prev) ? -1 : EC[z * Q1 + rnd() % Q1];
                if (M >= 0 && M != L) { int y = CE[M * Q1 + rnd() % Q1]; if (y != z && y != prev) x = y; }
            }
            if (x < 0) {
                do { x = rnd() % N; } while (in[x]);
                for (int tr = 0; tr < 3 && tight[x] > 1; tr++) { int y = rnd() % N; if (!in[y] && tight[y] < tight[x]) x = y; }
            }
            if (in[x]) continue;
            for (int i = 0; i < Q1; i++) { int c = EC[x * Q1 + i]; if (owner[c] >= 0) { rl[nrl++] = owner[c]; rem(owner[c]); } }
            add(x); push(x); prev = x;
        }
        for (int i = 0; i < nrl; i++) {
            int y = rl[i];
            for (int j = 0; j < Q1; j++) { int c = EC[y * Q1 + j];
                for (int t = 0; t < Q1; t++) { int f = CE[c * Q1 + t]; if (!in[f] && tight[f] == 0) { add(f); push(f); } } }
        }
        run_queue();
        if (ns > best) {
            best = ns; memcpy(bestsol, sol, sizeof(int) * ns);
        } else if (ns < best - 2 || (ns < best && rnd() % 128 == 0)) {
            while (ns) { int e = sol[ns - 1]; in[e] = 0; ns--; }
            memset(owner, -1, sizeof(int) * N); memset(tight, 0, sizeof(int) * N);
            for (int i = 0; i < best; i++) add(bestsol[i]);
            nq = 0;
        }
    }
    while (ns) { int e = sol[ns - 1]; in[e] = 0; ns--; }
    memset(owner, -1, sizeof(int) * N); memset(tight, 0, sizeof(int) * N);
    for (int i = 0; i < best; i++) { if (tight[bestsol[i]] || in[bestsol[i]]) { fprintf(stderr, "VERIFY FAIL\n"); return 2; } add(bestsol[i]); }
    FILE *o = fopen(outfn, "w"); for (int i = 0; i < ns; i++) fprintf(o, "%d\n", sol[i]); fclose(o);
    printf("best %d after %ld iterations (verified: at most one chosen element per cell)\n", best, it);
    return 0;
}
