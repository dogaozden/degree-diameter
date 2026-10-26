/* tabu.c: fixed-size tabu search for relaxed sets T of W(9) (card r2c1).
   Points: 820 (in_W9.txt, from export_in.py). Penalty C(T) = sum_{v in T} max(0, cnt_T(v)-1) + (#spread edges in T),
   where cnt_T(v) = collinear neighbours of v in T and spread edges are the collinear pairs on lines of S.
   C(T)=0 <=> valid relaxed set. Search at |T|=k with swap moves (remove u in T, add w not in T), tabu tenure,
   perturbation after stagnation; when feasible, record and grow k by one.
   usage: tabu IN SEEDFILE(- for greedy) RNG SECONDS OUT [PERTURB]
   SEEDFILE: whitespace-separated point ids of a valid set (may be empty file/"-").  OUT: best set, one id per line,
   first line = size. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n, D;
static int *nb, *fb;
static char *in;
static int *cnt, *sf, *Tl, *tpos, k = 0;
static long *tabu;
static unsigned long long rs;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }

static void addp(int w) {
    in[w] = 1; tpos[w] = k; Tl[k++] = w;
    for (int j = 0; j < D; j++) { int x = nb[w * D + j]; cnt[x]++; sf[x] += fb[w * D + j]; }
}
static void remp(int u) {
    in[u] = 0; int p = tpos[u]; int last = Tl[--k]; Tl[p] = last; tpos[last] = p;
    for (int j = 0; j < D; j++) { int x = nb[u * D + j]; cnt[x]--; sf[x] -= fb[u * D + j]; }
}
static long fullcost(void) {
    long c = 0, s = 0;
    for (int i = 0; i < k; i++) { int v = Tl[i]; if (cnt[v] > 1) c += cnt[v] - 1; s += sf[v]; }
    return c + s / 2;
}
/* change of cost when u (in T) is removed */
static int Rof(int u) {
    int r = -(cnt[u] > 1 ? cnt[u] - 1 : 0) - sf[u];
    for (int j = 0; j < D; j++) { int x = nb[u * D + j]; if (in[x] && cnt[x] >= 2) r--; }
    return r;
}
/* change of cost when w (not in T) is added */
static int Aof(int w) {
    int a = (cnt[w] > 1 ? cnt[w] - 1 : 0) + sf[w];
    for (int j = 0; j < D; j++) { int x = nb[w * D + j]; if (in[x] && cnt[x] >= 1) a++; }
    return a;
}
static void greedy_add(void) {  /* add the point of minimum A (random ties) outside T */
    int best = 1 << 30, nt = 0, pick = -1;
    for (int w = 0; w < n; w++) if (!in[w]) {
        int a = Aof(w);
        if (a < best) { best = a; nt = 0; }
        if (a == best) { nt++; if (rnd() % nt == 0) pick = w; }
    }
    addp(pick);
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: tabu IN SEEDFILE RNG SECONDS OUT [PERTURB]\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 1;
    if (fscanf(f, "%d", &n) != 1) return 1;
    D = 90;
    nb = malloc(sizeof(int) * n * D); fb = malloc(sizeof(int) * n * D);
    for (int i = 0; i < n; i++) {
        int dg; if (fscanf(f, "%d", &dg) != 1 || dg != D) { fprintf(stderr, "degree mismatch at %d\n", i); return 1; }
        for (int j = 0; j < D; j++) if (fscanf(f, "%d %d", &nb[i * D + j], &fb[i * D + j]) != 2) return 1;
    }
    fclose(f);
    in = calloc(n, 1); cnt = calloc(n, sizeof(int)); sf = calloc(n, sizeof(int));
    Tl = malloc(sizeof(int) * n); tpos = malloc(sizeof(int) * n); tabu = calloc(n, sizeof(long));
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[3]) * 2654435761ULL; if (!rs) rs = 1;
    double secs = atof(argv[4]);
    long perturb_len = argc > 6 ? atol(argv[6]) : 20000;

    /* seed */
    if (strcmp(argv[2], "-") != 0) {
        FILE *s = fopen(argv[2], "r");
        if (s) { int v; while (fscanf(s, "%d", &v) == 1) if (v >= 0 && v < n && !in[v]) addp(v); fclose(s); }
    }
    while (k < 1) greedy_add();
    /* grow to a point where the set is still feasible-ish: add greedily until cost > 0 would appear */
    int bestk = 0; int *bestT = malloc(sizeof(int) * n);
    int *curbest = malloc(sizeof(int) * n);
    long cur = fullcost();
    if (cur == 0) { bestk = k; memcpy(bestT, Tl, sizeof(int) * k); }
    clock_t t0 = clock();
    long iter = 0, last_imp = 0; long bestc_k = cur;
    if (cur != 0) { /* start from the greedy/seed set: do a short repair first */
    }
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        iter++;
        if (cur == 0) {
            if (k > bestk) {
                bestk = k; memcpy(bestT, Tl, sizeof(int) * k);
                FILE *o = fopen(argv[5], "w"); fprintf(o, "%d\n", bestk); for (int i = 0; i < bestk; i++) fprintf(o, "%d\n", bestT[i]); fclose(o);
                printf("feasible k=%d iter=%ld t=%.1f\n", bestk, iter, (double)(clock() - t0) / CLOCKS_PER_SEC); fflush(stdout);
            }
            greedy_add(); cur = fullcost(); bestc_k = cur; last_imp = iter;
            continue;
        }
        /* choose swap by min R(u)+A(w) over non-tabu vertices (random ties) */
        int minR = 1 << 30, minA = 1 << 30;
        static int Rv[4096], Av[4096];
        for (int i = 0; i < k; i++) { int u = Tl[i]; if (tabu[u] > iter) { Rv[u] = 1 << 29; continue; } Rv[u] = Rof(u); if (Rv[u] < minR) minR = Rv[u]; }
        for (int w = 0; w < n; w++) { if (in[w]) continue; if (tabu[w] > iter) { Av[w] = 1 << 29; continue; } Av[w] = Aof(w); if (Av[w] < minA) minA = Av[w]; }
        int u = -1, w = -1, nu = 0, nw = 0;
        for (int i = 0; i < k; i++) { int x = Tl[i]; if (Rv[x] == minR) { nu++; if (rnd() % nu == 0) u = x; } }
        for (int y = 0; y < n; y++) if (!in[y] && Av[y] == minA) { nw++; if (rnd() % nw == 0) w = y; }
        if (u < 0 || w < 0) { continue; }
        int tt = 5 + rnd() % (k / 6 + 4);
        remp(u); addp(w);
        tabu[u] = iter + tt; tabu[w] = iter + tt / 2 + 1;
        cur = fullcost();
        if (cur < bestc_k) { bestc_k = cur; last_imp = iter; }
        /* stagnation: perturb by random swaps */
        if (iter - last_imp > perturb_len) {
            int r = 2 + rnd() % 5;
            for (int t = 0; t < r; t++) {
                int a = Tl[rnd() % k]; remp(a); tabu[a] = iter + 10;
                int b; do { b = rnd() % n; } while (in[b] || tabu[b] > iter);
                addp(b); tabu[b] = iter + 3;
            }
            cur = fullcost(); bestc_k = cur; last_imp = iter;
        }
    }
    printf("done bestk=%d iters=%ld\n", bestk, iter);
    return 0;
}
