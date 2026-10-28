/* rstab.c: fixed-size tabu search for the spread-restricted relaxed sets of W(q) (card c3, squad d5relax-r1).
   Restricted model: T has at most 1 point on each non-spread line of W(q) and at most 2 points on each line of the
   regular spread (equivalently: every collinear pair of T lies on a spread line, and T is relaxed).
   Penalty f = sum_L max(0, cnt[L] - cap[L]), cap = 2 on spread lines, 1 elsewhere.  Same move scheme as rtabu:
   when f = 0 the set is recorded and grown by its cheapest addition; otherwise swap the most-conflicting non-tabu
   member for the cheapest non-tabu outside point; random perturbation after a long stall.
   usage: rstab PREFIX seconds seed out [-k kstart] [-i START]   PREFIX e.g. /path/data/W11 (reads _lines, _spread)
   output: size, then the points (rtabu format). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n, NL, d, q1;
static int *pl, *lp, *cap, *cnt, *inT, *Tl, *pos, *tabu, k;
static long f;
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (unsigned)(rs >> 11); }

static inline long addCost(int u) { long c = 0; for (int j = 0; j < d; j++) { int L = pl[u * d + j]; if (cnt[L] >= cap[L]) c++; } return c; }
static inline long remCost(int v) { long c = 0; for (int j = 0; j < d; j++) { int L = pl[v * d + j]; if (cnt[L] > cap[L]) c++; } return c; }
static void addv(int u) {
    f += addCost(u);
    for (int j = 0; j < d; j++) cnt[pl[u * d + j]]++;
    inT[u] = 1; pos[u] = k; Tl[k++] = u;
}
static void remv(int v) {
    f -= remCost(v);
    for (int j = 0; j < d; j++) cnt[pl[v * d + j]]--;
    inT[v] = 0; int p = pos[v]; Tl[p] = Tl[--k]; pos[Tl[p]] = p;
}
static long recompute(void) { long g = 0; for (int L = 0; L < NL; L++) if (cnt[L] > cap[L]) g += cnt[L] - cap[L]; return g; }
static void save(const char *fn) {
    FILE *o = fopen(fn, "w"); fprintf(o, "%d\n", k);
    for (int i = 0; i < k; i++) fprintf(o, "%d\n", Tl[i]);
    fclose(o);
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: rstab PREFIX seconds seed out [-k K] [-i START]\n"); return 1; }
    char fn[512]; FILE *g;
    /* lines */
    snprintf(fn, sizeof fn, "%s_lines.txt", argv[1]); g = fopen(fn, "r");
    if (!g || fscanf(g, "%d", &NL) != 1) return 1;
    int first = 1; (void)first;
    /* line length = q+1, read the first line to get it */
    int *tmp = NULL; int cap_pts = 0; (void)tmp; (void)cap_pts;
    int lenL = 0; { char buf[1 << 16]; if (!fgets(buf, sizeof buf, g)) return 1; if (!fgets(buf, sizeof buf, g)) return 1;
      for (char *p = buf; *p; p++) if (*p == ' ' || *p == '\n') {} lenL = 0; char *s = buf; int x, nread; while (sscanf(s, "%d%n", &x, &nread) == 1) { lenL++; s += nread; } }
    d = lenL; /* points per line = q+1, and lines per point = q+1 as well */
    lp = malloc((size_t)NL * d * sizeof(int));
    rewind(g); { int tmpNL; fscanf(g, "%d", &tmpNL); }
    for (int L = 0; L < NL; L++) for (int j = 0; j < d; j++) if (fscanf(g, "%d", &lp[L * d + j]) != 1) return 1;
    fclose(g);
    n = 0; for (int L = 0; L < NL; L++) for (int j = 0; j < d; j++) if (lp[L * d + j] + 1 > n) n = lp[L * d + j] + 1;
    /* spread */
    snprintf(fn, sizeof fn, "%s_spread.txt", argv[1]); g = fopen(fn, "r");
    int *sp = malloc(n * sizeof(int)); for (int i = 0; i < n; i++) if (fscanf(g, "%d", &sp[i]) != 1) return 1; fclose(g);
    /* point -> lines */
    int *pc = calloc(n, sizeof(int)); pl = malloc((size_t)n * d * sizeof(int));
    for (int L = 0; L < NL; L++) for (int j = 0; j < d; j++) { int v = lp[L * d + j]; if (pc[v] >= d) { fprintf(stderr, "bad incidence\n"); return 1; } pl[v * d + pc[v]++] = L; }
    for (int v = 0; v < n; v++) if (pc[v] != d) { fprintf(stderr, "bad incidence count\n"); return 1; }
    /* line capacities: a line is a spread line iff all its points share one spread class */
    cap = malloc(NL * sizeof(int));
    for (int L = 0; L < NL; L++) { int same = 1; for (int j = 1; j < d; j++) if (sp[lp[L * d + j]] != sp[lp[L * d]]) same = 0; cap[L] = same ? 2 : 1; }
    cnt = calloc(NL, sizeof(int)); inT = calloc(n, sizeof(int)); Tl = malloc(n * sizeof(int)); pos = malloc(n * sizeof(int));
    tabu = calloc(n, sizeof(int));
    double secs = atof(argv[2]); rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL;
    for (int i = 0; i < 20; i++) rnd();
    const char *outf = argv[4]; int kstart = 0; const char *startf = NULL;
    for (int a = 5; a + 1 < argc; a += 2) {
        if (!strcmp(argv[a], "-k")) kstart = atoi(argv[a + 1]);
        else if (!strcmp(argv[a], "-i")) startf = argv[a + 1];
    }
    k = 0; f = 0;
    if (startf) {
        FILE *st = fopen(startf, "r"); int m, v;
        if (fscanf(st, "%d", &m) == 1) while (fscanf(st, "%d", &v) == 1) if (!inT[v]) addv(v);
        fclose(st);
    }
    { /* greedy zero-cost fill in random order */
        int *perm = malloc(n * sizeof(int)); for (int i = 0; i < n; i++) perm[i] = i;
        for (int i = n - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        if (f == 0) for (int i = 0; i < n; i++) { int v = perm[i]; if (!inT[v] && addCost(v) == 0) addv(v); }
        free(perm);
    }
    int best = 0;
    if (f == 0) { best = k; save(outf); }
    while (k < kstart) { long bd = 1L << 40; int bu = -1, ties = 0; for (int u = 0; u < n; u++) if (!inT[u]) { long c = addCost(u); if (c < bd) { bd = c; bu = u; ties = 1; } else if (c == bd && rnd() % (++ties) == 0) bu = u; } addv(bu); }
    clock_t t0 = clock(); long it = 0, lastimp = 0, bestf = f; int *cand = malloc(n * sizeof(int));
    while (1) {
        it++;
        if ((it & 1023) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC > secs) break;
        if (f == 0) {
            if (k > best) { best = k; save(outf); lastimp = it; fprintf(stderr, "size %d at it %ld, %.1f s\n", best, it, (double)(clock() - t0) / CLOCKS_PER_SEC); }
            long bd = 1L << 40; int nc = 0;
            for (int u = 0; u < n; u++) if (!inT[u]) { long c = addCost(u); if (c < bd) { bd = c; nc = 0; } if (c == bd) cand[nc++] = u; }
            addv(cand[rnd() % nc]); bestf = f; continue;
        }
        /* remove: largest conflict count among non-tabu members */
        long bd = -1; int nc = 0;
        for (int i = 0; i < k; i++) { int v = Tl[i]; if (tabu[v] > it) continue; long c = remCost(v); if (c > bd) { bd = c; nc = 0; } if (c == bd) cand[nc++] = v; }
        if (nc == 0) { cand[0] = Tl[rnd() % k]; nc = 1; }
        int v = cand[rnd() % nc]; remv(v); tabu[v] = it + 7 + rnd() % 10;
        /* add: smallest cost among non-tabu outside points (aspiration if it reaches f = 0) */
        bd = 1L << 40; nc = 0;
        for (int u = 0; u < n; u++) {
            if (inT[u] || u == v) continue;
            long c = addCost(u);
            if (tabu[u] > it && f + c != 0) continue;
            if (c < bd) { bd = c; nc = 0; } if (c == bd) cand[nc++] = u;
        }
        if (nc == 0) { nc = 1; cand[0] = v; }
        int u = cand[rnd() % nc]; addv(u); tabu[u] = it + 3 + rnd() % 4;
        if (f < bestf) { bestf = f; lastimp = it; }
        if (it - lastimp > 200000) {
            for (int r = 0; r < 3 + (int)(rnd() % 5); r++) {
                int a = Tl[rnd() % k]; remv(a); tabu[a] = it + 10;
                int b; do { b = rnd() % n; } while (inT[b]); addv(b); tabu[b] = it + 3;
            }
            lastimp = it; bestf = f;
        }
    }
    if (recompute() != f) { fprintf(stderr, "internal error: f mismatch\n"); return 2; }
    printf("best %d after %ld iterations\n", best, it);
    return 0;
}
