/* dlx2.c: Knuth Algorithm X (dancing links, min-column heuristic, random tie-breaks) for an orbit exact-cover instance.
   usage: dlx2 INST OUT CPU_SECONDS SEED
   INST: "rows cols" then per row: "rowid c1 c2 ..."  (rowid = orbit-graph vertex / orbit index, reported back)
   Writes the rowids of the best solution to OUT: a full exact cover if one is found, otherwise the deepest
   partial cover reached (a packing: its rows have pairwise disjoint columns). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

static int *Lf, *Rt, *Up, *Dn, *Cl, *Rw, *Sz;
static int ncol, nrow;
static int *sol, *bestsol, maxdepth = 0, bestdepth = 0, found = 0, soldepth = 0;
static long long nodes = 0;
static double budget;
static int timed_out = 0;
static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

static void cover(int c) {
    Rt[Lf[c]] = Rt[c]; Lf[Rt[c]] = Lf[c];
    for (int i = Dn[c]; i != c; i = Dn[i])
        for (int j = Rt[i]; j != i; j = Rt[j]) {
            Dn[Up[j]] = Dn[j]; Up[Dn[j]] = Up[j]; Sz[Cl[j]]--;
        }
}
static void uncover(int c) {
    for (int i = Up[c]; i != c; i = Up[i])
        for (int j = Lf[i]; j != i; j = Lf[j]) {
            Sz[Cl[j]]++; Dn[Up[j]] = j; Up[Dn[j]] = j;
        }
    Rt[Lf[c]] = c; Lf[Rt[c]] = c;
}
static int search(int k) {
    nodes++;
    if (k > maxdepth) maxdepth = k;
    if (k > bestdepth) { bestdepth = k; memcpy(bestsol, sol, sizeof(int) * k); }
    if ((nodes & 0xFFFF) == 0) {
        if ((double)clock() / CLOCKS_PER_SEC > budget) timed_out = 1;
    }
    if (timed_out) return 0;
    int root = ncol;
    if (Rt[root] == root) { found = 1; soldepth = k; memcpy(bestsol, sol, sizeof(int) * k); bestdepth = k; return 1; }
    int best = -1, bs = 1 << 30, ncand = 0;
    for (int c = Rt[root]; c != root; c = Rt[c]) {
        if (Sz[c] < bs) { bs = Sz[c]; best = c; ncand = 1; }
        else if (Sz[c] == bs) { ncand++; if (rnd() % ncand == 0) best = c; }
    }
    if (bs == 0) return 0;
    int c = best;
    cover(c);
    for (int r = Dn[c]; r != c; r = Dn[r]) {
        sol[k] = Rw[r];
        for (int j = Rt[r]; j != r; j = Rt[j]) cover(Cl[j]);
        if (search(k + 1)) return 1;
        for (int j = Lf[r]; j != r; j = Lf[j]) uncover(Cl[j]);
        if (timed_out) break;
    }
    uncover(c);
    return 0;
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: dlx2 INST OUT CPU SEED\n"); return 1; }
    budget = atof(argv[3]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)atoll(argv[4]) * 2654435761ULL); if (!rs) rs = 1;
    FILE *f = fopen(argv[1], "r");
    if (!f) return 1;
    if (fscanf(f, "%d %d", &nrow, &ncol) != 2) return 1;
    int *rid = malloc(sizeof(int) * nrow);
    int **rc = malloc(sizeof(int *) * nrow);
    int *rl = malloc(sizeof(int) * nrow);
    char line[1 << 16];
    fgets(line, sizeof line, f);
    for (int i = 0; i < nrow; i++) {
        if (!fgets(line, sizeof line, f)) return 1;
        int cap = 16, n = 0; rc[i] = malloc(sizeof(int) * cap);
        char *p = line; int v, off;
        if (sscanf(p, "%d%n", &rid[i], &off) != 1) return 1;
        p += off;
        while (sscanf(p, "%d%n", &v, &off) == 1) {
            if (n == cap) { cap *= 2; rc[i] = realloc(rc[i], sizeof(int) * cap); }
            rc[i][n++] = v; p += off;
        }
        rl[i] = n;
    }
    fclose(f);
    int *perm = malloc(sizeof(int) * nrow);
    for (int i = 0; i < nrow; i++) perm[i] = i;
    for (int i = nrow - 1; i > 0; i--) { int j = rnd() % (i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
    int total = 0; for (int i = 0; i < nrow; i++) total += rl[i];
    int tot = ncol + 1 + total + 1;
    Lf = malloc(sizeof(int) * tot); Rt = malloc(sizeof(int) * tot);
    Up = malloc(sizeof(int) * tot); Dn = malloc(sizeof(int) * tot);
    Cl = malloc(sizeof(int) * tot); Rw = malloc(sizeof(int) * tot);
    Sz = malloc(sizeof(int) * (ncol + 1));
    for (int c = 0; c <= ncol; c++) {
        Up[c] = Dn[c] = c; Cl[c] = c; Sz[c] = 0; Rw[c] = -1;
    }
    /* header ring: 0..ncol-1 with root ncol */
    for (int c = 0; c <= ncol; c++) {
        Lf[c] = (c == 0) ? ncol : c - 1;
        Rt[c] = (c == ncol) ? 0 : c + 1;
    }
    int nd = ncol + 1;
    for (int pi = 0; pi < nrow; pi++) {
        int i = perm[pi];
        int first = -1;
        for (int k = 0; k < rl[i]; k++) {
            int c = rc[i][k];
            int x = nd++;
            Cl[x] = c; Rw[x] = i;
            Up[x] = Up[c]; Dn[x] = c; Dn[Up[c]] = x; Up[c] = x; Sz[c]++;
            if (first < 0) { first = x; Lf[x] = Rt[x] = x; }
            else { Rt[x] = first; Lf[x] = Lf[first]; Rt[Lf[first]] = x; Lf[first] = x; }
        }
    }
    sol = malloc(sizeof(int) * (ncol + 2)); bestsol = malloc(sizeof(int) * (ncol + 2));
    int ok = search(0);
    double used = (double)clock() / CLOCKS_PER_SEC;
    printf("result %s nodes %lld maxdepth %d cpu %.1f\n", ok ? "FOUND" : (timed_out ? "TIMEOUT" : "EXHAUSTED"), nodes, maxdepth, used);
    FILE *o = fopen(argv[2], "w");
    int d = ok ? soldepth : bestdepth;
    for (int k = 0; k < d; k++) fprintf(o, "%d\n", rid[bestsol[k]]);
    fclose(o);
    printf("wrote %d rows (%s)\n", d, ok ? "cover" : "packing");
    return 0;
}
