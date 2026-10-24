/* arw.c -- ARW-style iterated local search (Andrade, Resende, Werneck 2012) for a maximum independent set
 * in the orthogonality graph on the 15,984 points of E (elliptic quadric Q^-(5,11)), built from the
 * coordinates in E11.map. Independent set = pairwise non-orthogonal points (partial ovoid).
 *
 * Machinery: tightness counts tight[w] = #solution neighbours, sumS[w] = sum of their ids (so the unique
 * solution neighbour of a 1-tight vertex is sumS[w]); free list; (1,2)-swap candidates kept in a queue
 * (a solution vertex is queued when one of its neighbours becomes 1-tight); perturbation = forced insertion
 * of a candidate (least tightness among SAMP random non-solution vertices, ties to the oldest); journal of
 * add/remove operations for undo; acceptance: worse solutions accepted with prob 1/(1+d*d*) (ARW rule);
 * restart from the best solution after RESTART iterations without a new best.
 *
 * Usage: ./arw SECONDS SEED OUTFLAGS [INFLAGS|-] [SAMP] [RESTART]
 *   OUTFLAGS is rewritten on every improvement, lines "point_id spread_line_id" (scorer format).
 *   INFLAGS (optional) is a start set in the same format; it must be independent.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>

#define QP 11
#define MAPFILE "/home/user/degree-diameter/research/cell147/data/E11.map"

static int n, D;
static int *nbr;                 /* n*D adjacency lists */
static int *pidv, *lidv;         /* point id, spread line id per vertex */
static int (*co)[7];             /* coordinates x0..x6 per vertex */
static int maxpid, *pidmap;

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27; return rs * 2685821657736338717ULL; }
static inline int rndi(int m) { return (int)((rnd() >> 11) % (uint64_t)m); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

/* adjacency = orthogonality: B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 = 0 (mod 11) */
static inline int isadj(int a, int b) {
    const int *x = co[a], *y = co[b];
    int s = x[0]*y[4] + x[4]*y[0] + x[1]*y[5] + x[5]*y[1] + x[2]*y[6] + x[6]*y[2] - 2*x[3]*y[3];
    s %= QP; if (s < 0) s += QP;
    return s == 0;
}

static char *inS, *inQ;
static int *tight, *sumS, *stampv;
static int *sol, *spos, sz;
static int *fl, *fpos, fsz;
static int *qu, qh, qt, QCAP, enq_on = 1;
static int *jv; static char *jo; static long jn, jcap;
static int journaling, undoing;
static long iter;
static int *Lb, *tmpS, *bestsol, bestsz;

static void jpush(int v, char op) {
    if (jn == jcap) {
        jcap = jcap * 2 + 4096;
        jv = realloc(jv, jcap * sizeof(int));
        jo = realloc(jo, jcap);
        if (!jv || !jo) { fprintf(stderr, "oom\n"); exit(1); }
    }
    jv[jn] = v; jo[jn] = op; jn++;
}
static void fl_add(int v) { if (fpos[v] < 0) { fpos[v] = fsz; fl[fsz++] = v; } }
static void fl_del(int v) {
    int p = fpos[v];
    if (p >= 0) { int last = fl[--fsz]; fl[p] = last; fpos[last] = p; fpos[v] = -1; }
}
static void sol_add(int v) { spos[v] = sz; sol[sz++] = v; }
static void sol_del(int v) { int p = spos[v]; int last = sol[--sz]; sol[p] = last; spos[last] = p; spos[v] = -1; }
static void enq(int x) {
    if (!enq_on || inQ[x]) return;
    inQ[x] = 1; qu[qt] = x; qt = (qt + 1) % QCAP;
}
static int deq(void) { int x = qu[qh]; qh = (qh + 1) % QCAP; inQ[x] = 0; return x; }

/* precondition: v not in S and tight[v] == 0 */
static void addv(int v) {
    inS[v] = 1; sol_add(v); fl_del(v);
    if (journaling) jpush(v, 1);
    const int *nb = nbr + (long)v * D;
    for (int k = 0; k < D; k++) {
        int w = nb[k];
        tight[w]++; sumS[w] += v;
        if (!inS[w] && tight[w] == 1) { fl_del(w); enq(v); }
    }
}
/* precondition: v in S */
static void remv(int v) {
    inS[v] = 0; sol_del(v);
    if (!undoing) stampv[v] = (int)iter;
    if (journaling) jpush(v, -1);
    const int *nb = nbr + (long)v * D;
    for (int k = 0; k < D; k++) {
        int w = nb[k];
        tight[w]--; sumS[w] -= v;
        if (!inS[w]) {
            if (tight[w] == 0) fl_add(w);
            else if (tight[w] == 1) enq(sumS[w]);
        }
    }
    fl_add(v);
}
static void undo_all(void) {
    journaling = 0; undoing = 1; enq_on = 0;
    for (long i = jn - 1; i >= 0; i--) { if (jo[i] == 1) remv(jv[i]); else addv(jv[i]); }
    jn = 0; undoing = 0; enq_on = 1;
    while (qh != qt) deq();
}
static void insert_free(void) { while (fsz > 0) addv(fl[rndi(fsz)]); }

static void local_search(void) {
    insert_free();
    while (qh != qt) {
        int x = deq();
        if (!inS[x]) continue;
        const int *nb = nbr + (long)x * D;
        int c = 0;
        for (int k = 0; k < D; k++) { int w = nb[k]; if (!inS[w] && tight[w] == 1) Lb[c++] = w; }
        if (c < 2) continue;
        int a = -1, b = -1, s0 = rndi(c);
        for (int ii = 0; ii < c && a < 0; ii++) {
            int i = (s0 + ii) % c;
            for (int jj = ii + 1; jj < c; jj++) {
                int j = (s0 + jj) % c;
                if (!isadj(Lb[i], Lb[j])) { a = Lb[i]; b = Lb[j]; break; }
            }
        }
        if (a >= 0) { remv(x); addv(a); addv(b); insert_free(); }   /* (1,2)-swap */
    }
}

static void perturb(int kf, int samp) {
    for (int t = 0; t < kf; t++) {
        int bv = -1;
        for (int s = 0; s < samp; s++) {
            int v; do { v = rndi(n); } while (inS[v]);
            if (bv < 0 || tight[v] < tight[bv] || (tight[v] == tight[bv] && stampv[v] < stampv[bv])) bv = v;
        }
        const int *nb = nbr + (long)bv * D;
        int c = 0;
        for (int k = 0; k < D; k++) if (inS[nb[k]]) tmpS[c++] = nb[k];
        for (int i = 0; i < c; i++) remv(tmpS[i]);
        addv(bv);
    }
}

static void load_best(void) {
    journaling = 0; enq_on = 0;
    while (sz > 0) remv(sol[sz - 1]);
    for (int i = 0; i < bestsz; i++) addv(bestsol[i]);
    enq_on = 1;
    local_search();
    jn = 0;
}

static void save_flags(const char *path, const int *vs, int m) {
    char tmp[4096];
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "w");
    if (!f) { perror(tmp); return; }
    for (int i = 0; i < m; i++) fprintf(f, "%d %d\n", pidv[vs[i]], lidv[vs[i]]);
    fclose(f);
    rename(tmp, path);
}

static void read_map(void) {
    FILE *f = fopen(MAPFILE, "r");
    if (!f) { perror(MAPFILE); exit(1); }
    int cap = 16384, v[9];
    pidv = malloc(cap * sizeof(int)); lidv = malloc(cap * sizeof(int));
    co = malloc(cap * sizeof(*co));
    n = 0;
    for (;;) {
        int ok = 1;
        for (int k = 0; k < 9 && ok; k++) if (fscanf(f, "%d", &v[k]) != 1) ok = 0;
        if (!ok) break;
        if (n == cap) {
            cap *= 2;
            pidv = realloc(pidv, cap * sizeof(int)); lidv = realloc(lidv, cap * sizeof(int));
            co = realloc(co, cap * sizeof(*co));
        }
        pidv[n] = v[0]; lidv[n] = v[1];
        for (int k = 0; k < 7; k++) co[n][k] = v[2 + k];
        n++;
    }
    fclose(f);
    maxpid = 0;
    for (int i = 0; i < n; i++) if (pidv[i] > maxpid) maxpid = pidv[i];
    pidmap = malloc((maxpid + 1) * sizeof(int));
    for (int p = 0; p <= maxpid; p++) pidmap[p] = -1;
    for (int i = 0; i < n; i++) pidmap[pidv[i]] = i;
}

static void build_graph(void) {
    int d0 = 0;
    for (int j = 1; j < n; j++) if (isadj(0, j)) d0++;
    D = d0;
    nbr = malloc((size_t)n * D * sizeof(int));
    for (int i = 0; i < n; i++) {
        int c = 0, *nb = nbr + (long)i * D;
        for (int j = 0; j < n; j++) {
            if (j == i || !isadj(i, j)) continue;
            if (c >= D) { fprintf(stderr, "not regular at %d\n", i); exit(1); }
            nb[c++] = j;
        }
        if (c != D) { fprintf(stderr, "degree %d at vertex %d, expected %d\n", c, i, D); exit(1); }
    }
}

static void load_initial(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); exit(1); }
    int p, l;
    while (fscanf(f, "%d %d", &p, &l) == 2) {
        if (p < 0 || p > maxpid || pidmap[p] < 0) { fprintf(stderr, "point %d not in E\n", p); exit(1); }
        int v = pidmap[p];
        if (lidv[v] != l) { fprintf(stderr, "line mismatch for point %d: %d vs %d\n", p, l, lidv[v]); exit(1); }
        if (inS[v] || tight[v] != 0) { fprintf(stderr, "start set not independent at point %d\n", p); exit(1); }
        addv(v);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: %s SECONDS SEED OUTFLAGS [INFLAGS|-] [SAMP] [RESTART]\n", argv[0]); return 1; }
    double secs = atof(argv[1]);
    rs ^= (uint64_t)strtoull(argv[2], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    const char *outp = argv[3];
    const char *inp = (argc > 4 && strcmp(argv[4], "-") != 0) ? argv[4] : NULL;
    int samp = argc > 5 ? atoi(argv[5]) : 2; if (samp < 1) samp = 1;
    long restart = argc > 6 ? atol(argv[6]) : 50000;

    read_map();
    build_graph();
    fprintf(stderr, "n=%d D=%d\n", n, D);
    inS = calloc(n, 1); inQ = calloc(n, 1);
    tight = calloc(n, sizeof(int)); sumS = calloc(n, sizeof(int)); stampv = calloc(n, sizeof(int));
    sol = malloc(n * sizeof(int)); spos = malloc(n * sizeof(int));
    fl = malloc(n * sizeof(int)); fpos = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++) { spos[i] = -1; fpos[i] = -1; }
    fsz = 0; for (int i = 0; i < n; i++) fl_add(i);
    QCAP = n + 1; qu = malloc(QCAP * sizeof(int)); qh = qt = 0;
    Lb = malloc(D * sizeof(int)); tmpS = malloc(D * sizeof(int)); bestsol = malloc(n * sizeof(int));
    journaling = 0; undoing = 0; iter = 0;

    if (inp) load_initial(inp);
    local_search();
    bestsz = sz;
    memcpy(bestsol, sol, sz * sizeof(int));
    save_flags(outp, bestsol, bestsz);
    printf("start size %d\n", sz); fflush(stdout);

    double t0 = now(), tend = t0 + secs, tprint = t0 + 10.0;
    long lastImp = 0, nIter = 0;
    while (now() < tend) {
        iter++; nIter++;
        jn = 0; journaling = 1;
        int s0 = sz;
        int kf = 1;
        if (rndi(2 * sz + 2) == 0) { kf = 2; while (rndi(2) == 0) kf++; }
        perturb(kf, samp);
        local_search();
        int s1 = sz;
        if (s1 > bestsz) {
            bestsz = s1;
            memcpy(bestsol, sol, s1 * sizeof(int));
            save_flags(outp, bestsol, bestsz);
            lastImp = iter;
            printf("iter %ld t=%.1f best %d\n", iter, now() - t0, bestsz); fflush(stdout);
        }
        int acc = 1;
        if (s1 < s0) {
            long delta = s0 - s1, dstar = bestsz - s1;
            acc = rndi((int)(1 + delta * dstar)) == 0;
        }
        if (!acc) undo_all();
        jn = 0; journaling = 0;
        if (sz < bestsz && iter - lastImp > restart) { load_best(); lastImp = iter; }
        if (now() >= tprint) {
            printf("t=%.0f iters=%ld cur=%d best=%d\n", now() - t0, nIter, sz, bestsz); fflush(stdout);
            tprint += 10.0;
        }
    }
    for (int i = 0; i < bestsz; i++)
        for (int j = i + 1; j < bestsz; j++)
            if (isadj(bestsol[i], bestsol[j])) { fprintf(stderr, "BUG: best not independent\n"); return 2; }
    printf("FINAL best %d iters %ld time %.1f file %s\n", bestsz, nIter, now() - t0, outp); fflush(stdout);
    return 0;
}
