/* sa.c (card c5, squad d14D7-r3, cell (14,7)): simulated annealing with penalties for an independent set S in the
   orthogonality graph of E (E11.graph: 15,984 vertices, 1,342-regular; independent = pairwise non-orthogonal points).
   Energy E = -|S| + lam * e(S), e(S) = number of graph edges inside S.
   Each step proposes a uniform random vertex v (c[v] = #S-neighbours of v, sumS[v] = sum of ids of S-neighbours):
     v in S:              remove v,                 dE = 1 - lam*c[v]          (Metropolis)
     v outside, c[v] = 0: add v,                    dE = -1                    (always)
     v outside, c[v] = 1: swap v in for u = sumS[v], dE = -lam*c[u] <= 0      (always)
     v outside, c[v] >= 2: add v with penalty,      dE = -1 + lam*c[v]         (Metropolis)
   lam and T follow a geometric schedule in wall-clock time from (LAM0,T0) to (LAM1,T1).
   Every improvement of the best independent set is written to OUTFLAGS as "point_id spread_line_id" lines (columns
   1-2 of E11.map). At the end the state is repaired (remove the max-conflict vertex until e(S)=0, then maximalize).
   Usage: sa GRAPH MAP SECONDS SEED LAM0 LAM1 T0 T1 OUTFLAGS [INIT_VERTEX_IDS]
   Build: gcc -O3 -march=native -o sa sa.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int N, M;
static int *off, *nb;                 /* CSR adjacency */
static int *cnt, *sumS, *sList, *sPos; /* S-neighbour counts, sums of S-neighbour ids, members of S */
static unsigned char *inS;
static int sz = 0, e = 0;             /* |S| and e(S) */
static int *ptId, *slId;              /* E11.map columns 1-2 */

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rndu(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static inline int rndi(int n) { return (int)((rnd64() >> 11) % (uint64_t)n); }

static FILE *fin; static char ibuf[1 << 16]; static size_t ilen = 0, ipos = 0;
static inline int gc(void) {
    if (ipos == ilen) { ilen = fread(ibuf, 1, sizeof ibuf, fin); ipos = 0; if (ilen == 0) return -1; }
    return (unsigned char)ibuf[ipos++];
}
static int readint(int *out) {
    int ch = gc(); while (ch != -1 && (ch < '0' || ch > '9')) ch = gc();
    if (ch == -1) return 0;
    int x = 0; while (ch >= '0' && ch <= '9') { x = x * 10 + (ch - '0'); ch = gc(); }
    *out = x; return 1;
}

static void read_graph(const char *fn) {
    fin = fopen(fn, "rb"); if (!fin) { perror(fn); exit(1); }
    if (!readint(&N) || !readint(&M)) { fprintf(stderr, "bad graph header\n"); exit(1); }
    int *eu = malloc(sizeof(int) * (size_t)M), *ev = malloc(sizeof(int) * (size_t)M);
    off = calloc(N + 1, sizeof(int));
    for (int i = 0; i < M; i++) {
        if (!readint(&eu[i]) || !readint(&ev[i])) { fprintf(stderr, "short edge list\n"); exit(1); }
        off[eu[i] + 1]++; off[ev[i] + 1]++;
    }
    fclose(fin);
    for (int v = 0; v < N; v++) off[v + 1] += off[v];
    nb = malloc(sizeof(int) * (size_t)(2 * M));
    int *fill = malloc(sizeof(int) * N); memcpy(fill, off, sizeof(int) * N);
    for (int i = 0; i < M; i++) { nb[fill[eu[i]]++] = ev[i]; nb[fill[ev[i]]++] = eu[i]; }
    free(fill); free(eu); free(ev);
    int mn = 1 << 30, mx = 0;
    for (int v = 0; v < N; v++) { int d = off[v + 1] - off[v]; if (d < mn) mn = d; if (d > mx) mx = d; }
    fprintf(stderr, "graph: n=%d m=%d degree %d..%d\n", N, M, mn, mx);
}

static void read_map(const char *fn) {
    fin = fopen(fn, "rb"); if (!fin) { perror(fn); exit(1); }
    ptId = malloc(sizeof(int) * N); slId = malloc(sizeof(int) * N);
    for (int i = 0; i < N; i++) {
        int x;
        if (!readint(&ptId[i]) || !readint(&slId[i])) { fprintf(stderr, "bad map\n"); exit(1); }
        for (int k = 0; k < 7; k++) readint(&x);
    }
    fclose(fin);
}

static void write_flags(const char *fn, const int *set, int k) {
    char tmp[4096]; snprintf(tmp, sizeof tmp, "%s.tmp", fn);
    FILE *f = fopen(tmp, "w"); if (!f) { perror(tmp); exit(1); }
    for (int i = 0; i < k; i++) fprintf(f, "%d %d\n", ptId[set[i]], slId[set[i]]);
    fclose(f); rename(tmp, fn);
}

static void addV(int v) {          /* v must be outside S */
    inS[v] = 1; e += cnt[v]; sPos[v] = sz; sList[sz++] = v;
    for (int k = off[v]; k < off[v + 1]; k++) { int w = nb[k]; cnt[w]++; sumS[w] += v; }
}
static void remV(int v) {          /* v must be inside S */
    inS[v] = 0; e -= cnt[v];
    int p = sPos[v]; int last = sList[--sz]; sList[p] = last; sPos[last] = p;
    for (int k = off[v]; k < off[v + 1]; k++) { int w = nb[k]; cnt[w]--; sumS[w] -= v; }
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: sa GRAPH MAP SECONDS SEED LAM0 LAM1 T0 T1 OUTFLAGS\n"); return 2; }
    read_graph(argv[1]); read_map(argv[2]);
    double secs = atof(argv[3]);
    rs ^= (uint64_t)strtoull(argv[4], 0, 10) * 0x9E3779B97F4A7C15ULL; if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd64();
    double lam0 = atof(argv[5]), lam1 = atof(argv[6]), T0 = atof(argv[7]), T1 = atof(argv[8]);
    const char *outfn = argv[9];

    cnt = calloc(N, sizeof(int)); sumS = calloc(N, sizeof(int));
    sList = malloc(sizeof(int) * N); sPos = malloc(sizeof(int) * N); inS = calloc(N, 1);
    int *bestS = malloc(sizeof(int) * N); int best = 0;
    if (argc > 10) {   /* optional warm start: vertex ids (one per line); added only where they create no conflict */
        fin = fopen(argv[10], "rb"); if (!fin) { perror(argv[10]); return 1; }
        int v, added = 0; while (readint(&v)) if (v >= 0 && v < N && !inS[v] && cnt[v] == 0) { addV(v); added++; }
        fclose(fin); fprintf(stderr, "warm start: %d vertices added, size %d\n", added, sz);
    }
    long long it = 0, nAdd = 0, nSwap = 0, nRem = 0, nPen = 0;
    double lastLog = -1e9;
    struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
    double lam = lam0, T = T0;
    for (;;) {
        if ((it & 0xFFF) == 0) {
            clock_gettime(CLOCK_MONOTONIC, &t1);
            double el = (t1.tv_sec - t0.tv_sec) + 1e-9 * (t1.tv_nsec - t0.tv_nsec);
            double fr = el / secs; if (fr >= 1.0) break;
            lam = lam0 * pow(lam1 / lam0, fr); T = T0 * pow(T1 / T0, fr);
            if (e == 0 && sz > best) { best = sz; memcpy(bestS, sList, sizeof(int) * sz); write_flags(outfn, bestS, best); }
            if (el - lastLog >= 30) {
                lastLog = el;
                fprintf(stderr, "t=%.0f lam=%.3f T=%.4f size=%d edges=%d best=%d add0=%lld swap=%lld rem=%lld pen=%lld\n",
                        el, lam, T, sz, e, best, nAdd, nSwap, nRem, nPen);
            }
        }
        it++;
        int v = rndi(N);
        if (inS[v]) {
            double dE = 1.0 - lam * cnt[v];
            if (dE <= 0 || rndu() < exp(-dE / T)) { remV(v); nRem++; }
        } else if (cnt[v] == 0) {
            addV(v); nAdd++;
        } else if (cnt[v] == 1) {
            int u = sumS[v]; remV(u); addV(v); nSwap++;
        } else {
            double dE = -1.0 + lam * cnt[v];
            if (rndu() < exp(-dE / T)) { addV(v); nPen++; }
        }
    }
    /* repair: remove the member with most S-neighbours until no edge is left inside S, then maximalize */
    int edgesBefore = e, szBefore = sz;
    while (e > 0) {
        int bv = -1, bc = -1;
        for (int i = 0; i < sz; i++) { int v = sList[i]; if (cnt[v] > bc) { bc = cnt[v]; bv = v; } }
        remV(bv);
    }
    for (int v = 0; v < N; v++) if (!inS[v] && cnt[v] == 0) addV(v);
    if (sz > best) { best = sz; memcpy(bestS, sList, sizeof(int) * sz); write_flags(outfn, bestS, best); }
    fprintf(stderr, "final: state size=%d edges=%d (repaired from %d,%d); best=%d iters=%lld\n",
            szBefore, edgesBefore, szBefore, edgesBefore, best, it);
    printf("BEST %d\n", best);
    return 0;
}
