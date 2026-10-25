/* tabu.c (card c3, squad round 5, d10D7): k-fixed swap tabu search for a maximum independent set
   (= pairwise opposite set) in the conflict graph of the 4617 Hermitian-line candidates.
   Vertex v = 9*i + t: point t of line i (i = Hermitian point of PG(2,64), 9 GF(8)-points per line).
   Conflict lists from prep.py: conf_lists_u16.bin (NV x 520 uint16), two vertices conflict iff B = 0.
   build: gcc -O2 -o tabu tabu.c
   run:   ./tabu SEED SECONDS OUTFILE [K0 TA TB STALL PERT]
          OUTFILE is rewritten (vertex ids, one per line) every time the independent set grows. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#define NV 4617
#define DEG 520
static uint16_t NB[NV * DEG];
static int inS[NV], conf[NV], S[NV], posS[NV], K, F;
static long long tabuAdd[NV], tabuRm[NV];
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void addv(int v) { inS[v] = 1; posS[v] = K; S[K++] = v; F += conf[v];
    for (int j = 0; j < DEG; j++) conf[NB[v * DEG + j]]++; }
static void remv(int v) { inS[v] = 0; int p = posS[v]; S[p] = S[--K]; posS[S[p]] = p; F -= conf[v];
    for (int j = 0; j < DEG; j++) conf[NB[v * DEG + j]]--; }
static int check_independent_now(void);
static void save(const char *path) {
    if (!check_independent_now()) { fprintf(stderr, "BUG: saved set not independent\n"); exit(3); }
    FILE *f = fopen(path, "w"); if (!f) return;
    for (int i = 0; i < K; i++) fprintf(f, "%d\n", S[i]);
    fclose(f);
}
static int check_independent_now(void) {
    for (int i = 0; i < K; i++) for (int j = 0; j < DEG; j++) if (inS[NB[S[i] * DEG + j]]) return 0;
    return 1;
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: tabu SEED SECONDS OUTFILE [K0 TA TB STALL PERT]\n"); return 2; }
    uint64_t seed = strtoull(argv[1], 0, 10); double secs = atof(argv[2]); const char *out = argv[3];
    int K0 = argc > 4 ? atoi(argv[4]) : 40, TA = argc > 5 ? atoi(argv[5]) : 10, TB = argc > 6 ? atoi(argv[6]) : 3;
    long long STALL = argc > 7 ? atoll(argv[7]) : 200000; int PERT = argc > 8 ? atoi(argv[8]) : 4;
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 1; for (int i = 0; i < 10; i++) rnd();
    FILE *f = fopen("conf_lists_u16.bin", "rb"); if (!f) { perror("conf_lists_u16.bin"); return 2; }
    if (fread(NB, 2, (size_t)NV * DEG, f) != (size_t)NV * DEG) { fprintf(stderr, "short file\n"); return 2; }
    fclose(f);
    clock_t t0 = clock(); int best = 0; long long iter = 0, lastImp = 0;
    /* initial set: K0 random vertices, each added at minimum conflict */
    while (K < K0) {
        int bc = 1 << 30, cnt = 0, bv = -1;
        for (int v = 0; v < NV; v++) if (!inS[v]) {
            if (conf[v] < bc) { bc = conf[v]; bv = v; cnt = 1; }
            else if (conf[v] == bc && (rnd() % (++cnt)) == 0) bv = v;
        }
        addv(bv);
    }
    while ((double)(clock() - t0) / CLOCKS_PER_SEC < secs) {
        iter++;
        if (F == 0) {
            if (K > best) {
                best = K; save(out); lastImp = iter;
                fprintf(stderr, "size %d at iter %lld t=%.1fs\n", best, iter, (double)(clock() - t0) / CLOCKS_PER_SEC);
            }
            int bc = 1 << 30, cnt = 0, bv = -1;   /* grow: add a minimum-conflict outsider */
            for (int v = 0; v < NV; v++) if (!inS[v]) {
                if (conf[v] < bc) { bc = conf[v]; bv = v; cnt = 1; }
                else if (conf[v] == bc && (rnd() % (++cnt)) == 0) bv = v;
            }
            addv(bv); continue;
        }
        /* remove: member with max conflicts, non-tabu */
        int bu = -1, bcu = -1, cnt = 0;
        for (int i = 0; i < K; i++) { int u = S[i];
            if (tabuRm[u] > iter) continue;
            if (conf[u] > bcu) { bcu = conf[u]; bu = u; cnt = 1; }
            else if (conf[u] == bcu && (rnd() % (++cnt)) == 0) bu = u; }
        if (bu < 0) bu = S[rnd() % K];
        remv(bu); tabuAdd[bu] = iter + TA + (long long)(rnd() % (TA + 1));
        /* add: non-member with min conflicts (after removal), non-tabu */
        int bv = -1, bcv = 1 << 30; cnt = 0;
        for (int v = 0; v < NV; v++) if (!inS[v]) {
            if (tabuAdd[v] > iter && !(F + conf[v] == 0)) continue;
            if (conf[v] < bcv) { bcv = conf[v]; bv = v; cnt = 1; }
            else if (conf[v] == bcv && (rnd() % (++cnt)) == 0) bv = v; }
        if (bv < 0) bv = bu;
        addv(bv); tabuRm[bv] = iter + TB + (long long)(rnd() % (TB + 1));
        /* stall: random perturbation */
        if (iter - lastImp > STALL) {
            for (int r = 0; r < PERT; r++) {
                int u = S[rnd() % K]; remv(u); tabuAdd[u] = iter + TA;
                int w; do { w = rnd() % NV; } while (inS[w]);
                addv(w); tabuRm[w] = iter + TB;
            }
            lastImp = iter;
        }
    }
    printf("best %d iters %lld\n", best, iter);
    return 0;
}
