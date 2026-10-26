/* sa3.c: simulated annealing over edge voltages of a Z_m lift of a bipartite base (H(q) + one matching).
   Cost = uncovered (A-source, B-vertex, sheet) triples for walks of length 7 (D = 8), same as lifteval.
   Moves: re-voltage one random edge. Usage: sa3 BASE OUT iters seed T0
   Writes the best voltages to OUT (lifteval format). Stops early at cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
typedef uint64_t u64;
static int nA, nB, m, nE;
static int *ea, *eb, *ev;
static int *Aoff, *Aadj, *Avol, *Boff, *Badj, *Bvol, *Aedge, *Bedge;
static u64 FULL;
static u64 *bA, *bB;
static inline u64 rot(u64 x, int v) { if (!v) return x; return ((x << v) | (x >> (m - v))) & FULL; }
static u64 rs = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void sync(void) {
    for (int k = 0; k < nE; k++) { Avol[k] = ev[Aedge[k]]; Bvol[k] = ev[Bedge[k]]; }
}

static long long cost_all(void) {
    sync();
    long long total = 0;
    for (int s = 0; s < nA; s++) {
        memset(bA, 0, sizeof(u64) * nA); memset(bB, 0, sizeof(u64) * nB);
        bA[s] = 1;
        for (int step = 0; step < 7; step++) {
            if (step % 2 == 0) {
                memset(bB, 0, sizeof(u64) * nB);
                for (int a = 0; a < nA; a++) { u64 x = bA[a]; if (!x) continue;
                    for (int k = Aoff[a]; k < Aoff[a + 1]; k++) bB[Aadj[k]] |= rot(x, Avol[k]); }
            } else {
                memset(bA, 0, sizeof(u64) * nA);
                for (int b = 0; b < nB; b++) { u64 x = bB[b]; if (!x) continue;
                    for (int k = Boff[b]; k < Boff[b + 1]; k++) bA[Badj[k]] |= rot(x, (m - Bvol[k]) % m); }
            }
        }
        for (int i = 0; i < nB; i++) total += m - __builtin_popcountll(bB[i]);
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: sa3 BASE OUT iters seed T0\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) return 2;
    long iters = atol(argv[3]); rs += (u64)atol(argv[4]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    double T0 = atof(argv[5]);
    if (fscanf(f, "%d %d %d", &nA, &nB, &m) != 3) return 2;
    FULL = (1ULL << m) - 1;
    int cap = 1 << 16; ea = malloc(sizeof(int) * cap); eb = malloc(sizeof(int) * cap); ev = malloc(sizeof(int) * cap);
    nE = 0; int a, b, v;
    while (fscanf(f, "%d %d %d", &a, &b, &v) == 3) {
        if (nE == cap) { cap *= 2; ea = realloc(ea, sizeof(int) * cap); eb = realloc(eb, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        ea[nE] = a; eb[nE] = b; ev[nE] = ((v % m) + m) % m; nE++;
    }
    fclose(f);
    Aoff = calloc(nA + 1, sizeof(int)); Boff = calloc(nB + 1, sizeof(int));
    for (int e = 0; e < nE; e++) { Aoff[ea[e] + 1]++; Boff[eb[e] + 1]++; }
    for (int i = 0; i < nA; i++) Aoff[i + 1] += Aoff[i];
    for (int i = 0; i < nB; i++) Boff[i + 1] += Boff[i];
    Aadj = malloc(sizeof(int) * nE); Avol = malloc(sizeof(int) * nE); Aedge = malloc(sizeof(int) * nE);
    Badj = malloc(sizeof(int) * nE); Bvol = malloc(sizeof(int) * nE); Bedge = malloc(sizeof(int) * nE);
    int *pa = malloc(sizeof(int) * nA), *pb = malloc(sizeof(int) * nB);
    memcpy(pa, Aoff, sizeof(int) * nA); memcpy(pb, Boff, sizeof(int) * nB);
    for (int e = 0; e < nE; e++) {
        int ka = pa[ea[e]]++; Aadj[ka] = eb[e]; Aedge[ka] = e;
        int kb = pb[eb[e]]++; Badj[kb] = ea[e]; Bedge[kb] = e;
    }
    bA = malloc(sizeof(u64) * nA); bB = malloc(sizeof(u64) * nB);
    long long cur = cost_all(), best = cur;
    int *bestv = malloc(sizeof(int) * nE); memcpy(bestv, ev, sizeof(int) * nE);
    fprintf(stderr, "start cost %lld\n", cur);
    for (long it = 0; it < iters && best > 0; it++) {
        int e = rnd() % nE; int old = ev[e]; int nv = rnd() % m; if (nv == old) continue;
        ev[e] = nv;
        long long c = cost_all();
        double T = T0 * (1.0 - (double)it / iters) + 1e-9;
        if (c <= cur || urand() < exp(-(double)(c - cur) / T)) {
            cur = c;
            if (c < best) { best = c; memcpy(bestv, ev, sizeof(int) * nE); fprintf(stderr, "it %ld best %lld\n", it, best); }
        } else ev[e] = old;
        if (it % 50 == 0) fprintf(stderr, "it %ld cur %lld best %lld\n", it, cur, best);
    }
    memcpy(ev, bestv, sizeof(int) * nE);
    FILE *g = fopen(argv[2], "w");
    fprintf(g, "%d %d %d\n", nA, nB, m);
    for (int e = 0; e < nE; e++) fprintf(g, "%d %d %d\n", ea[e], eb[e], ev[e]);
    fclose(g);
    printf("BEST %lld\n", best);
    return 0;
}
