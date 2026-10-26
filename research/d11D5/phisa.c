/* phisa: simulated annealing / focused local search for a delta-invariant Z2 voltage phi on W(q) such that no
   opposite point pair has all q+1 GQ 4-paths of the same parity.  Input: pairs file from export_pairs.py.
   usage: phisa pairs.bin seed seconds [T0] [pfocus] [outbits]  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
static unsigned long long rs;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "rb"); int hdr[5]; if (fread(hdr, sizeof(int), 5, f) != 5) return 1;
    int q = hdr[0], norb = hdr[1], np = hdr[2], npath = hdr[3];
    long ne = (long)np * npath;
    int *ids = malloc(ne * 4 * sizeof(int)); if (fread(ids, sizeof(int), ne * 4, f) != (size_t)(ne * 4)) return 1;
    fclose(f);
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[2]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[3]); double T0 = argc > 4 ? atof(argv[4]) : 2.0; double pf = argc > 5 ? atof(argv[5]) : 0.5;
    const char *outb = argc > 6 ? argv[6] : NULL;
    /* occurrence lists (odd multiplicity only) */
    int *cntocc = calloc(norb, sizeof(int));
    for (long e = 0; e < ne; e++) {
        int *p = ids + 4 * e;
        for (int a = 0; a < 4; a++) { int m = 0; for (int b = 0; b < 4; b++) if (p[b] == p[a]) m++; int first = 1; for (int b = 0; b < a; b++) if (p[b] == p[a]) first = 0; if (first && (m & 1)) cntocc[p[a]]++; }
    }
    int *ooff = malloc((norb + 1) * sizeof(int)); ooff[0] = 0; for (int o = 0; o < norb; o++) ooff[o + 1] = ooff[o] + cntocc[o];
    int *occ = malloc((long)ooff[norb] * sizeof(int)); int *fillo = calloc(norb, sizeof(int));
    for (long e = 0; e < ne; e++) {
        int *p = ids + 4 * e;
        for (int a = 0; a < 4; a++) { int m = 0; for (int b = 0; b < 4; b++) if (p[b] == p[a]) m++; int first = 1; for (int b = 0; b < a; b++) if (p[b] == p[a]) first = 0; if (first && (m & 1)) occ[ooff[p[a]] + fillo[p[a]]++] = (int)e; }
    }
    unsigned char *bits = malloc(norb), *best = malloc(norb), *par = malloc(ne);
    for (int o = 0; o < norb; o++) bits[o] = rnd() & 1;
    int *cnt = calloc(np, sizeof(int));
    for (long e = 0; e < ne; e++) { int *p = ids + 4 * e; par[e] = bits[p[0]] ^ bits[p[1]] ^ bits[p[2]] ^ bits[p[3]]; cnt[e / npath] += par[e]; }
    long cost = 0; for (int i = 0; i < np; i++) cost += (cnt[i] == 0 || cnt[i] == npath);
    /* list of violated pairs for focused moves */
    int *vlist = malloc(np * sizeof(int)), *vpos = malloc(np * sizeof(int)); int nv = 0;
    for (int i = 0; i < np; i++) { vpos[i] = -1; if (cnt[i] == 0 || cnt[i] == npath) { vpos[i] = nv; vlist[nv++] = i; } }
    long bestc = cost; memcpy(best, bits, norb);
    int *dc = calloc(np, sizeof(int)), *touched = malloc(np * sizeof(int));
    clock_t t0 = clock(); long it = 0; double T = T0;
    printf("q=%d norb=%d pairs=%d paths/pair=%d initial cost=%ld\n", q, norb, np, npath, cost); fflush(stdout);
    while (1) {
        if ((it & 1023) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs || bestc == 0) break;
            T = T0 * (1.0 - el / secs) + 0.02;
            if ((it & ((1 << 20) - 1)) == 0) { printf("t=%.0f it=%ld cost=%ld best=%ld T=%.3f\n", el, it, cost, bestc, T); fflush(stdout); }
        }
        it++;
        int o;
        if (nv > 0 && urand() < pf) { int pi = vlist[rnd() % nv]; int k = rnd() % npath; o = ids[4 * ((long)pi * npath + k) + (rnd() & 3)]; }
        else o = rnd() % norb;
        int nt = 0; long delta = 0;
        for (int j = ooff[o]; j < ooff[o + 1]; j++) { long e = occ[j]; int pi = e / npath; if (dc[pi] == 0 && 1) {} int d = par[e] ? -1 : 1; if (dc[pi] == 0) touched[nt++] = pi; dc[pi] += d; if (dc[pi] == 0) dc[pi] = 1000000; }
        for (int t = 0; t < nt; t++) { int pi = touched[t]; int d = dc[pi] == 1000000 ? 0 : dc[pi]; int c0 = cnt[pi], c1 = c0 + d; delta += (c1 == 0 || c1 == npath) - (c0 == 0 || c0 == npath); }
        if (delta <= 0 || urand() < exp(-delta / T)) {
            bits[o] ^= 1;
            for (int j = ooff[o]; j < ooff[o + 1]; j++) { long e = occ[j]; par[e] ^= 1; }
            for (int t = 0; t < nt; t++) { int pi = touched[t]; int d = dc[pi] == 1000000 ? 0 : dc[pi]; int was = (cnt[pi] == 0 || cnt[pi] == npath); cnt[pi] += d; int now = (cnt[pi] == 0 || cnt[pi] == npath);
                if (was && !now) { int pos = vpos[pi]; vlist[pos] = vlist[--nv]; vpos[vlist[pos]] = pos; vpos[pi] = -1; }
                else if (!was && now) { vpos[pi] = nv; vlist[nv++] = pi; } }
            cost += delta;
            if (cost < bestc) { bestc = cost; memcpy(best, bits, norb); }
        }
        for (int t = 0; t < nt; t++) dc[touched[t]] = 0;
    }
    printf("RESULT q=%d best=%ld iters=%ld time=%.1f\n", q, bestc, it, (double)(clock() - t0) / CLOCKS_PER_SEC);
    if (outb) { FILE *g = fopen(outb, "w"); fprintf(g, "{\"q\": %d, \"best\": %ld, \"orbit_bits\": [", q, bestc); for (int o = 0; o < norb; o++) fprintf(g, "%s%d", o ? ", " : "", best[o]); fprintf(g, "]}\n"); fclose(g); }
    return 0;
}
