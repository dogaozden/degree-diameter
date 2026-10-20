/* wsa2.c: annealing for a maximum b-packing: choose multiplicities m_c in {0..cap} for candidate sets (q free points
   each) with total multiplicity <= cap at every free point; maximize sum m_c.
   Usage: wsa2 cand.txt cap seconds seed out.txt [init.txt]   (out: line ids, repeated m_c times) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int cap = atoi(argv[2]); double secs = atof(argv[3]); rs ^= (uint64_t)atoi(argv[4]) * 0x9E3779B97F4A7C15ULL;
    int nf, nc, q; if (fscanf(f, "%d %d %d", &nf, &nc, &q) != 3) return 1;
    int *lid = malloc(sizeof(int) * nc), *pt = malloc(sizeof(int) * (long)nc * q);
    int *deg = calloc(nf, sizeof(int));
    for (int c = 0; c < nc; c++) { if (fscanf(f, "%d", &lid[c]) != 1) return 1; for (int j = 0; j < q; j++) { if (fscanf(f, "%d", &pt[(long)c * q + j]) != 1) return 1; deg[pt[(long)c * q + j]]++; } }
    int *off = malloc(sizeof(int) * (nf + 1)); off[0] = 0; for (int r = 0; r < nf; r++) off[r + 1] = off[r] + deg[r];
    int *inc = malloc(sizeof(int) * off[nf]); int *fill = calloc(nf, sizeof(int));
    for (int c = 0; c < nc; c++) for (int j = 0; j < q; j++) { int r = pt[(long)c * q + j]; inc[off[r] + fill[r]++] = c; }
    int *m = calloc(nc, sizeof(int)), *ld = calloc(nf, sizeof(int)); long cur = 0;
    if (argc > 6) { FILE *g = fopen(argv[6], "r"); int k; int *pos = calloc(1 << 22, sizeof(int)); for (int c = 0; c < nc; c++) pos[lid[c]] = c + 1;
        while (fscanf(g, "%d", &k) == 1) { int c = pos[k] - 1; if (c < 0) return 1; int ok = m[c] < cap; for (int j = 0; j < q; j++) if (ld[pt[(long)c * q + j]] >= cap) ok = 0;
            if (ok) { m[c]++; cur++; for (int j = 0; j < q; j++) ld[pt[(long)c * q + j]]++; } }
        fclose(g); fprintf(stderr, "init %ld\n", cur); }
    long best = cur; int *bm = malloc(sizeof(int) * nc); for (int c = 0; c < nc; c++) bm[c] = m[c];
    double T0 = getenv("T0") ? atof(getenv("T0")) : 0.3, T1 = 0.05, T = T0; clock_t t0 = clock(); long it = 0;
    int ev[64];
    for (;;) {
        if ((it & 0xFFFFF) == 0) { double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break; T = T0 * pow(T1 / T0, el / secs);
            if ((it & 0x7FFFFFF) == 0) fprintf(stderr, "t=%.0f cur=%ld best=%ld T=%.3f\n", el, cur, best, T); }
        it++;
        int c = rnd() % nc; if (m[c] >= cap) continue;
        int k = 0;
        for (int j = 0; j < q; j++) { int r = pt[(long)c * q + j]; if (ld[r] < cap) continue;
            /* evict one unit of a random other candidate through r */
            int d; int tries = 0; do { d = inc[off[r] + rnd() % (off[r + 1] - off[r])]; tries++; } while ((d == c || m[d] == 0) && tries < 50);
            if (d == c || m[d] == 0) { k = 99; break; }
            ev[k++] = d; }
        if (k == 99) continue;
        int delta = 1 - k;
        if (delta < 0 && (double)(rnd() >> 11) / 9007199254740992.0 >= exp(delta / T)) continue;
        for (int s = 0; s < k; s++) { int d = ev[s]; if (m[d] == 0) { delta++; continue; } m[d]--; for (int j = 0; j < q; j++) ld[pt[(long)d * q + j]]--; }
        /* an evicted candidate might be listed twice; recheck capacity before adding */
        int ok = 1; for (int j = 0; j < q; j++) if (ld[pt[(long)c * q + j]] >= cap) ok = 0;
        cur += delta - 1 + ok;  /* delta counted the +1 */
        if (ok) { m[c]++; for (int j = 0; j < q; j++) ld[pt[(long)c * q + j]]++; }
        if (cur > best) { best = cur; for (int e = 0; e < nc; e++) bm[e] = m[e]; }
    }
    long chk = 0; FILE *o = fopen(argv[5], "w");
    for (int c = 0; c < nc; c++) for (int t = 0; t < bm[c]; t++) { fprintf(o, "%d\n", lid[c]); chk++; }
    fclose(o); fprintf(stderr, "best %ld (written %ld) after %ld moves\n", best, chk, it);
    return 0;
}
