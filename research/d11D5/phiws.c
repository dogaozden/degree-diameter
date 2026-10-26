/* phiws: WalkSAT-style focused search for a delta-invariant Z2 voltage phi on W(q) with no opposite point pair
   whose q+1 GQ 4-paths all have the same parity.  Pick a violated pair, consider the orbit bits on its paths,
   flip the one with the best (breaks - makes) score, or a random one with probability noise.
   usage: phiws pairs.bin seed seconds noise [outbits] [initbits.json] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
static unsigned long long rs;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
int q, norb, np, npath; long ne; int *ids, *ooff, *occ, *cnt; unsigned char *bits, *par;
static inline int viol(int c) { return c == 0 || c == npath; }
int *dc, *touched;
static void eval(int o, int *brk, int *mk) {
    int nt = 0; *brk = 0; *mk = 0;
    for (int j = ooff[o]; j < ooff[o + 1]; j++) {
        long e = occ[j]; int pi = e / npath;
        if (dc[pi] == 0) touched[nt++] = pi;
        dc[pi] += par[e] ? -1 : 1;
        if (dc[pi] == 0) dc[pi] = 1 << 20;
    }
    for (int t = 0; t < nt; t++) {
        int pi = touched[t]; int d = dc[pi] == (1 << 20) ? 0 : dc[pi];
        int a = viol(cnt[pi]), b = viol(cnt[pi] + d);
        if (!a && b) (*brk)++;
        if (a && !b) (*mk)++;
        dc[pi] = 0;
    }
}
int *vlist, *vpos, nv;
static void flip(int o) {
    bits[o] ^= 1;
    for (int j = ooff[o]; j < ooff[o + 1]; j++) {
        long e = occ[j]; int pi = e / npath; int was = viol(cnt[pi]);
        cnt[pi] += par[e] ? -1 : 1; par[e] ^= 1; int now = viol(cnt[pi]);
        if (was && !now) { int pos = vpos[pi]; vlist[pos] = vlist[--nv]; vpos[vlist[pos]] = pos; vpos[pi] = -1; }
        else if (!was && now) { vpos[pi] = nv; vlist[nv++] = pi; }
    }
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: phiws pairs.bin seed seconds noise [out] [init]\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); int hdr[5]; if (fread(hdr, sizeof(int), 5, f) != 5) return 1;
    q = hdr[0]; norb = hdr[1]; np = hdr[2]; npath = hdr[3]; ne = (long)np * npath;
    ids = malloc(ne * 4 * sizeof(int)); if (fread(ids, sizeof(int), ne * 4, f) != (size_t)(ne * 4)) return 1; fclose(f);
    rs = 0x9E3779B97F4A7C15ULL ^ (unsigned long long)atoll(argv[2]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[3]), noise = atof(argv[4]);
    const char *outb = argc > 5 ? argv[5] : NULL; const char *init = argc > 6 ? argv[6] : NULL;
    int *co = calloc(norb, sizeof(int));
    for (long e = 0; e < ne; e++) { int *p = ids + 4 * e; for (int a = 0; a < 4; a++) { int m = 0, first = 1; for (int b = 0; b < 4; b++) if (p[b] == p[a]) m++; for (int b = 0; b < a; b++) if (p[b] == p[a]) first = 0; if (first && (m & 1)) co[p[a]]++; } }
    ooff = malloc((norb + 1) * sizeof(int)); ooff[0] = 0; for (int o = 0; o < norb; o++) ooff[o + 1] = ooff[o] + co[o];
    occ = malloc((long)ooff[norb] * sizeof(int)); int *fo = calloc(norb, sizeof(int));
    for (long e = 0; e < ne; e++) { int *p = ids + 4 * e; for (int a = 0; a < 4; a++) { int m = 0, first = 1; for (int b = 0; b < 4; b++) if (p[b] == p[a]) m++; for (int b = 0; b < a; b++) if (p[b] == p[a]) first = 0; if (first && (m & 1)) occ[ooff[p[a]] + fo[p[a]]++] = (int)e; } }
    bits = malloc(norb); unsigned char *best = malloc(norb); par = malloc(ne); cnt = calloc(np, sizeof(int));
    for (int o = 0; o < norb; o++) bits[o] = rnd() & 1;
    if (init) {
        FILE *g = fopen(init, "r"); static char buf[1 << 20]; size_t n = fread(buf, 1, sizeof buf - 1, g); buf[n] = 0; fclose(g);
        char *s = strstr(buf, "orbit_bits"); s = strchr(s, '[');
        for (int o = 0; o < norb; o++) { while (*s && (*s < '0' || *s > '1')) s++; bits[o] = *s - '0'; s++; }
    }
    for (long e = 0; e < ne; e++) { int *p = ids + 4 * e; par[e] = bits[p[0]] ^ bits[p[1]] ^ bits[p[2]] ^ bits[p[3]]; cnt[e / npath] += par[e]; }
    vlist = malloc(np * sizeof(int)); vpos = malloc(np * sizeof(int)); nv = 0;
    for (int i = 0; i < np; i++) { vpos[i] = -1; if (viol(cnt[i])) { vpos[i] = nv; vlist[nv++] = i; } }
    dc = calloc(np, sizeof(int)); touched = malloc(np * sizeof(int));
    int bestc = nv; memcpy(best, bits, norb);
    printf("q=%d norb=%d pairs=%d initial violations=%d noise=%.3f\n", q, norb, np, nv, noise); fflush(stdout);
    clock_t t0 = clock(); long it = 0; int cand[64];
    while (nv > 0) {
        if ((it & 255) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC; if (el > secs) break;
            if ((it & ((1 << 16) - 1)) == 0) { printf("t=%.0f it=%ld viol=%d best=%d\n", el, it, nv, bestc); fflush(stdout); }
        }
        it++;
        int pi = vlist[rnd() % nv]; int nc = 0;
        for (int k = 0; k < npath; k++) for (int a = 0; a < 4; a++) {
            int o = ids[4 * ((long)pi * npath + k) + a]; int dup = 0;
            for (int c = 0; c < nc; c++) if (cand[c] == o) dup = 1;
            if (!dup && nc < 64) cand[nc++] = o;
        }
        int pick;
        if (urand() < noise) pick = cand[rnd() % nc];
        else {
            int bb = 1 << 30, nb = 0, bl[64];
            for (int c = 0; c < nc; c++) { int b, m; eval(cand[c], &b, &m); int sc = b - m; if (sc < bb) { bb = sc; nb = 0; } if (sc == bb) bl[nb++] = cand[c]; }
            pick = bl[rnd() % nb];
        }
        flip(pick);
        if (nv < bestc) { bestc = nv; memcpy(best, bits, norb); }
    }
    if (nv < bestc) { bestc = nv; memcpy(best, bits, norb); }
    printf("RESULT q=%d best=%d iters=%ld time=%.1f\n", q, bestc, it, (double)(clock() - t0) / CLOCKS_PER_SEC);
    if (outb) {
        FILE *g = fopen(outb, "w"); fprintf(g, "{\"q\": %d, \"best\": %d, \"orbit_bits\": [", q, bestc);
        for (int o = 0; o < norb; o++) fprintf(g, "%s%d", o ? ", " : "", best[o]);
        fprintf(g, "]}\n"); fclose(g);
    }
    return 0;
}
