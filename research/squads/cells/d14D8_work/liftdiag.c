/* liftdiag.c: diagnostics for a cyclic lift of H(q) + extra edges (cell-14-8 job, round 2).
   Same base-file format as lifteval.c (m <= 64). The first NH = nA*(q+1) edges must be the hexagon flags.
   For each source (a, 0) it walks exactly D-1 = 7 steps (all edges) and tabulates the uncovered (line, g) pairs by
   hexagon distance d(a, line) in {1,3,5} and by g mod Lv (level group size; Lv = 1 for none).
   Usage: liftdiag FILE q Lv srcspec    (srcspec: all | r:K:seed | i:a1,a2,..) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int nA, nB, m, nE;
static int *Aoff, *Aadj, *Avol, *Boff, *Badj, *Bvol;
static u64 FULL;
static inline u64 rot(u64 x, int v) { if (!v) return x; return ((x << v) | (x >> (m - v))) & FULL; }
static u64 rs = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: liftdiag FILE q Lv srcspec\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); int q = atoi(argv[2]), Lv = atoi(argv[3]); const char *spec = argv[4];
    if (fscanf(f, "%d %d %d", &nA, &nB, &m) != 3 || m > 64) return 2;
    FULL = m == 64 ? ~0ULL : (1ULL << m) - 1;
    int cap = 1 << 20; int *ea = malloc(4 * cap), *eb = malloc(4 * cap), *ev = malloc(4 * cap); int a, b, v; nE = 0;
    while (fscanf(f, "%d %d %d", &a, &b, &v) == 3) { if (nE == cap) { cap *= 2; ea = realloc(ea, 4 * cap); eb = realloc(eb, 4 * cap); ev = realloc(ev, 4 * cap); }
        ea[nE] = a; eb[nE] = b; ev[nE] = ((v % m) + m) % m; nE++; }
    fclose(f);
    int NH = nA * (q + 1);
    /* hexagon adjacency */
    int *HPo = calloc(nA + 1, 4), *HLo = calloc(nB + 1, 4), *HP = malloc(4 * NH), *HL = malloc(4 * NH);
    for (int e = 0; e < NH; e++) { HPo[ea[e] + 1]++; HLo[eb[e] + 1]++; }
    for (int i = 0; i < nA; i++) HPo[i + 1] += HPo[i]; for (int i = 0; i < nB; i++) HLo[i + 1] += HLo[i];
    { int *pp = malloc(4 * nA), *pl = malloc(4 * nB); memcpy(pp, HPo, 4 * nA); memcpy(pl, HLo, 4 * nB);
      for (int e = 0; e < NH; e++) { HP[pp[ea[e]]++] = eb[e]; HL[pl[eb[e]]++] = ea[e]; } }
    Aoff = calloc(nA + 1, 4); Boff = calloc(nB + 1, 4);
    for (int e = 0; e < nE; e++) { Aoff[ea[e] + 1]++; Boff[eb[e] + 1]++; }
    for (int i = 0; i < nA; i++) Aoff[i + 1] += Aoff[i]; for (int i = 0; i < nB; i++) Boff[i + 1] += Boff[i];
    Aadj = malloc(4 * nE); Avol = malloc(4 * nE); Badj = malloc(4 * nE); Bvol = malloc(4 * nE);
    { int *pa = malloc(4 * nA), *pb = malloc(4 * nB); memcpy(pa, Aoff, 4 * nA); memcpy(pb, Boff, 4 * nB);
      for (int e = 0; e < nE; e++) { Aadj[pa[ea[e]]] = eb[e]; Avol[pa[ea[e]]++] = ev[e]; Badj[pb[eb[e]]] = ea[e]; Bvol[pb[eb[e]]++] = ev[e]; } }
    int nsrc = 0, *src = malloc(4 * (nA + 8));
    if (!strcmp(spec, "all")) for (int i = 0; i < nA; i++) src[nsrc++] = i;
    else if (spec[0] == 'r') { int K; unsigned long long seed; sscanf(spec, "r:%d:%llu", &K, &seed); rs += seed * 0xD1B54A32D192ED03ULL + 12345; for (int i = 0; i < 20; i++) rnd(); for (int i = 0; i < K; i++) src[nsrc++] = rnd() % nA; }
    else { const char *p = spec + 2; while (*p) { src[nsrc++] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; } }
    u64 *bA = malloc(8 * nA), *bB = malloc(8 * nB);
    signed char *dA = malloc(nA), *dB = malloc(nB); int *qu = malloc(4 * (nA + nB));
    long long tab[3][64]; memset(tab, 0, sizeof tab); long long cnt[3] = {0, 0, 0};
    for (int s = 0; s < nsrc; s++) {
        int p0 = src[s];
        memset(dA, -1, nA); memset(dB, -1, nB); dA[p0] = 0; int h = 0, t = 0; qu[t++] = p0;
        while (h < t) { int x = qu[h++];
            if (x < nA) { for (int k = HPo[x]; k < HPo[x + 1]; k++) { int y = HP[k]; if (dB[y] < 0) { dB[y] = dA[x] + 1; qu[t++] = nA + y; } } }
            else { int y = x - nA; for (int k = HLo[y]; k < HLo[y + 1]; k++) { int z = HL[k]; if (dA[z] < 0) { dA[z] = dB[y] + 1; qu[t++] = z; } } } }
        memset(bA, 0, 8 * nA); bA[p0] = 1;
        for (int step = 0; step < 7; step++) {
            if (step % 2 == 0) { memset(bB, 0, 8 * nB); for (int x = 0; x < nA; x++) { u64 w = bA[x]; if (!w) continue; for (int k = Aoff[x]; k < Aoff[x + 1]; k++) bB[Aadj[k]] |= rot(w, Avol[k]); } }
            else { memset(bA, 0, 8 * nA); for (int y = 0; y < nB; y++) { u64 w = bB[y]; if (!w) continue; for (int k = Boff[y]; k < Boff[y + 1]; k++) bA[Badj[k]] |= rot(w, (m - Bvol[k]) % m); } }
        }
        for (int y = 0; y < nB; y++) { int dc = dB[y] / 2; if (dc < 0 || dc > 2) dc = 2; cnt[dc]++; u64 miss = ~bB[y] & FULL;
            while (miss) { int g = __builtin_ctzll(miss); miss &= miss - 1; tab[dc][g % Lv]++; } }
    }
    printf("sources %d m %d Lv %d\n", nsrc, m, Lv);
    for (int dc = 0; dc < 3; dc++) { long long tot = 0; for (int g = 0; g < Lv; g++) tot += tab[dc][g];
        printf("d=%d lines/src %.0f uncovered/src %.2f  by level:", 2 * dc + 1, (double)cnt[dc] / nsrc, (double)tot / nsrc);
        for (int g = 0; g < Lv; g++) printf(" %.2f", (double)tab[dc][g] / nsrc); printf("\n"); }
    return 0;
}
