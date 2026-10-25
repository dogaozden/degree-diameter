/* nblev.c: counts non-backtracking walks of length 1,3,5,7 from (p, 0) to every (line, level) in a Z_L-lift
   (levels = voltages mod L) of a base graph in lifteval format; the first nA*(q+1) edges must be hexagon flags.
   Non-backtracking in the lift = never reuse the same base edge (edge id) immediately. Reports per hexagon distance
   class (1, 3, 5) and level: min and mean number of walks per target. Usage: nblev FILE q L srcspec */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int nA, nB, m, nE;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); int q = atoi(argv[2]), L = atoi(argv[3]); const char *spec = argv[4];
    if (fscanf(f, "%d %d %d", &nA, &nB, &m) != 3) return 2;
    int cap = 1 << 20; int *ea = malloc(4 * cap), *eb = malloc(4 * cap), *ev = malloc(4 * cap); int a, b, v; nE = 0;
    while (fscanf(f, "%d %d %d", &a, &b, &v) == 3) { if (nE == cap) { cap *= 2; ea = realloc(ea, 4 * cap); eb = realloc(eb, 4 * cap); ev = realloc(ev, 4 * cap); }
        ea[nE] = a; eb[nE] = b; ev[nE] = ((v % L) + L) % L; nE++; }
    fclose(f);
    int NH = nA * (q + 1);
    int *Ao = calloc(nA + 1, 4), *Bo = calloc(nB + 1, 4), *AE = malloc(4 * nE), *BE = malloc(4 * nE);
    for (int e = 0; e < nE; e++) { Ao[ea[e] + 1]++; Bo[eb[e] + 1]++; }
    for (int i = 0; i < nA; i++) Ao[i + 1] += Ao[i]; for (int i = 0; i < nB; i++) Bo[i + 1] += Bo[i];
    { int *pa = malloc(4 * nA), *pb = malloc(4 * nB); memcpy(pa, Ao, 4 * nA); memcpy(pb, Bo, 4 * nB);
      for (int e = 0; e < nE; e++) { AE[pa[ea[e]]++] = e; BE[pb[eb[e]]++] = e; } }
    /* hexagon distances */
    int *HPo = calloc(nA + 1, 4), *HLo = calloc(nB + 1, 4), *HP = malloc(4 * NH), *HL = malloc(4 * NH);
    for (int e = 0; e < NH; e++) { HPo[ea[e] + 1]++; HLo[eb[e] + 1]++; }
    for (int i = 0; i < nA; i++) HPo[i + 1] += HPo[i]; for (int i = 0; i < nB; i++) HLo[i + 1] += HLo[i];
    { int *pp = malloc(4 * nA), *pl = malloc(4 * nB); memcpy(pp, HPo, 4 * nA); memcpy(pl, HLo, 4 * nB);
      for (int e = 0; e < NH; e++) { HP[pp[ea[e]]++] = eb[e]; HL[pl[eb[e]]++] = ea[e]; } }
    int nsrc = 0, *src = malloc(4 * (nA + 8));
    if (!strcmp(spec, "all")) for (int i = 0; i < nA; i++) src[nsrc++] = i;
    else if (spec[0] == 'r') { int K; unsigned long long seed; sscanf(spec, "r:%d:%llu", &K, &seed); rs += seed * 0xD1B54A32D192ED03ULL + 99; for (int i = 0; i < 20; i++) rnd(); for (int i = 0; i < K; i++) src[nsrc++] = rnd() % nA; }
    /* state: (edge e just traversed, level) ; count arrays per side: cnt[e*L + lev] = number of NB walks ending by edge e */
    int64_t *cur = calloc((size_t)nE * L, 8), *nxt = calloc((size_t)nE * L, 8);
    int64_t *tot = calloc((size_t)nB * L, 8);
    signed char *dA = malloc(nA), *dB = malloc(nB); int *qu = malloc(4 * (nA + nB));
    int64_t mn[3][16], cnt[3][16]; double sum[3][16];
    for (int c = 0; c < 3; c++) for (int g = 0; g < L; g++) { mn[c][g] = 1LL << 60; sum[c][g] = 0; cnt[c][g] = 0; }
    for (int s = 0; s < nsrc; s++) {
        int p0 = src[s];
        memset(dA, -1, nA); memset(dB, -1, nB); dA[p0] = 0; int h = 0, t = 0; qu[t++] = p0;
        while (h < t) { int x = qu[h++];
            if (x < nA) { for (int k = HPo[x]; k < HPo[x + 1]; k++) { int y = HP[k]; if (dB[y] < 0) { dB[y] = dA[x] + 1; qu[t++] = nA + y; } } }
            else { int y = x - nA; for (int k = HLo[y]; k < HLo[y + 1]; k++) { int z = HL[k]; if (dA[z] < 0) { dA[z] = dB[y] + 1; qu[t++] = z; } } } }
        memset(cur, 0, (size_t)nE * L * 8); memset(tot, 0, (size_t)nB * L * 8);
        for (int k = Ao[p0]; k < Ao[p0 + 1]; k++) { int e = AE[k]; cur[(size_t)e * L + ev[e]] += 1; }
        for (int step = 1; step <= 7; step++) {
            /* cur: walks of length step ending at the far endpoint of edge e; side of endpoint: B if step odd */
            if (step % 2 == 1) { for (int e = 0; e < nE; e++) for (int g = 0; g < L; g++) tot[(size_t)eb[e] * L + g] += cur[(size_t)e * L + g]; }
            if (step == 7) break;
            memset(nxt, 0, (size_t)nE * L * 8);
            for (int e = 0; e < nE; e++) for (int g = 0; g < L; g++) { int64_t c = cur[(size_t)e * L + g]; if (!c) continue;
                if (step % 2 == 1) { int y = eb[e]; for (int k = Bo[y]; k < Bo[y + 1]; k++) { int e2 = BE[k]; if (e2 == e) continue; int g2 = (g - ev[e2] + L) % L; nxt[(size_t)e2 * L + g2] += c; } }
                else { int x = ea[e]; for (int k = Ao[x]; k < Ao[x + 1]; k++) { int e2 = AE[k]; if (e2 == e) continue; int g2 = (g + ev[e2]) % L; nxt[(size_t)e2 * L + g2] += c; } } }
            int64_t *tmp = cur; cur = nxt; nxt = tmp;
        }
        for (int y = 0; y < nB; y++) { int c = dB[y] / 2; if (c < 0 || c > 2) c = 2;
            for (int g = 0; g < L; g++) { int64_t x = tot[(size_t)y * L + g]; if (x < mn[c][g]) mn[c][g] = x; sum[c][g] += x; cnt[c][g]++; } }
    }
    printf("sources %d L %d\n", nsrc, L);
    for (int c = 0; c < 3; c++) { printf("d=%d", 2 * c + 1); for (int g = 0; g < L; g++) printf("  lev%d min %lld mean %.1f", g, (long long)mn[c][g], sum[c][g] / cnt[c][g]); printf("\n"); }
    return 0;
}
