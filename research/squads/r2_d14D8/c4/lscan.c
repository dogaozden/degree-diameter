/* lscan.c (card c4, squad r2_d14D8): lifteval.c (even D) with two changes for the level scan.
   FILE may be "-" (base graph read from stdin). With EARLY=1 in the environment the scan stops at the first source
   that leaves a lift vertex uncovered. The verdict is unchanged: exit code 0 iff COST 0 (exact over the srcspec).
   Base-graph format, lift semantics and srcspec as in lifteval.c.
   Usage: lscan FILE D [srcspec] [verbose]   (srcspec: all | r:K:seed | i:a1,a2,... | s:start:step)
   Build: gcc -O3 -march=native -o lscan lscan.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t u64;
static int nA, nB, m, nE;
static int *Aoff, *Aadj, *Avol, *Boff, *Badj, *Bvol;
static u64 FULL;

static inline u64 rot(u64 x, int v) { if (!v) return x; return ((x << v) | (x >> (m - v))) & FULL; }

static u64 rnd_state = 0x9E3779B97F4A7C15ULL;
static u64 rnd(void) { rnd_state ^= rnd_state << 13; rnd_state ^= rnd_state >> 7; rnd_state ^= rnd_state << 17; return rnd_state; }

/* walks of length L from (src, 0) on side A; the result for side B (L odd) is left in bufB */
static void walk(int src, int L, u64 *bufA, u64 *bufB) {
    memset(bufA, 0, sizeof(u64) * nA); memset(bufB, 0, sizeof(u64) * nB);
    bufA[src] = 1;
    int cur = 0;
    for (int step = 0; step < L; step++) {
        if (cur == 0) {
            memset(bufB, 0, sizeof(u64) * nB);
            for (int a = 0; a < nA; a++) { u64 x = bufA[a]; if (!x) continue;
                for (int k = Aoff[a]; k < Aoff[a + 1]; k++) bufB[Aadj[k]] |= rot(x, Avol[k]); }
            cur = 1;
        } else {
            memset(bufA, 0, sizeof(u64) * nA);
            for (int b = 0; b < nB; b++) { u64 x = bufB[b]; if (!x) continue;
                for (int k = Boff[b]; k < Boff[b + 1]; k++) bufA[Badj[k]] |= rot(x, (m - Bvol[k]) % m); }
            cur = 0;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: lscan FILE D [srcspec] [verbose]\n"); return 2; }
    FILE *f = strcmp(argv[1], "-") ? fopen(argv[1], "r") : stdin;
    if (!f) { perror("open"); return 2; }
    int D = atoi(argv[2]);
    if (D < 2 || D % 2) { fprintf(stderr, "lscan: even D only\n"); return 2; }
    const char *spec = argc > 3 ? argv[3] : "all";
    int verbose = argc > 4 ? atoi(argv[4]) : 0;
    int early = getenv("EARLY") ? atoi(getenv("EARLY")) : 0;
    if (fscanf(f, "%d %d %d", &nA, &nB, &m) != 3 || m < 1 || m > 64) { fprintf(stderr, "bad header\n"); return 2; }
    FULL = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
    int cap = 1 << 20; int *ea = malloc(sizeof(int) * cap), *eb = malloc(sizeof(int) * cap), *ev = malloc(sizeof(int) * cap);
    nE = 0; int a, b, v;
    while (fscanf(f, "%d %d %d", &a, &b, &v) == 3) {
        if (a < 0 || a >= nA || b < 0 || b >= nB) { fprintf(stderr, "bad edge %d %d\n", a, b); return 2; }
        if (nE == cap) { cap *= 2; ea = realloc(ea, sizeof(int) * cap); eb = realloc(eb, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        ea[nE] = a; eb[nE] = b; ev[nE] = ((v % m) + m) % m; nE++;
    }
    if (f != stdin) fclose(f);
    Aoff = calloc(nA + 1, sizeof(int)); Boff = calloc(nB + 1, sizeof(int));
    for (int e = 0; e < nE; e++) { Aoff[ea[e] + 1]++; Boff[eb[e] + 1]++; }
    int maxdA = 0, maxdB = 0;
    for (int i = 0; i < nA; i++) { if (Aoff[i + 1] > maxdA) maxdA = Aoff[i + 1]; Aoff[i + 1] += Aoff[i]; }
    for (int i = 0; i < nB; i++) { if (Boff[i + 1] > maxdB) maxdB = Boff[i + 1]; Boff[i + 1] += Boff[i]; }
    Aadj = malloc(sizeof(int) * nE); Avol = malloc(sizeof(int) * nE); Badj = malloc(sizeof(int) * nE); Bvol = malloc(sizeof(int) * nE);
    int *pa = malloc(sizeof(int) * nA), *pb = malloc(sizeof(int) * nB);
    memcpy(pa, Aoff, sizeof(int) * nA); memcpy(pb, Boff, sizeof(int) * nB);
    for (int e = 0; e < nE; e++) { Aadj[pa[ea[e]]] = eb[e]; Avol[pa[ea[e]]++] = ev[e]; Badj[pb[eb[e]]] = ea[e]; Bvol[pb[eb[e]]++] = ev[e]; }
    long multi = 0;
    for (int i = 0; i < nA; i++) for (int k = Aoff[i]; k < Aoff[i + 1]; k++) for (int k2 = Aoff[i]; k2 < k; k2++)
        if (Aadj[k] == Aadj[k2] && Avol[k] == Avol[k2]) multi++;
    fprintf(stderr, "base: nA %d nB %d m %d edges %d maxdeg A %d B %d; lift %lld vertices; multi-edges %ld\n",
            nA, nB, m, nE, maxdA, maxdB, (long long)(nA + nB) * m, multi);
    int nsrc = 0; int *src = malloc(sizeof(int) * (nA + 8));
    if (!strcmp(spec, "all")) { for (int i = 0; i < nA; i++) src[nsrc++] = i; }
    else if (spec[0] == 'r') { int K = 0; unsigned long long seed = 1; sscanf(spec, "r:%d:%llu", &K, &seed);
        rnd_state = 0x9E3779B97F4A7C15ULL + (seed + 1) * 0xD1B54A32D192ED03ULL; if (!rnd_state) rnd_state = 1; for (int i = 0; i < 20; i++) rnd();
        for (int i = 0; i < K; i++) src[nsrc++] = (int)(rnd() % (u64)nA); }
    else if (spec[0] == 's') { int st = 0, sp = 1; sscanf(spec, "s:%d:%d", &st, &sp); for (int i = st; i < nA; i += sp) src[nsrc++] = i; }
    else if (spec[0] == 'i') { const char *p = spec + 2; while (*p) { src[nsrc++] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; } }
    u64 *bA = malloc(sizeof(u64) * nA), *bB = malloc(sizeof(u64) * nB);
    long long total = 0; int worst = -1; long long worstc = -1; int bad = 0; int done = 0;
    for (int s = 0; s < nsrc; s++) {
        walk(src[s], D - 1, bA, bB);
        long long unc = 0;
        for (int i = 0; i < nB; i++) unc += m - __builtin_popcountll(bB[i]);
        done++;
        if (verbose >= 2 && unc) {
            fprintf(stderr, "src %d: %lld uncovered:", src[s], unc); int shown = 0;
            for (int i = 0; i < nB && shown < 20; i++) if (bB[i] != FULL) { fprintf(stderr, " b%d:%016llx", i, (unsigned long long)(~bB[i] & FULL)); shown++; }
            fprintf(stderr, "\n");
        }
        if (unc) bad++;
        total += unc; if (unc > worstc) { worstc = unc; worst = src[s]; }
        if (unc && early) break;
    }
    printf("COST %lld sources %d bad %d worst_src %d worst %lld maxdeg %d lift_vertices %lld early %d\n", total, done, bad, worst,
           worstc, maxdA > maxdB ? maxdA : maxdB, (long long)(nA + nB) * m, early);
    return total ? 1 : 0;
}
