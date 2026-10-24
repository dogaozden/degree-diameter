/* lifteval.c: diameter test for cyclic voltage lifts of a bipartite base graph (cell-14-8 job, 2026-10-24).

   Base graph: sides A (nA vertices) and B (nB vertices), edges (a, b, v) with voltage v in Z_m, m <= 64.
   Lift: vertices (a, g), (b, g), g in Z_m; (a, g) ~ (b, g + v) for every base edge.
   Z_m acts on the lift (g -> g + 1), so every vertex is equivalent to one at level 0.
   For even D = 2k: the lift has diameter <= D iff from every (a, 0) every B-vertex (b, g) is reached by a walk of
   length exactly D - 1 (walks of length D - 1 reach all B-vertices at distance <= D - 1, by padding).
   Opposite-side pairs are then within D - 1 (also those starting on B: reverse the walk and translate),
   same-side pairs within D. For odd D = 2k+1: also every (a', g) must be reached by walks of length D - 1 from
   (a, 0), and every (b', g) from (b, 0); both are tested when ODD=1.

   Reach sets are bitmasks over Z_m per base vertex; one step is OR of rotated masks over the edges.

   Input (text): "nA nB m" then lines "a b v". Edges repeated with the same voltage are an error (multi-edge).
   Usage: lifteval FILE D [srcspec] [verbose]
     srcspec: "all" (default) | "r:K:seed" (K random A-sources) | "i:a1,a2,..." | "s:start:step" (every step-th)
   Output: per run "COST total_uncovered sources n" and the worst sources; exit code 0 iff cost 0.
   With ODD=1 in the environment and odd D, same-side targets are counted too (and B-sources are used). */
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

/* walks of length L from (src, 0) on side s (0 = A, 1 = B); returns masks for the final side in out (nA or nB) */
static void walk(int side, int src, int L, u64 *bufA, u64 *bufB) {
    memset(bufA, 0, sizeof(u64) * nA); memset(bufB, 0, sizeof(u64) * nB);
    if (side == 0) bufA[src] = 1; else bufB[src] = 1;
    int cur = side;
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
    if (argc < 3) { fprintf(stderr, "usage: lifteval FILE D [srcspec] [verbose]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    int D = atoi(argv[2]);
    const char *spec = argc > 3 ? argv[3] : "all";
    int verbose = argc > 4 ? atoi(argv[4]) : 0;
    int odd = (D % 2 == 1) && getenv("ODD") && atoi(getenv("ODD"));
    if (fscanf(f, "%d %d %d", &nA, &nB, &m) != 3 || m < 1 || m > 64) { fprintf(stderr, "bad header\n"); return 2; }
    FULL = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
    int cap = 1 << 20; int *ea = malloc(sizeof(int) * cap), *eb = malloc(sizeof(int) * cap), *ev = malloc(sizeof(int) * cap);
    nE = 0; int a, b, v;
    while (fscanf(f, "%d %d %d", &a, &b, &v) == 3) {
        if (a < 0 || a >= nA || b < 0 || b >= nB) { fprintf(stderr, "bad edge %d %d\n", a, b); return 2; }
        if (nE == cap) { cap *= 2; ea = realloc(ea, sizeof(int) * cap); eb = realloc(eb, sizeof(int) * cap); ev = realloc(ev, sizeof(int) * cap); }
        ea[nE] = a; eb[nE] = b; ev[nE] = ((v % m) + m) % m; nE++;
    }
    fclose(f);
    Aoff = calloc(nA + 1, sizeof(int)); Boff = calloc(nB + 1, sizeof(int));
    for (int e = 0; e < nE; e++) { Aoff[ea[e] + 1]++; Boff[eb[e] + 1]++; }
    int maxdA = 0, maxdB = 0;
    for (int i = 0; i < nA; i++) { if (Aoff[i + 1] > maxdA) maxdA = Aoff[i + 1]; Aoff[i + 1] += Aoff[i]; }
    for (int i = 0; i < nB; i++) { if (Boff[i + 1] > maxdB) maxdB = Boff[i + 1]; Boff[i + 1] += Boff[i]; }
    Aadj = malloc(sizeof(int) * nE); Avol = malloc(sizeof(int) * nE); Badj = malloc(sizeof(int) * nE); Bvol = malloc(sizeof(int) * nE);
    int *pa = malloc(sizeof(int) * nA), *pb = malloc(sizeof(int) * nB);
    memcpy(pa, Aoff, sizeof(int) * nA); memcpy(pb, Boff, sizeof(int) * nB);
    for (int e = 0; e < nE; e++) { Aadj[pa[ea[e]]] = eb[e]; Avol[pa[ea[e]]++] = ev[e]; Badj[pb[eb[e]]] = ea[e]; Bvol[pb[eb[e]]++] = ev[e]; }
    /* multi-edge check: same (a, b, v) twice */
    long multi = 0;
    for (int i = 0; i < nA; i++) for (int k = Aoff[i]; k < Aoff[i + 1]; k++) for (int k2 = Aoff[i]; k2 < k; k2++)
        if (Aadj[k] == Aadj[k2] && Avol[k] == Avol[k2]) multi++;
    fprintf(stderr, "base: nA %d nB %d m %d edges %d maxdeg A %d B %d; lift %lld vertices; multi-edges %ld\n",
            nA, nB, m, nE, maxdA, maxdB, (long long)(nA + nB) * m, multi);
    /* sources */
    int nsrc = 0; int *src = malloc(sizeof(int) * (nA + 8));
    if (!strcmp(spec, "all")) { for (int i = 0; i < nA; i++) src[nsrc++] = i; }
    else if (spec[0] == 'r') { int K = 0; unsigned long long seed = 1; sscanf(spec, "r:%d:%llu", &K, &seed);
        rnd_state = 0x9E3779B97F4A7C15ULL + (seed + 1) * 0xD1B54A32D192ED03ULL; if (!rnd_state) rnd_state = 1; for (int i = 0; i < 20; i++) rnd();
        for (int i = 0; i < K; i++) src[nsrc++] = (int)(rnd() % (u64)nA); }
    else if (spec[0] == 's') { int st = 0, sp = 1; sscanf(spec, "s:%d:%d", &st, &sp); for (int i = st; i < nA; i += sp) src[nsrc++] = i; }
    else if (spec[0] == 'i') { const char *p = spec + 2; while (*p) { src[nsrc++] = atoi(p); while (*p && *p != ',') p++; if (*p) p++; } }
    u64 *bA = malloc(sizeof(u64) * nA), *bB = malloc(sizeof(u64) * nB);
    long long total = 0; int worst = -1; long long worstc = -1; int bad = 0;
    for (int s = 0; s < nsrc; s++) {
        long long unc = 0;
        if (D % 2 == 0) { walk(0, src[s], D - 1, bA, bB); for (int i = 0; i < nB; i++) unc += m - __builtin_popcountll(bB[i]); }
        else {
            walk(0, src[s], D - 1, bA, bB); for (int i = 0; i < nA; i++) unc += m - __builtin_popcountll(bA[i]);
            walk(0, src[s], D, bA, bB); for (int i = 0; i < nB; i++) unc += m - __builtin_popcountll(bB[i]);
        }
        if (verbose >= 2 && unc) {
            fprintf(stderr, "src %d: %lld uncovered:", src[s], unc); int shown = 0;
            for (int i = 0; i < nB && shown < 20; i++) if (bB[i] != FULL) { fprintf(stderr, " b%d:%016llx", i, (unsigned long long)(~bB[i] & FULL)); shown++; }
            fprintf(stderr, "\n");
        }
        if (unc) bad++;
        total += unc; if (unc > worstc) { worstc = unc; worst = src[s]; }
    }
    if (odd) {
        for (int s = 0; s < nsrc && src[s] < nB; s++) {
            long long unc = 0; walk(1, src[s], D - 1, bA, bB);
            for (int i = 0; i < nB; i++) unc += m - __builtin_popcountll(bB[i]);
            total += unc; if (unc) bad++;
        }
    }
    printf("COST %lld sources %d bad %d worst_src %d worst %lld maxdeg %d lift_vertices %lld\n", total, nsrc, bad, worst,
           worstc, maxdA > maxdB ? maxdA : maxdB, (long long)(nA + nB) * m);
    return total ? 1 : 0;
}
