/* pvlift.c: permutation-voltage lift evaluator (card c7, squad r1_d14D8).

   Base: bipartite, A-vertices 0..nA-1 and B-vertices 0..nB-1, edges (a, b, pid). Each pid indexes a permutation
   pi_pid of {0..m-1} (given explicitly, so any voltage group, abelian or not, affine maps, dihedral ...).
   Lift: vertices (a,k) in A and (b,j) in B; edge (a,k) ~ (b, pi_pid(k)).
   Even D: the lift has diameter <= D iff from every A-source (a,k) every B-vertex is at distance <= D-1
   (bipartite lift; this implies all other pairs are within D). Checked by a depth-limited BFS on the lift.

   Input (text): "nA nB m P", then P lines of m integers (pi_p(0) .. pi_p(m-1)), then E lines "a b pid".
   Usage: pvlift FILE D spec
     all          every source (a,k), a in A, k in 0..m-1 (exact)
     r:K:seed     K random sources (a,k)
     reg:K:seed   K random a with k = 0 (use when the monodromy group acts regularly on the fibre)
     all0         every a in A with k = 0 (exact for regular voltage groups)
     i:a1,a2,...  sources (a_i, 0) for the listed a (cross-check against liftevalw)
   Output: "COST total sources n bad b worst_src s worst w lift_vertices V". Exit 0 iff COST 0.
   Cost of a source = number of B-lift-vertices at distance > D-1. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int nA, nB, m, P;
static int *perm, *inv;
static int *offA, *adjA, *pidA, *offB, *adjB, *pidB;
static unsigned int rs = 2463534242u;
static unsigned int rnd(void) { rs ^= rs << 13; rs ^= rs >> 17; rs ^= rs << 5; return rs; }

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: pvlift FILE D spec\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror("open"); return 2; }
    int D = atoi(argv[2]);
    const char *spec = argv[3];
    if (fscanf(f, "%d %d %d %d", &nA, &nB, &m, &P) != 4 || m < 1 || P < 1) { fprintf(stderr, "bad header\n"); return 2; }
    perm = malloc(sizeof(int) * (size_t)P * m); inv = malloc(sizeof(int) * (size_t)P * m);
    for (int p = 0; p < P; p++) {
        for (int k = 0; k < m; k++) {
            if (fscanf(f, "%d", &perm[(size_t)p * m + k]) != 1) { fprintf(stderr, "bad perm\n"); return 2; }
        }
        int seen[1024]; memset(seen, 0, sizeof(seen));
        for (int k = 0; k < m; k++) {
            int v = perm[(size_t)p * m + k];
            if (v < 0 || v >= m || seen[v]) { fprintf(stderr, "perm %d not a bijection\n", p); return 2; }
            seen[v] = 1; inv[(size_t)p * m + v] = k;
        }
    }
    int cap = 1 << 16, E = 0;
    int *ea = malloc(sizeof(int) * cap), *eb = malloc(sizeof(int) * cap), *ep = malloc(sizeof(int) * cap);
    int a, b, pid;
    while (fscanf(f, "%d %d %d", &a, &b, &pid) == 3) {
        if (a < 0 || a >= nA || b < 0 || b >= nB || pid < 0 || pid >= P) { fprintf(stderr, "bad edge %d %d %d\n", a, b, pid); return 2; }
        if (E == cap) { cap *= 2; ea = realloc(ea, sizeof(int) * cap); eb = realloc(eb, sizeof(int) * cap); ep = realloc(ep, sizeof(int) * cap); }
        ea[E] = a; eb[E] = b; ep[E] = pid; E++;
    }
    fclose(f);
    offA = calloc(nA + 1, sizeof(int)); offB = calloc(nB + 1, sizeof(int));
    for (int e = 0; e < E; e++) { offA[ea[e] + 1]++; offB[eb[e] + 1]++; }
    int maxdA = 0, maxdB = 0;
    for (int i = 0; i < nA; i++) { if (offA[i + 1] > maxdA) maxdA = offA[i + 1]; offA[i + 1] += offA[i]; }
    for (int i = 0; i < nB; i++) { if (offB[i + 1] > maxdB) maxdB = offB[i + 1]; offB[i + 1] += offB[i]; }
    adjA = malloc(sizeof(int) * E); pidA = malloc(sizeof(int) * E); adjB = malloc(sizeof(int) * E); pidB = malloc(sizeof(int) * E);
    int *pa = malloc(sizeof(int) * nA), *pb = malloc(sizeof(int) * nB);
    memcpy(pa, offA, sizeof(int) * nA); memcpy(pb, offB, sizeof(int) * nB);
    for (int e = 0; e < E; e++) {
        adjA[pa[ea[e]]] = eb[e]; pidA[pa[ea[e]]++] = ep[e];
        adjB[pb[eb[e]]] = ea[e]; pidB[pb[eb[e]]++] = ep[e];
    }
    int nv = (nA + nB) * m;
    fprintf(stderr, "base nA %d nB %d m %d P %d edges %d maxdeg A %d B %d; lift vertices %d\n", nA, nB, m, P, E, maxdA, maxdB, nv);

    /* sources: pairs (a, k) */
    int cap_s = (nA * m > 0 ? nA * m : 1);
    int *srcA = malloc(sizeof(int) * cap_s), *srcK = malloc(sizeof(int) * cap_s), nsrc = 0;
    if (!strcmp(spec, "all")) {
        for (int x = 0; x < nA; x++) for (int k = 0; k < m; k++) { srcA[nsrc] = x; srcK[nsrc++] = k; }
    } else if (!strncmp(spec, "r:", 2)) {
        int K = 0; unsigned long long seed = 1; sscanf(spec, "r:%d:%llu", &K, &seed);
        rs ^= (unsigned int)(seed * 2654435761u) | 1u; for (int i = 0; i < 20; i++) rnd();
        for (int i = 0; i < K; i++) { srcA[nsrc] = rnd() % nA; srcK[nsrc++] = rnd() % m; }
    } else if (!strncmp(spec, "reg:", 4)) {
        int K = 0; unsigned long long seed = 1; sscanf(spec, "reg:%d:%llu", &K, &seed);
        rs ^= (unsigned int)(seed * 2654435761u) | 1u; for (int i = 0; i < 20; i++) rnd();
        for (int i = 0; i < K; i++) { srcA[nsrc] = rnd() % nA; srcK[nsrc++] = 0; }
    } else if (!strcmp(spec, "all0")) {  /* every base vertex a with k = 0 (exact when the voltage group acts regularly) */
        for (int x = 0; x < nA; x++) { srcA[nsrc] = x; srcK[nsrc++] = 0; }
    } else if (spec[0] == 'i') {
        const char *p = spec + 2;
        while (*p) { srcA[nsrc] = atoi(p); srcK[nsrc++] = 0; while (*p && *p != ',') p++; if (*p) p++; }
    } else { fprintf(stderr, "bad spec\n"); return 2; }

    int *stamp = calloc(nv, sizeof(int));
    int *cur = malloc(sizeof(int) * nv), *nxt = malloc(sizeof(int) * nv);
    int stc = 0;
    long long total = 0, worstc = -1; int bad = 0, worst_a = -1, worst_k = -1;
    for (int s = 0; s < nsrc; s++) {
        int src = srcA[s] * m + srcK[s];
        stc++;
        int ncur = 0, visB = 0;
        cur[ncur++] = src; stamp[src] = stc;
        for (int d = 1; d <= D - 1; d++) {
            int nn = 0;
            for (int i = 0; i < ncur; i++) {
                int x = cur[i], base = x / m, k = x - base * m;
                if (base < nA) {
                    for (int e = offA[base]; e < offA[base + 1]; e++) {
                        int y = (nA + adjA[e]) * m + perm[(size_t)pidA[e] * m + k];
                        if (stamp[y] != stc) { stamp[y] = stc; nxt[nn++] = y; visB++; }
                    }
                } else {
                    int bb = base - nA;
                    for (int e = offB[bb]; e < offB[bb + 1]; e++) {
                        int y = adjB[e] * m + inv[(size_t)pidB[e] * m + k];
                        if (stamp[y] != stc) { stamp[y] = stc; nxt[nn++] = y; }
                    }
                }
            }
            /* visB counted B-vertices added at any level; A-vertices are added at even levels only */
            int *t = cur; cur = nxt; nxt = t; ncur = nn;
        }
        /* visB counted B-side additions; A-side additions were not counted (they are not B) */
        long long unc = (long long)nB * m - visB;
        total += unc;
        if (unc) bad++;
        if (unc > worstc) { worstc = unc; worst_a = srcA[s]; worst_k = srcK[s]; }
    }
    printf("COST %lld sources %d bad %d worst_src %d worst %lld worst_k %d lift_vertices %d\n", total, nsrc, bad,
           worst_a, worstc, worst_k, (nA + nB) * m);
    return total ? 1 : 0;
}
