/* liftcheck.c: diameter check for a voltage lift of a bipartite base multigraph by a group A of order m <= 64.

   Base file (text):
     line 1:  NP NL m GROUP
              NP points (side 0, ids 0..NP-1), NL lines (side 1, ids 0..NL-1), group order m.
              GROUP = "cyc" (Z_m, element a = integer 0..m-1, product = sum mod m)
                    | "table" followed on the next m lines by the m x m multiplication table (row g: g*h for h = 0..m-1,
                      element 0 must be the identity).
     then one edge per line:  p l g   (point p, line l, voltage g in A).
   Lift: vertices (p,x), (l,x), x in A; (p,x) ~ (l, x*g) for every base edge (p,l,g). Parallel base edges allowed.

   Check: for every point source p (or a subset), BFS in the lift from (p,e) to depth MAXLEN (default 7, i.e. D-1 for
   even D = 8). Reports the number of (line, x) pairs not reached. Every opposite pair within 7 means diameter <= 8
   (a same-side pair (u,v): v has a neighbour w, d(u,w) <= 7). The lift is invariant under left multiplication by A,
   so sources (p,e) cover all (p,x).

   Usage: liftcheck BASEFILE [MAXLEN] [STEP]   (STEP s: only sources p = 0, s, 2s, ...; default 1 = all)
   Output: per-source worst, total uncovered, RESULT line. Threads via OpenMP. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef uint64_t u64;
static int NP, NL, m, cyc;
static int *tab;           /* m*m */
static int *inv_;          /* m */
static u64 FULL;

/* adjacency: CSR for points -> (line, g) and lines -> (point, g^-1) */
static int *pstart, *padj, *pg;
static int *lstart, *ladj, *lg;
/* byte tables for general groups: T[g][b][v] = image of byte value v at byte position b under right mult by g */
static u64 *T;

static inline u64 act(u64 x, int g) {
    if (cyc) {
        if (g == 0) return x;
        return ((x << g) | (x >> (m - g))) & FULL;
    }
    const u64 *t = T + (size_t)g * 8 * 256;
    u64 r = 0;
    for (int b = 0; b < 8 && x; b++, x >>= 8) { unsigned v = x & 255; if (v) r |= t[b * 256 + v]; }
    return r;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: liftcheck BASE [MAXLEN] [STEP]\n"); return 1; }
    int maxlen = argc > 2 ? atoi(argv[2]) : 7;
    int step = argc > 3 ? atoi(argv[3]) : 1;
    FILE *f = fopen(argv[1], "r");
    if (!f) { perror("open"); return 1; }
    char gs[32];
    if (fscanf(f, "%d %d %d %31s", &NP, &NL, &m, gs) != 4) { fprintf(stderr, "bad header\n"); return 1; }
    if (m < 1 || m > 64) { fprintf(stderr, "m must be 1..64\n"); return 1; }
    FULL = (m == 64) ? ~0ULL : ((1ULL << m) - 1);
    tab = malloc(sizeof(int) * m * m); inv_ = malloc(sizeof(int) * m);
    cyc = !strcmp(gs, "cyc");
    if (cyc) { for (int a = 0; a < m; a++) for (int b = 0; b < m; b++) tab[a * m + b] = (a + b) % m; }
    else if (!strcmp(gs, "table")) { for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &tab[i]) != 1) { fprintf(stderr, "bad table\n"); return 1; } }
    else { fprintf(stderr, "unknown group %s\n", gs); return 1; }
    for (int a = 0; a < m; a++) { inv_[a] = -1; for (int b = 0; b < m; b++) if (tab[a * m + b] == 0) inv_[a] = b; if (inv_[a] < 0) { fprintf(stderr, "no inverse\n"); return 1; } }
    /* read edges */
    int cap = 1 << 20, ne = 0; int *E = malloc(sizeof(int) * 3 * cap);
    int p, l, g;
    while (fscanf(f, "%d %d %d", &p, &l, &g) == 3) {
        if (p < 0 || p >= NP || l < 0 || l >= NL || g < 0 || g >= m) { fprintf(stderr, "bad edge %d %d %d\n", p, l, g); return 1; }
        if (ne == cap) { cap *= 2; E = realloc(E, sizeof(int) * 3 * cap); }
        E[3 * ne] = p; E[3 * ne + 1] = l; E[3 * ne + 2] = g; ne++;
    }
    fclose(f);
    pstart = calloc(NP + 1, sizeof(int)); lstart = calloc(NL + 1, sizeof(int));
    for (int i = 0; i < ne; i++) { pstart[E[3 * i] + 1]++; lstart[E[3 * i + 1] + 1]++; }
    int maxdp = 0, maxdl = 0, mindp = 1 << 30, mindl = 1 << 30;
    for (int i = 0; i < NP; i++) { int d = pstart[i + 1]; if (d > maxdp) maxdp = d; if (d < mindp) mindp = d; }
    for (int i = 0; i < NL; i++) { int d = lstart[i + 1]; if (d > maxdl) maxdl = d; if (d < mindl) mindl = d; }
    for (int i = 0; i < NP; i++) pstart[i + 1] += pstart[i];
    for (int i = 0; i < NL; i++) lstart[i + 1] += lstart[i];
    padj = malloc(sizeof(int) * ne); pg = malloc(sizeof(int) * ne); ladj = malloc(sizeof(int) * ne); lg = malloc(sizeof(int) * ne);
    int *pc = calloc(NP, sizeof(int)), *lc = calloc(NL, sizeof(int));
    for (int i = 0; i < ne; i++) {
        int a = E[3 * i], b = E[3 * i + 1], v = E[3 * i + 2];
        int k = pstart[a] + pc[a]++; padj[k] = b; pg[k] = v;          /* point -> line: x -> x*g */
        int k2 = lstart[b] + lc[b]++; ladj[k2] = a; lg[k2] = inv_[v];  /* line -> point: x -> x*g^-1 */
    }
    if (!cyc) {
        T = calloc((size_t)m * 8 * 256, sizeof(u64));
        for (int gg = 0; gg < m; gg++) for (int b = 0; b < 8; b++) for (int v = 0; v < 256; v++) {
            u64 r = 0;
            for (int bit = 0; bit < 8; bit++) if (v >> bit & 1) { int x = b * 8 + bit; if (x < m) r |= 1ULL << tab[x * m + gg]; }
            T[((size_t)gg * 8 + b) * 256 + v] = r;
        }
    }
    fprintf(stderr, "base: %d points, %d lines, %d edges, group order %d (%s); degrees points %d..%d lines %d..%d; lift %lld vertices\n",
            NP, NL, ne, m, cyc ? "cyclic" : "table", mindp, maxdp, mindl, maxdl, (long long)(NP + NL) * m);
    long long total = 0; int worst = 0, worstsrc = -1, nsrc = 0, badsrc = 0;
    #pragma omp parallel
    {
        u64 *rp = malloc(sizeof(u64) * NP), *rl = malloc(sizeof(u64) * NL);
        u64 *fp = malloc(sizeof(u64) * NP), *fl = malloc(sizeof(u64) * NL);
        #pragma omp for schedule(dynamic, 16) reduction(+:total,nsrc,badsrc)
        for (int s = 0; s < NP; s += step) {
            memset(rp, 0, sizeof(u64) * NP); memset(rl, 0, sizeof(u64) * NL);
            memset(fp, 0, sizeof(u64) * NP); memset(fl, 0, sizeof(u64) * NL);
            rp[s] = fp[s] = 1;   /* identity = element 0 = bit 0 */
            for (int t = 1; t <= maxlen; t++) {
                if (t & 1) { /* points -> lines */
                    for (int y = 0; y < NL; y++) {
                        u64 acc = 0;
                        for (int k = lstart[y]; k < lstart[y + 1]; k++) { u64 x = fp[ladj[k]]; if (x) acc |= act(x, inv_[lg[k]]); }
                        acc &= ~rl[y]; fl[y] = acc; rl[y] |= acc;
                    }
                } else {
                    for (int x0 = 0; x0 < NP; x0++) {
                        u64 acc = 0;
                        for (int k = pstart[x0]; k < pstart[x0 + 1]; k++) { u64 x = fl[padj[k]]; if (x) acc |= act(x, inv_[pg[k]]); }
                        acc &= ~rp[x0]; fp[x0] = acc; rp[x0] |= acc;
                    }
                }
            }
            long long unc = 0;
            for (int y = 0; y < NL; y++) unc += m - __builtin_popcountll(rl[y]);
            total += unc; nsrc++; if (unc) badsrc++;
            #pragma omp critical
            { if (unc > worst) { worst = (int)unc; worstsrc = s; } }
        }
        free(rp); free(rl); free(fp); free(fl);
    }
    printf("sources %d, bad sources %d, total uncovered (line,x) pairs %lld, worst source %d with %d\n", nsrc, badsrc, total, worstsrc, worst);
    printf("RESULT %s maxlen=%d lift_vertices=%lld maxdeg=%d\n", total == 0 ? "OK" : "FAIL", maxlen, (long long)(NP + NL) * m, maxdp > maxdl ? maxdp : maxdl);
    return total != 0;
}
