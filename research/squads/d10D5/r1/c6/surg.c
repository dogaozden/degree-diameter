/* surg: edge-surgery and vertex-insertion tester for bipartite graphs (card c6).
   bad(G) = number of ORDERED pairs (s,t) with dist(s,t) > D (unreached counts as bad). Bit-parallel BFS, 64 sources.
   Usage:
     surg degs  EDGES                     degree histogram, vertices of degree < d, colour classes
     surg scan  EDGES FROM TO STEP        delete each edge e = FROM, FROM+STEP, ... < TO; print bad(G - e)
     surg eval  EDGES MODS                apply MODS (lines: "N k" add k vertices; "- u v" delete edge;
                                          "+ u v" add edge) and report bad, max degree, bipartiteness
   Env: D (default 5), DMAX (default 10). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct { long n, m; long *U, *W; long *st, *adjv, *adje; } G;

static int D = 5, DMAX = 10;

static void load(const char *fn, G *g) {
    FILE *f = fopen(fn, "r");
    if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(2); }
    if (fscanf(f, "%ld", &g->n) != 1) { fprintf(stderr, "bad header\n"); exit(2); }
    long cap = 1 << 16; g->m = 0; g->U = malloc(cap * sizeof(long)); g->W = malloc(cap * sizeof(long));
    long a, b;
    while (fscanf(f, "%ld %ld", &a, &b) == 2) {
        if (g->m == cap) { cap *= 2; g->U = realloc(g->U, cap * sizeof(long)); g->W = realloc(g->W, cap * sizeof(long)); }
        g->U[g->m] = a; g->W[g->m] = b; g->m++;
    }
    fclose(f);
}

static void build(G *g) {
    long n = g->n, m = g->m;
    long *deg = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) { deg[g->U[i]]++; deg[g->W[i]]++; }
    g->st = calloc(n + 1, sizeof(long));
    for (long i = 0; i < n; i++) g->st[i + 1] = g->st[i] + deg[i];
    g->adjv = malloc((2 * m + 1) * sizeof(long)); g->adje = malloc((2 * m + 1) * sizeof(long));
    long *pos = calloc(n + 1, sizeof(long));
    for (long i = 0; i < m; i++) {
        long a = g->U[i], b = g->W[i];
        g->adjv[g->st[a] + pos[a]] = b; g->adje[g->st[a] + pos[a]] = i; pos[a]++;
        g->adjv[g->st[b] + pos[b]] = a; g->adje[g->st[b] + pos[b]] = i; pos[b]++;
    }
    free(deg); free(pos);
}

static void unbuild(G *g) { free(g->st); free(g->adjv); free(g->adje); }

/* ordered pairs at distance > D (bit-parallel BFS). rem[e] != 0 means edge e is deleted (rem may be NULL). */
static long bad_pairs(G *g, const char *rem, uint64_t *vis, uint64_t *fr, uint64_t *nx) {
    long n = g->n, bad = 0;
    for (long s0 = 0; s0 < n; s0 += 64) {
        int ns = (n - s0 < 64) ? (int)(n - s0) : 64;
        uint64_t full = ns == 64 ? ~0ULL : ((1ULL << ns) - 1);
        memset(vis, 0, n * sizeof(uint64_t)); memset(fr, 0, n * sizeof(uint64_t));
        for (int k = 0; k < ns; k++) { vis[s0 + k] |= 1ULL << k; fr[s0 + k] |= 1ULL << k; }
        for (int lev = 0; lev < D; lev++) {
            for (long v = 0; v < n; v++) {
                uint64_t x = 0;
                if (rem) { for (long i = g->st[v]; i < g->st[v + 1]; i++) if (!rem[g->adje[i]]) x |= fr[g->adjv[i]]; }
                else { for (long i = g->st[v]; i < g->st[v + 1]; i++) x |= fr[g->adjv[i]]; }
                x &= ~vis[v]; vis[v] |= x; nx[v] = x;
            }
            uint64_t *t = fr; fr = nx; nx = t;
        }
        for (long v = 0; v < n; v++) bad += __builtin_popcountll(~vis[v] & full);
    }
    return bad;
}

/* 2-colour by BFS from every uncoloured vertex; returns 1 if bipartite */
static int colour(G *g, int *col) {
    long n = g->n; long *q = malloc((n + 1) * sizeof(long)); int bip = 1;
    for (long i = 0; i < n; i++) col[i] = -1;
    for (long s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0; long h = 0, t = 0; q[t++] = s;
        while (h < t) { long x = q[h++];
            for (long i = g->st[x]; i < g->st[x + 1]; i++) { long y = g->adjv[i];
                if (col[y] < 0) { col[y] = 1 - col[x]; q[t++] = y; } else if (col[y] == col[x]) bip = 0; } }
    }
    free(q); return bip;
}

static void stats(G *g, int *ncomp_unused) {
    (void)ncomp_unused;
    long n = g->n; long hist[64] = {0}; long maxd = 0;
    for (long v = 0; v < n; v++) { long d = g->st[v + 1] - g->st[v]; if (d < 64) hist[d]++; if (d > maxd) maxd = d; }
    printf("n=%ld m=%ld maxdeg=%ld\n", n, g->m, maxd);
    for (int d = 0; d < 64; d++) if (hist[d]) printf("deg %d: %ld vertices\n", d, hist[d]);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: surg degs|scan|eval EDGES ...\n"); return 2; }
    if (getenv("D")) D = atoi(getenv("D"));
    if (getenv("DMAX")) DMAX = atoi(getenv("DMAX"));
    G g; load(argv[2], &g);
    const char *mode = argv[1];
    if (!strcmp(mode, "degs")) {
        build(&g); stats(&g, NULL);
        int *col = malloc(g.n * sizeof(int)); int bip = colour(&g, col);
        printf("bipartite=%d\n", bip);
        long cnt[2] = {0, 0}; for (long v = 0; v < g.n; v++) cnt[col[v]]++;
        printf("colour0=%ld colour1=%ld\n", cnt[0], cnt[1]);
        long spare = 0;
        for (long v = 0; v < g.n; v++) { long d = g.st[v + 1] - g.st[v];
            if (d < DMAX) { spare += DMAX - d; printf("LOW v=%ld deg=%ld colour=%d\n", v, d, col[v]); } }
        printf("total spare degree (to DMAX)=%ld\n", spare);
        return 0;
    }
    if (!strcmp(mode, "scan")) {
        long from = argc > 3 ? atol(argv[3]) : 0, to = argc > 4 ? atol(argv[4]) : g.m, step = argc > 5 ? atol(argv[5]) : 1;
        build(&g);
        uint64_t *vis = malloc(g.n * 8), *fr = malloc(g.n * 8), *nx = malloc(g.n * 8);
        char *rem = calloc(g.m + 1, 1);
        int *col = malloc(g.n * sizeof(int)); colour(&g, col);
        long zero = 0, tested = 0, minbad = -1;
        for (long e = from; e < to && e < g.m; e += step) {
            rem[e] = 1;
            long b = bad_pairs(&g, rem, vis, fr, nx);
            rem[e] = 0;
            tested++;
            if (b == 0) zero++;
            if (minbad < 0 || b < minbad) minbad = b;
            printf("e=%ld u=%ld v=%ld cu=%d cv=%d bad=%ld\n", e, g.U[e], g.W[e], col[g.U[e]], col[g.W[e]], b);
            fflush(stdout);
        }
        printf("SUMMARY tested=%ld zero_bad=%ld min_bad=%ld\n", tested, zero, minbad);
        return 0;
    }
    if (!strcmp(mode, "eval")) {
        FILE *mf = fopen(argv[3], "r");
        if (!mf) { fprintf(stderr, "cannot open mods\n"); return 2; }
        long newn = g.n; char op[8]; long a, b, k;
        long cap = g.m + 4096;
        long *U = malloc(cap * sizeof(long)), *W = malloc(cap * sizeof(long)); long m = 0;
        char *rem = calloc(g.m + 1, 1);
        long nadd = 0; long *AU = malloc(4096 * 8), *AW = malloc(4096 * 8);
        while (fscanf(mf, "%7s", op) == 1) {
            if (!strcmp(op, "N")) { if (fscanf(mf, "%ld", &k) == 1) newn += k; }
            else if (op[0] == '-') { if (fscanf(mf, "%ld %ld", &a, &b) != 2) break; int found = 0;
                for (long e = 0; e < g.m; e++) if (!rem[e] && ((g.U[e] == a && g.W[e] == b) || (g.U[e] == b && g.W[e] == a))) { rem[e] = 1; found = 1; break; }
                if (!found) { printf("RESULT INVALID no edge %ld %ld to delete\n", a, b); return 1; } }
            else if (op[0] == '+') { if (fscanf(mf, "%ld %ld", &a, &b) != 2) break; AU[nadd] = a; AW[nadd] = b; nadd++; }
        }
        fclose(mf);
        for (long e = 0; e < g.m; e++) if (!rem[e]) { U[m] = g.U[e]; W[m] = g.W[e]; m++; }
        for (long e = 0; e < nadd; e++) { U[m] = AU[e]; W[m] = AW[e]; m++; }
        G h; h.n = newn; h.m = m; h.U = U; h.W = W; build(&h);
        long maxd = 0; int degok = 1;
        for (long v = 0; v < h.n; v++) { long d = h.st[v + 1] - h.st[v]; if (d > maxd) maxd = d; if (d > DMAX) degok = 0; }
        int *col = malloc(h.n * sizeof(int)); int bip = colour(&h, col);
        uint64_t *vis = malloc(h.n * 8), *fr = malloc(h.n * 8), *nx = malloc(h.n * 8);
        long bad = bad_pairs(&h, NULL, vis, fr, nx);
        printf("n=%ld edges=%ld maxdeg=%ld degok=%d bipartite=%d bad_pairs=%ld\n", h.n, m, maxd, degok, bip, bad);
        if (bad == 0 && degok && bip) printf("RESULT VALID d=%ld D=%d n=%ld\n", DMAX, D, h.n);
        else printf("RESULT INVALID bad=%ld\n", bad);
        return 0;
    }
    fprintf(stderr, "unknown mode\n");
    return 2;
}
