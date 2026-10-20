/*
 * an.c -- analyse a list of graph6 graphs (distinct, from tc): for each graph
 *   |Aut|, number of Moore edges E_M (edges uv whose distance layers from {u,v} have sizes 2(d-1)^i, i < g/2),
 *   local girth of every vertex, girth histogram, girth norm N1 = sum (g - g(v)).
 * Writes one TSV line per graph to OUT.tsv and prints aggregate tables:
 *   - classes by girth histogram (count of graphs)
 *   - for every |Aut| value, the number of graphs and sum of E_M  (for the mass-formula check)
 *
 * Usage: an DELTA G IN.g6 OUT.tsv
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include "nauty/nauty.h"

typedef uint64_t u64;
#define MAXV 40
static int n, delta, gg, half;
static u64 adj[MAXV];

static void parse(const char *s)
{
    n = s[0] - 63; int p = 1, bits = 0; unsigned cur = 0;
    for (int i = 0; i < n; i++) adj[i] = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        if (bits == 0) { cur = s[p++] - 63; bits = 6; }
        bits--;
        if ((cur >> bits) & 1) { adj[i] |= 1ULL << j; adj[j] |= 1ULL << i; }
    }
}

static u64 nbrs(u64 set) { u64 r = 0; while (set) { int v = __builtin_ctzll(set); set &= set - 1; r |= adj[v]; } return r; }

static int is_moore_edge(int a, int b)
{
    u64 seen = (1ULL << a) | (1ULL << b), front = seen;
    long expect = 2;
    for (int i = 0; i < half; i++) {
        if (__builtin_popcountll(front) != expect) return 0;
        u64 nxt = nbrs(front) & ~seen;
        seen |= nxt; front = nxt;
        expect *= (delta - 1);
    }
    return 1;
}

/* local girth of v: shortest cycle through v (BFS with branch labels) */
static int local_girth(int v)
{
    int d[MAXV], br[MAXV], q[MAXV], qh = 0, qt = 0;
    for (int i = 0; i < n; i++) d[i] = -1;
    d[v] = 0; br[v] = -1; q[qt++] = v;
    int best = 99, nb = 0;
    while (qh < qt) {
        int x = q[qh++];
        u64 a = adj[x];
        while (a) {
            int y = __builtin_ctzll(a); a &= a - 1;
            if (d[y] < 0) {
                d[y] = d[x] + 1; br[y] = (x == v) ? nb++ : br[x]; q[qt++] = y;
            } else if (x != v && y != v && br[y] != br[x]) {
                int c = d[x] + d[y] + 1;
                if (c < best) best = c;
            }
        }
    }
    return best;
}

typedef struct { char key[64]; long cnt; int n1; } Cls;
static Cls cls[4096]; static int ncls;

#define MAXAUT 4096
static long long autv[MAXAUT]; static long autcnt[MAXAUT]; static long autsumE[MAXAUT]; static int nauts;

int main(int argc, char **argv)
{
    if (argc < 5) { fprintf(stderr, "usage: an DELTA G IN.g6 OUT.tsv\n"); return 1; }
    delta = atoi(argv[1]); gg = atoi(argv[2]); half = gg / 2;
    FILE *fin = fopen(argv[3], "r"), *fout = fopen(argv[4], "w");
    if (!fin || !fout) { perror("open"); return 1; }
    static DEFAULTOPTIONS_GRAPH(options);
    statsblk stats;
    int lab[MAXV], ptn[MAXV], orbits[MAXV];
    graph g[MAXV * 2];
    char line[256];
    long total = 0, nonmoore = 0;
    while (fgets(line, sizeof line, fin)) {
        line[strcspn(line, "\r\n")] = 0;
        if (!line[0]) continue;
        parse(line);
        int m = SETWORDSNEEDED(n);
        EMPTYGRAPH(g, m, n);
        for (int i = 0; i < n; i++) { u64 a = adj[i]; while (a) { int j = __builtin_ctzll(a); a &= a - 1; if (j > i) ADDONEEDGE(g, i, j, m); } }
        options.getcanon = FALSE;
        densenauty(g, lab, ptn, orbits, &options, &stats, m, n, NULL);
        long long aut = llround(stats.grpsize1 * pow(10.0, stats.grpsize2));
        int em = 0;
        for (int i = 0; i < n; i++) { u64 a = adj[i]; while (a) { int j = __builtin_ctzll(a); a &= a - 1; if (j > i && is_moore_edge(i, j)) em++; } }
        if (em == 0) nonmoore++;
        int cnt[100]; memset(cnt, 0, sizeof cnt);
        for (int v = 0; v < n; v++) cnt[local_girth(v)]++;
        char key[64]; int p = 0;
        long n1 = 0;
        for (int gl = 99; gl >= 3; gl--) if (cnt[gl]) {
            if (gl == 99) p += sprintf(key + p, "inf^%d ", cnt[gl]); else p += sprintf(key + p, "%d^%d ", gl, cnt[gl]);
            n1 += (long)cnt[gl] * (gg - (gl == 99 ? gg : gl));
        }
        if (p) key[p-1] = 0;
        fprintf(fout, "%s\t%lld\t%d\t%ld\t%s\n", line, aut, em, n1, key);
        int c;
        for (c = 0; c < ncls; c++) if (!strcmp(cls[c].key, key)) break;
        if (c == ncls) { strcpy(cls[c].key, key); cls[c].cnt = 0; cls[c].n1 = (int)n1; ncls++; }
        cls[c].cnt++;
        int a2;
        for (a2 = 0; a2 < nauts; a2++) if (autv[a2] == aut) break;
        if (a2 == nauts) { autv[a2] = aut; nauts++; }
        autcnt[a2]++; autsumE[a2] += em;
        total++;
    }
    printf("total graphs %ld, graphs with no Moore edge %ld\n", total, nonmoore);
    printf("CLASSES (girth histogram, N1, count)\n");
    for (int c = 0; c < ncls; c++) printf("C\t%s\t%d\t%ld\n", cls[c].key, cls[c].n1, cls[c].cnt);
    printf("AUT (|Aut|, graphs, sum of E_M)\n");
    for (int a = 0; a < nauts; a++) printf("A\t%lld\t%ld\t%ld\n", autv[a], autcnt[a], autsumE[a]);
    return 0;
}
