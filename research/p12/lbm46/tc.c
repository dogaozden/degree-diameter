/*
 * tc.c -- tree completion for local bipartite Moore graphs LBM(delta, g), g = 6 or 8.
 *
 * Every G in LBM(delta,g) contains a bipartite Moore tree hung from an edge uv. With B = delta-1 and
 * D = g/2-1, each side of the tree has levels 1..D below its root, B^l nodes at level l; the B^D leaves
 * of u's side (set X) and v's side (set Y) lie in opposite colour classes and need B more edges each, and
 * these extra edges can only join X to Y. So G = tree + H where H is a B-regular bipartite graph on X + Y.
 *
 * Method: H runs over all B-regular bipartite graphs on L+L vertices (L = B^D) up to isomorphism with the
 * two classes distinguished (genbg output, read from a file). For each H, X and Y are each "hung" under the
 * tree in every way that is distinct up to the tree's own symmetry (hierarchical partitions of the L leaves
 * into blocks of size B, then blocks into blocks of size B, ...). Every resulting graph is canonically
 * labelled with nauty; new canonical forms are written (graph6) and remembered in a hash table.
 *
 * Usage: tc DELTA G H.g6 RES MOD OUT.g6      (H number i is handled when i % MOD == RES)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "nauty/nauty.h"

typedef uint64_t u64;
#define MAXLOC 64

static int B, D, L, I, NS;        /* NS = number of non-root nodes per side = I + L */
static int nlev[8], off[8];       /* nodes per level, local id offset per level (level 1.. D) */

typedef struct { unsigned char par[MAXLOC]; } Struct;   /* par[l] = parent local id of local node l (1..NS) */
static Struct *structs; static long nstructs, capstructs;

/* ---- structure enumeration ---- */
static int cur_par[8][MAXLOC];    /* cur_par[lev][unit] = parent unit index at level lev-1 */

static void emit(void)
{
    Struct s; memset(&s, 0, sizeof s);
    for (int lev = 1; lev <= D; lev++)
        for (int j = 0; j < nlev[lev]; j++) {
            int id = off[lev] + j;
            int p = (lev == 1) ? 0 : off[lev-1] + cur_par[lev][j];
            s.par[id] = (unsigned char)p;
        }
    if (nstructs == capstructs) {
        capstructs = capstructs ? 2*capstructs : 1024;
        structs = realloc(structs, capstructs * sizeof(Struct));
    }
    structs[nstructs++] = s;
}

static void level_rec(int lev);
static void group_rec2(int lev, unsigned long long used, int ngroups);

/* combination recursion: pick members for the group of unit f */
static void pick_rec(int lev, unsigned long long used, int ngroups, int f, int cnt, int from)
{
    int U = nlev[lev];
    if (cnt == B) { group_rec2(lev, used, ngroups + 1); return; }
    for (int x = from; x < U; x++) {
        if (used >> x & 1) continue;
        cur_par[lev][x] = ngroups;
        pick_rec(lev, used | (1ULL << x), ngroups, f, cnt + 1, x + 1);
    }
}

static void group_rec2(int lev, unsigned long long used, int ngroups)
{
    int U = nlev[lev];
    int f = 0;
    while (f < U && (used >> f & 1)) f++;
    if (f == U) { level_rec(lev - 1); return; }
    cur_par[lev][f] = ngroups;
    pick_rec(lev, used | (1ULL << f), ngroups, f, 1, f + 1);
}

static void level_rec(int lev)
{
    if (lev == 1) {
        for (int j = 0; j < nlev[1]; j++) cur_par[1][j] = 0;
        emit();
        return;
    }
    group_rec2(lev, 0ULL, 0);
}

/* ---- graph6 ---- */
static int parse_g6(const char *s, int *n, unsigned char *adj /* n*n */)
{
    *n = s[0] - 63;
    int p = 1, bits = 0; unsigned cur = 0, k = 0;
    for (int j = 1; j < *n; j++) for (int i = 0; i < j; i++) {
        if (bits == 0) { cur = s[p++] - 63; bits = 6; }
        bits--;
        int b = (cur >> bits) & 1;
        adj[i * *n + j] = adj[j * *n + i] = (unsigned char)b;
    }
    (void)k;
    return 1;
}

static void write_g6(FILE *f, const graph *g, int m, int n)
{
    char buf[400]; int p = 0;
    buf[p++] = (char)(n + 63);
    int bits = 0; unsigned cur = 0;
    for (int j = 1; j < n; j++) for (int i = 0; i < j; i++) {
        cur = (cur << 1) | (ISELEMENT(GRAPHROW(g, i, m), j) ? 1 : 0);
        if (++bits == 6) { buf[p++] = (char)(cur + 63); bits = 0; cur = 0; }
    }
    if (bits) { cur <<= (6 - bits); buf[p++] = (char)(cur + 63); }
    buf[p++] = '\n';
    fwrite(buf, 1, p, f);
}

/* ---- hash set ---- */
static u64 *tab; static u64 tabmask; static long tabcount;
static void hash_graph(const graph *g, int len, u64 *h1, u64 *h2)
{
    u64 a = 0x9E3779B97F4A7C15ULL, b = 0xC2B2AE3D27D4EB4FULL;
    for (int i = 0; i < len; i++) {
        u64 w = (u64)g[i];
        a = (a ^ w) * 0x100000001B3ULL; a ^= a >> 29; a *= 0xBF58476D1CE4E5B9ULL;
        b = (b + w + 0x632BE59BD9B4E019ULL) * 0x94D049BB133111EBULL; b ^= b >> 31;
    }
    *h1 = a; *h2 = b ? b : 1;
}
/* returns 1 if newly inserted */
static int tab_insert(u64 h1, u64 h2)
{
    u64 i = h1 & tabmask;
    for (;;) {
        if (tab[2*i + 1] == 0) { tab[2*i] = h1; tab[2*i+1] = h2; tabcount++; return 1; }
        if (tab[2*i] == h1 && tab[2*i+1] == h2) return 0;
        i = (i + 1) & tabmask;
    }
}

int main(int argc, char **argv)
{
    if (argc < 7) { fprintf(stderr, "usage: tc DELTA G H.g6 RES MOD OUT.g6\n"); return 1; }
    int delta = atoi(argv[1]), gg = atoi(argv[2]);
    int res = atoi(argv[4]), mod = atoi(argv[5]);
    B = delta - 1; D = gg / 2 - 1;
    nlev[0] = 1; off[0] = 0;
    L = 1; I = 0;
    for (int l = 1; l <= D; l++) { nlev[l] = nlev[l-1] * B; }
    off[1] = 1; for (int l = 2; l <= D; l++) off[l] = off[l-1] + nlev[l-1];
    L = nlev[D]; I = off[D] - 1; NS = I + L;
    int n = 2 + 2 * NS;
    int m = SETWORDSNEEDED(n);
    if (L > 20 || NS >= MAXLOC) { fprintf(stderr, "too big\n"); return 1; }

    level_rec(D);
    fprintf(stderr, "B=%d D=%d L=%d I=%d n=%d structures=%ld\n", B, D, L, I, n, nstructs);

    tabmask = (1ULL << 24) - 1;
    tab = calloc(2 * (tabmask + 1), sizeof(u64));
    FILE *fin = fopen(argv[3], "r"), *fout = fopen(argv[6], "w");
    if (!fin || !fout) { perror("open"); return 1; }

    static DEFAULTOPTIONS_GRAPH(options);
    statsblk stats;
    options.getcanon = TRUE;
    int lab[MAXLOC], ptn[MAXLOC], orbits[MAXLOC];
    graph gbase[MAXLOC * 4], g[MAXLOC * 4], cg[MAXLOC * 4];
    char line[256];
    long hidx = -1, mine = 0, tried = 0;
    unsigned char hadj[64 * 64];
    while (fgets(line, sizeof line, fin)) {
        hidx++;
        if (hidx % mod != res) continue;
        int hn; memset(hadj, 0, sizeof hadj);
        parse_g6(line, &hn, hadj);
        if (hn != 2 * L) { fprintf(stderr, "H has %d vertices, expected %d\n", hn, 2*L); return 1; }
        mine++;
        /* base graph: root edge + H edges */
        EMPTYGRAPH(gbase, m, n);
        ADDONEEDGE(gbase, 0, 1, m);
        for (int i = 0; i < L; i++) for (int j = 0; j < L; j++)
            if (hadj[i * hn + (L + j)]) ADDONEEDGE(gbase, 2 + I + i, 2 + NS + I + j, m);
        for (long sx = 0; sx < nstructs; sx++) {
            for (long sy = 0; sy < nstructs; sy++) {
                memcpy(g, gbase, sizeof(graph) * m * n);
                for (int l = 1; l <= NS; l++) {
                    int p = structs[sx].par[l];
                    int a = (p == 0) ? 0 : 2 + (p - 1);
                    ADDONEEDGE(g, a, 2 + (l - 1), m);
                    p = structs[sy].par[l];
                    a = (p == 0) ? 1 : 2 + NS + (p - 1);
                    ADDONEEDGE(g, a, 2 + NS + (l - 1), m);
                }
                densenauty(g, lab, ptn, orbits, &options, &stats, m, n, cg);
                tried++;
                u64 h1, h2; hash_graph(cg, m * n, &h1, &h2);
                if (tab_insert(h1, h2)) {
                    write_g6(fout, cg, m, n);
                    if (tabcount * 2 > (long)tabmask) { fprintf(stderr, "table full\n"); return 2; }
                }
            }
        }
        fprintf(stderr, "H %ld done: tried %ld, distinct so far %ld\n", hidx, tried, tabcount);
        fflush(fout);
    }
    fprintf(stderr, "finished: %ld H graphs, tried %ld, distinct %ld\n", mine, tried, tabcount);
    fclose(fout);
    return 0;
}
