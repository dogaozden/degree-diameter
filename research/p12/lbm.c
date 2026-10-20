/*
 * lbm.c -- filter for local bipartite Moore graphs LBM(delta, g).
 *
 * Reads graph6 lines on stdin (one graph per line, e.g. from genbg | labelg -q),
 * and for each graph that is a local bipartite Moore graph prints one line:
 *
 *   <graph6> <TAB> <girth histogram> <TAB> S1 <TAB> S2 <TAB> S3 <TAB> inf
 *
 * where the girth histogram lists local girths g(v) in decreasing order, e.g. "6^6 4^8",
 * S_p = sum over v of |g - g(v)|^p (so N1 = S1 and N2 = sqrt(S2)), and inf counts
 * vertices lying on no cycle. Summary counts go to stderr.
 *
 * LBM test (Definition 1 of Araujo-Pardo & Lopez, arXiv:2005.02427): the graph has
 * n = M = 2(1 + (delta-1) + ... + (delta-1)^(g/2-1)) vertices and some edge uv such that
 * for i = 0 .. g/2-1 the number of vertices at distance i from {u,v} is 2(delta-1)^i.
 *
 * Usage: genbg ... | labelg -q | ./lbm DELTA G
 * Graphs are assumed bipartite and delta-regular with n = M.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef uint64_t u64;
#define MAXN 64
#define INF_G 99

static int n;
static u64 adj[MAXN];
static int delta, gg, half;
static long expect[64];   /* expect[i] = 2 (delta-1)^i, i < half */

static int parse_g6(const char *s)
{
    int i, j, p, bitsleft;
    unsigned cur;
    if (s[0] < 63 || s[0] > 126) return 0;
    n = s[0] - 63;
    if (n > MAXN) return 0;
    memset(adj, 0, sizeof adj);
    p = 1;
    cur = (unsigned)(s[p] - 63);
    bitsleft = 6;
    for (j = 1; j < n; j++)
        for (i = 0; i < j; i++) {
            if (bitsleft == 0) {
                p++;
                if (s[p] == '\0') return 0;
                cur = (unsigned)(s[p] - 63);
                bitsleft = 6;
            }
            bitsleft--;
            if ((cur >> bitsleft) & 1u) {
                adj[i] |= 1ULL << j;
                adj[j] |= 1ULL << i;
            }
        }
    return 1;
}

static int popc(u64 x) { return __builtin_popcountll(x); }

/* Layer check from every edge until one passes. */
static int is_lbm(void)
{
    int u, v, i, ok;
    for (u = 0; u < n; u++)
        for (v = u + 1; v < n; v++) {
            u64 vis, fr, nb, nxt, f;
            if (!((adj[u] >> v) & 1ULL)) continue;
            vis = (1ULL << u) | (1ULL << v);
            fr = vis;
            ok = 1;
            for (i = 1; i < half && ok; i++) {
                nb = 0;
                for (f = fr; f; f &= f - 1) nb |= adj[__builtin_ctzll(f)];
                nxt = nb & ~vis;
                if (popc(nxt) != expect[i]) ok = 0;
                vis |= nxt;
                fr = nxt;
            }
            if (ok && popc(vis) == n) return 1;
        }
    return 0;
}

/* Local girth g(v): shortest cycle through v = min over neighbours a of
 * (dist from a to another neighbour b in G - v) + 2. INF_G if no cycle. */
static void local_girth(int *gv)
{
    int v, a, d, best;
    u64 nv, others, seen, fr, nb, f;
    for (v = 0; v < n; v++) {
        best = INF_G;
        nv = adj[v];
        for (f = nv; f; f &= f - 1) {
            a = __builtin_ctzll(f);
            others = nv & ~(1ULL << a);
            seen = (1ULL << a) | (1ULL << v);
            fr = 1ULL << a;
            d = 0;
            while (fr) {
                d++;
                if (d + 2 >= best) break;
                nb = 0;
                for (u64 g2 = fr; g2; g2 &= g2 - 1) nb |= adj[__builtin_ctzll(g2)];
                nb &= ~seen;
                if (nb & others) { best = d + 2; break; }
                seen |= nb;
                fr = nb;
            }
        }
        gv[v] = best;
    }
}

int main(int argc, char **argv)
{
    char *line = NULL;
    size_t cap = 0;
    ssize_t len;
    long total = 0, hits = 0, bad = 0;
    int gv[MAXN], g, i, k, cnt[INF_G + 1];
    long S1, S2, S3, ninf;

    if (argc < 3) {
        fprintf(stderr, "usage: %s DELTA G < graph6\n", argv[0]);
        return 2;
    }
    delta = atoi(argv[1]);
    gg = atoi(argv[2]);
    half = gg / 2;
    for (i = 0; i < half; i++) {
        long p = 1;
        int j;
        for (j = 0; j < i; j++) p *= (delta - 1);
        expect[i] = 2 * p;   /* layer i of a bipartite Moore tree: 2 (delta-1)^i */
    }

    while ((len = getline(&line, &cap, stdin)) != -1) {
        while (len > 0 && (line[len - 1] == '\n' || line[len - 1] == '\r')) line[--len] = '\0';
        if (len == 0) continue;
        total++;
        if (!parse_g6(line)) { bad++; continue; }
        if (!is_lbm()) continue;
        hits++;

        local_girth(gv);
        memset(cnt, 0, sizeof cnt);
        S1 = S2 = S3 = ninf = 0;
        for (k = 0; k < n; k++) {
            if (gv[k] == INF_G) { ninf++; continue; }
            cnt[gv[k]]++;
            long dv = labs((long)gg - gv[k]);
            S1 += dv;
            S2 += dv * dv;
            S3 += dv * dv * dv;
        }
        printf("%s\t", line);
        {
            int first = 1;
            for (g = INF_G - 1; g >= 0; g--)
                if (cnt[g]) {
                    printf(first ? "%d^%d" : " %d^%d", g, cnt[g]);
                    first = 0;
                }
        }
        printf("\t%ld\t%ld\t%ld\t%ld\n", S1, S2, S3, ninf);
    }
    fprintf(stderr, "lbm delta=%d g=%d: read %ld graphs, LBM hits %ld, unparsed %ld\n",
            delta, gg, total, hits, bad);
    free(line);
    return 0;
}
