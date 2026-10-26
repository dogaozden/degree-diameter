/* liftx: exhaustive voltage lifts of a small bipartite base graph over every group in a table file.
   Usage: liftx BASE GROUPS D [id ...]
     BASE   : "k E" then E lines "u v" (u in 0..k/2-1, v in k/2..k-1; parallel edges allowed; k <= 64)
     GROUPS : file of blocks "G N id name" + N rows of the multiplication table (index 0 = identity), from gap_export.g
     D      : diameter bound
   Lift: vertex (u,g) = u*N+g; base edge e = (u,v) with voltage a gives (u,g) ~ (v, g*a). Left multiplication by the
   group is a semiregular automorphism group, so a multi-source BFS from the k vertices (u,0) gives the exact diameter.
   Voltages: identity on a BFS spanning tree, every value on the cotree edges (parallel edges get distinct values).
   Prints one line per group: best cost (number of (source, vertex) pairs at distance > D) and the number of solutions,
   and "SOL ..." lines for cost 0.
   Env AUT=groups/a<N>.txt restricts the first cotree voltage to Aut(G)-orbit representatives (gap_aut.g). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int k, E, eu[256], ev[256];
static int N, *mul, *inv;
static uint64_t *R, *R2;

static long cost_of(const int *volt, int D, uint64_t full) {
    int n = k * N;
    /* dart lists */
    static int dv[64][3], da[64][3], dn[64];
    memset(dn, 0, sizeof dn);
    for (int e = 0; e < E; e++) {
        int u = eu[e], v = ev[e], a = volt[e];
        dv[u][dn[u]] = v; da[u][dn[u]++] = a;
        dv[v][dn[v]] = u; da[v][dn[v]++] = inv[a];
    }
    memset(R, 0, n * 8);
    for (int u = 0; u < k; u++) R[u * N] = 1ULL << u;
    for (int t = 0; t < D; t++) {
        for (int u = 0; u < k; u++) {
            int d = dn[u];
            for (int g = 0; g < N; g++) {
                uint64_t acc = R[u * N + g];
                const int *row = mul + (long)g * N;
                for (int j = 0; j < d; j++) acc |= R[dv[u][j] * N + row[da[u][j]]];
                R2[u * N + g] = acc;
            }
        }
        uint64_t *tmp = R; R = R2; R2 = tmp;
    }
    long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~R[x] & full);
    return c;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: liftx BASE GROUPS D [id ...]\n"); return 2; }
    FILE *fb = fopen(argv[1], "r");
    if (!fb || fscanf(fb, "%d %d", &k, &E) != 2) { fprintf(stderr, "bad base\n"); return 2; }
    for (int e = 0; e < E; e++) if (fscanf(fb, "%d %d", &eu[e], &ev[e]) != 2) return 2;
    fclose(fb);
    int D = atoi(argv[3]);
    int nsel = argc - 4; int *sel = malloc(sizeof(int) * (nsel + 1));
    for (int i = 0; i < nsel; i++) sel[i] = atoi(argv[4 + i]);
    /* spanning tree by BFS from 0 */
    int intree[256] = {0}, seen[64] = {0}, q[64], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    while (h < t) { int x = q[h++]; for (int e = 0; e < E; e++) { int y = -1; if (eu[e] == x) y = ev[e]; else if (ev[e] == x) y = eu[e];
        if (y >= 0 && !seen[y]) { seen[y] = 1; intree[e] = 1; q[t++] = y; } } }
    if (t != k) { fprintf(stderr, "base disconnected\n"); return 2; }
    int cot[256], r = 0; for (int e = 0; e < E; e++) if (!intree[e]) cot[r++] = e;
    uint64_t full = (k == 64) ? ~0ULL : ((1ULL << k) - 1);
    FILE *fg = fopen(argv[2], "r"); char tag[8], name[256]; int gid;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * N * N); inv = malloc(sizeof(int) * N);
        for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        int want = nsel == 0; for (int i = 0; i < nsel; i++) if (sel[i] == gid) want = 1;
        if (!want) { free(mul); free(inv); continue; }
        for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv[a] = b;
        R = malloc(8L * k * N); R2 = malloc(8L * k * N);
        /* allowed values per cotree position; position 0 restricted to Aut(G)-orbit representatives if AUT is set */
        int *vals[256], cnt[256];
        for (int i = 0; i < r; i++) { vals[i] = malloc(sizeof(int) * N); cnt[i] = N; for (int a = 0; a < N; a++) vals[i][a] = a; }
        const char *ap = getenv("AUT");
        if (ap && r > 0) { FILE *fa = fopen(ap, "r"); char line[65536];
            while (fa && fgets(line, sizeof line, fa)) { int an, aid, off; if (sscanf(line, "A %d %d%n", &an, &aid, &off) != 2) continue;
                if (an != N || aid != gid) continue; char *p = line + off; int v, c = 0, o2;
                while (sscanf(p, "%d%n", &v, &o2) == 1) { vals[0][c++] = v; p += o2; } cnt[0] = c; }
            if (fa) fclose(fa); }
        int volt[256] = {0}, idx[256] = {0};
        long best = -1, nsol = 0, ntried = 0; int bestv[256] = {0};
        for (;;) {
            for (int i = 0; i < r; i++) volt[cot[i]] = vals[i][idx[i]];
            int ok = 1;
            for (int e = 0; e < E && ok; e++) for (int f = e + 1; f < E; f++)
                if (eu[e] == eu[f] && ev[e] == ev[f] && volt[e] == volt[f]) { ok = 0; break; }
            if (ok) {
                ntried++;
                long c = cost_of(volt, D, full);
                if (best < 0 || c < best) { best = c; memcpy(bestv, volt, sizeof volt); }
                if (c == 0) { nsol++; if (nsol <= 20) { printf("SOL N=%d id=%d %s volt", N, gid, name);
                    for (int e = 0; e < E; e++) printf(" %d", volt[e]); printf("\n"); } }
            }
            int i = 0; while (i < r && ++idx[i] == cnt[i]) { idx[i] = 0; i++; }
            if (i == r) break;
        }
        printf("GROUP N=%d id=%d %s n=%d tried=%ld best=%ld nsol=%ld\n", N, gid, name, k * N, ntried, best, nsol);
        if (getenv("PRINTBEST") && best > 0) { printf("BEST N=%d id=%d cost=%ld volt", N, gid, best); for (int e = 0; e < E; e++) printf(" %d", bestv[e]); printf("\n"); }
        fflush(stdout);
        for (int i = 0; i < r; i++) free(vals[i]);
        free(mul); free(inv); free(R); free(R2);
    }
    return 0;
}
