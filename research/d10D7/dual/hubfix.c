/* hubfix.c: repair a bipartite hub graph (H line-side ~ H point-side, degrees kept) by random 2-switches until every
   same-side pair is within hub-graph distance LIM (default 6). Twins (hubs 2k, 2k+1 of one freed point, which share
   all level neighbours) are exempt when TWINS=1.  Usage: hubfix IN OUT [lim] [seed] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int H, m, *ej, *ek, lim = 6, twins = 0;
static int *st, *adj, *dd, *qq;
static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static void build(void) {
    int *deg = calloc(2 * H, sizeof(int)); for (int e = 0; e < m; e++) { deg[ej[e]]++; deg[H + ek[e]]++; }
    st[0] = 0; for (int v = 0; v < 2 * H; v++) st[v + 1] = st[v] + deg[v];
    int *pos = calloc(2 * H, sizeof(int));
    for (int e = 0; e < m; e++) { int a = ej[e], b = H + ek[e]; adj[st[a] + pos[a]++] = b; adj[st[b] + pos[b]++] = a; }
    free(deg); free(pos);
}
static void bfs(int s, int *d) {
    for (int v = 0; v < 2 * H; v++) d[v] = -1; int h = 0, t = 0; d[s] = 0; qq[t++] = s;
    while (h < t) { int v = qq[h++]; for (int i = st[v]; i < st[v + 1]; i++) { int w = adj[i]; if (d[w] < 0) { d[w] = d[v] + 1; qq[t++] = w; } } }
}
static long count_bad(int *ba, int *bb, int cap) {
    long bad = 0; int nb = 0;
    for (int s = 0; s < 2 * H; s++) { bfs(s, dd); int lo = s < H ? 0 : H;
        for (int v = lo; v < lo + H; v++) { if (v <= s) continue; if (twins && (v - lo) / 2 == (s - lo) / 2) continue;
            if (dd[v] < 0 || dd[v] > lim) { bad++; if (nb < cap) { ba[nb] = s; bb[nb] = v; nb++; } } } }
    return bad;
}
int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &H, &m) != 2) return 1;
    lim = argc > 3 ? atoi(argv[3]) : 6; rs ^= (unsigned long long)(argc > 4 ? atoll(argv[4]) : 1) * 0x9E3779B97F4A7C15ULL;
    twins = getenv("TWINS") ? atoi(getenv("TWINS")) : 0;
    ej = malloc(sizeof(int) * m); ek = malloc(sizeof(int) * m);
    for (int e = 0; e < m; e++) if (fscanf(f, "%d %d", &ej[e], &ek[e]) != 2) return 1; fclose(f);
    st = malloc(sizeof(int) * (2 * H + 1)); adj = malloc(sizeof(int) * 2 * m); dd = malloc(sizeof(int) * 2 * H); qq = malloc(sizeof(int) * 2 * H);
    int *db = malloc(sizeof(int) * 2 * H), cap = 4096, *ba = malloc(sizeof(int) * cap), *bb = malloc(sizeof(int) * cap);
    build(); long bad = count_bad(ba, bb, cap);
    fprintf(stderr, "initial bad pairs %ld\n", bad);
    for (int it = 0; it < 20000 && bad > 0; it++) {
        int k = (int)(rnd() % (bad < cap ? bad : cap)), a = ba[k], b = bb[k];
        bfs(b, db);
        /* a side: if a is line-side (a < H), its neighbours are point-side; pick neighbour x of a, a point-side x2 close to b */
        int deg_a = st[a + 1] - st[a]; if (!deg_a) continue;
        int x = adj[st[a] + rnd() % deg_a], x2 = -1;
        for (int tr = 0; tr < 200; tr++) { int c = (a < H ? H : 0) + (int)(rnd() % H); if (db[c] >= 0 && db[c] <= lim - 1) { int dup = 0; for (int i = st[a]; i < st[a + 1]; i++) if (adj[i] == c) dup = 1; if (!dup) { x2 = c; break; } } }
        if (x2 < 0) continue;
        int deg2 = st[x2 + 1] - st[x2]; if (!deg2) continue;
        int c = adj[st[x2] + rnd() % deg2]; if (c == a) continue;
        int dup = 0; for (int i = st[c]; i < st[c + 1]; i++) if (adj[i] == x) dup = 1; if (dup) continue;
        /* find edge ids (a,x) and (c,x2) */
        int e1 = -1, e2 = -1;
        for (int e = 0; e < m; e++) {
            int L = ej[e], P = H + ek[e];
            if ((L == a && P == x) || (P == a && L == x)) e1 = e;
            if ((L == c && P == x2) || (P == c && L == x2)) e2 = e;
        }
        if (e1 < 0 || e2 < 0) continue;
        int s1j = ej[e1], s1k = ek[e1], s2j = ej[e2], s2k = ek[e2];
        if (a < H) { ej[e1] = a; ek[e1] = x2 - H; ej[e2] = c; ek[e2] = x - H; } else { ej[e1] = x2; ek[e1] = a - H; ej[e2] = x; ek[e2] = c - H; }
        build(); long nb = count_bad(ba, bb, cap);
        if (nb <= bad) { bad = nb; fprintf(stderr, "it %d: bad %ld\n", it, bad); }
        else { ej[e1] = s1j; ek[e1] = s1k; ej[e2] = s2j; ek[e2] = s2k; build(); count_bad(ba, bb, cap); }
    }
    FILE *o = fopen(argv[2], "w"); fprintf(o, "%d %d\n", H, m); for (int e = 0; e < m; e++) fprintf(o, "%d %d\n", ej[e], ek[e]); fclose(o);
    printf("final bad pairs %ld\n", bad);
    return bad ? 1 : 0;
}
