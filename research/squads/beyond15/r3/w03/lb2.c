/* w03: lbound (r4/g11, Z^E net-vector counting) extended: per source s, prints
   minW = min_v W_v(s,D) (the lift bound for that source), total walks T, avg ratio sumW/T
   (distinct net vectors / walks, averaged over endpoints) and min_v W_v/C_v (C_v = walks s->v).
   Usage: lb2 EDGEFILE D seed [src-list]   EDGEFILE: "V E" then E lines "a b" (cubic/regular) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef struct { uint64_t h; uint32_t c; uint32_t L; } ent;
static int V, E, D, deg;
static size_t *cnt, *start, *off; static uint64_t *hb;
static int *nb, *ne, *ns; static uint64_t *r;
static ent *buf; static size_t n, cap;
static int cmpu(const void *a, const void *b) { uint64_t x = *(const uint64_t*)a, y = *(const uint64_t*)b; return x < y ? -1 : x > y; }
static void dfs(int v, int pe, uint64_t h, int L) {
    if (n >= cap) { fprintf(stderr, "cap exceeded\n"); exit(2); }
    buf[n].h = h; buf[n].c = v; buf[n].L = L; n++;
    if (L == D) return;
    for (int j = 0; j < deg; j++) {
        int e = ne[v*deg+j];
        if (e == pe) continue;
        int w = nb[v*deg+j], sg = ns[v*deg+j];
        uint64_t hh = sg > 0 ? h + r[e] : h - r[e];
        dfs(w, e, hh, L+1);
    }
}
static uint64_t sm(uint64_t *s) {
    uint64_t z = (*s += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}
int main(int argc, char **argv) {
    if (argc < 4) return 1;
    FILE *f = fopen(argv[1], "r");
    D = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], 0, 10);
    if (fscanf(f, "%d %d", &V, &E) != 2) return 1;
    int *ea = malloc(sizeof(int)*E), *eb = malloc(sizeof(int)*E), *dg = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) { if (fscanf(f, "%d %d", &ea[e], &eb[e]) != 2) return 1; dg[ea[e]]++; dg[eb[e]]++; }
    fclose(f);
    deg = dg[0];
    for (int v = 0; v < V; v++) if (dg[v] != deg) { fprintf(stderr, "not regular\n"); return 1; }
    nb = malloc(sizeof(int)*V*deg); ne = malloc(sizeof(int)*V*deg); ns = malloc(sizeof(int)*V*deg);
    int *fill = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) {
        int a = ea[e], b = eb[e];
        nb[a*deg+fill[a]] = b; ne[a*deg+fill[a]] = e; ns[a*deg+fill[a]] = +1; fill[a]++;
        nb[b*deg+fill[b]] = a; ne[b*deg+fill[b]] = e; ns[b*deg+fill[b]] = -1; fill[b]++;
    }
    r = malloc(sizeof(uint64_t)*E);
    uint64_t st = seed;
    for (int e = 0; e < E; e++) r[e] = sm(&st);
    double tot = 1, p = 1;
    for (int L = 1; L <= D; L++) { tot += deg*p; p *= (deg-1); }
    cap = (size_t)tot + 16;
    buf = malloc(sizeof(ent) * cap);
    hb = malloc(sizeof(uint64_t)*cap);
    cnt = malloc(sizeof(size_t)*V); off = malloc(sizeof(size_t)*V); start = malloc(sizeof(size_t)*V);
    int *srcs = malloc(sizeof(int)*V), ns_ = 0;
    if (argc > 4) { char *t = strdup(argv[4]); for (char *q = strtok(t, ","); q; q = strtok(NULL, ",")) srcs[ns_++] = atoi(q); }
    else for (int v = 0; v < V; v++) srcs[ns_++] = v;
    printf("# V=%d E=%d deg=%d D=%d seed=%llu nbwalks_per_source=%.0f\n", V, E, deg, D, (unsigned long long)seed, tot);
    long long gmin = 1LL<<60; int gs=-1, gv=-1; double gratio_min = 1e9, gratio_avg_min = 1e9;
    for (int si = 0; si < ns_; si++) {
        int s = srcs[si];
        n = 0; dfs(s, -1, 0, 0);
        for (int v = 0; v < V; v++) cnt[v] = 0;
        for (size_t i = 0; i < n; i++) cnt[buf[i].c]++;
        { size_t a2 = 0; for (int v = 0; v < V; v++) { start[v] = a2; off[v] = 0; a2 += cnt[v]; } }
        for (size_t i = 0; i < n; i++) hb[start[buf[i].c] + off[buf[i].c]++] = buf[i].h;
        long long smin = 1LL<<60; int sv=-1; double sumW = 0, rmin = 1e9;
        for (int v = 0; v < V; v++) {
            qsort(hb + start[v], cnt[v], sizeof(uint64_t), cmpu);
            size_t w = 0;
            for (size_t i = 0; i < cnt[v]; i++) if (i == 0 || hb[start[v]+i] != hb[start[v]+i-1]) w++;
            sumW += w;
            if ((long long)w < smin) { smin = w; sv = v; }
            double rv = cnt[v] ? (double)w / cnt[v] : 1.0; if (rv < rmin) rmin = rv;
        }
        double avgratio = sumW / (double)n;
        printf("src %d walks %zu minW %lld at v=%d sumW %.0f avg_ratio %.6f min_ratio_v %.6f\n", s, n, smin, sv, sumW, avgratio, rmin);
        fflush(stdout);
        if (smin < gmin) { gmin = smin; gs = s; gv = sv; }
        if (rmin < gratio_min) gratio_min = rmin;
        if (avgratio < gratio_avg_min) gratio_avg_min = avgratio;
    }
    printf("RESULT D=%d nmax=%lld argmin_s=%d argmin_v=%d min_ratio_v=%.6f min_avg_ratio=%.6f\n", D, gmin, gs, gv, gratio_min, gratio_avg_min);
    return 0;
}
