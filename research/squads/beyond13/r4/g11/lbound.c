/* g11: exact upper bound n_max(B,D) = min over (s,v) of W_v(s,D) for Z_n lifts of a regular base B.
   W_v(s,D) = number of distinct net traversal vectors of walks s->v of length <= D.
   Net vectors are hashed: x -> sum_e x_e r_e mod 2^64 with random 64-bit r_e (collision probability ~ 1e-12 per run).
   Usage: lbound EDGEFILE D [seed]     (EDGEFILE: "V E" then E lines "a b") */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef struct { uint64_t h; uint32_t c; uint32_t L; } ent;
static int V, E, D, deg;
static size_t *cnt, *off, *start; static uint64_t *hb;
static int cmpu(const void *a, const void *b) { uint64_t x = *(const uint64_t*)a, y = *(const uint64_t*)b; return x < y ? -1 : x > y; }
static int *nb, *ne, *ns;      /* per vertex, deg slots */
static uint64_t *r;
static ent *buf; static size_t n, cap;

static int cmp(const void *a, const void *b) {
    const ent *x = a, *y = b;
    if (x->c != y->c) return x->c < y->c ? -1 : 1;
    if (x->h != y->h) return x->h < y->h ? -1 : 1;
    return 0;
}
static void dfs(int v, int pe, uint64_t h, int L) {
    if (n >= cap) { fprintf(stderr, "cap exceeded\n"); exit(2); }
    buf[n].h = h; buf[n].c = v; buf[n].L = L; n++;
    if (L == D) return;
    for (int j = 0; j < deg; j++) {
        int e = ne[v*deg+j];
        if (e == pe) continue;               /* no immediate reversal */
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
    if (argc < 3) return 1;
    FILE *f = fopen(argv[1], "r");
    D = atoi(argv[2]);
    uint64_t seed = argc > 3 ? strtoull(argv[3], 0, 10) : 1;
    if (fscanf(f, "%d %d", &V, &E) != 2) return 1;
    int *ea = malloc(sizeof(int)*E), *eb = malloc(sizeof(int)*E), *dg = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) {
        if (fscanf(f, "%d %d", &ea[e], &eb[e]) != 2) return 1;
        dg[ea[e]]++; dg[eb[e]]++;
    }
    fclose(f);
    deg = dg[0];
    for (int v = 0; v < V; v++) if (dg[v] != deg) { fprintf(stderr, "not regular\n"); return 1; }
    nb = malloc(sizeof(int)*V*deg); ne = malloc(sizeof(int)*V*deg); ns = malloc(sizeof(int)*V*deg);
    int *fill = calloc(V, sizeof(int));
    for (int e = 0; e < E; e++) {       /* orientation a->b is +1 */
        int a = ea[e], b = eb[e];
        nb[a*deg+fill[a]] = b; ne[a*deg+fill[a]] = e; ns[a*deg+fill[a]] = +1; fill[a]++;
        nb[b*deg+fill[b]] = a; ne[b*deg+fill[b]] = e; ns[b*deg+fill[b]] = -1; fill[b]++;
    }
    r = malloc(sizeof(uint64_t)*E);
    uint64_t st = seed;
    for (int e = 0; e < E; e++) r[e] = sm(&st);
    /* number of nonbacktracking walks of length <= D from one vertex (upper bound on buffer) */
    double tot = 1, p = 1;
    for (int L = 1; L <= D; L++) { tot += deg*p; p *= (deg-1); }   /* deg*(deg-1)^(L-1) walks of length L */
    cap = (size_t)tot + 16;
    buf = malloc(sizeof(ent) * cap);
    int *W = malloc(sizeof(int)*V);
    cnt = malloc(sizeof(size_t)*V); off = malloc(sizeof(size_t)*V); start = malloc(sizeof(size_t)*V);
    hb = malloc(sizeof(uint64_t)*cap);
    int gmin = 1 << 30, gs = -1, gv = -1;
    printf("# V=%d E=%d deg=%d D=%d seed=%llu walks_per_source=%.0f bytes=%.1fMB\n", V, E, deg, D,
           (unsigned long long)seed, tot, tot*sizeof(ent)/1e6);
    /* optional 4th argument: comma-separated source list (default: all sources) */
    int *srcs = malloc(sizeof(int)*V), ns_ = 0;
    if (argc > 4) { char *t = strdup(argv[4]); for (char *q = strtok(t, ","); q; q = strtok(NULL, ",")) srcs[ns_++] = atoi(q); }
    else for (int v = 0; v < V; v++) srcs[ns_++] = v;
    for (int si = 0; si < ns_; si++) {
        int s = srcs[si];
        n = 0;
        dfs(s, -1, 0, 0);
        /* bucket by endpoint (counting sort), then sort each bucket's hashes */
        for (int v = 0; v < V; v++) cnt[v] = 0;
        for (size_t i = 0; i < n; i++) cnt[buf[i].c]++;
        { size_t a2 = 0; for (int v = 0; v < V; v++) { start[v] = a2; off[v] = 0; a2 += cnt[v]; } }
        for (size_t i = 0; i < n; i++) hb[start[buf[i].c] + off[buf[i].c]++] = buf[i].h;
        for (int v = 0; v < V; v++) {
            qsort(hb + start[v], cnt[v], sizeof(uint64_t), cmpu);
            W[v] = 0;
            for (size_t i = 0; i < cnt[v]; i++)
                if (i == 0 || hb[start[v]+i] != hb[start[v]+i-1]) W[v]++;
        }
        int smin = 1 << 30, sv = -1, smax = 0; long long sum = 0;
        for (int v = 0; v < V; v++) {
            if (W[v] < smin) { smin = W[v]; sv = v; }
            if (W[v] > smax) smax = W[v];
            sum += W[v];
        }
        printf("src %d walks %zu minW %d at v=%d maxW %d sumW %lld\n", s, n, smin, sv, smax, sum);
        fflush(stdout);
        if (smin < gmin) { gmin = smin; gs = s; gv = sv; }
    }
    printf("RESULT D=%d nmax=%d argmin_s=%d argmin_v=%d\n", D, gmin, gs, gv);
    return 0;
}
