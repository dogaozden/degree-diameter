/* orbdfs: exhaustive search for G-invariant cubic bipartite graphs of diameter <= D on a fixed G-set.
   deep-37 (Nov 1 2026). Generalises jsearch (Z_p, free) to any finite permutation group G, with non-free orbits
   (vertex stabilisers) and colour-reversing elements.

   Input (argv[1]): group file in the handsoff-37 format: "n order", then `order` lines, each a permutation of
   0..n-1 (all group elements), then one line with the colour (0/1) of every vertex. Colours must be compatible
   with G (every element maps colour classes to colour classes). argv[2] = D (odd). Env:
     PROBE=N     Knuth estimate of the search-tree size from N random descents (prints and exits)
     MAXSOL=k    stop after k solutions (default 10); SOLPREFIX=path writes path_<i>.edges
     ROOT=o      index (in the orbit list printed at start) of the root orbit (default: the orbit with the largest
                 stabiliser, ties -> smallest index). Every connected G-invariant graph is found from a root of any
                 fixed type, because untouched orbits of one type are interchangeable.
     SHARD=i/m SHARDDEPTH=d   split the tree: at depth d keep only nodes with (counter % m) == i.

   Construction. The graph is a union of G-orbits of edges. Orbits of vertices are "discovered" in BFS order from
   the root orbit; the representative x of the earliest discovered orbit with a free half-edge is filled next. x's
   remaining half-edges get, in this order: (A) edge orbits G{x,y} with y in an orbit discovered before x's fill
   started, by increasing canonical id; then (B) openings of new orbits: target = a class representative y of the
   first untouched orbit of a type, by non-decreasing (type, class), each optionally followed by (C) further edge
   orbits into that same newly opened orbit, by increasing id. Classes: vertices of the new orbit O_j of the right
   colour modulo left multiplication by Stab(x) (same edge orbit) and the colour-preserving G-equivariant maps of
   O_j (g*y_j -> g*n*y_j, n in N_G(Stab(y_j))), which relabel an untouched orbit without changing anything else
   (the gauge). Two untouched orbits are of the same type iff a colour-preserving G-equivariant bijection maps one
   onto the other (identity elsewhere). Every connected G-invariant cubic graph is generated at least once
   (duplicates possible, misses not).
   Pruning (as jsearch): collisions(v) = #NB walks of even length <= D-1 from v minus #distinct endpoints, computed
   in the partial graph from every discovered orbit representative; it never decreases as edges are added, and a
   cubic graph has diameter <= D iff collisions(v) <= delta = (2^D - 1) - n/2 for every v (n/2 per side).
   Output: SOL lines and files; final line DONE nodes=... sols=... */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 512
#define MAXG 2048
static int n, ng, D, L, delta, half;
static short *P;            /* P[g*n+v] */
#define PERM(g, v) P[(size_t)(g) * n + (v)]
static int col[MAXN], rev_[MAXG], inv_[MAXG];
static int norb, orb[MAXN], rep[MAXN], orbsz[MAXN], gv[MAXN], typ[MAXN], ntyp;
static int stabsz[MAXN]; static int *stab[MAXN];
static int adj[MAXN][3], deg[MAXN];
static int disc[MAXN], ndisc, discorder[MAXN];
static int root;
static long long nodes = 0, nsol = 0, maxsol = 10;
static char *solprefix = NULL;
/* classes for opening: cls[i][j] list of y */
static int *clsl[MAXN][MAXN]; static int clsn[MAXN][MAXN];
static int probe = 0; static double probeest, probe_prod, probe_sum; static int shard_i = -1, shard_m = 1, sharddepth = 0; static long long shardctr = 0;

/* edge orbit computation */
static int estamp[MAXN][MAXN], ecur = 1;
static int ebuf[MAXN * 3][2];
static int edge_orbit(int x, int y, int *ne, int *id) { /* fills ebuf, returns 0 if invalid (degree overflow) */
    ecur++; int m = 0, best = 1 << 30; static int inc[MAXN]; static int incstamp[MAXN], ic = 1; ic++;
    for (int g = 0; g < ng; g++) {
        int a = PERM(g, x), b = PERM(g, y); if (a > b) { int t = a; a = b; b = t; }
        if (estamp[a][b] == ecur) continue;
        estamp[a][b] = ecur; ebuf[m][0] = a; ebuf[m][1] = b; m++;
        int key = a * n + b; if (key < best) best = key;
        if (incstamp[a] != ic) { incstamp[a] = ic; inc[a] = 0; }
        if (incstamp[b] != ic) { incstamp[b] = ic; inc[b] = 0; }
        if (deg[a] + ++inc[a] > 3) return 0;
        if (deg[b] + ++inc[b] > 3) return 0;
    }
    *ne = m; *id = best; return 1;
}
static int isadj(int a, int b) { for (int j = 0; j < deg[a]; j++) if (adj[a][j] == b) return 1; return 0; }
static void add_edges(int (*eb)[2], int m) { for (int i = 0; i < m; i++) { int a = eb[i][0], b = eb[i][1]; adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; } }
static void del_edges(int (*eb)[2], int m) { for (int i = m - 1; i >= 0; i--) { int a = eb[i][0], b = eb[i][1]; deg[a]--; deg[b]--; } }
/* note: del relies on LIFO order (edges removed in reverse order of addition) */

/* collisions from v */
static int wstamp[MAXN], wcur = 1, wcount, wdist;
static void walk(int v, int from, int len) {
    if ((len & 1) == 0) { wcount++; if (wstamp[v] == wcur) { if (wcount - wdist > delta) return; } else { wstamp[v] = wcur; wdist++; } }
    if (len == L) return;
    for (int j = 0; j < deg[v]; j++) { int w = adj[v][j]; if (w == from) continue; walk(w, v, len + 1); if (wcount - wdist > delta) return; }
}
static int coll(int v) { wcur++; wcount = 0; wdist = 0; walk(v, -1, 0); return wcount - wdist; }
/* note: NB walk = never reverses the edge just used; in a simple graph that is "next vertex != previous" */
static int prune_ok(void) {
    for (int k = 0; k < ndisc; k++) { int o = discorder[k]; if (coll(rep[o]) > delta) return 0; }
    return 1;
}

static void leaf(void) {
    nsol++;
    printf("SOL %lld:", nsol);
    for (int v = 0; v < n; v++) for (int j = 0; j < 3; j++) if (adj[v][j] > v) printf(" %d-%d", v, adj[v][j]);
    printf("\n"); fflush(stdout);
    if (solprefix) {
        char fn[1024]; snprintf(fn, sizeof fn, "%s_%lld.edges", solprefix, nsol);
        FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", n);
        for (int v = 0; v < n; v++) for (int j = 0; j < 3; j++) if (adj[v][j] > v) fprintf(f, "%d %d\n", v, adj[v][j]);
        fclose(f);
    }
}

/* option list at a node */
typedef struct { int kind, y, key, id, j; } Opt; /* kind 0 = A, 1 = open, 2 = extra */
static int stop = 0;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

/* fill state: x's orbit index fo, D0 = number of orbits discovered before the fill started (discorder prefix),
   phase (0: A allowed, 1: after an opening), lastA id, last open key, current extra orbit jx, last extra id */
static void search(int depth, int fo, int d0, int phase, int lastA, int lastkey, int jx, int lastC);

static void next_fill(int depth) {
    /* find earliest discovered orbit with free slot */
    for (int k = 0; k < ndisc; k++) { int o = discorder[k]; if (deg[rep[o]] < 3) { search(depth, o, ndisc, 0, -1, -1, -1, -1); return; } }
    if (ndisc == norb) { if (probe) { probeest += probe_prod; return; } leaf(); if (nsol >= maxsol) stop = 1; }
}

static void search(int depth, int fo, int d0, int phase, int lastA, int lastkey, int jx, int lastC) {
    if (stop) return;
    nodes++;
    if (probe) probe_sum += probe_prod;
    if (shard_i >= 0 && depth == sharddepth) { if ((shardctr++ % shard_m) != shard_i) return; }
    int x = rep[fo];
    if (deg[x] == 3) { next_fill(depth); return; }
    Opt *opt = malloc(sizeof(Opt) * (n * 4 + 16)); int no = 0;
    int cx = col[x];
    if (phase == 0) { /* A options */
        for (int k = 0; k < d0; k++) { int o = discorder[k];
            for (int y = 0; y < n; y++) if (orb[y] == o && col[y] != cx && deg[y] < 3 && !isadj(x, y)) {
                int ne, id; if (!edge_orbit(x, y, &ne, &id)) continue;
                if (id <= lastA) continue;
                /* dedupe same id within this list */
                int dup = 0; for (int t = 0; t < no; t++) if (opt[t].kind == 0 && opt[t].id == id) { dup = 1; break; }
                if (dup) continue;
                opt[no].kind = 0; opt[no].y = y; opt[no].id = id; opt[no].key = 0; opt[no].j = o; no++;
            } }
    }
    /* C options: extras into jx */
    if (jx >= 0) {
        for (int y = 0; y < n; y++) if (orb[y] == jx && col[y] != cx && deg[y] < 3 && !isadj(x, y)) {
            int ne, id; if (!edge_orbit(x, y, &ne, &id)) continue;
            if (id <= lastC) continue;
            int dup = 0; for (int t = 0; t < no; t++) if (opt[t].kind == 2 && opt[t].id == id) { dup = 1; break; }
            if (dup) continue;
            opt[no].kind = 2; opt[no].y = y; opt[no].id = id; opt[no].key = 0; opt[no].j = jx; no++;
        }
    }
    /* B options: openings */
    for (int t = 0; t < ntyp; t++) {
        int j = -1; for (int o = 0; o < norb; o++) if (!disc[o] && typ[o] == t) { j = o; break; }
        if (j < 0) continue;
        for (int c = 0; c < clsn[fo][j]; c++) {
            int key = t * 4096 + c; if (key < lastkey) continue;
            int y = clsl[fo][j][c]; int ne, id; if (!edge_orbit(x, y, &ne, &id)) continue;
            opt[no].kind = 1; opt[no].y = y; opt[no].id = id; opt[no].key = key; opt[no].j = j; no++;
        }
    }
    int lo = 0, hi = no;
    if (probe) { /* keep only children that pass the prune, pick one uniformly */
        int nv = 0;
        for (int t = 0; t < no; t++) { int ne, id; edge_orbit(x, opt[t].y, &ne, &id);
            int nd = 0; if (opt[t].kind == 1) { disc[opt[t].j] = 1; discorder[ndisc++] = opt[t].j; nd = 1; }
            int (*eb)[2] = malloc(sizeof(int) * 2 * ne); memcpy(eb, ebuf, sizeof(int) * 2 * ne);
            add_edges(eb, ne); int ok = prune_ok(); del_edges(eb, ne); free(eb);
            if (nd) { disc[opt[t].j] = 0; ndisc--; }
            if (ok) opt[nv++] = opt[t]; }
        no = nv; if (no == 0) { free(opt); return; }
        probe_prod *= no; lo = (int)(xr() % no); hi = lo + 1; }
    for (int t = lo; t < hi && !stop; t++) {
        Opt o = opt[t]; int ne, id;
        edge_orbit(x, o.y, &ne, &id);
        int (*eb)[2] = malloc(sizeof(int) * 2 * ne); memcpy(eb, ebuf, sizeof(int) * 2 * ne);
        int newdisc = 0;
        if (o.kind == 1) { disc[o.j] = 1; discorder[ndisc++] = o.j; newdisc = 1; }
        add_edges(eb, ne);
        if (prune_ok()) {
            if (o.kind == 0) search(depth + 1, fo, d0, 0, id, -1, -1, -1);
            else if (o.kind == 1) search(depth + 1, fo, d0, 1, lastA, o.key, o.j, -1);
            else search(depth + 1, fo, d0, 1, lastA, lastkey, jx, id);
        }
        del_edges(eb, ne);
        if (newdisc) { disc[o.j] = 0; ndisc--; }
        free(eb);
    }
    free(opt);
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: orbdfs GROUPFILE D\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 2; }
    if (fscanf(f, "%d %d", &n, &ng) != 2) return 2;
    D = atoi(argv[2]); L = D - 1; half = n / 2; delta = (1 << D) - 1 - half;
    P = malloc(sizeof(short) * (size_t)n * ng);
    for (int g = 0; g < ng; g++) for (int v = 0; v < n; v++) { int t; if (fscanf(f, "%d", &t) != 1) return 3; PERM(g, v) = t; }
    for (int v = 0; v < n; v++) if (fscanf(f, "%d", &col[v]) != 1) return 4;
    fclose(f);
    if (getenv("MAXSOL")) maxsol = atoll(getenv("MAXSOL"));
    solprefix = getenv("SOLPREFIX");
    if (getenv("PROBE")) probe = atoi(getenv("PROBE"));
    if (getenv("SHARD")) { sscanf(getenv("SHARD"), "%d/%d", &shard_i, &shard_m); sharddepth = getenv("SHARDDEPTH") ? atoi(getenv("SHARDDEPTH")) : 6; }
    if (getenv("SEED")) rng ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL;
    /* identity, colour behaviour, inverses */
    int idg = -1;
    for (int g = 0; g < ng; g++) {
        int isid = 1; for (int v = 0; v < n; v++) if (PERM(g, v) != v) { isid = 0; break; }
        if (isid) idg = g;
        rev_[g] = col[PERM(g, 0)] != col[0];
        for (int v = 0; v < n; v++) if ((col[PERM(g, v)] != col[v]) != rev_[g]) { fprintf(stderr, "colour not preserved/reversed by element %d\n", g); return 5; }
    }
    if (idg < 0) { fprintf(stderr, "no identity\n"); return 6; }
    /* orbits */
    for (int v = 0; v < n; v++) orb[v] = -1;
    norb = 0;
    for (int v = 0; v < n; v++) if (orb[v] < 0) {
        int o = norb++; rep[o] = v; orbsz[o] = 0;
        for (int g = 0; g < ng; g++) { int w = PERM(g, v); if (orb[w] < 0) { orb[w] = o; gv[w] = g; orbsz[o]++; } }
    }
    for (int o = 0; o < norb; o++) { int x = rep[o]; stab[o] = malloc(sizeof(int) * ng); stabsz[o] = 0;
        for (int g = 0; g < ng; g++) if (PERM(g, x) == x) stab[o][stabsz[o]++] = g; }
    /* inverses */
    for (int g = 0; g < ng; g++) { inv_[g] = -1; }
    /* compose helper: find element h = g1*g2 by matching action on a base... use full perm compare (small groups) */
    /* types: orbits o, p same type iff exists y in O_p with Stab(y) == Stab(rep_o) (as sets) and col[y] == col[rep_o] */
    for (int o = 0; o < norb; o++) typ[o] = -1;
    ntyp = 0;
    char *instab = malloc(ng);
    for (int o = 0; o < norb; o++) {
        if (typ[o] >= 0) continue;
        typ[o] = ntyp;
        memset(instab, 0, ng); for (int s = 0; s < stabsz[o]; s++) instab[stab[o][s]] = 1;
        for (int p = o + 1; p < norb; p++) if (typ[p] < 0 && orbsz[p] == orbsz[o]) {
            for (int y = 0; y < n; y++) if (orb[y] == p && col[y] == col[rep[o]]) {
                int cnt = 0, ok = 1;
                for (int g = 0; g < ng; g++) if (PERM(g, y) == y) { cnt++; if (!instab[g]) { ok = 0; break; } }
                if (ok && cnt == stabsz[o]) { typ[p] = ntyp; break; }
            }
        }
        ntyp++;
    }
    /* centraliser maps on each orbit j: for n_ in G normalising Stab(rep_j), rev 0: y = g*y_j -> g*n_*y_j.
       g*n_*y_j = PERM(g, PERM(n_, y_j)). Classes for opening from orbit i into orbit j: candidates y in O_j with
       col != col(rep_i), modulo left Stab(rep_i) and right centraliser maps. Union-find. */
    int *uf = malloc(sizeof(int) * n);
    for (int j = 0; j < norb; j++) {
        int yj = rep[j];
        /* normaliser elements of Stab(yj): n_ with n_ Stab n_^-1 = Stab  <=> n_*yj has the same stabiliser set */
        memset(instab, 0, ng); for (int s = 0; s < stabsz[j]; s++) instab[stab[j][s]] = 1;
        int *nl = malloc(sizeof(int) * ng); int nn = 0;
        for (int g = 0; g < ng; g++) { if (rev_[g]) continue; int z = PERM(g, yj); int cnt = 0, ok = 1;
            for (int h = 0; h < ng; h++) if (PERM(h, z) == z) { cnt++; if (!instab[h]) { ok = 0; break; } }
            if (ok && cnt == stabsz[j]) nl[nn++] = g; }
        for (int i = 0; i < norb; i++) {
            int x = rep[i];
            for (int v = 0; v < n; v++) uf[v] = v;
            #define FIND(a) ({ int _a = (a); while (uf[_a] != _a) { uf[_a] = uf[uf[_a]]; _a = uf[_a]; } _a; })
            for (int y = 0; y < n; y++) if (orb[y] == j) {
                int g = gv[y];
                for (int t = 0; t < nn; t++) { int y2 = PERM(g, PERM(nl[t], yj)); int a = FIND(y), b = FIND(y2); if (a != b) uf[a] = b; }
                for (int s = 0; s < stabsz[i]; s++) { int y2 = PERM(stab[i][s], y); int a = FIND(y), b = FIND(y2); if (a != b) uf[a] = b; }
            }
            clsl[i][j] = malloc(sizeof(int) * orbsz[j]); clsn[i][j] = 0;
            /* class representative: smallest member with the right colour; a class may contain both colours only
               if a colour-reversing... (centraliser maps are colour preserving, left stab too) -> classes monochromatic */
            for (int y = 0; y < n; y++) if (orb[y] == j && col[y] != col[x]) {
                int r = FIND(y), first = 1;
                for (int z = 0; z < y; z++) if (orb[z] == j && col[z] != col[x] && FIND(z) == r) { first = 0; break; }
                if (first) clsl[i][j][clsn[i][j]++] = y;
            }
        }
        free(nl);
    }
    /* root */
    root = -1;
    if (getenv("ROOT")) root = atoi(getenv("ROOT"));
    else { for (int o = 0; o < norb; o++) if (root < 0 || stabsz[o] > stabsz[root]) root = o; }
    fprintf(stderr, "n=%d |G|=%d D=%d delta=%d orbits=%d types=%d root=%d\n", n, ng, D, delta, norb, ntyp, root);
    for (int o = 0; o < norb; o++) {
        int na = 0; for (int y = 0; y < n; y++) if (orb[y] == o && col[y] == 0) na++;
        fprintf(stderr, "  orbit %d: rep %d size %d (A %d, B %d) stab %d type %d\n", o, rep[o], orbsz[o], na, orbsz[o] - na, stabsz[o], typ[o]);
    }
    memset(disc, 0, sizeof disc); ndisc = 0;
    disc[root] = 1; discorder[ndisc++] = root;
    clock_t t0 = clock();
    if (probe) {
        double tot = 0, tot2 = 0, totl = 0;
        for (int r = 0; r < probe; r++) { probe_prod = 1; probe_sum = 0; probeest = 0;
            search(0, root, 1, 0, -1, -1, -1, -1);
            tot += probe_sum; tot2 += probe_sum * probe_sum; totl += probeest; }
        double mean = tot / probe, sd = sqrt(fmax(0, tot2 / probe - mean * mean));
        printf("PROBE runs=%d nodes_est=%.3e (sd %.2e, se %.2e) leaves_est=%.3e time=%.1fs\n", probe, mean, sd, sd / sqrt(probe), totl / probe, (double)(clock() - t0) / CLOCKS_PER_SEC);
        return 0;
    }
    search(0, root, 1, 0, -1, -1, -1, -1);
    printf("DONE nodes=%lld sols=%lld time=%.1fs%s\n", nodes, nsol, (double)(clock() - t0) / CLOCKS_PER_SEC, stop ? " (stopped at MAXSOL)" : "");
    return 0;
}
