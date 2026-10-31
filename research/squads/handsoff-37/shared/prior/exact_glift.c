/* glift: exhaustive voltage lifts over arbitrary finite groups (from gap_groups.g tables) of cubic bipartite base
   multigraphs (nauty multig -T format on stdin); keeps lifts of bipartite diameter <= D (D odd).
   Usage: glift GROUPFILE D [-maxsol N] < bases
   A cubic bipartite graph with a colour-preserving group H of automorphisms acting freely (semiregularly) is an
   H-lift of its quotient: vertex (x, g), base edge e = (a, b) with voltage h gives (a, g) ~ (b, g*h); H acts by left
   multiplication. Voltages are the identity on a BFS spanning tree (gauge); the other k+1 edges are free; the first
   non-identity voltage (in search order) is an Aut(H)-orbit representative (all voltages may be moved by one
   automorphism of H). Diameter test as in zplift: from every base vertex u the NB walks of even length <= D-1 must
   reach every (v, g), v on u's side, i.e. collisions(u) <= delta = (2^D - 1) - k|H|. A walk's voltage is the product
   of its cotree letters (tree edges are the identity), so walks with the same freely reduced word always collide
   (counted up front); a walk is evaluated as soon as all its letters are assigned. Pruning as in zplift.
   Output: per (base, group) "RES base id N k nodes sols [skip]" and "SOL base id volt ..." lines. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXV 48
#define MAXE 80
#define MAXC 40
#define MAXEV 60000
#define MAXG 128

static int D; static long maxsol = 1000;
static int nv, ne, ea[MAXE], eb[MAXE], side_[MAXV];
static int dn[MAXV], de[MAXV][3], dto[MAXV][3], dsg[MAXV][3];
static int cotidx[MAXE], ncot;
/* walks as words: letters = cotree index*2 + (sign<0) */
typedef struct { int u, v, opp, len; signed char w[8]; } Walk;
static Walk *W; static int nw;
static signed char cur[8]; static int curlen;

static void push_letter(int c, int s) { /* free reduction */
    int L = c * 2 + (s < 0);
    if (curlen > 0 && (cur[curlen - 1] ^ 1) == L) curlen--; else cur[curlen++] = L;
}
static void rec(int u, int x, int lastedge, int len, int Ls) {
    if (side_[u] == side_[x] && len % 2 == 0) {
        if (nw >= MAXEV) { fprintf(stderr, "too many walks\n"); exit(3); }
        W[nw].u = u; W[nw].v = x; W[nw].opp = 0; W[nw].len = curlen; memcpy(W[nw].w, cur, 8); nw++;
    }
    if (len == Ls) return;
    for (int j = 0; j < dn[x]; j++) {
        int e = de[x][j]; if (e == lastedge) continue;
        int ci = cotidx[e]; signed char save[8]; int savelen = curlen; memcpy(save, cur, 8);
        if (ci >= 0) push_letter(ci, dsg[x][j]);
        rec(u, dto[x][j], e, len + 1, Ls);
        memcpy(cur, save, 8); curlen = savelen;
    }
}

/* groups */
typedef struct { int N, id; char name[64]; int *mul; int inv[MAXG]; int nrep; int rep[MAXG]; } Grp;
static Grp *grp; static int ngrp;

/* search state */
static int order[MAXC], posof[MAXC];
static int evstart[MAXC + 3]; static int *evlist; static int *vid; static char *dup;
static int npair, pot[MAXV * MAXV], pot0[MAXV * MAXV];
static uint64_t bits[MAXV * MAXV][2];
static int coll[MAXV], coll0[MAXV], slack[MAXV];
static int x[MAXC]; static long nodes, nsol; static int baseid; static Grp *G;
static int ust[MAXEV * 2], usp;

static inline int evalw(int w) {
    int g = 0; /* identity */
    for (int i = 0; i < W[w].len; i++) { int L = W[w].w[i]; int h = x[L >> 1]; if (L & 1) h = G->inv[h]; g = G->mul[g * G->N + h]; }
    return g;
}
static int apply_level(int t) {
    for (int i = evstart[t]; i < evstart[t + 1]; i++) {
        int w = evlist[i]; int g = evalw(w); int pi = vid[w];
        uint64_t m = 1ULL << (g & 63); int wd = g >> 6;
        if (bits[pi][wd] & m) { int u = W[w].u; coll[u]++; pot[pi]--; ust[usp++] = -1 - w;
            if (coll[u] > slack[u] || pot[pi] < G->N) return 0; }
        else { bits[pi][wd] |= m; ust[usp++] = w; }
    }
    return 1;
}
static void undo_to(int mark) {
    while (usp > mark) { int r = ust[--usp];
        if (r >= 0) { int g = evalw(r); bits[vid[r]][g >> 6] &= ~(1ULL << (g & 63)); }
        else { int w = -1 - r; coll[W[w].u]--; pot[vid[w]]++; } }
}
static void dfs(int t, int anynz) {
    nodes++;
    if (t == ncot) { nsol++; if (nsol <= maxsol) { printf("SOL %d %d volt", baseid, G->id);
            for (int e = 0; e < ne; e++) printf(" %d", cotidx[e] >= 0 ? x[cotidx[e]] : 0); printf("\n"); } return; }
    int var = order[t];
    int cnt = anynz ? G->N : G->nrep; /* reps include the identity 0 */
    for (int i = 0; i < cnt; i++) {
        int val = anynz ? i : G->rep[i];
        x[var] = val; int mark = usp;
        if (apply_level(t + 1)) dfs(t + 1, anynz || val != 0);
        undo_to(mark);
    }
    x[var] = 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: glift GROUPFILE D [-maxsol N] < bases\n"); return 2; }
    D = atoi(argv[2]); for (int i = 3; i < argc; i++) if (!strcmp(argv[i], "-maxsol")) maxsol = atol(argv[++i]);
    if (D % 2 == 0) { fprintf(stderr, "D odd\n"); return 2; }
    int Ls = D - 1, Wtot = (1 << D) - 1;
    /* read groups */
    FILE *fg = fopen(argv[1], "r"); if (!fg) { perror("groups"); return 2; }
    grp = calloc(1024, sizeof(Grp)); ngrp = 0; char tag[8];
    while (fscanf(fg, "%7s", tag) == 1) {
        if (!strcmp(tag, "G")) { Grp *g = &grp[ngrp++]; if (fscanf(fg, "%d %d %63s", &g->N, &g->id, g->name) != 3) return 3;
            g->mul = malloc(sizeof(int) * g->N * g->N);
            for (int i = 0; i < g->N * g->N; i++) if (fscanf(fg, "%d", &g->mul[i]) != 1) return 3;
            for (int a = 0; a < g->N; a++) for (int b = 0; b < g->N; b++) if (g->mul[a * g->N + b] == 0) g->inv[a] = b; }
        else if (!strcmp(tag, "A")) { Grp *g = &grp[ngrp - 1]; if (fscanf(fg, "%d", &g->nrep) != 1) return 3;
            for (int i = 0; i < g->nrep; i++) if (fscanf(fg, "%d", &g->rep[i]) != 1) return 3; }
    }
    fclose(fg);
    W = malloc(sizeof(Walk) * MAXEV); evlist = malloc(sizeof(int) * MAXEV); vid = malloc(sizeof(int) * MAXEV);
    dup = malloc(MAXEV);
    char line[1 << 16]; baseid = -1;
    while (fgets(line, sizeof line, stdin)) {
        int nsimple, off; char *ptr = line;
        if (sscanf(ptr, "%d %d%n", &nv, &nsimple, &off) != 2) continue;
        baseid++; ptr += off; ne = 0;
        for (int i = 0; i < nsimple; i++) { int a, b, mu; if (sscanf(ptr, "%d %d %d%n", &a, &b, &mu, &off) != 3) return 2; ptr += off;
            for (int r = 0; r < mu; r++) { ea[ne] = a; eb[ne] = b; ne++; } }
        for (int i = 0; i < nv; i++) side_[i] = -1;
        int q[MAXV], h = 0, tq = 0; side_[0] = 0; q[tq++] = 0;
        while (h < tq) { int y = q[h++]; for (int e = 0; e < ne; e++) { int z = -1; if (ea[e] == y) z = eb[e]; else if (eb[e] == y) z = ea[e];
            if (z >= 0 && side_[z] < 0) { side_[z] = 1 - side_[y]; q[tq++] = z; } } }
        int bad = tq != nv;
        for (int e = 0; e < ne; e++) { if (side_[ea[e]] == side_[eb[e]]) bad = 1; if (side_[ea[e]] == 1) { int t2 = ea[e]; ea[e] = eb[e]; eb[e] = t2; } }
        for (int i = 0; i < nv; i++) dn[i] = 0;
        for (int e = 0; e < ne; e++) { int a = ea[e], b = eb[e];
            de[a][dn[a]] = e; dto[a][dn[a]] = b; dsg[a][dn[a]] = +1; dn[a]++;
            de[b][dn[b]] = e; dto[b][dn[b]] = a; dsg[b][dn[b]] = -1; dn[b]++; }
        for (int i = 0; i < nv; i++) if (dn[i] != 3) bad = 1;
        if (bad) { printf("RES %d skip=not-cubic\n", baseid); continue; }
        int k = nv / 2;
        int intree[MAXE] = {0}, seen[MAXV] = {0}; h = 0; tq = 0; seen[0] = 1; q[tq++] = 0;
        while (h < tq) { int y = q[h++]; for (int j = 0; j < dn[y]; j++) { int z = dto[y][j]; if (!seen[z]) { seen[z] = 1; intree[de[y][j]] = 1; q[tq++] = z; } } }
        ncot = 0; for (int e = 0; e < ne; e++) cotidx[e] = intree[e] ? -1 : ncot++;
        nw = 0; curlen = 0;
        for (int u = 0; u < nv; u++) rec(u, u, -1, 0, Ls);
        static int pidx[MAXV][MAXV]; npair = 0;
        for (int u = 0; u < nv; u++) for (int v = 0; v < nv; v++) pidx[u][v] = -1;
        memset(coll0, 0, sizeof coll0);
        for (int w = 0; w < nw; w++) { int u = W[w].u, v = W[w].v; if (pidx[u][v] < 0) { pidx[u][v] = npair; pot0[npair] = 0; npair++; } vid[w] = pidx[u][v]; }
        memset(dup, 0, nw);
        for (int w = 0; w < nw; w++) { if (dup[w]) continue;
            for (int w2 = w + 1; w2 < nw; w2++) if (!dup[w2] && vid[w2] == vid[w] && W[w2].len == W[w].len && !memcmp(W[w].w, W[w2].w, W[w].len)) { dup[w2] = 1; coll0[W[w].u]++; } }
        for (int w = 0; w < nw; w++) if (!dup[w]) pot0[vid[w]]++;
        /* variable order: greedy, most walks completed */
        int chosen[MAXC] = {0};
        for (int t = 0; t < ncot; t++) { int best = -1, bestcnt = -1;
            for (int c = 0; c < ncot; c++) if (!chosen[c]) { int cnt = 0;
                for (int w = 0; w < nw; w++) { if (dup[w]) continue; int ok = 1, uses = 0;
                    for (int i = 0; i < W[w].len; i++) { int c2 = W[w].w[i] >> 1; if (c2 == c) uses = 1; else if (!chosen[c2]) { ok = 0; break; } }
                    if (ok && uses) cnt++; }
                if (cnt > bestcnt) { bestcnt = cnt; best = c; } }
            chosen[best] = 1; order[t] = best; posof[best] = t; }
        int cntl[MAXC + 2] = {0}; static int lev[MAXEV];
        for (int w = 0; w < nw; w++) { if (dup[w]) { lev[w] = -1; continue; } int L = 0;
            for (int i = 0; i < W[w].len; i++) { int c = W[w].w[i] >> 1; if (posof[c] + 1 > L) L = posof[c] + 1; }
            lev[w] = L; cntl[L]++; }
        evstart[0] = 0; for (int t = 0; t <= ncot; t++) evstart[t + 1] = evstart[t] + cntl[t];
        int fill[MAXC + 2]; for (int t = 0; t <= ncot; t++) fill[t] = evstart[t];
        for (int w = 0; w < nw; w++) if (lev[w] >= 0) evlist[fill[lev[w]]++] = w;
        for (int gi = 0; gi < ngrp; gi++) {
            G = &grp[gi]; int N = G->N;
            int skip = 0; const char *why = "";
            for (int u = 0; u < nv && !skip; u++) for (int v = 0; v < nv; v++) if (side_[u] == side_[v] && (pidx[u][v] < 0 || pot0[pidx[u][v]] < N)) { skip = 1; why = "walkcount<N"; break; }
            for (int u = 0; u < nv; u++) { slack[u] = Wtot - k * N; if (!skip && coll0[u] > slack[u]) { skip = 1; why = "forced-collisions"; } }
            if (skip) { printf("RES %d %d N=%d k=%d skip=%s\n", baseid, G->id, N, k, why); continue; }
            memcpy(coll, coll0, sizeof coll); memcpy(pot, pot0, sizeof(int) * npair);
            memset(bits, 0, sizeof(bits[0]) * npair); memset(x, 0, sizeof x); usp = 0; nodes = 0; nsol = 0;
            int ok0 = apply_level(0);
            if (ok0) dfs(0, 0);
            printf("RES %d %d N=%d k=%d nodes=%ld sols=%ld%s\n", baseid, G->id, N, k, nodes, nsol, ok0 ? "" : " skip=level0");
            fflush(stdout);
        }
    }
    return 0;
}
