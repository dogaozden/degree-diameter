/* zplift: exhaustive Z_p voltage lifts of cubic bipartite base multigraphs; keeps lifts of bipartite diameter <= D.
   Usage: zplift p D [-brute] [-maxsol N]  < bases   (bases in nauty multig -T format: "nv ne {v1 v2 mult}")
   A cubic bipartite graph with a colour-preserving semiregular automorphism of order p is a Z_p-lift of its
   quotient (a cubic bipartite multigraph without loops, k+k vertices, n = 2kp).
   Lift: vertex (x, g), x base vertex, g in Z_p; base edge e = (a, b) (a on side 0) with voltage t gives
   (a, g) ~ (b, g + t). Voltages are 0 on a BFS spanning tree (gauge) and free on the k+1 cotree edges; the first
   nonzero cotree voltage (in search order) is 1 (all voltages may be multiplied by a unit of Z_p).
   Diameter test (exact): the lift has diameter <= D iff for every base vertex u, the non-backtracking (NB) walks
   from u of the right lengths reach every (v, g) with v on the required side. Same-side lengths: even <= Ls,
   Ls = D (D even) or D-1 (D odd). For D even also opposite-side: odd <= D-1. (For D odd opposite-side distances
   <= D follow from the same-side condition.) With W walks and k*p targets, coverage holds iff
   #collisions(u) = W - #distinct(endpoint, voltage) <= W - k*p. The search assigns cotree voltages one by one
   and prunes as soon as the walks already fully determined collide more than that, or some (u, v) can no longer
   be covered (fewer than p distinct walks left). -brute disables both prunings (validation).
   Output per base: "BASE i k=.. nodes=.. sols=.. [skip reason]" and "SOL i p volt e0 e1 .." lines, where the
   voltages are listed for the expanded edge list (multig order, multiplicities expanded). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAXV 48
#define MAXE 80
#define MAXC 40
#define MAXWALK 600
#define MAXEV 60000

static int p, D, brute = 0; static long maxsol = 1000000;
static int nv, ne, ea[MAXE], eb[MAXE], side_[MAXV];
static int dn[MAXV], de[MAXV][3], dto[MAXV][3], dsg[MAXV][3]; /* darts: edge id, other end, sign (+1 if a->b) */
static int cotidx[MAXE], ncot, cotedge[MAXC];

/* walks */
typedef struct { int u, v; signed char c[MAXC]; int lev; int opp; } Walk;
static Walk *W; static int nw;
static signed char cur[MAXC]; static int curv;

static void rec(int u, int x, int lastedge, int len, int Ls, int Lo) {
    int s = side_[u] == side_[x];
    if (len > 0 || 1) {
        if (s && (len % 2 == 0) && len <= Ls) {
            if (nw >= MAXEV) { fprintf(stderr, "too many walks\n"); exit(3); }
            W[nw].u = u; W[nw].v = x; memcpy(W[nw].c, cur, MAXC); W[nw].opp = 0; nw++;
        }
        if (!s && (len % 2 == 1) && len <= Lo) {
            if (nw >= MAXEV) { fprintf(stderr, "too many walks\n"); exit(3); }
            W[nw].u = u; W[nw].v = x; memcpy(W[nw].c, cur, MAXC); W[nw].opp = 1; nw++;
        }
    }
    int Lm = Ls > Lo ? Ls : Lo;
    if (len == Lm) return;
    for (int j = 0; j < dn[x]; j++) {
        int e = de[x][j]; if (e == lastedge) continue;
        int ci = cotidx[e];
        if (ci >= 0) cur[ci] += dsg[x][j];
        rec(u, dto[x][j], e, len + 1, Ls, Lo);
        if (ci >= 0) cur[ci] -= dsg[x][j];
    }
}

/* search state */
static int order[MAXC], posof[MAXC];
static int *evstart; static int *evlist; /* events grouped by level */
static int *vid;      /* walk -> (u,v) pair index */
static int npair; static int pairu[MAXV * MAXV], pairv[MAXV * MAXV], pot[MAXV * MAXV];
static uint64_t bits[MAXV * MAXV][2]; /* p <= 128 */
static int coll[MAXV][2], slack[MAXV][2];
static int x[MAXC];
static long nodes, nsol;
static int baseid;
/* undo stack */
static int ust[MAXEV * 2], usp;

static int apply_level(int t) {
    /* process events at level t; return 0 if pruned. Pushes undo records. */
    for (int i = evstart[t]; i < evstart[t + 1]; i++) {
        int w = evlist[i]; long g = 0;
        for (int c = 0; c < ncot; c++) if (W[w].c[c]) g += (long)W[w].c[c] * x[c];
        g %= p; if (g < 0) g += p;
        int pi = vid[w];
        uint64_t m = 1ULL << (g & 63); int wd = (int)(g >> 6);
        if (bits[pi][wd] & m) {
            int u = W[w].u, o = W[w].opp;
            coll[u][o]++; pot[pi]--;
            ust[usp++] = -1 - w; /* collision record */
            if (!brute && (coll[u][o] > slack[u][o] || pot[pi] < p)) return 0;
        } else { bits[pi][wd] |= m; ust[usp++] = w; }
    }
    return 1;
}
static void undo_to(int mark) {
    while (usp > mark) {
        int r = ust[--usp];
        if (r >= 0) { int w = r; long g = 0; for (int c = 0; c < ncot; c++) if (W[w].c[c]) g += (long)W[w].c[c] * x[c];
            g %= p; if (g < 0) g += p; bits[vid[w]][g >> 6] &= ~(1ULL << (g & 63)); }
        else { int w = -1 - r; coll[W[w].u][W[w].opp]--; pot[vid[w]]++; }
    }
}
static void report(void) {
    nsol++;
    if (nsol <= maxsol) {
        printf("SOL %d %d volt", baseid, p);
        for (int e = 0; e < ne; e++) { int ci = cotidx[e]; printf(" %d", ci >= 0 ? x[ci] : 0); }
        printf("\n");
    }
}
static int leafcheck(void) {
    for (int u = 0; u < nv; u++) for (int o = 0; o < 2; o++) if (coll[u][o] > slack[u][o]) return 0;
    for (int i = 0; i < npair; i++) if (pot[i] < p) return 0;
    return 1;
}
static void dfs(int t, int anynz) {
    nodes++;
    if (t == ncot) { if (leafcheck()) report(); return; }
    int var = order[t];
    int hi = anynz ? p : 2;
    for (int val = 0; val < hi; val++) {
        x[var] = val;
        int mark = usp;
        if (apply_level(t + 1)) dfs(t + 1, anynz || val);
        undo_to(mark);
    }
    x[var] = 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: zplift p D [-brute] [-maxsol N] < bases\n"); return 2; }
    p = atoi(argv[1]); D = atoi(argv[2]);
    for (int i = 3; i < argc; i++) { if (!strcmp(argv[i], "-brute")) brute = 1; else if (!strcmp(argv[i], "-maxsol")) maxsol = atol(argv[++i]); }
    if (p > 128) { fprintf(stderr, "p <= 128\n"); return 2; }
    int Ls = (D % 2 == 0) ? D : D - 1, Lo = (D % 2 == 0) ? D - 1 : -1;
    W = malloc(sizeof(Walk) * MAXEV);
    evstart = malloc(sizeof(int) * (MAXC + 3)); evlist = malloc(sizeof(int) * MAXEV); vid = malloc(sizeof(int) * MAXEV);
    char line[1 << 16];
    baseid = -1;
    while (fgets(line, sizeof line, stdin)) {
        int nsimple, off; char *ptr = line;
        if (sscanf(ptr, "%d %d%n", &nv, &nsimple, &off) != 2) continue;
        baseid++; ptr += off; ne = 0;
        for (int i = 0; i < nsimple; i++) { int a, b, mu; if (sscanf(ptr, "%d %d %d%n", &a, &b, &mu, &off) != 3) { fprintf(stderr, "parse\n"); return 2; } ptr += off;
            for (int r = 0; r < mu; r++) { ea[ne] = a; eb[ne] = b; ne++; } }
        if (nv > MAXV || ne > MAXE) { fprintf(stderr, "base too big\n"); return 2; }
        /* 2-colour and orient */
        for (int i = 0; i < nv; i++) side_[i] = -1;
        int q[MAXV], h = 0, tq = 0; side_[0] = 0; q[tq++] = 0;
        while (h < tq) { int y = q[h++]; for (int e = 0; e < ne; e++) { int z = -1; if (ea[e] == y) z = eb[e]; else if (eb[e] == y) z = ea[e];
            if (z >= 0 && side_[z] < 0) { side_[z] = 1 - side_[y]; q[tq++] = z; } } }
        int bad = (tq != nv);
        for (int e = 0; e < ne; e++) { if (side_[ea[e]] == side_[eb[e]]) bad = 1; if (side_[ea[e]] == 1) { int t2 = ea[e]; ea[e] = eb[e]; eb[e] = t2; } }
        for (int i = 0; i < nv; i++) dn[i] = 0;
        for (int e = 0; e < ne; e++) { int a = ea[e], b = eb[e];
            de[a][dn[a]] = e; dto[a][dn[a]] = b; dsg[a][dn[a]] = +1; dn[a]++;
            de[b][dn[b]] = e; dto[b][dn[b]] = a; dsg[b][dn[b]] = -1; dn[b]++; }
        for (int i = 0; i < nv; i++) if (dn[i] != 3) bad = 1;
        if (bad) { printf("BASE %d skip=not-cubic-bipartite-connected\n", baseid); continue; }
        int k = nv / 2;
        /* spanning tree (BFS from 0) */
        int intree[MAXE] = {0}, seen[MAXV] = {0}; h = 0; tq = 0; seen[0] = 1; q[tq++] = 0;
        while (h < tq) { int y = q[h++]; for (int j = 0; j < dn[y]; j++) { int z = dto[y][j]; if (!seen[z]) { seen[z] = 1; intree[de[y][j]] = 1; q[tq++] = z; } } }
        ncot = 0; for (int e = 0; e < ne; e++) { if (intree[e]) cotidx[e] = -1; else { cotidx[e] = ncot; cotedge[ncot++] = e; } }
        if (ncot > MAXC) { fprintf(stderr, "too many cotree edges\n"); return 2; }
        /* walks */
        nw = 0; memset(cur, 0, sizeof cur);
        for (int u = 0; u < nv; u++) rec(u, u, -1, 0, Ls, Lo);
        /* pairs and dedupe identical coefficient vectors per pair (forced collisions) */
        static int pidx[MAXV][MAXV]; npair = 0;
        for (int u = 0; u < nv; u++) for (int v = 0; v < nv; v++) pidx[u][v] = -1;
        int wtot[MAXV][2]; memset(wtot, 0, sizeof wtot); memset(coll, 0, sizeof coll);
        for (int w = 0; w < nw; w++) { wtot[W[w].u][W[w].opp]++;
            int u = W[w].u, v = W[w].v; if (pidx[u][v] < 0) { pidx[u][v] = npair; pairu[npair] = u; pairv[npair] = v; pot[npair] = 0; npair++; } vid[w] = pidx[u][v]; }
        /* dedupe: mark duplicates */
        char *dup = calloc(nw, 1);
        for (int w = 0; w < nw; w++) { if (dup[w]) continue; for (int w2 = w + 1; w2 < nw; w2++) if (!dup[w2] && vid[w2] == vid[w] && !memcmp(W[w].c, W[w2].c, ncot)) { dup[w2] = 1; coll[W[w].u][W[w].opp]++; } }
        for (int w = 0; w < nw; w++) if (!dup[w]) pot[vid[w]]++;
        /* targets: every (u, v) with v on the right side must be a pair with pot >= p */
        int skip = 0; char why[64] = "";
        for (int u = 0; u < nv && !skip; u++) for (int v = 0; v < nv; v++) {
            int same = side_[u] == side_[v];
            if (!same && Lo < 0) continue;
            if (pidx[u][v] < 0 || pot[pidx[u][v]] < p) { skip = 1; strcpy(why, "walkcount<p"); break; } }
        for (int u = 0; u < nv; u++) { slack[u][0] = wtot[u][0] - k * p; slack[u][1] = (Lo < 0) ? 1 << 30 : wtot[u][1] - k * p;
            if (!skip && (coll[u][0] > slack[u][0] || coll[u][1] > slack[u][1])) { skip = 1; strcpy(why, "forced-collisions"); } }
        if (skip && !brute) { printf("BASE %d k=%d skip=%s\n", baseid, k, why); fflush(stdout); free(dup); continue; }
        /* variable order: greedy, maximise number of walks fully determined */
        int chosen[MAXC] = {0};
        for (int t = 0; t < ncot; t++) {
            int best = -1, bestcnt = -1;
            for (int c = 0; c < ncot; c++) if (!chosen[c]) {
                int cnt = 0;
                for (int w = 0; w < nw; w++) { if (dup[w]) continue; int ok = 1, uses = 0;
                    for (int c2 = 0; c2 < ncot; c2++) if (W[w].c[c2]) { if (c2 == c) uses = 1; else if (!chosen[c2]) { ok = 0; break; } }
                    if (ok && uses) cnt++; }
                if (cnt > bestcnt) { bestcnt = cnt; best = c; } }
            chosen[best] = 1; order[t] = best; posof[best] = t;
        }
        /* levels: level 0 = constant walks; level t+1 = determined after assigning order[t] */
        int *lev = malloc(sizeof(int) * nw), cnt[MAXC + 2] = {0};
        for (int w = 0; w < nw; w++) { if (dup[w]) { lev[w] = -1; continue; } int L = 0;
            for (int c = 0; c < ncot; c++) if (W[w].c[c] && posof[c] + 1 > L) L = posof[c] + 1; lev[w] = L; cnt[L]++; }
        evstart[0] = 0; for (int t = 0; t <= ncot; t++) evstart[t + 1] = evstart[t] + cnt[t];
        int fill[MAXC + 2]; for (int t = 0; t <= ncot; t++) fill[t] = evstart[t];
        for (int w = 0; w < nw; w++) if (lev[w] >= 0) evlist[fill[lev[w]]++] = w;
        memset(bits, 0, sizeof(bits[0]) * npair); memset(x, 0, sizeof x); usp = 0; nodes = 0; nsol = 0;
        int ok0 = apply_level(0);
        if (ok0 || brute) dfs(0, 0);
        printf("BASE %d k=%d ncot=%d nodes=%ld sols=%ld%s\n", baseid, k, ncot, nodes, nsol, (!ok0 && !brute) ? " skip=level0" : "");
        fflush(stdout);
        free(lev); free(dup);
    }
    return 0;
}
