/* jsearch: exhaustive search for Z_p voltage graphs (cubic bipartite base multigraph on k+k vertices + voltages)
   whose lift has bipartite diameter <= D, D odd. Builds the base and the voltages together, so the bases never
   have to be listed (zplift needs the full base list, which is out of reach for k > 11).
   Usage: jsearch p k D [-root0 ...]   Output: "SOL" lines (base edges with voltages) and a final "DONE" line.

   Construction (BFS-canonical): vertex 0 (side 0) is the root. The smallest-labelled vertex x with a free
   half-edge is filled next. x's remaining half-edges get a sorted multiset of targets: first existing vertices
   y > x on the other side (sorted by (y, voltage)), then new vertices (next labels, voltage 0: the edges to new
   vertices form a spanning tree, so the gauge is fixed). Every connected base with every labelling reachable by
   this BFS rule is generated at least once (from every root of side 0). The first nonzero voltage is 1 (scaling
   by a unit of Z_p). Parallel edges need distinct voltages (else the lift has a double edge).
   Pruning: for every base vertex u, the NB walks from u of even length <= D-1 inside the partial base give
   (endpoint, voltage) pairs; collisions(u) = #walks - #distinct. In the final base u has 2^D - 1 such walks and
   needs every one of the k*p same-side targets, so collisions(u) <= delta = 2^D - 1 - k*p, and collisions only
   grow as edges are added. At a complete base, collisions(u) <= delta for all u is equivalent to diameter <= D. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define MAXV 64
#define MAXE 96
static int p, k, D, L, delta;
static int nv, ne, side_[MAXV], deg_[MAXV], nside[2];
static int adjv[MAXV][3], adje[MAXV][3];
static int ea[MAXE], eb[MAXE], et[MAXE]; /* ea side 0, eb side 1, voltage a->b */
static int anynz;
static uint64_t seen_[MAXV][MAXV][2]; /* [start][end] bitset of voltages, p <= 128 */
static int coll[MAXV];
static long nodes, nsol, maxsol = 100;
/* log of insertions for undo: (u, v, g, wascollision) */
typedef struct { short u, v, g; char c; } Rec;
static Rec *logbuf; static long lsp, lcap;

static inline int dartv(int x, int j, int *g) { int e = adje[x][j]; *g = (side_[x] == 0) ? et[e] : (p - et[e]) % p; return adjv[x][j]; }

/* Walks through the new edge e = (a, b): W = W1 . e . W2 with e's first occurrence; W1 (from the start u to the
   tail of e) avoids e, W2 (from the head of e) does not start with e. Enumerate reversed prefixes from the tail
   and suffixes from the head and combine. */
typedef struct { short x, g, len; } PW;
static PW pre[4096], suf[4096]; static int npre, nsuf;
static int enew, bad;
static void gen_pre(int x, int laste, int len, int g, int maxlen) { /* NB walks from tail avoiding enew; g = voltage tail->x */
    pre[npre].x = x; pre[npre].g = g; pre[npre].len = len; npre++;
    if (len == maxlen) return;
    for (int j = 0; j < deg_[x]; j++) { int e = adje[x][j]; if (e == laste || e == enew) continue;
        int dg; int y = dartv(x, j, &dg); gen_pre(y, e, len + 1, (g + dg) % p, maxlen); }
}
static void gen_suf(int x, int laste, int len, int g, int maxlen) { /* NB walks from head, first edge != enew */
    suf[nsuf].x = x; suf[nsuf].g = g; suf[nsuf].len = len; nsuf++;
    if (len == maxlen) return;
    for (int j = 0; j < deg_[x]; j++) { int e = adje[x][j]; if (e == laste) continue;
        int dg; int y = dartv(x, j, &dg); gen_suf(y, e, len + 1, (g + dg) % p, maxlen); }
}
static inline void record(int u, int v, int g) {
    uint64_t m = 1ULL << (g & 63); int w = g >> 6;
    Rec r; r.u = u; r.v = v; r.g = g;
    if (seen_[u][v][w] & m) { r.c = 1; coll[u]++; if (coll[u] > delta) bad = 1; }
    else { r.c = 0; seen_[u][v][w] |= m; }
    if (lsp == lcap) { lcap *= 2; logbuf = realloc(logbuf, sizeof(Rec) * lcap); }
    logbuf[lsp++] = r;
}
static void through(int tail, int head, int gt) { /* gt = voltage of traversing e from tail to head */
    npre = 0; nsuf = 0;
    gen_pre(tail, enew, 0, 0, L - 1);
    gen_suf(head, enew, 0, 0, L - 1);
    /* bucket suffixes by length */
    static int sb[16][2048], sn[16];
    for (int l = 0; l < L; l++) sn[l] = 0;
    for (int j = 0; j < nsuf; j++) { int l = suf[j].len; sb[l][sn[l]++] = j; }
    for (int i = 0; i < npre && !bad; i++) {
        /* W1 from u = pre.x to tail has voltage -pre.g */
        int u = pre[i].x, g1 = (p - pre[i].g + gt) % p, li = pre[i].len;
        for (int l = (li & 1) ? 0 : 1; li + 1 + l <= L; l += 2)
            for (int jj = 0; jj < sn[l]; jj++) { int j = sb[l][jj];
                record(u, suf[j].x, (g1 + suf[j].g) % p);
                if (bad) return; }
    }
}
static void undo_to(long mark) {
    while (lsp > mark) { Rec r = logbuf[--lsp];
        if (r.c) coll[r.u]--; else seen_[r.u][r.v][r.g >> 6] &= ~(1ULL << (r.g & 63)); }
}
static void add_edge(int a, int b, int t) { /* a side 0 */
    int e = ne++; ea[e] = a; eb[e] = b; et[e] = t;
    adjv[a][deg_[a]] = b; adje[a][deg_[a]++] = e; adjv[b][deg_[b]] = a; adje[b][deg_[b]++] = e;
}
static void del_edge(void) { int e = --ne; deg_[ea[e]]--; deg_[eb[e]]--; }
static int probe_mode = 0;
static int shard_id = 0, shard_mod = 1, shard_depth = 0; static long shard_counter = 0;
static int check_new_edge(void) { /* record walks through the newest edge; 0 if pruned (or not in this shard) */
    enew = ne - 1; bad = 0;
    int a = ea[enew], b = eb[enew], t = et[enew];
    through(a, b, t);
    if (!bad) through(b, a, (p - t) % p);
    /* sharding: subtrees rooted where the edge count reaches shard_depth are dealt out round-robin. Above that depth
       every shard runs the same deterministic search, so the shards partition the search tree. */
    if (!bad && shard_mod > 1 && ne == shard_depth && !probe_mode) { if ((shard_counter++ % shard_mod) != shard_id) return 0; }
    return !bad;
}
static void report(void) {
    nsol++;
    if (nsol <= maxsol) { printf("SOL nv=%d", nv); for (int e = 0; e < ne; e++) printf(" %d-%d:%d", ea[e], eb[e], et[e]); printf("\n"); fflush(stdout); }
}

/* fill vertex x: its remaining half-edges get a sorted multiset of targets. First existing vertices y > x on the
   other side, key = y*p + t (t = voltage seen from x), non-decreasing; then new vertices (next labels). A new
   vertex y gets the tree edge (voltage 0) and possibly more parallel edges to x with increasing nonzero voltages. */
static void fill(int x, int minkey);
static void next_vertex(void) {
    int x = -1; for (int i = 0; i < nv; i++) if (deg_[i] < 3) { x = i; break; }
    if (x < 0) { if (nv == 2 * k) report(); return; } /* complete, or closed early (then not connected): dead */
    fill(x, 0);
}
#define BIG (1 << 20)
static int try_edge(int x, int y, int tx) { /* add edge x-y with voltage tx seen from x; 1 if kept (caller undoes) */
    int s = side_[x];
    int vt = (s == 0) ? tx : (p - tx) % p;
    if (!anynz && vt > 1) return -1;
    for (int j = 0; j < deg_[x]; j++) if (adjv[x][j] == y && et[adje[x][j]] == vt) return -1; /* parallel, same voltage */
    add_edge(s == 0 ? x : y, s == 0 ? y : x, vt);
    return vt;
}
static void par_new(int x, int y, int lastt) { /* optional further parallel edges x-y (y new), voltages > lastt */
    fill(x, BIG); /* stop adding parallels */
    if (deg_[x] == 3 || deg_[y] == 3) return;
    for (int t = lastt + 1; t < p; t++) {
        int was = anynz; int vt = try_edge(x, y, t); if (vt < 0) continue;
        if (vt) anynz = 1;
        long mark = lsp;
        if (check_new_edge()) par_new(x, y, t);
        undo_to(mark); del_edge(); anynz = was;
    }
}
static void fill(int x, int minkey) {
    nodes++;
    if ((nodes & ((1L << 22) - 1)) == 0) { fprintf(stderr, "progress nodes=%ld nv=%d ne=%d sols=%ld\n", nodes, nv, ne, nsol); }
    if (deg_[x] == 3) { next_vertex(); return; }
    int s = side_[x], o = 1 - s;
    if (minkey < BIG) for (int y = x + 1; y < nv; y++) {
        if (side_[y] != o || deg_[y] >= 3) continue;
        for (int t = 0; t < p; t++) {
            int key = y * p + t; if (key < minkey) continue;
            int was = anynz; int vt = try_edge(x, y, t); if (vt < 0) continue;
            if (vt) anynz = 1;
            long mark = lsp;
            if (check_new_edge()) fill(x, key + 1);
            undo_to(mark); del_edge(); anynz = was;
        }
    }
    if (nv < 2 * k && nside[o] < k) {
        int y = nv++; side_[y] = o; deg_[y] = 0; nside[o]++;
        seen_[y][y][0] |= 1ULL; /* trivial walk at y */
        add_edge(s == 0 ? x : y, s == 0 ? y : x, 0);
        long mark = lsp;
        if (check_new_edge()) par_new(x, y, 0);
        undo_to(mark); del_edge();
        seen_[y][y][0] &= ~1ULL; nv--; nside[o]--;
    }
}


/* ---- Knuth estimator (-probe N): random descents; each node's weight = product of feasible branch counts ---- */
static double pw; static double pnodes; static unsigned long long rng = 88172645463325252ULL;
static unsigned rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (unsigned)(rng >> 11); }
typedef struct { int type, y, t; } Opt; /* type 0: existing y voltage t (seen from x); 1: new vertex; 2: stop parallels; 3: parallel t */
static int probe_feasible_edge(int x, int y, int t) {
    int was = anynz; int vt = try_edge(x, y, t); if (vt < 0) return 0;
    if (vt) anynz = 1; long mark = lsp; int ok = check_new_edge(); undo_to(mark); del_edge(); anynz = was; return ok;
}
static void probe_fill(int x, int minkey);
static void probe_next(void) {
    int x = -1; for (int i = 0; i < nv; i++) if (deg_[i] < 3) { x = i; break; }
    if (x < 0) { if (nv == 2 * k) nsol++; return; }
    probe_fill(x, 0);
}
static void probe_par(int x, int y, int lastt);
static void probe_fill(int x, int minkey) {
    pnodes += pw;
    if (deg_[x] == 3) { probe_next(); return; }
    int s = side_[x], o = 1 - s; Opt op[4096]; int no = 0;
    if (minkey < BIG) for (int y = x + 1; y < nv; y++) { if (side_[y] != o || deg_[y] >= 3) continue;
        for (int t = 0; t < p; t++) { int key = y * p + t; if (key < minkey) continue;
            if (probe_feasible_edge(x, y, t)) { op[no].type = 0; op[no].y = y; op[no].t = t; no++; } } }
    if (nv < 2 * k && nside[o] < k) {
        int y = nv++; side_[y] = o; deg_[y] = 0; nside[o]++; seen_[y][y][0] |= 1ULL;
        add_edge(s == 0 ? x : y, s == 0 ? y : x, 0); long mark = lsp; int ok = check_new_edge(); undo_to(mark); del_edge();
        seen_[y][y][0] &= ~1ULL; nv--; nside[o]--;
        if (ok) { op[no].type = 1; no++; } }
    if (no == 0) return;
    Opt c = op[rnd() % no]; pw *= no;
    if (c.type == 0) { int vt = try_edge(x, c.y, c.t); if (vt) anynz = 1; check_new_edge(); probe_fill(x, c.y * p + c.t + 1); }
    else { int y = nv++; side_[y] = o; deg_[y] = 0; nside[o]++; seen_[y][y][0] |= 1ULL;
        add_edge(s == 0 ? x : y, s == 0 ? y : x, 0); check_new_edge(); probe_par(x, y, 0); }
}
static void probe_par(int x, int y, int lastt) {
    Opt op[256]; int no = 0; op[no++].type = 2;
    if (deg_[x] < 3 && deg_[y] < 3) for (int t = lastt + 1; t < p; t++) if (probe_feasible_edge(x, y, t)) { op[no].type = 3; op[no].t = t; no++; }
    Opt c = op[rnd() % no]; pw *= no;
    if (c.type == 2) probe_fill(x, BIG);
    else { int vt = try_edge(x, y, c.t); if (vt) anynz = 1; check_new_edge(); probe_par(x, y, c.t); }
}
static void probe_reset(void) { /* rebuild empty state */
    memset(seen_, 0, sizeof seen_); memset(coll, 0, sizeof coll); lsp = 0;
    nv = 1; side_[0] = 0; deg_[0] = 0; nside[0] = 1; nside[1] = 0; ne = 0; anynz = 0; seen_[0][0][0] |= 1ULL;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: jsearch p k D [maxsol]\n"); return 2; }
    p = atoi(argv[1]); k = atoi(argv[2]); D = atoi(argv[3]); if (argc > 4) maxsol = atol(argv[4]);
    if (D % 2 == 0 || p > 128 || 2 * k > MAXV) { fprintf(stderr, "D odd, p <= 128, k <= 32\n"); return 2; }
    L = D - 1; delta = (1 << D) - 1 - k * p;
    if (delta < 0) { printf("DONE p=%d k=%d D=%d delta<0 nodes=0 sols=0\n", p, k, D); return 0; }
    lcap = 1 << 20; logbuf = malloc(sizeof(Rec) * lcap);
    nv = 1; side_[0] = 0; deg_[0] = 0; nside[0] = 1; nside[1] = 0; ne = 0; anynz = 0;
    /* root: its trivial walk */
    seen_[0][0][0] |= 1ULL; /* trivial walk at the root; other vertices get theirs on creation */
    if (getenv("SHARD")) { sscanf(getenv("SHARD"), "%d/%d", &shard_id, &shard_mod); shard_depth = getenv("SHARDDEPTH") ? atoi(getenv("SHARDDEPTH")) : 20; }
    if (getenv("PROBE")) { probe_mode = 1; long np = atol(getenv("PROBE")); double tot = 0, tot2 = 0, solsum = 0; rng ^= (unsigned long long)np * 7919;
        for (long i = 0; i < np; i++) { probe_reset(); pw = 1; pnodes = 0; nsol = 0; probe_fill(0, 0); tot += pnodes; tot2 += pnodes * pnodes; solsum += nsol * pw; }
        double mean = tot / np; printf("PROBE p=%d k=%d D=%d delta=%d probes=%ld est_nodes=%.3g rel_se=%.2f est_sols=%.3g\n", p, k, D, delta, np, mean,
            sqrt(tot2 / np - mean * mean) / mean / sqrt((double)np), solsum / np); return 0; }
    fill(0, 0);
    printf("DONE p=%d k=%d D=%d delta=%d nodes=%ld sols=%ld shard=%d/%d depth=%d cut_subtrees=%ld\n", p, k, D, delta, nodes, nsol, shard_id, shard_mod, shard_depth, shard_counter);
    return 0;
}
