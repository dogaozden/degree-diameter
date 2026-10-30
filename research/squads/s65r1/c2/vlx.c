/* vl.c: simulated annealing over voltage lifts of a small bipartite base multigraph by a finite group.
 *
 * Lift of base B by G (voltages alpha on edges, oriented side 0 -> side 1): vertices (v, h), h in G, and for each
 * base edge e = (a, b) the lift edges (a, h) ~ (b, h * alpha(e)). Left multiplication by G is an automorphism, so the
 * lift has diameter <= D iff, for every base vertex s, every (v, h) is within distance D of (s, 1).
 * Within distance D (bipartite): same side by a walk of even length <= D-1, other side by odd length <= D.
 * Every walk reduces to a non-backtracking one (same end, same product, length lower by an even number), so it is
 * enough to enumerate non-backtracking walks (a parallel edge is a different edge, so a->b->a along two parallel
 * edges is allowed).
 * Pairs are symmetric (W(u->s) = W(s->u)^-1), so side-1 sources only need their same-side targets.
 * Cost = sum over sources of the number of uncovered (v, h). Cost 0 <=> diameter <= D (lift connected).
 *
 * usage: vl BASE GROUP
 *   BASE:  "b E" / b side bits / E lines "u w [volt]" (u on side 0, w on side 1). Voltages default to 0 (identity).
 *   GROUP: m, then the m x m multiplication table (element 0 = identity).
 * env: D (5), ITERS (annealing steps per run, 200000), SECS (60), SEED (1), T0 (3), T1 (0.2),
 *      SWAP (probability of a base 2-switch move, 0), FIXTREE (1 if SWAP=0: spanning-tree voltages stay 1),
 *      OUT (solution file, written whenever a new best is found), EVAL=1 (just print the cost of the input),
 *      MAXDEG (refuse inputs with a larger base degree, default 64)
 * Output: "RESULT best <cost> ..." on stdout; OUT gets the base with voltages.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXB 512
#define MAXE 4096
#define MAXDEG 64

static int b, E, m, D = 5, W;
static int side[MAXB];
static int eu[MAXE], ew[MAXE], volt[MAXE], fixed_[MAXE];
static int deg[MAXB], dn[MAXB][MAXDEG], de[MAXB][MAXDEG], dd[MAXB][MAXDEG]; /* neighbour, edge, dir (0: u->w) */
static uint16_t *mul;
static int *inv_;
static uint64_t *cov;     /* b x W words */

static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void build_adj(void) {
    memset(deg, 0, sizeof(deg));
    for (int e = 0; e < E; e++) {
        int u = eu[e], w = ew[e];
        dn[u][deg[u]] = w; de[u][deg[u]] = e; dd[u][deg[u]] = 0; deg[u]++;
        dn[w][deg[w]] = u; de[w][deg[w]] = e; dd[w][deg[w]] = 1; deg[w]++;
    }
}

static inline int dvolt(int v, int i) { int g = volt[de[v][i]]; return dd[v][i] ? inv_[g] : g; }

static int maxlen;
static void dfs(int v, int laste, int h, int len) {
    cov[(size_t)v * W + (h >> 6)] |= 1ULL << (h & 63);
    if (len == maxlen) return;
    for (int i = 0; i < deg[v]; i++) {
        int e = de[v][i];
        if (e == laste) continue;
        dfs(dn[v][i], e, mul[(size_t)h * m + dvolt(v, i)], len + 1);
    }
}

/* uncovered count for source s */
static long src_cost(int s) {
    memset(cov, 0, sizeof(uint64_t) * b * W);
    maxlen = side[s] == 0 ? D : D - 1;
    dfs(s, -1, 0, 0);
    long c = 0;
    for (int v = 0; v < b; v++) {
        if (side[s] == 1 && side[v] == 0) continue;
        int par = (side[v] != side[s]);           /* needed parity of the walk */
        if (!par && D % 2 == 0 && 0) continue;
        long k = 0;
        for (int w = 0; w < W; w++) k += __builtin_popcountll(cov[(size_t)v * W + w]);
        c += m - k;
    }
    return c;
}

/* total cost; abort (return > limit) once the partial sum exceeds limit */
static int order[MAXB];
static long total_cost(long limit) {
    long c = 0;
    for (int i = 0; i < b; i++) {
        c += src_cost(order[i]);
        if (c > limit) return c;
    }
    return c;
}


/* ---------- incremental mode: cnt[s][v][h] = number of counted walks from (s,1) to (v,h) ---------- */
static uint16_t *cnt; static signed char *bdist; static long inc_delta;
static int ie_a, ie_c, ie_e, ie_old, ie_new, ie_s, ie_L;
static inline int relevant(int s, int v) { return side[s] == 0 || side[v] == 1; }
static void base_dist(void) {
    bdist = malloc((size_t)b * b);
    for (int s = 0; s < b; s++) {
        signed char *d = bdist + (size_t)s * b; for (int v = 0; v < b; v++) d[v] = 100;
        int q[MAXB], h = 0, t = 0; d[s] = 0; q[t++] = s;
        while (h < t) { int x = q[h++]; for (int i = 0; i < deg[x]; i++) { int y = dn[x][i]; if (d[y] == 100) { d[y] = d[x] + 1; q[t++] = y; } } }
    }
}
static void fill_dfs(int s, int v, int laste, int h, int len, int L) {
    if (relevant(s, v)) cnt[((size_t)s * b + v) * m + h]++;
    if (len == L) return;
    for (int i = 0; i < deg[v]; i++) { int e = de[v][i]; if (e == laste) continue;
        fill_dfs(s, dn[v][i], e, mul[(size_t)h * m + dvolt(v, i)], len + 1, L); }
}
static long inc_init(void) {
    size_t sz = (size_t)b * b * m; if (!cnt) cnt = malloc(sizeof(uint16_t) * sz);
    memset(cnt, 0, sizeof(uint16_t) * sz);
    for (int s = 0; s < b; s++) fill_dfs(s, s, -1, 0, 0, side[s] == 0 ? D : D - 1);
    long c = 0;
    for (int s = 0; s < b; s++) for (int v = 0; v < b; v++) if (relevant(s, v))
        for (int h = 0; h < m; h++) if (!cnt[((size_t)s * b + v) * m + h]) c++;
    return c;
}
static void inc_dfs(int v, int laste, int ho, int hn, int len, int used) {
    if (used && ho != hn && relevant(ie_s, v)) {
        uint16_t *p = cnt + ((size_t)ie_s * b + v) * m;
        if (--p[ho] == 0) inc_delta++;
        if (p[hn]++ == 0) inc_delta--;
    }
    if (len == ie_L) return;
    for (int i = 0; i < deg[v]; i++) {
        int e = de[v][i]; if (e == laste) continue;
        int y = dn[v][i], go, gn, u2 = used;
        if (e == ie_e) { go = dd[v][i] ? inv_[ie_old] : ie_old; gn = dd[v][i] ? inv_[ie_new] : ie_new; u2 = 1; }
        else { go = gn = dvolt(v, i);
            if (!used) { int dmin = bdist[(size_t)y * b + ie_a] < bdist[(size_t)y * b + ie_c] ? bdist[(size_t)y * b + ie_a] : bdist[(size_t)y * b + ie_c];
                if (dmin + 1 > ie_L - (len + 1)) continue; } }
        inc_dfs(y, e, mul[(size_t)ho * m + go], mul[(size_t)hn * m + gn], len + 1, u2);
    }
}
/* change volt[e] to g, return the cost change */
static long inc_move(int e, int g) {
    ie_e = e; ie_a = eu[e]; ie_c = ew[e]; ie_old = volt[e]; ie_new = g; inc_delta = 0;
    for (int s = 0; s < b; s++) {
        ie_s = s; ie_L = side[s] == 0 ? D : D - 1;
        int dmin = bdist[(size_t)s * b + ie_a] < bdist[(size_t)s * b + ie_c] ? bdist[(size_t)s * b + ie_a] : bdist[(size_t)s * b + ie_c];
        if (dmin + 1 > ie_L) continue;
        inc_dfs(s, -1, 0, 0, 0, 0);
    }
    volt[e] = g;
    return inc_delta;
}


/* focused move (INC mode): pick an uncovered (s, v, h), a random non-backtracking walk s -> v of the right parity,
   and an edge used once on it; return the voltage of that edge that makes the walk end at sheet h (or -1). */
static int focus_move(int *pe) {
    long tot = (long)b * b * m; int s = -1, v = -1, h = -1;
    for (int t = 0; t < 20000; t++) {
        long r = rnd() % tot; int ss = r / ((long)b * m), vv = (r / m) % b, hh = r % m;
        if (!relevant(ss, vv)) continue;
        if (cnt[r] == 0) { s = ss; v = vv; h = hh; break; }
    }
    if (s < 0) return -1;
    int L0 = side[s] == 0 ? D : D - 1;
    for (int t = 0; t < 2000; t++) {
        int L = L0 - (rnd() % 2) * 2;                     /* lengths L0 or L0-2 */
        if (((L & 1) != (side[s] != side[v])) ) L--;      /* fix parity */
        if (L < 1) continue;
        int x = s, laste = -1, we[16], wd[16], wv[16];
        for (int k = 0; k < L; k++) {
            int i, tries = 0;
            do { i = rnd() % deg[x]; } while (de[x][i] == laste && ++tries < 50);
            if (de[x][i] == laste) break;
            we[k] = de[x][i]; wd[k] = dd[x][i]; wv[k] = x; laste = we[k]; x = dn[x][i];
            if (k == L - 1 && x != v) { L = -1; break; }
        }
        if (L < 1 || x != v) continue;
        int pos = rnd() % L, e = we[pos], once = 1;
        for (int k = 0; k < L; k++) if (k != pos && we[k] == e) once = 0;
        if (!once || fixed_[e]) continue;
        /* product = P1 * g' * P2 with g' = volt (dir 0) or volt^-1 (dir 1) */
        int P1 = 0, P2 = 0;
        for (int k = 0; k < pos; k++) { int g = volt[we[k]]; if (wd[k]) g = inv_[g]; P1 = mul[(size_t)P1 * m + g]; }
        for (int k = pos + 1; k < L; k++) { int g = volt[we[k]]; if (wd[k]) g = inv_[g]; P2 = mul[(size_t)P2 * m + g]; }
        int gp = mul[(size_t)mul[(size_t)inv_[P1] * m + h] * m + inv_[P2]];
        int g = wd[pos] ? inv_[gp] : gp;
        (void)wv;
        *pe = e; return g;
    }
    return -1;
}

static void write_sol(const char *path, long cost, const char *gname) {
    if (!path) return;
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "w"); if (!f) return;
    fprintf(f, "%d %d\n", b, E);
    for (int v = 0; v < b; v++) fprintf(f, "%d%c", side[v], v == b - 1 ? '\n' : ' ');
    for (int e = 0; e < E; e++) fprintf(f, "%d %d %d\n", eu[e], ew[e], volt[e]);
    fprintf(f, "# group %s m %d D %d cost %ld\n", gname, m, D, cost);
    fclose(f); rename(tmp, path);
}

static int connected(void) {
    int seen[MAXB] = {0}, q[MAXB], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    while (h < t) { int v = q[h++]; for (int i = 0; i < deg[v]; i++) if (!seen[dn[v][i]]) { seen[dn[v][i]] = 1; q[t++] = dn[v][i]; } }
    return t == b;
}

static void mark_tree(void) {
    int seen[MAXB] = {0}, q[MAXB], h = 0, t = 0; seen[0] = 1; q[t++] = 0;
    for (int e = 0; e < E; e++) fixed_[e] = 0;
    while (h < t) { int v = q[h++]; for (int i = 0; i < deg[v]; i++) if (!seen[dn[v][i]]) {
        seen[dn[v][i]] = 1; q[t++] = dn[v][i]; fixed_[de[v][i]] = 1; volt[de[v][i]] = 0; } }
}

/* ---------- SEMI mode (vlx.c, card c2): the wedge edge WE is not annealed. At every evaluation its voltage is
 * the best value w for the current other voltages: w-free walks give the coverage cov_free; every missed (s, v, x)
 * is covered by a walk P w^d Q through WE once iff w = (P^-1 x Q^-1)^d, so tally[w] counts the misses that w
 * covers (dedupe per x), and w* = argmax over the values allowed by the simple-graph rule (distinct voltages in a
 * parallel class). The cost is then the exact total_cost with volt[WE] = w*. Walks through WE twice are only seen
 * by the exact cost. ---------- */
#define MAXT (1 << 17)
#define MAXM 256
static int WE = -1;
static uint64_t fcov_[MAXB][4];
static int tv_[MAXT], tP_[MAXT], td_[MAXT], tQ_[MAXT], nt_, pmaxlen, vidx_[MAXT];
static int bad_[MAXM];
static long tally_[MAXM];
static uint64_t mark_[MAXM], stamp_ = 0;

static void padd(int v, int P, int d, int suf) {
    if (nt_ >= MAXT) { fprintf(stderr, "walk buffer overflow\n"); exit(4); }
    tv_[nt_] = v; tP_[nt_] = P; td_[nt_] = d; tQ_[nt_] = suf; nt_++;
}
/* phase 0 (used = 0): walks avoiding WE, h = product so far; phase 1: one use of WE, P = prefix, d = its sign,
   suf = product after it. A second use of WE is not followed. */
static void pdfs(int v, int laste, int h, int len, int used, int P, int d, int suf) {
    if (!used) fcov_[v][h >> 6] |= 1ULL << (h & 63);
    else padd(v, P, d, suf);
    if (len == pmaxlen) return;
    for (int i = 0; i < deg[v]; i++) {
        int e = de[v][i]; if (e == laste) continue;
        int y = dn[v][i];
        if (e == WE) {
            if (used) continue;
            pdfs(y, e, 0, len + 1, 1, h, dd[v][i] ? -1 : 1, 0);
        } else if (!used) {
            pdfs(y, e, (int)mul[(size_t)h * m + dvolt(v, i)], len + 1, 0, 0, 0, 0);
        } else {
            pdfs(y, e, 0, len + 1, 1, P, d, (int)mul[(size_t)suf * m + dvolt(v, i)]);
        }
    }
}

/* returns the chosen w (and sets volt[WE] = w), or -1; *approx = misses - tally[w] (no double walks) */
static int choose_w(long *approx) {
    for (int c = 0; c < m; c++) { tally_[c] = 0; bad_[c] = 0; }
    for (int f = 0; f < E; f++)
        if (f != WE && eu[f] == eu[WE] && ew[f] == ew[WE] && volt[f] >= 0) bad_[volt[f]] = 1;
    long miss = 0;
    for (int s = 0; s < b; s++) {
        pmaxlen = side[s] == 0 ? D : D - 1;
        memset(fcov_, 0, sizeof fcov_);
        nt_ = 0; pdfs(s, -1, 0, 0, 0, 0, 0, 0);
        for (int v = 0; v < b; v++) {
            if (side[s] == 1 && side[v] == 0) continue;
            int nv = 0;
            for (int k = 0; k < nt_; k++) if (tv_[k] == v) vidx_[nv++] = k;
            for (int x = 0; x < m; x++) {
                if ((fcov_[v][x >> 6] >> (x & 63)) & 1) continue;
                miss++;
                stamp_++;
                for (int j = 0; j < nv; j++) {
                    int k = vidx_[j];
                    int t = (int)mul[(size_t)mul[(size_t)inv_[tP_[k]] * m + x] * m + inv_[tQ_[k]]];
                    int c = td_[k] > 0 ? t : inv_[t];
                    if (mark_[c] != stamp_) { mark_[c] = stamp_; tally_[c]++; }
                }
            }
        }
    }
    long bt = -1; int bc = -1, nties = 0;
    for (int c = 0; c < m; c++) {
        if (bad_[c]) continue;
        if (tally_[c] > bt) { bt = tally_[c]; bc = c; nties = 1; }
        else if (tally_[c] == bt && (rnd() % (++nties)) == 0) bc = c;
    }
    if (bc < 0) return -1;
    volt[WE] = bc;
    if (approx) *approx = miss - bt;
    return bc;
}

static long semi_eval(long *approx, long limit) {   /* exact cost; aborts (returns > limit) once above limit */
    if (choose_w(approx) < 0) return 1L << 40;
    return total_cost(limit);
}

/* simple-graph rule: edges parallel to e (same endpoints) must get distinct voltages (tree edges are 0) */
static int dup_ok(int e, int g) {
    for (int f = 0; f < E; f++)
        if (f != e && eu[f] == eu[e] && ew[f] == ew[e] && volt[f] >= 0 && volt[f] == g) return 0;
    return 1;
}

static int semi_main(int *freee, int nfree, double SECS, long ITERS, double T0, double T1,
                     const char *OUT, const char *gname) {
    static int aol[MAXE], sbv[MAXE];
    int nA = 0;
    for (int i = 0; i < nfree; i++) if (freee[i] != WE) aol[nA++] = freee[i];
    for (int e = 0; e < E; e++) if (!fixed_[e]) volt[e] = -1;
    for (int i = 0; i < nA; i++) {
        int e = aol[i], tries = 0;
        do { volt[e] = rnd() % m; } while (!dup_ok(e, volt[e]) && ++tries < 100000);
    }
    long approx = 0, cur = semi_eval(&approx, 1L << 60);
    long best = cur;
    memcpy(sbv, volt, sizeof(int) * E);
    write_sol(OUT, best, gname);
    double t_start = now(), t_end = t_start + SECS;
    long it_total = 0; int run = 0;
    while (best > 0 && now() < t_end) {
        run++;
        if (run > 1) {   /* restart from the best with a kick on a few free edges */
            memcpy(volt, sbv, sizeof(int) * E);
            int kick = 1 + nA / 10;
            for (int k = 0; k < kick; k++) {
                int e = aol[rnd() % nA];
                for (int t = 0; t < 100; t++) { int g = rnd() % m; if (dup_ok(e, g)) { volt[e] = g; break; } }
            }
            cur = semi_eval(&approx, 1L << 60);
        }
        for (long it = 0; it < ITERS && best > 0; it++) {
            if ((it & 255) == 0 && now() > t_end) break;
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            double r = rnd01(); if (r < 1e-300) r = 1e-300;
            long limit = cur + (long)floor(-T * log(r));
            int e = aol[rnd() % nA], old = volt[e], g = rnd() % m;
            if (g == old || !dup_ok(e, g)) continue;
            int oldw = volt[WE];
            volt[e] = g;
            long c = semi_eval(&approx, limit);
            if (c <= limit) cur = c; else { volt[e] = old; volt[WE] = oldw; }
            it_total++;
            if (cur < best) {
                best = cur; memcpy(sbv, volt, sizeof(int) * E); write_sol(OUT, best, gname);
                fprintf(stderr, "  t=%.1fs run %d it %ld best %ld (approx %ld)\n", now() - t_start, run, it, best, approx);
            }
        }
    }
    memcpy(volt, sbv, sizeof(int) * E);
    long fin = total_cost(1L << 60);
    printf("RESULT best %ld check %ld b %d m %d vertices %ld iters %ld runs %d secs %.1f wedge %d%s\n", best, fin, b, m,
           (long)b * m, it_total, run, now() - t_start, WE, fin == 0 ? " DIAMETER_OK" : "");
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: vl BASE GROUP\n"); return 2; }
    const char *gs;
    if ((gs = getenv("D"))) D = atoi(gs);
    long ITERS = getenv("ITERS") ? atol(getenv("ITERS")) : 200000;
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 60;
    rs ^= getenv("SEED") ? (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL : 0; for (int i = 0; i < 20; i++) rnd();
    double T0 = getenv("T0") ? atof(getenv("T0")) : 3, T1 = getenv("T1") ? atof(getenv("T1")) : 0.2;
    double SWAP = getenv("SWAP") ? atof(getenv("SWAP")) : 0;
    int FIXTREE = getenv("FIXTREE") ? atoi(getenv("FIXTREE")) : (SWAP == 0);
    int EVAL = getenv("EVAL") ? atoi(getenv("EVAL")) : 0;
    int maxdeg = getenv("MAXDEG") ? atoi(getenv("MAXDEG")) : MAXDEG;
    const char *OUT = getenv("OUT");

    FILE *f = fopen(argv[1], "r"); if (!f) { perror("base"); return 2; }
    if (fscanf(f, "%d %d", &b, &E) != 2 || b > MAXB || E > MAXE) { fprintf(stderr, "bad base\n"); return 2; }
    for (int v = 0; v < b; v++) if (fscanf(f, "%d", &side[v]) != 1) return 2;
    int hasv = 0;
    {   char line[256]; fgets(line, sizeof line, f);
        for (int e = 0; e < E; e++) {
            if (!fgets(line, sizeof line, f)) { fprintf(stderr, "short base\n"); return 2; }
            int a, c, g; int k = sscanf(line, "%d %d %d", &a, &c, &g);
            if (k < 2) { e--; continue; }
            if (side[a] == side[c]) { fprintf(stderr, "edge %d not bipartite\n", e); return 2; }
            if (side[a] == 1) { int t = a; a = c; c = t; }
            eu[e] = a; ew[e] = c; volt[e] = (k == 3) ? g : 0; if (k == 3) hasv = 1;
        }
    }
    fclose(f);
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "%d", &m) != 1) { fprintf(stderr, "bad group\n"); return 2; }
    mul = malloc(sizeof(uint16_t) * m * m); inv_ = malloc(sizeof(int) * m);
    for (long i = 0; i < (long)m * m; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; mul[i] = x; }
    fclose(f);
    for (int x = 0; x < m; x++) { inv_[x] = -1; for (int y = 0; y < m; y++) if (mul[(size_t)x * m + y] == 0) inv_[x] = y; }
    W = (m + 63) / 64;
    cov = malloc(sizeof(uint64_t) * b * W);
    build_adj();
    for (int v = 0; v < b; v++) if (deg[v] > maxdeg) { fprintf(stderr, "degree %d > %d\n", deg[v], maxdeg); return 2; }
    if (!connected()) { fprintf(stderr, "base disconnected\n"); }
    for (int i = 0; i < b; i++) order[i] = i;
    const char *gname = argv[2];

    long cur = total_cost(1L << 60);
    if (EVAL) { printf("RESULT cost %ld b %d m %d vertices %ld\n", cur, b, m, (long)b * m); return 0; }
    if (FIXTREE) { mark_tree(); }
    int nfree = 0, freee[MAXE]; for (int e = 0; e < E; e++) if (!fixed_[e]) freee[nfree++] = e;
    if (getenv("SEMI") && atoi(getenv("SEMI"))) {   /* semi-exact mode: WEDGE edge solved at every evaluation */
        WE = getenv("WEDGE") ? atoi(getenv("WEDGE")) : -1;
        if (WE < 0 || WE >= E || fixed_[WE]) {   /* default: a non-tree edge alone in its parallel class, else the last one of the largest class */
            int bestsz = -1; WE = -1;
            for (int e = 0; e < E; e++) if (!fixed_[e]) {
                int sz = 0;
                for (int f = 0; f < E; f++) if (eu[f] == eu[e] && ew[f] == ew[e]) sz++;
                if (sz == 1) { WE = e; break; }
                if (sz >= bestsz) { bestsz = sz; WE = e; }
            }
        }
        if (nfree < 2) { fprintf(stderr, "need >= 2 free edges\n"); return 2; }
        return semi_main(freee, nfree, SECS, ITERS, T0, T1, OUT, gname);
    }
    if (!hasv) for (int i = 0; i < nfree; i++) volt[freee[i]] = rnd() % m;
    cur = total_cost(1L << 60);
    long best = cur; write_sol(OUT, best, gname);
    double t_start = now(), t_end = t_start + SECS;
    long it_total = 0; int run = 0;
    int bvolt[MAXE], beu[MAXE], bew[MAXE];
    memcpy(bvolt, volt, sizeof(int) * E); memcpy(beu, eu, sizeof(int) * E); memcpy(bew, ew, sizeof(int) * E);
    int INC = getenv("INC") ? atoi(getenv("INC")) : 0;
    double FOCUS = getenv("FOCUS") ? atof(getenv("FOCUS")) : 0;
    double GIBBS = getenv("GIBBS") ? atof(getenv("GIBBS")) : 0;
    if (INC) {
        if (SWAP > 0) { fprintf(stderr, "INC mode has no swap moves\n"); return 2; }
        base_dist();
        cur = inc_init();
        long chk = total_cost(1L << 60);
        if (chk != cur) { fprintf(stderr, "inc init mismatch %ld vs %ld\n", cur, chk); return 3; }
        best = cur;
        for (run = 1; best > 0 && now() < t_end; run++) {
            if (run > 1) { memcpy(volt, bvolt, sizeof(int) * E);
                for (int k = 0; k < 1 + nfree / 20; k++) { int e = freee[rnd() % nfree]; volt[e] = rnd() % m; }
                cur = inc_init(); }
            for (long it = 0; it < ITERS && best > 0; it++) {
                if ((it & 255) == 0 && now() > t_end) break;
                double T = T0 * pow(T1 / T0, (double)it / ITERS);
                int e = freee[rnd() % nfree], old, g = rnd() % m;
                if (GIBBS > 0 && rnd01() < GIBBS) {   /* heat bath on one edge: try every value */
                    static long dl[65536]; int o = volt[e]; long acc = 0; double wsum = 0;
                    for (int x = 0; x < m; x++) { if (x == o) { dl[x] = 0; continue; } dl[x] = inc_move(e, x); inc_move(e, o); }
                    long mn = dl[0]; for (int x = 1; x < m; x++) if (dl[x] < mn) mn = dl[x];
                    for (int x = 0; x < m; x++) wsum += exp(-(dl[x] - mn) / T);
                    double r = rnd01() * wsum; int pick = m - 1;
                    for (int x = 0; x < m; x++) { r -= exp(-(dl[x] - mn) / T); if (r <= 0) { pick = x; break; } }
                    if (pick != o) { acc = inc_move(e, pick); cur += acc; }
                    it_total++;
                    if (cur < best) { best = cur; memcpy(bvolt, volt, sizeof(int) * E); write_sol(OUT, best, gname);
                        fprintf(stderr, "  t=%.1fs run %d it %ld best %ld\n", now() - t_start, run, it, best); }
                    continue;
                }
                if (FOCUS > 0 && rnd01() < FOCUS) { int fe, fg = focus_move(&fe); if (fg >= 0) { e = fe; g = fg; } }
                old = volt[e]; if (g == old) continue;
                long dlt = inc_move(e, g);
                if (dlt <= 0 || rnd01() < exp(-dlt / T)) cur += dlt; else inc_move(e, old);
                it_total++;
                if (cur < best) { best = cur; memcpy(bvolt, volt, sizeof(int) * E); write_sol(OUT, best, gname);
                    if (best < 50 || (it_total % 64) == 0) fprintf(stderr, "  t=%.1fs run %d it %ld best %ld\n", now() - t_start, run, it, best); }
            }
        }
        memcpy(volt, bvolt, sizeof(int) * E);
        long fin = total_cost(1L << 60);
        printf("RESULT best %ld check %ld b %d m %d vertices %ld iters %ld runs %d secs %.1f%s\n", best, fin, b, m,
               (long)b * m, it_total, run - 1, now() - t_start, fin == 0 ? " DIAMETER_OK" : "");
        return 0;
    }
    int TABU = getenv("TABU") ? atoi(getenv("TABU")) : 0;      /* tabu tenure (in steps) on edges; 0 = annealing */
    int SAMPLE = getenv("SAMPLE") ? atoi(getenv("SAMPLE")) : 0; /* moves sampled per tabu step; 0 = all */
    if (TABU > 0) {
        static long tabu_until[MAXE];
        long step = 0, since = 0;
        while (best > 0 && now() < t_end) {
            step++;
            long bc = 1L << 60; int be = -1, bg = -1, nties = 0;
            long nm = SAMPLE > 0 ? SAMPLE : (long)nfree * (m - 1);
            for (long k = 0; k < nm; k++) {
                int e, g;
                if (SAMPLE > 0) { e = freee[rnd() % nfree]; g = rnd() % m; if (g == volt[e]) continue; }
                else { e = freee[k / (m - 1)]; g = (int)(k % (m - 1)); if (g >= volt[e]) g++; }
                int old = volt[e]; volt[e] = g;
                long c = total_cost(bc);
                volt[e] = old;
                int ok = tabu_until[e] < step || c < best;
                if (!ok) continue;
                if (c < bc) { bc = c; be = e; bg = g; nties = 1; }
                else if (c == bc && (rnd() % (++nties)) == 0) { be = e; bg = g; }
            }
            if (be < 0) continue;
            volt[be] = bg; cur = bc; tabu_until[be] = step + TABU + rnd() % (TABU + 1);
            it_total++; since++;
            if (cur < best) { best = cur; since = 0; memcpy(bvolt, volt, sizeof(int) * E); write_sol(OUT, best, gname);
                fprintf(stderr, "  t=%.1fs step %ld best %ld\n", now() - t_start, step, best); }
            if (since > ITERS) {   /* restart from a perturbed best */
                memcpy(volt, bvolt, sizeof(int) * E);
                for (int k = 0; k < 1 + nfree / 5; k++) { int e = freee[rnd() % nfree]; volt[e] = rnd() % m; }
                cur = total_cost(1L << 60); since = 0; run++;
            }
        }
    }
    while (best > 0 && now() < t_end) {
        run++;
        if (run > 1) {   /* restart from best with a kick */
            memcpy(volt, bvolt, sizeof(int) * E); memcpy(eu, beu, sizeof(int) * E); memcpy(ew, bew, sizeof(int) * E);
            build_adj();
            int kick = 1 + nfree / 10;
            for (int k = 0; k < kick; k++) { int e = freee[rnd() % nfree]; volt[e] = rnd() % m; }
            cur = total_cost(1L << 60);
        }
        for (long it = 0; it < ITERS && best > 0; it++) {
            if ((it & 255) == 0 && now() > t_end) break;
            double T = T0 * pow(T1 / T0, (double)it / ITERS);
            double r = rnd01(); if (r < 1e-300) r = 1e-300;
            long limit = cur + (long)floor(-T * log(r));
            if (SWAP > 0 && rnd01() < SWAP) {
                int e1 = rnd() % E, e2 = rnd() % E;
                if (e1 == e2 || eu[e1] == eu[e2] || ew[e1] == ew[e2]) continue;
                int t = ew[e1]; ew[e1] = ew[e2]; ew[e2] = t; build_adj();
                if (!connected()) { t = ew[e1]; ew[e1] = ew[e2]; ew[e2] = t; build_adj(); continue; }
                long c = total_cost(limit);
                if (c <= limit) cur = c; else { t = ew[e1]; ew[e1] = ew[e2]; ew[e2] = t; build_adj(); }
            } else {
                int e = freee[rnd() % nfree], old = volt[e];
                int g = rnd() % m; if (g == old) continue;
                volt[e] = g;
                long c = total_cost(limit);
                if (c <= limit) cur = c; else volt[e] = old;
            }
            it_total++;
            if (cur < best) {
                best = cur;
                memcpy(bvolt, volt, sizeof(int) * E); memcpy(beu, eu, sizeof(int) * E); memcpy(bew, ew, sizeof(int) * E);
                write_sol(OUT, best, gname);
                fprintf(stderr, "  t=%.1fs run %d it %ld best %ld\n", now() - t_start, run, it, best);
            }
        }
    }
    memcpy(volt, bvolt, sizeof(int) * E); memcpy(eu, beu, sizeof(int) * E); memcpy(ew, bew, sizeof(int) * E); build_adj();
    long fin = total_cost(1L << 60);
    printf("RESULT best %ld check %ld b %d m %d vertices %ld iters %ld runs %d secs %.1f%s\n", best, fin, b, m,
           (long)b * m, it_total, run, now() - t_start, fin == 0 ? " DIAMETER_OK" : "");
    return 0;
}
