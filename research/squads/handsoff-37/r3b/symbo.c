/* r3b: focused breakout local search over G-invariant cubic bipartite graphs (orbit 2-switches).
 * Same move set and group file format as r2f/symloc.c. Cost: weighted far. For every orbit representative r and
 * every same-side vertex v at distance > 6 from r ("violated pair" (r,v)), the cost adds W[r][v] (times orbit size).
 * Each step: pick a random violated pair; sample K orbit 2-switches whose removed edges lie near r or v (radius 3,
 * with prob PF; otherwise anywhere); keep the best non-tabu candidate. If no candidate lowers the weighted cost (local
 * minimum), all violated pairs get W += BUMP (breakout), and the best candidate is applied anyway (walk).
 * Tabu: an edge removed at iteration it may not be re-added before it + TEN (aspiration if it beats the raw best).
 * usage: symbo GROUP GRAPH SECONDS SEED OUTPREFIX [K=40] [TEN=10] [PF=0.7] [BUMP=1] [WCAP=1000000]
 * writes OUTPREFIX_best.edges on every new best raw far (raw far = unordered same-side pairs at distance > 6).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 400
#define MAXG 64
int n, ng, half;
int G[MAXG][MAXN];
int adj[MAXN][3];
int side[MAXN];
int nrep, rep[MAXN], wrep[MAXN];
int Alist[MAXN], nA;
int Vs[2][MAXN], nVs[2];
int W[MAXN][MAXN];            /* [rep index][target vertex] */
int Rv[MAXG * 2][2], nR;
int Av[MAXG * 2][2], nAe;
int stamp[MAXN], gen = 1;
int dq[MAXN], dd[MAXN];
int tabu_until[MAXN * MAXN];
unsigned long long rs;

#define MAXV 20000
int vr[MAXV], vv[MAXV], nviol;

static unsigned long long rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double rnd01(void) { return (rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static int rndint(int m) { return (int)(rnd64() % (unsigned long long)m); }

static int has_edge(int a, int b) {
    for (int i = 0; i < 3; i++) if (adj[a][i] == b) return 1;
    return 0;
}

/* raw far (unordered same-side pairs at distance > 6, summed with orbit weights) and weighted cost wc.
 * if list != 0, fills vr/vv with the violated (rep index, vertex) pairs (once per rep orbit, not weighted). */
static void evaluate(long long *raw, long long *wc, int list) {
    long long tot = 0, wtot = 0;
    nviol = 0;
    for (int r = 0; r < nrep; r++) {
        int s = rep[r];
        gen++;
        int head = 0, tail = 0;
        dq[tail++] = s; stamp[s] = gen; dd[s] = 0;
        while (head < tail) {
            int x = dq[head++];
            if (dd[x] >= 6) continue;
            for (int i = 0; i < 3; i++) {
                int y = adj[x][i];
                if (stamp[y] != gen) { stamp[y] = gen; dd[y] = dd[x] + 1; dq[tail++] = y; }
            }
        }
        int sd = side[s];
        long long bad = 0, wb = 0;
        for (int i = 0; i < nVs[sd]; i++) {
            int v = Vs[sd][i];
            if (stamp[v] != gen) {
                bad++; wb += W[r][v];
                if (list && nviol < MAXV) { vr[nviol] = r; vv[nviol] = v; nviol++; }
            }
        }
        tot += (long long)wrep[r] * bad;
        wtot += (long long)wrep[r] * wb;
    }
    *raw = tot / 2;
    *wc = wtot;
}

/* validity of the collected move (Rv removed, Av added): removed edges exist, added edges are new or removed,
 * no loops, every vertex keeps degree 3 */
static int finish_move(void) {
    static int delta[MAXN];
    static int touched[MAXN * 2 + 8], nt;
    nt = 0;
    int ok = 1;
    for (int i = 0; i < nR && ok; i++) if (!has_edge(Rv[i][0], Rv[i][1])) ok = 0;
    for (int i = 0; i < nR && ok; i++) {
        int a = Rv[i][0], b = Rv[i][1];
        if (delta[a] == 0) touched[nt++] = a;
        delta[a]--;
        if (delta[b] == 0) touched[nt++] = b;
        delta[b]--;
    }
    for (int i = 0; i < nAe && ok; i++) {
        int a = Av[i][0], b = Av[i][1];
        int inR = 0;
        for (int j = 0; j < nR; j++) if (Rv[j][0] == a && Rv[j][1] == b) { inR = 1; break; }
        if (a == b || (has_edge(a, b) && !inR)) { ok = 0; break; }
        if (delta[a] == 0) touched[nt++] = a;
        delta[a]++;
        if (delta[b] == 0) touched[nt++] = b;
        delta[b]++;
    }
    for (int i = 0; i < nt && ok; i++) if (delta[touched[i]] != 0) ok = 0;
    for (int i = 0; i < nt; i++) delta[touched[i]] = 0;
    return ok;
}

/* build the orbit switch removing (x,y),(z,w) (x,z in A) and adding (x,w),(z,y) on every G-image */
static int build_move(int x, int y, int z, int w) {
    nR = 0; nAe = 0;
    for (int g = 0; g < ng; g++) {
        int pairs[2][2] = { {G[g][x], G[g][y]}, {G[g][z], G[g][w]} };
        for (int p = 0; p < 2; p++) {
            int a = pairs[p][0], b = pairs[p][1];
            if (side[a] != 0) { int t = a; a = b; b = t; }
            int dup = 0;
            for (int i = 0; i < nR; i++) if (Rv[i][0] == a && Rv[i][1] == b) { dup = 1; break; }
            if (!dup) { Rv[nR][0] = a; Rv[nR][1] = b; nR++; }
        }
        int nw[2][2] = { {G[g][x], G[g][w]}, {G[g][z], G[g][y]} };
        for (int p = 0; p < 2; p++) {
            int a = nw[p][0], b = nw[p][1];
            if (side[a] != 0) { int t = a; a = b; b = t; }
            int dup = 0;
            for (int i = 0; i < nAe; i++) if (Av[i][0] == a && Av[i][1] == b) { dup = 1; break; }
            if (!dup) { Av[nAe][0] = a; Av[nAe][1] = b; nAe++; }
        }
    }
    return finish_move();
}

/* voltage move: remove the G-orbit of edge (x,p) and add the G-orbit of (x,y) (x in A, p, y in B) */
static int build_vmove(int x, int p, int y) {
    nR = 0; nAe = 0;
    for (int g = 0; g < ng; g++) {
        int a = G[g][x], b = G[g][p];
        if (side[a] != 0) { int t = a; a = b; b = t; }
        int dup = 0;
        for (int i = 0; i < nR; i++) if (Rv[i][0] == a && Rv[i][1] == b) { dup = 1; break; }
        if (!dup) { Rv[nR][0] = a; Rv[nR][1] = b; nR++; }
        a = G[g][x]; b = G[g][y];
        if (side[a] != 0) { int t = a; a = b; b = t; }
        dup = 0;
        for (int i = 0; i < nAe; i++) if (Av[i][0] == a && Av[i][1] == b) { dup = 1; break; }
        if (!dup) { Av[nAe][0] = a; Av[nAe][1] = b; nAe++; }
    }
    return finish_move();
}

static int saved_n, saved_v[MAXN * 2];
static int saved_adj[MAXN * 2][3];

static void apply_move(void) {
    int cnt = 0; static int mark[MAXN]; static int list[MAXN * 2]; int nl = 0;
    for (int i = 0; i < nR; i++) for (int p = 0; p < 2; p++) {
        int v = p ? Rv[i][1] : Rv[i][0];
        if (!mark[v]) { mark[v] = 1; list[nl++] = v; }
    }
    for (int i = 0; i < nAe; i++) for (int p = 0; p < 2; p++) {
        int v = p ? Av[i][1] : Av[i][0];
        if (!mark[v]) { mark[v] = 1; list[nl++] = v; }
    }
    for (int i = 0; i < nl; i++) { saved_v[cnt] = list[i]; memcpy(saved_adj[cnt], adj[list[i]], sizeof(adj[0])); cnt++; mark[list[i]] = 0; }
    saved_n = cnt;
    for (int i = 0; i < nR; i++) {
        int a = Rv[i][0], b = Rv[i][1];
        for (int j = 0; j < 3; j++) if (adj[a][j] == b) { adj[a][j] = -1; break; }
        for (int j = 0; j < 3; j++) if (adj[b][j] == a) { adj[b][j] = -1; break; }
    }
    for (int i = 0; i < nAe; i++) {
        int a = Av[i][0], b = Av[i][1];
        for (int j = 0; j < 3; j++) if (adj[a][j] == -1) { adj[a][j] = b; break; }
        for (int j = 0; j < 3; j++) if (adj[b][j] == -1) { adj[b][j] = a; break; }
    }
}

static void undo_move(void) {
    for (int i = 0; i < saved_n; i++) memcpy(adj[saved_v[i]], saved_adj[i], sizeof(adj[0]));
}

static void write_graph(const char *fn) {
    FILE *f = fopen(fn, "w");
    if (!f) return;
    fprintf(f, "%d\n", n);
    for (int a = 0; a < n; a++) if (side[a] == 0)
        for (int j = 0; j < 3; j++) fprintf(f, "%d %d\n", a, adj[a][j]);
    fclose(f);
}

/* collect A-vertices within distance R of s or t in the current graph (distinct, at most MAXN) */
static int fseen[MAXN], fgen = 1;
static int focus_set(int s, int t, int R, int *out) {
    int cnt = 0;
    int srcs[2] = { s, t };
    static int qs[MAXN], dl[MAXN];
    for (int q = 0; q < 2; q++) {
        fgen++;
        int qh = 0, qt = 0;
        qs[qt++] = srcs[q]; fseen[srcs[q]] = fgen; dl[srcs[q]] = 0;
        while (qh < qt) {
            int x = qs[qh++];
            if (side[x] == 0) {
                int dup = 0;
                for (int i = 0; i < cnt; i++) if (out[i] == x) { dup = 1; break; }
                if (!dup) out[cnt++] = x;
            }
            if (dl[x] >= R) continue;
            for (int i = 0; i < 3; i++) {
                int y = adj[x][i];
                if (fseen[y] != fgen) { fseen[y] = fgen; dl[y] = dl[x] + 1; qs[qt++] = y; }
            }
        }
    }
    return cnt;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: symbo GROUP GRAPH SECONDS SEED OUTPREFIX [K TEN PF BUMP WCAP PV]\n"); return 1; }
    int K = argc > 6 ? atoi(argv[6]) : 40;
    int TEN = argc > 7 ? atoi(argv[7]) : 10;
    double PF = argc > 8 ? atof(argv[8]) : 0.7;
    int BUMP = argc > 9 ? atoi(argv[9]) : 1;
    int WCAP = argc > 10 ? atoi(argv[10]) : 1000000;
    double PV = argc > 11 ? atof(argv[11]) : 0.5;
    FILE *f = fopen(argv[1], "r");
    if (!f) { fprintf(stderr, "no group file\n"); return 1; }
    if (fscanf(f, "%d %d", &n, &ng) != 2) return 1;
    for (int g = 0; g < ng; g++) for (int v = 0; v < n; v++) if (fscanf(f, "%d", &G[g][v]) != 1) return 1;
    for (int v = 0; v < n; v++) if (fscanf(f, "%d", &side[v]) != 1) return 1;
    fclose(f);
    half = n / 2;
    double secs = atof(argv[3]);
    rs = 88172645463325252ULL ^ (unsigned long long)atoll(argv[4]) * 2654435761ULL;
    for (int i = 0; i < 10; i++) rnd64();
    const char *outp = argv[5];
    f = fopen(argv[2], "r");
    int nn; if (fscanf(f, "%d", &nn) != 1 || nn != n) { fprintf(stderr, "graph n mismatch\n"); return 1; }
    for (int v = 0; v < n; v++) for (int j = 0; j < 3; j++) adj[v][j] = -1;
    int deg[MAXN] = {0};
    int a, b;
    while (fscanf(f, "%d %d", &a, &b) == 2) { adj[a][deg[a]++] = b; adj[b][deg[b]++] = a; }
    fclose(f);
    for (int v = 0; v < n; v++) if (deg[v] != 3) { fprintf(stderr, "degree %d at %d\n", deg[v], v); return 1; }
    static int orb[MAXN];
    for (int v = 0; v < n; v++) orb[v] = -1;
    nrep = 0;
    for (int v = 0; v < n; v++) if (orb[v] < 0) {
        int sz = 0;
        for (int g = 0; g < ng; g++) { int w = G[g][v]; if (orb[w] < 0) { orb[w] = nrep; sz++; } }
        rep[nrep] = v; wrep[nrep] = sz; nrep++;
    }
    nA = 0; nVs[0] = nVs[1] = 0;
    for (int v = 0; v < n; v++) { Vs[side[v]][nVs[side[v]]++] = v; if (side[v] == 0) Alist[nA++] = v; }
    for (int r = 0; r < nrep; r++) for (int v = 0; v < n; v++) W[r][v] = 1;
    for (int i = 0; i < MAXN * MAXN; i++) tabu_until[i] = -1;

    long long raw, wc;
    evaluate(&raw, &wc, 1);
    long long best_raw = raw;
    fprintf(stderr, "group %d reps %d start raw far %lld wc %lld\n", ng, nrep, raw, wc);
    char fn[512]; sprintf(fn, "%s_best.edges", outp);
    write_graph(fn);
    time_t t0 = time(NULL);
    long long nbumps = 0, nwalk = 0, nimp = 0, neval = 0;
    static int fset[MAXN];
    for (int it = 0; it < 100000000; it++) {
        if (raw == 0) break;
        if ((it & 63) == 0 && difftime(time(NULL), t0) > secs) break;
        if (nviol == 0) break;
        int pi = rndint(nviol);
        int r = vr[pi], v = vv[pi];
        int s = rep[r];
        int nf = focus_set(s, v, 3, fset);
        if (nf < 2) nf = 0;
        long long best_c = -1; int bx = -1, by = -1, bz = -1, bw = -1, bt = 0; int bx_t = 0, bx_x = 0, bx_y = 0, bx_z = 0, bx_w = 0;
        for (int k = 0; k < K; k++) {
            int x, z;
            int isv = rnd01() < PV;
            if (nf > 0 && rnd01() < PF) x = fset[rndint(nf)];
            else x = Alist[rndint(nA)];
            int y = adj[x][rndint(3)];
            if (isv) {
                /* voltage move: the G-orbit of (x,y) is replaced by the orbit of (x, G[h][y]) */
                int hh = rndint(ng);
                int y2 = G[hh][y];
                if (y2 == y || has_edge(x, y2)) continue;
                if (!build_vmove(x, y, y2)) continue;
                bx_t = 1; bx_x = x; bx_y = y; bx_z = y2; bx_w = -1;
            } else {
                if (nf > 0 && rnd01() < PF) z = fset[rndint(nf)];
                else z = Alist[rndint(nA)];
                int w = adj[z][rndint(3)];
                if (x == z || y == w) continue;
                if (!build_move(x, y, z, w)) continue;
                bx_t = 0; bx_x = x; bx_y = y; bx_z = z; bx_w = w;
            }
            int tabu = 0;
            for (int i = 0; i < nAe && !tabu; i++) if (tabu_until[Av[i][0] * n + Av[i][1]] > it) tabu = 1;
            apply_move();
            long long cr, cw;
            evaluate(&cr, &cw, 0);
            neval++;
            undo_move();
            if (cw > WCAP) cw = WCAP;
            if (tabu && cr >= best_raw) continue;
            if (best_c < 0 || cw < best_c) { best_c = cw; bt = bx_t; bx = bx_x; by = bx_y; bz = bx_z; bw = bx_w; }
        }
        if (best_c < 0) { /* no candidate: bump and retry */
            for (int i = 0; i < nviol; i++) if (W[vr[i]][vv[i]] < WCAP) W[vr[i]][vv[i]] += BUMP;
            nbumps++;
            evaluate(&raw, &wc, 1);
            continue;
        }
        long long cur_wc = wc;
        if (best_c >= cur_wc) { /* local minimum of weighted cost: breakout */
            for (int i = 0; i < nviol; i++) if (W[vr[i]][vv[i]] < WCAP) W[vr[i]][vv[i]] += BUMP;
            nbumps++;
            nwalk++;
        } else nimp++;
        if (!(bt ? build_vmove(bx, by, bz) : build_move(bx, by, bz, bw))) { evaluate(&raw, &wc, 1); continue; }
        /* tabu: edges removed now may not be re-added for TEN iterations */
        for (int i = 0; i < nR; i++) tabu_until[Rv[i][0] * n + Rv[i][1]] = it + TEN;
        apply_move();
        evaluate(&raw, &wc, 1);
        if (raw < best_raw) {
            best_raw = raw;
            write_graph(fn);
            fprintf(stderr, "it %d t %.0fs NEW BEST raw far %lld (wc %lld, bumps %lld, walks %lld)\n", it,
                    difftime(time(NULL), t0), best_raw, wc, nbumps, nwalk);
        }
        if ((it % 2000) == 0)
            fprintf(stderr, "it %d t %.0fs raw %lld wc %lld best %lld viol %d bumps %lld walks %lld imp %lld evals %lld\n",
                    it, difftime(time(NULL), t0), raw, wc, best_raw, nviol, nbumps, nwalk, nimp, neval);
    }
    fprintf(stderr, "done best %lld raw %lld evals %lld bumps %lld time %.0fs\n", best_raw, raw, neval, nbumps,
            difftime(time(NULL), t0));
    printf("%lld\n", best_raw);
    return 0;
}
