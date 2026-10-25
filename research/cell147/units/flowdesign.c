/* flowdesign.c: exact designs for many units on the polygon cover GH(q) + j matchings over Z_m (DGQ lift), by a
   max-flow between constraint types. Session cell-14-7 (second), 2026-10-24.

   A unit (p, t) with l = sigma_t(p) a line THROUGH p ("incident flag") deletes the lifted matching edges at p and adds
   hubs z ~ {(p,c)}, z' ~ {(l,c)}. Its endpoints keep eccentricity <= 7 if
     Y = {u : d(p,u) = 4, d(l,u) = 5}  (every line opposite l contains exactly one point of Y) maps into D4(l), and
     Z = {N : d(l,N) = 4, d(p,N) = 5}  (every point opposite p lies on exactly one line of Z) has preimages in D4(p),
   with no freed point in Y and no freed line in Z:  (p,0) -4- (u,0) -hop- (N,h) -1- (y,h)  and
   (l,h) -4- (sigma(u),h) -hop- (u,0) -1- (K,0) are routes of length 6 to every opposite element.
   For K units on one matching these are constraints on the bijection sigma_t: point u may go to line N iff
     Ymask(u) is contained in D4lmask(N)  and  Zmask(N) is contained in D4pmask(u).
   Points (and lines) with the same masks are interchangeable, so a sigma_t exists iff the transportation problem
   between point types and line types has a perfect flow (Dinic). The design is realized from the flow.

   Usage:
     flowdesign GHFILE STATE_IN UNITS_IN STATE_OUT UNITS_OUT [SEED]
        UNITS_IN: lines "p t l" (l must be a line through p). Fails (exit 1) if some matching has no design.
     flowdesign GHFILE STATE_IN greedy:J:KMAX:MODE STATE_OUT UNITS_OUT [SEED]
        adds random incident flags one at a time, on matchings 1..J alternately, keeping each one that leaves a design;
        MODE 0 random flags, 1 flags pairwise opposite within a matching, 2 freed points on one line per matching.
   Compile: gcc -O3 -march=native -o flowdesign flowdesign.c */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int P, q, Q1, J, m;
static int32_t *LP, *PL;            /* line -> points, point -> lines */
static int *sig, *hv;               /* sig[t*P+p] */
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }

static void bfs(int s, uint8_t *d, int *qu) {           /* s in 0..2P-1 (lines P..2P-1) */
    memset(d, 255, 2 * (size_t)P); int h = 0, t = 0; d[s] = 0; qu[t++] = s;
    while (h < t) { int x = qu[h++]; uint8_t dx = d[x];
        if (x < P) { for (int k = 0; k < Q1; k++) { int y = P + PL[x * Q1 + k]; if (d[y] == 255) { d[y] = dx + 1; qu[t++] = y; } } }
        else { int l = x - P; for (int k = 0; k < Q1; k++) { int y = LP[l * Q1 + k]; if (d[y] == 255) { d[y] = dx + 1; qu[t++] = y; } } } }
}

/* ---------- Dinic ---------- */
typedef struct { int to; long cap; int rev; } Edge;
static Edge *G; static int *gstart, *gcnt, NN, NE_; static int *lvl, *it_, *bq;
/* edges stored as a list, then CSR-ified */
static int *eu, *ev; static long *ec; static int ne_list;
static void add_edge(int u, int v, long c) { eu[ne_list] = u; ev[ne_list] = v; ec[ne_list] = c; ne_list++; }
static void build_csr(void) {
    gcnt = calloc(NN + 1, sizeof(int)); for (int i = 0; i < ne_list; i++) { gcnt[eu[i]]++; gcnt[ev[i]]++; }
    gstart = malloc(sizeof(int) * (NN + 1)); gstart[0] = 0; for (int i = 0; i < NN; i++) gstart[i + 1] = gstart[i] + gcnt[i];
    int *pos = calloc(NN, sizeof(int));
    for (int i = 0; i < ne_list; i++) { int u = eu[i], v = ev[i]; int a = gstart[u] + pos[u]++, b = gstart[v] + pos[v]++;
        G[a].to = v; G[a].cap = ec[i]; G[a].rev = b; G[b].to = u; G[b].cap = 0; G[b].rev = a; }
    free(pos);
    lvl = malloc(sizeof(int) * NN); it_ = malloc(sizeof(int) * NN); bq = malloc(sizeof(int) * NN);
}
static int dbfs(int s, int t) {
    for (int i = 0; i < NN; i++) lvl[i] = -1; int h = 0, tl = 0; lvl[s] = 0; bq[tl++] = s;
    while (h < tl) { int x = bq[h++]; for (int e = gstart[x]; e < gstart[x + 1]; e++) if (G[e].cap > 0 && lvl[G[e].to] < 0) { lvl[G[e].to] = lvl[x] + 1; bq[tl++] = G[e].to; } }
    return lvl[t] >= 0;
}
static long ddfs(int x, int t, long f) {
    if (x == t) return f;
    for (; it_[x] < gstart[x + 1]; it_[x]++) { Edge *e = &G[it_[x]];
        if (e->cap > 0 && lvl[e->to] == lvl[x] + 1) { long d = ddfs(e->to, t, f < e->cap ? f : e->cap);
            if (d > 0) { e->cap -= d; G[e->rev].cap += d; return d; } } }
    return 0;
}
static long maxflow(int s, int t) {
    long fl = 0; while (dbfs(s, t)) { for (int i = 0; i < NN; i++) it_[i] = gstart[i]; long f; while ((f = ddfs(s, t, 1L << 60)) > 0) fl += f; }
    return fl;
}
static void dinic_free(void) { free(G); free(gstart); free(gcnt); free(lvl); free(it_); free(bq); free(eu); free(ev); free(ec); }

/* ---------- one matching ---------- */
typedef struct { uint64_t a, b; int id; } Key;
static int cmpkey(const void *x, const void *y) { const Key *p = x, *r = y; if (p->a != r->a) return p->a < r->a ? -1 : 1; if (p->b != r->b) return p->b < r->b ? -1 : 1; return 0; }

static int nu; static int *up, *ut, *ul;     /* all units */
static uint8_t **dP, **dL;                   /* per unit: BFS distances from p_i and from l_i */
static int *qu;

/* design sigma_t for the units of matching t (indices in list[0..k-1]); returns deficit (0 = feasible).
   If realize, writes sigma_t. */
static long design(int t, int *list, int k, int realize, long *conflicts) {
    *conflicts = 0;
    char *fixP = calloc(P, 1), *fixL = calloc(P, 1);
    for (int a = 0; a < k; a++) { int i = list[a]; if (fixP[up[i]] || fixL[ul[i]]) { free(fixP); free(fixL); *conflicts = 1; return -1; } fixP[up[i]] = 1; fixL[ul[i]] = 1; }
    /* freed elements must not lie in other units' Y / Z (their hop is deleted) */
    for (int a = 0; a < k; a++) for (int b = 0; b < k; b++) if (a != b) {
        int i = list[a], j = list[b];
        if (dP[i][up[j]] == 4 && dL[i][up[j]] == 5) (*conflicts)++;
        if (dL[i][P + ul[j]] == 4 && dP[i][P + ul[j]] == 5) (*conflicts)++;
    }
    if (*conflicts) { free(fixP); free(fixL); return -1; }
    Key *kp = malloc(sizeof(Key) * P), *kl = malloc(sizeof(Key) * P); int np = 0, nl = 0;
    for (int u = 0; u < P; u++) { if (fixP[u]) continue; uint64_t y = 0, d = 0;
        for (int a = 0; a < k; a++) { int i = list[a]; if (dP[i][u] == 4) { d |= 1ULL << a; if (dL[i][u] == 5) y |= 1ULL << a; } }
        kp[np].a = y; kp[np].b = d; kp[np].id = u; np++; }
    for (int L = 0; L < P; L++) { if (fixL[L]) continue; uint64_t z = 0, d = 0;
        for (int a = 0; a < k; a++) { int i = list[a]; if (dL[i][P + L] == 4) { d |= 1ULL << a; if (dP[i][P + L] == 5) z |= 1ULL << a; } }
        kl[nl].a = z; kl[nl].b = d; kl[nl].id = L; nl++; }
    qsort(kp, np, sizeof(Key), cmpkey); qsort(kl, nl, sizeof(Key), cmpkey);
    /* types */
    int *pts = malloc(sizeof(int) * (np + 1)), *lts = malloc(sizeof(int) * (nl + 1)); int ntp = 0, ntl = 0;
    for (int x = 0; x < np; x++) if (x == 0 || cmpkey(&kp[x], &kp[x - 1])) pts[ntp++] = x; pts[ntp] = np;
    for (int x = 0; x < nl; x++) if (x == 0 || cmpkey(&kl[x], &kl[x - 1])) lts[ntl++] = x; lts[ntl] = nl;
    /* count allowed type pairs */
    long nedge = 0;
    for (int a = 0; a < ntp; a++) { uint64_t y = kp[pts[a]].a, d = kp[pts[a]].b;
        for (int b = 0; b < ntl; b++) { uint64_t z = kl[lts[b]].a, dl = kl[lts[b]].b; if (!(y & ~dl) && !(z & ~d)) nedge++; } }
    int S = ntp + ntl, T = S + 1;
    NN = T + 1; ne_list = 0; long maxe = nedge + ntp + ntl + 4;
    eu = malloc(sizeof(int) * maxe); ev = malloc(sizeof(int) * maxe); ec = malloc(sizeof(long) * maxe);
    G = malloc(sizeof(Edge) * (size_t)maxe * 2);
    for (int a = 0; a < ntp; a++) add_edge(S, a, pts[a + 1] - pts[a]);
    for (int b = 0; b < ntl; b++) add_edge(ntp + b, T, lts[b + 1] - lts[b]);
    for (int a = 0; a < ntp; a++) { uint64_t y = kp[pts[a]].a, d = kp[pts[a]].b;
        for (int b = 0; b < ntl; b++) { uint64_t z = kl[lts[b]].a, dl = kl[lts[b]].b; if (!(y & ~dl) && !(z & ~d)) add_edge(a, ntp + b, 1L << 40); } }
    build_csr();
    long fl = maxflow(S, T);
    long deficit = np - fl;
    if (realize) {
        for (int u = 0; u < P; u++) if (!fixP[u]) sig[t * P + u] = -1;
        int *pi = malloc(sizeof(int) * ntp), *li = malloc(sizeof(int) * ntl);
        for (int a = 0; a < ntp; a++) pi[a] = pts[a]; for (int b = 0; b < ntl; b++) li[b] = lts[b];
        /* shuffle members within types for randomness */
        for (int a = 0; a < ntp; a++) for (int x = pts[a + 1] - 1; x > pts[a]; x--) { int r = pts[a] + rndi(x - pts[a] + 1); Key tk = kp[x]; kp[x] = kp[r]; kp[r] = tk; }
        for (int b = 0; b < ntl; b++) for (int x = lts[b + 1] - 1; x > lts[b]; x--) { int r = lts[b] + rndi(x - lts[b] + 1); Key tk = kl[x]; kl[x] = kl[r]; kl[r] = tk; }
        for (int a = 0; a < ntp; a++) for (int e = gstart[a]; e < gstart[a + 1]; e++) {
            int b = G[e].to - ntp; if (b < 0 || b >= ntl) continue;
            long f = G[G[e].rev].cap;   /* flow on a->b */
            for (long c = 0; c < f; c++) { int u = kp[pi[a]++].id, L = kl[li[b]++].id; sig[t * P + u] = L; }
        }
        for (int a = 0; a < k; a++) { int i = list[a]; sig[t * P + up[i]] = ul[i]; }
        if (deficit) {   /* pair the leftovers at random */
            char *usedL = calloc(P, 1); for (int u = 0; u < P; u++) if (sig[t * P + u] >= 0) usedL[sig[t * P + u]] = 1;
            int *fp = malloc(sizeof(int) * P), *fl = malloc(sizeof(int) * P), nfp = 0, nfl = 0;
            for (int u = 0; u < P; u++) if (sig[t * P + u] < 0) fp[nfp++] = u;
            for (int L = 0; L < P; L++) if (!usedL[L]) fl[nfl++] = L;
            if (nfp != nfl) { fprintf(stderr, "internal error: leftovers %d %d\n", nfp, nfl); exit(3); }
            for (int x = nfl - 1; x > 0; x--) { int r = rndi(x + 1); int tt = fl[x]; fl[x] = fl[r]; fl[r] = tt; }
            for (int x = 0; x < nfp; x++) sig[t * P + fp[x]] = fl[x];
            free(usedL); free(fp); free(fl);
        }
        /* verify bijection */
        char *seen = calloc(P, 1); long bad = 0; for (int u = 0; u < P; u++) { int L = sig[t * P + u]; if (L < 0 || L >= P || seen[L]) bad++; else seen[L] = 1; }
        free(seen); if (bad) { fprintf(stderr, "internal error: sigma not a bijection (%ld)\n", bad); exit(3); }
        free(pi); free(li);
    }
    fprintf(stderr, "  matching %d: %d units, point types %d, line types %d, type edges %ld, flow %ld of %d (deficit %ld)\n",
            t + 1, k, ntp, ntl, nedge, fl, np, deficit);
    dinic_free(); free(kp); free(kl); free(pts); free(lts); free(fixP); free(fixL);
    return deficit;
}

static void add_unit(int p, int t, int l) {
    up[nu] = p; ut[nu] = t; ul[nu] = l;
    dP[nu] = malloc(2 * (size_t)P); bfs(p, dP[nu], qu);
    dL[nu] = malloc(2 * (size_t)P); bfs(P + l, dL[nu], qu);
    nu++;
}

int main(int argc, char **argv) {
    if (argc < 6) { fprintf(stderr, "usage: flowdesign GHFILE STATE_IN UNITS_IN|greedy:J:KMAX:MODE STATE_OUT UNITS_OUT [SEED]\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d %d", &P, &q) != 2) return 2; Q1 = q + 1;
    LP = malloc(sizeof(int32_t) * (size_t)P * Q1); PL = malloc(sizeof(int32_t) * (size_t)P * Q1);
    for (size_t i = 0; i < (size_t)P * Q1; i++) if (fscanf(f, "%d", &LP[i]) != 1) return 2;
    fclose(f);
    { int *c = calloc(P, sizeof(int)); for (int l = 0; l < P; l++) for (int k = 0; k < Q1; k++) { int p = LP[l * Q1 + k]; PL[p * Q1 + c[p]++] = l; } free(c); }
    if (argc > 6) rs ^= strtoull(argv[6], 0, 10) * 0x2545F4914F6CDD1DULL;
    char buf[256]; int dd;
    f = fopen(argv[2], "r"); if (!f || fscanf(f, "glift %d %d %d %d\n", &dd, &J, &m, &dd) != 4) { fprintf(stderr, "bad state\n"); return 2; }
    if (!fgets(buf, sizeof buf, f)) return 2;
    sig = malloc(sizeof(int) * (size_t)J * P); hv = malloc(sizeof(int) * (size_t)J * P);
    for (int p = 0; p < P; p++) for (int t = 0; t < J; t++) if (fscanf(f, "%d %d", &sig[t * P + p], &hv[t * P + p]) != 2) return 2;
    fclose(f);
    qu = malloc(sizeof(int) * 2 * P);
    int cap = 4096; up = malloc(sizeof(int) * cap); ut = malloc(sizeof(int) * cap); ul = malloc(sizeof(int) * cap);
    dP = malloc(sizeof(uint8_t *) * cap); dL = malloc(sizeof(uint8_t *) * cap); nu = 0;
    if (strncmp(argv[3], "greedy:", 7) == 0) {
        int JJ, KMAX, MODE; if (sscanf(argv[3] + 7, "%d:%d:%d", &JJ, &KMAX, &MODE) != 3) return 2;
        int *list = malloc(sizeof(int) * cap), tries = 0;
        int *lineM = malloc(sizeof(int) * J); for (int t = 0; t < J; t++) lineM[t] = rndi(P);
        uint8_t *tmp = malloc(2 * (size_t)P);
        int t = 0, fails = 0; long MAXDEF = getenv("MAXDEF") ? atol(getenv("MAXDEF")) : 0;
        while (nu < KMAX && fails < 60 * JJ) {
            tries++;
            int p, l;
            if (MODE == 2) { p = LP[lineM[t] * Q1 + rndi(Q1)]; l = PL[p * Q1 + rndi(Q1)]; }
            else { p = rndi(P); l = PL[p * Q1 + rndi(Q1)]; }
            int ok = 1;
            for (int i = 0; i < nu && ok; i++) if (ut[i] == t) {
                if (up[i] == p || ul[i] == l) ok = 0;
                if (MODE == 1 && (dP[i][p] != 6 || dL[i][P + l] != 6 || dP[i][P + l] != 5 || dL[i][p] != 5)) ok = 0;
            }
            if (!ok) { fails++; continue; }
            add_unit(p, t, l);
            int k = 0; for (int i = 0; i < nu; i++) if (ut[i] == t) list[k++] = i;
            long conf; long def = design(t, list, k, 0, &conf);
            if (def < 0 || def > MAXDEF) { nu--; free(dP[nu]); free(dL[nu]); fails++; fprintf(stderr, "  reject (deficit %ld, conflicts %ld)\n", def, conf); continue; }
            fprintf(stderr, "unit %d: p=%d t=%d l=%d accepted (%d on this matching)\n", nu - 1, p, t + 1, l, k);
            fails = 0; t = (t + 1) % JJ;
        }
        free(tmp);
    } else {
        f = fopen(argv[3], "r"); int a, b, c;
        while (f && fscanf(f, "%d %d %d", &a, &b, &c) == 3) add_unit(a, b - 1, c);
        if (f) fclose(f);
    }
    /* final designs */
    int *list = malloc(sizeof(int) * cap); long totdef = 0;
    for (int t = 0; t < J; t++) {
        int k = 0; for (int i = 0; i < nu; i++) if (ut[i] == t) { if (dP[i][P + ul[i]] != 1) { fprintf(stderr, "unit %d: l is not through p\n", i); return 1; } list[k++] = i; }
        if (!k) continue;
        long conf; long def = design(t, list, k, 1, &conf);
        if (def != 0) { fprintf(stderr, "matching %d: deficit %ld, conflicts %ld%s\n", t + 1, def, conf, getenv("MAXDEF") ? " (leftovers paired at random)" : ""); if (def < 0 || !getenv("MAXDEF")) totdef += def ? def : 1; }
    }
    if (totdef) return 1;
    f = fopen(argv[4], "w");
    fprintf(f, "glift %d %d %d 7\ncyc %d\n", q, J, m, m);
    for (int p = 0; p < P; p++) { for (int t = 0; t < J; t++) fprintf(f, "%s%d %d", t ? " " : "", sig[t * P + p], hv[t * P + p]); fprintf(f, "\n"); }
    for (int l = 0; l < P; l++) { for (int k = 0; k < Q1; k++) fprintf(f, k ? " 0" : "0"); fprintf(f, "\n"); }
    fclose(f);
    f = fopen(argv[5], "w"); for (int i = 0; i < nu; i++) fprintf(f, "%d %d %d\n", up[i], ut[i] + 1, ul[i]); fclose(f);
    fprintf(stderr, "wrote %d units\n", nu);
    return 0;
}
