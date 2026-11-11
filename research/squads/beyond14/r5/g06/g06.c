/* g06: hole-directed tabu finisher for voltage lifts of cubic bipartite p+p base multigraphs (salift states).
   Usage: D=14 [START=f.best] [K=40] [STUCK=200] [TEN=5] ./g06 p GROUPS id seed seconds OUT
   Lift and cost exactly as salift_s (cost = #(base root u, lifted vertex x) with dist > D; 2p-source bit-parallel BFS).
   Each round: K candidates. A candidate picks a random uncovered pair (u, x = (v,g)), samples a random base walk
   u -> v of length <= D in which some edge e occurs exactly once, and sets a_e so the lifted walk ends at g.
   Half of the candidates first re-randomize another walk edge e2 (double move). Exact cost of each candidate;
   the best non-tabu candidate is applied even if worse (tabu on (edge, old value)). Output format = salift_s
   ("N id p cost" + 3p lines "u v a"), so build_lift_tab.py and apsp work. OUT.best on every improvement, OUT on cost 0. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

static int p, k, N, D = 14, *mul, *inv, ne;
static int eu[96], ev[96], ea[96];
static uint64_t *R, *R2;
static int *nbr;
static int *Uu, *Ux, nU;
static int *tabu;
static uint64_t rng = 88172645463325252ULL;
static inline uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static long cost(void) {
    for (int e = 0; e < ne; e++) for (int f = e + 1; f < ne; f++)
        if (eu[e] == eu[f] && ev[e] == ev[f] && ea[e] == ea[f]) return 1L << 40;
    int n = k * N, dg[64] = {0};
    static int dv[64][3], da[64][3];
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        dv[u][dg[u]] = v; da[u][dg[u]++] = ea[e]; dv[v][dg[v]] = u; da[v][dg[v]++] = inv[ea[e]]; }
    for (int u = 0; u < k; u++) for (int g = 0; g < N; g++) for (int j = 0; j < 3; j++)
        nbr[(u * N + g) * 3 + j] = dv[u][j] * N + mul[g * N + da[u][j]];
    memset(R, 0, 8L * n);
    for (int u = 0; u < k; u++) R[u * N] = 1ULL << u;
    for (int t = 0; t < D; t++) {
        for (int x = 0; x < n; x++) R2[x] = R[x] | R[nbr[3 * x]] | R[nbr[3 * x + 1]] | R[nbr[3 * x + 2]];
        uint64_t *tmp = R; R = R2; R2 = tmp;
    }
    uint64_t full = (1ULL << k) - 1; long c = 0;
    for (int x = 0; x < n; x++) c += __builtin_popcountll(~R[x] & full);
    return c;
}

/* uncovered pairs (root u, vertex x) from the R of the last cost() call */
static void uncovered(void) {
    int n = k * N; uint64_t full = (1ULL << k) - 1; nU = 0;
    for (int x = 0; x < n; x++) { uint64_t m = ~R[x] & full;
        while (m) { int u = __builtin_ctzll(m); Uu[nU] = u; Ux[nU] = x; nU++; m &= m - 1; } }
}

/* base adjacency: sl_e[u][j] edge index, sl_to[u][j] neighbour */
static int sl_e[64][3], sl_to[64][3], sl_dg[64];
static void build_adj(void) {
    memset(sl_dg, 0, sizeof sl_dg);
    for (int e = 0; e < ne; e++) { int u = eu[e], v = ev[e];
        sl_e[u][sl_dg[u]] = e; sl_to[u][sl_dg[u]++] = v;
        sl_e[v][sl_dg[v]] = e; sl_to[v][sl_dg[v]++] = u; }
}
/* lifted step label when walking from base vertex 'from' along edge e */
static inline int step_lab(int e, int from) { return from < p ? ea[e] : inv[ea[e]]; }

typedef struct { int L, e[40], from[40], to[40]; } walk_t;
static int sample_walk(int u, int v, int L, walk_t *w) {
    int cur = u; w->L = L;
    for (int t = 0; t < L; t++) { int j = xr() % 3;
        w->e[t] = sl_e[cur][j]; w->from[t] = cur; w->to[t] = sl_to[cur][j]; cur = sl_to[cur][j]; }
    return cur == v;
}
/* value for edge at walk position t so that the lifted walk from (u,0) ends at group element g */
static int solve_val(walk_t *w, int t, int g) {
    int s[40], pre[41], suf[41], L = w->L;
    for (int i = 0; i < L; i++) s[i] = step_lab(w->e[i], w->from[i]);
    pre[0] = 0; for (int i = 0; i < L; i++) pre[i + 1] = mul[pre[i] * N + s[i]];
    suf[L] = 0; for (int i = L - 1; i >= 0; i--) suf[i] = mul[s[i] * N + suf[i + 1]];
    int st = mul[mul[inv[pre[t]] * N + g] * N + inv[suf[t + 1]]];
    return w->from[t] < p ? st : inv[st];
}

static void write_state(const char *path, long c, int gid, int final) {
    FILE *f = fopen(path, "w"); if (!f) return;
    fprintf(f, "%d %d %d %ld\n", N, gid, p, c);
    for (int e = 0; e < ne; e++) fprintf(f, "%d %d %d\n", eu[e], ev[e], ea[e]);
    fclose(f); (void)final;
}

int main(int argc, char **argv) {
    if (argc < 7) { fprintf(stderr, "usage: D=14 [START=f.best] g06 p GROUPS id seed seconds OUT\n"); return 2; }
    p = atoi(argv[1]); k = 2 * p; int want = atoi(argv[3]);
    rng ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; xr(); xr();
    double secs = atof(argv[5]); const char *out = argv[6];
    int K = getenv("K") ? atoi(getenv("K")) : 40;
    int STUCK = getenv("STUCK") ? atoi(getenv("STUCK")) : 200;
    int TEN = getenv("TEN") ? atoi(getenv("TEN")) : 5;
    int EXH = getenv("EXH") ? atoi(getenv("EXH")) : 0;
    int FAILMAX = getenv("FAILMAX") ? atoi(getenv("FAILMAX")) : 30; int fails = 0;
    if (getenv("D")) D = atoi(getenv("D"));
    FILE *fg = fopen(argv[2], "r"); char tag[8], name[256]; int gid, found = 0;
    while (fscanf(fg, "%7s %d %d %255s", tag, &N, &gid, name) == 4) {
        mul = malloc(sizeof(int) * N * N);
        for (int i = 0; i < N * N; i++) if (fscanf(fg, "%d", &mul[i]) != 1) return 3;
        if (gid == want) { found = 1; break; }
        free(mul);
    }
    if (!found) { fprintf(stderr, "group not found\n"); return 2; }
    inv = malloc(sizeof(int) * N);
    for (int a = 0; a < N; a++) for (int b = 0; b < N; b++) if (mul[a * N + b] == 0) inv[a] = b;
    int n = k * N;
    R = malloc(8L * n); R2 = malloc(8L * n); nbr = malloc(sizeof(int) * 3 * n);
    Uu = malloc(sizeof(int) * n * k); Ux = malloc(sizeof(int) * n * k);
    tabu = malloc(sizeof(int) * 96 * N);
    for (int i = 0; i < 96 * N; i++) tabu[i] = -1;
    ne = 0;
    for (int m = 0; m < 3; m++) { int pm[32]; for (int i = 0; i < p; i++) pm[i] = i;
        for (int i = p - 1; i > 0; i--) { int j = xr() % (i + 1); int t = pm[i]; pm[i] = pm[j]; pm[j] = t; }
        for (int i = 0; i < p; i++) { eu[ne] = i; ev[ne] = p + pm[i]; ea[ne] = xr() % N; ne++; } }
    if (getenv("START")) { FILE *fs = fopen(getenv("START"), "r"); int sN, sg, sp; long sc; char hl[256];
        if (!fs || !fgets(hl, sizeof hl, fs) || sscanf(hl, "%d %d %d %ld", &sN, &sg, &sp, &sc) < 3 || sN != N || sp != p) { fprintf(stderr, "bad START\n"); return 2; }
        for (int e = 0; e < ne; e++) if (fscanf(fs, "%d %d %d", &eu[e], &ev[e], &ea[e]) != 3) { fprintf(stderr, "bad START\n"); return 2; }
        fclose(fs); }
    long c = cost();
    if (c >= (1L << 40)) { fprintf(stderr, "start state has parallel duplicate edges\n"); return 2; }
    long best = c; int beu[96], bev[96], bea[96];
    memcpy(beu, eu, sizeof eu); memcpy(bev, ev, sizeof ev); memcpy(bea, ea, sizeof ea);
    printf("group N=%d id=%d %s p=%d n=%d K=%d STUCK=%d TEN=%d start %ld\n", N, gid, name, p, n, K, STUCK, TEN, c); fflush(stdout);
    clock_t st = clock(); long rounds = 0, since = 0; int round_tag = 0;
    while (1) {
        double el = (double)(clock() - st) / CLOCKS_PER_SEC; if (el > secs) break;
        c = cost(); uncovered(); build_adj();
        int saved[96]; memcpy(saved, ea, sizeof ea);
        long bestc = 1L << 50; int bE = -1, bV = 0, bE2 = -1, bV2 = 0, ties = 0;
        static walk_t XW; static int XT = -1, XE = -1, XG = 0, XU = 0;
        if (EXH && rounds % 1 == 0) { /* exhaustive 2-opt on one hole: fix walk once per round, scan all values of e2 */
            int q = xr() % nU; int u = Uu[q], x = Ux[q], v = x / N, g = x % N; int ok = 0, pos[40], np = 0;
            for (int tries = 0; tries < 400 && !ok; tries++) {
                int L = 1 + xr() % D; if (!sample_walk(u, v, L, &XW)) continue;
                np = 0; for (int t = 0; t < L; t++) { int cnt = 0; for (int i = 0; i < L; i++) cnt += XW.e[i] == XW.e[t]; if (cnt == 1) pos[np++] = t; }
                int n2 = 0; for (int i = 0; i < L; i++) if (XW.e[i] != (np ? XW.e[pos[0]] : -9)) n2++;
                if (np && n2) ok = 1; }
            if (ok) { XT = pos[xr() % np]; XE = XW.e[XT]; XG = g; XU = 1; } else XU = 0;
        }
        for (int kk = 0; kk < (EXH ? N : K); kk++) {
            if (EXH) { if (!XU) break; }
            int q = xr() % nU; int u = Uu[q], x = Ux[q], v = x / N, g = x % N;
            walk_t w; int ok = 0, pos[40], np = 0;
            if (EXH) { w = XW; np = 0; for (int t = 0; t < w.L; t++) { int cnt = 0; for (int i = 0; i < w.L; i++) cnt += w.e[i] == w.e[t]; if (cnt == 1) pos[np++] = t; } ok = 1; }
            for (int tries = 0; tries < 400 && !ok; tries++) {
                int L = 1 + xr() % D;
                if (!sample_walk(u, v, L, &w)) continue;
                np = 0;
                for (int t = 0; t < L; t++) { int cnt = 0;
                    for (int i = 0; i < L; i++) cnt += w.e[i] == w.e[t];
                    if (cnt == 1) pos[np++] = t; }
                if (np) ok = 1;
            }
            if (!ok) continue;
            int t = EXH ? XT : pos[xr() % np], e = w.e[t], e2 = -1, v2 = 0;
            if (EXH) { e2 = -1; for (int i = 0; i < w.L && e2 < 0; i++) if (w.e[i] != e) e2 = w.e[i];
                v2 = kk; ea[e2] = v2; int val = solve_val(&w, t, g); ea[e] = val;
                long c2 = cost(); memcpy(ea, saved, sizeof ea);
                if (c2 < bestc) { bestc = c2; bE = e; bV = val; bE2 = e2; bV2 = v2; }
                if (c2 == 0) { bestc = 0; } continue; }
            if (xr() & 1) { int cand2[40], n2 = 0;
                for (int i = 0; i < w.L; i++) if (w.e[i] != e) cand2[n2++] = w.e[i];
                if (n2) { e2 = cand2[xr() % n2]; v2 = xr() % N; ea[e2] = v2; } }
            int val = solve_val(&w, t, g);
            ea[e] = val;
            long c2 = cost();
            memcpy(ea, saved, sizeof ea);
            if (c2 >= (1L << 40)) continue;
            /* tabu: forbidden unless it beats the best state ever */
            int isTabu = tabu[e * N + val] > rounds || (e2 >= 0 && tabu[e2 * N + v2] > rounds);
            if (isTabu && c2 >= best) continue;
            if (c2 < bestc) { bestc = c2; bE = e; bV = val; bE2 = e2; bV2 = v2; ties = 1; }
            else if (c2 == bestc && (xr() % (++ties)) == 0) { bE = e; bV = val; bE2 = e2; bV2 = v2; }
        }
        rounds++;
        if (EXH && getenv("TRACE")) { printf("  exh round %ld: min over 2-opt scan of one hole = %ld (cur %ld)\n", rounds, bestc, c); fflush(stdout); }
        if (getenv("TRACE") && rounds % 100 == 0) { printf("  r=%ld cur_after=%ld bestc=%ld nU=%d best=%ld\n", rounds, bestc, bestc, nU, best); fflush(stdout); }
        if (bE < 0 || bestc > c) { /* no sideways/improving candidate: count a failure, maybe kick */
            if (++fails < FAILMAX) continue;
            fails = 0; since = STUCK + 1; }
        else { fails = 0;
        /* apply best candidate (sideways or improving only) */
        tabu[bE * N + saved[bE]] = (int)rounds + TEN;
        if (bE2 >= 0) tabu[bE2 * N + saved[bE2]] = (int)rounds + TEN;
        ea[bE] = bV; if (bE2 >= 0) ea[bE2] = bV2;
        c = bestc;
        if (c < best) { best = c; since = 0;
            memcpy(beu, eu, sizeof eu); memcpy(bev, ev, sizeof ev); memcpy(bea, ea, sizeof ea);
            printf("t=%.1f round=%ld best %ld\n", el, rounds, best); fflush(stdout);
            char bp[600]; snprintf(bp, sizeof bp, "%s.best", out); write_state(bp, best, gid, 0);
            if (best == 0) { write_state(out, 0, gid, 1); printf("FOUND\n"); break; } }
        else since++; }
        if (since > STUCK) { /* kick: restart from best state with a random perturbation */
            since = 0; round_tag++;
            memcpy(eu, beu, sizeof eu); memcpy(ev, bev, sizeof ev); memcpy(ea, bea, sizeof ea);
            int i = xr() % ne, j = xr() % ne;
            if (round_tag & 1) { if (i != j && eu[i] != eu[j] && ev[i] != ev[j]) { int t = ev[i]; ev[i] = ev[j]; ev[j] = t; } }
            else { ea[i] = xr() % N; ea[j] = xr() % N; }
            c = cost();
            if (c >= (1L << 40)) { memcpy(eu, beu, sizeof eu); memcpy(ev, bev, sizeof ev); memcpy(ea, bea, sizeof ea); }
        }
    }
    printf("end best %ld rounds %ld\n", best, rounds);
    return 0;
}
