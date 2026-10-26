/* Maximum independent set local search for the collinearity graph of W(11) (c3 card).
 * usage: mis MODE SEED SECONDS OUTFILE [K0]
 *   MODE = tabu : k-fixed tabu search on conflicts (k grows whenever an independent k-set is found)
 *   MODE = arw  : Andrade-Resende-Werneck ILS with (1,2)-swaps and forced-insertion perturbation
 * Input graph file (col_W11.txt): "n m" then m lines "u v" (0-based).
 * Writes the best independent set found (sorted indices) to OUTFILE, one index per line, and prints progress.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define MAXN 1500
#define MAXD 200
static int n, m;
static unsigned char A[MAXN][MAXN];
static int adj[MAXN][MAXD], deg[MAXN];
static unsigned long long rs = 88172645463325252ULL;
static inline unsigned long long rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndi(int k) { return (int)(rnd() % (unsigned long long)k); }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

static void load(const char *fn) {
    FILE *f = fopen(fn, "r");
    if (!f) { perror("graph"); exit(1); }
    if (fscanf(f, "%d %d", &n, &m) != 2) exit(1);
    for (int i = 0; i < m; i++) {
        int u, v;
        if (fscanf(f, "%d %d", &u, &v) != 2) exit(1);
        if (A[u][v]) continue;
        A[u][v] = A[v][u] = 1;
        adj[u][deg[u]++] = v; adj[v][deg[v]++] = u;
    }
    fclose(f);
}

static void save(const char *fn, const int *set, int cnt) {
    int *tmp = malloc(sizeof(int) * (cnt + 1)); int c = 0;
    for (int v = 0; v < n; v++) if (set[v]) tmp[c++] = v;
    FILE *f = fopen(fn, "w");
    for (int i = 0; i < c; i++) fprintf(f, "%d\n", tmp[i]);
    fclose(f); free(tmp);
}

static int check_indep(const int *inS) {
    for (int u = 0; u < n; u++) if (inS[u]) for (int j = 0; j < deg[u]; j++) if (inS[adj[u][j]]) return 0;
    return 1;
}

/* ---------------- k-fixed tabu search ---------------- */
static int tb_inS[MAXN], tb_conf[MAXN], tb_tin[MAXN], tb_tout[MAXN];
static int tb_S[MAXN], tb_pos[MAXN];
static int tb_k;

static void tb_add(int v) {
    tb_inS[v] = 1; tb_pos[v] = tb_k; tb_S[tb_k++] = v;
    for (int j = 0; j < deg[v]; j++) tb_conf[adj[v][j]]++;
}
static void tb_rem(int v) {
    tb_inS[v] = 0;
    int p = tb_pos[v]; tb_S[p] = tb_S[tb_k - 1]; tb_pos[tb_S[p]] = p; tb_k--;
    for (int j = 0; j < deg[v]; j++) tb_conf[adj[v][j]]--;
}

static int run_tabu(double secs, int seed_k, const char *out, long long *iters_out) {
    double t0 = now();
    memset(tb_inS, 0, sizeof tb_inS); memset(tb_conf, 0, sizeof tb_conf);
    memset(tb_tin, 0, sizeof tb_tin); memset(tb_tout, 0, sizeof tb_tout);
    tb_k = 0;
    int best = 0;
    /* start: random k-set */
    int k = seed_k;
    while (tb_k < k) { int v = rndi(n); if (!tb_inS[v]) tb_add(v); }
    long long it = 0, last_imp = 0;
    int cost = 0;
    for (int i = 0; i < tb_k; i++) cost += tb_conf[tb_S[i]];
    cost /= 2;
    while (now() - t0 < secs) {
        it++;
        if (cost == 0) {
            /* found independent set of size tb_k */
            if (tb_k > best) {
                best = tb_k;
                save(out, tb_inS, best);
                printf("best %d at %.1fs iter %lld\n", best, now() - t0, it); fflush(stdout);
                last_imp = it;
            }
            /* grow: add the outside vertex with min conflicts */
            int bv = -1, bc = 1 << 30, cnt = 0;
            for (int v = 0; v < n; v++) if (!tb_inS[v]) {
                if (tb_conf[v] < bc) { bc = tb_conf[v]; bv = v; cnt = 1; }
                else if (tb_conf[v] == bc && rndi(++cnt) == 0) bv = v;
            }
            tb_add(bv); cost += tb_conf[bv] - 0; /* conf[bv] counted before add */
            /* recompute cost exactly to avoid bookkeeping mistakes */
            cost = 0; for (int i = 0; i < tb_k; i++) cost += tb_conf[tb_S[i]]; cost /= 2;
            continue;
        }
        /* pick u in S with conf>0, non-tabu-out, maximizing conf (random tie) */
        int u = -1, bu = -1, cnt = 0;
        for (int i = 0; i < tb_k; i++) {
            int w = tb_S[i];
            if (tb_conf[w] == 0 || tb_tout[w] > it) continue;
            if (tb_conf[w] > bu) { bu = tb_conf[w]; u = w; cnt = 1; }
            else if (tb_conf[w] == bu && rndi(++cnt) == 0) u = w;
        }
        if (u < 0) { /* all conflicting vertices tabu: pick random conflicting */
            for (int i = 0; i < tb_k; i++) if (tb_conf[tb_S[i]]) { u = tb_S[i]; break; }
        }
        tb_rem(u);
        cost -= tb_conf[u] + 0; /* u's conflicts are not affected by removing u */
        /* recompute cheap: cost = sum conf over S / 2 handled below */
        /* pick v outside S, non-tabu-in, min conf (after u removed) */
        int v = -1, bv = 1 << 30; cnt = 0;
        for (int w = 0; w < n; w++) {
            if (tb_inS[w] || w == u) continue;
            if (tb_tin[w] > it) continue;
            int c = tb_conf[w];
            if (c < bv) { bv = c; v = w; cnt = 1; }
            else if (c == bv && rndi(++cnt) == 0) v = w;
        }
        if (v < 0) v = u;
        tb_add(v);
        tb_tin[u] = it + 7 + rndi(10);
        tb_tout[v] = it + rndi(3);
        cost = 0; for (int i = 0; i < tb_k; i++) cost += tb_conf[tb_S[i]]; cost /= 2;
        if (it - last_imp > 2000000) { /* random restart of k-set */
            while (tb_k > 0) tb_rem(tb_S[0]);
            memset(tb_tin, 0, sizeof tb_tin); memset(tb_tout, 0, sizeof tb_tout);
            int kk = best > 0 ? best : seed_k;
            while (tb_k < kk) { int x = rndi(n); if (!tb_inS[x]) tb_add(x); }
            cost = 0; for (int i = 0; i < tb_k; i++) cost += tb_conf[tb_S[i]]; cost /= 2;
            last_imp = it;
        }
    }
    *iters_out = it;
    return best;
}

/* ---------------- ARW iterated local search ---------------- */
static int ax_inS[MAXN], ax_tau[MAXN], ax_prev[MAXN];
static long long ax_age[MAXN];
static int ax_cur;

static void ax_ins(int v) { ax_inS[v] = 1; ax_cur++; for (int j = 0; j < deg[v]; j++) ax_tau[adj[v][j]]++; }
static void ax_del(int v) { ax_inS[v] = 0; ax_cur--; for (int j = 0; j < deg[v]; j++) ax_tau[adj[v][j]]--; }

static void ax_ls(long long it) {
    int improved;
    static int perm[MAXN], L[MAXD];
    do {
        improved = 0;
        for (int i = 0; i < n; i++) perm[i] = i;
        for (int i = n - 1; i > 0; i--) { int j = rndi(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        for (int i = 0; i < n; i++) { int v = perm[i]; if (!ax_inS[v] && ax_tau[v] == 0) { ax_ins(v); ax_age[v] = it; improved = 1; } }
        for (int i = 0; i < n; i++) perm[i] = i;
        for (int i = n - 1; i > 0; i--) { int j = rndi(i + 1); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        for (int ii = 0; ii < n; ii++) {
            int x = perm[ii];
            if (!ax_inS[x]) continue;
            int nl = 0;
            for (int j = 0; j < deg[x]; j++) if (ax_tau[adj[x][j]] == 1) L[nl++] = adj[x][j];
            if (nl < 2) continue;
            int fa = -1, fb = -1;
            for (int a = 0; a < nl && fa < 0; a++) for (int b = a + 1; b < nl; b++) if (!A[L[a]][L[b]]) { fa = L[a]; fb = L[b]; break; }
            if (fa >= 0) {
                ax_del(x); ax_ins(fa); ax_ins(fb);
                ax_age[x] = ax_age[fa] = ax_age[fb] = it;
                improved = 1;
                /* add any other free vertices in the neighbourhood of x immediately */
                for (int j = 0; j < deg[x]; j++) { int w = adj[x][j]; if (!ax_inS[w] && ax_tau[w] == 0) { ax_ins(w); ax_age[w] = it; } }
            }
        }
    } while (improved);
}

static int run_arw(double secs, const char *out, long long *iters_out) {
    double t0 = now();
    memset(ax_inS, 0, sizeof ax_inS); memset(ax_tau, 0, sizeof ax_tau); memset(ax_age, 0, sizeof ax_age);
    ax_cur = 0;
    ax_ls(0);
    int best = ax_cur;
    static int bestS[MAXN];
    memcpy(bestS, ax_inS, sizeof(int) * n);
    save(out, bestS, best);
    printf("best %d at %.1fs (init)\n", best, now() - t0); fflush(stdout);
    long long it = 0;
    while (now() - t0 < secs) {
        it++;
        memcpy(ax_prev, ax_inS, sizeof(int) * n);
        int prevsz = ax_cur;
        /* perturbation: force-insert k vertices, preferring old ones */
        int kk = 1;
        if (rndi(2 * (ax_cur + 1)) == 0) kk = 2 + rndi(3);
        for (int r = 0; r < kk; r++) {
            int v = -1; long long ba = 1LL << 62;
            for (int t = 0; t < 4; t++) {
                int w = rndi(n);
                if (ax_inS[w]) continue;
                if (ax_age[w] < ba) { ba = ax_age[w]; v = w; }
            }
            if (v < 0) continue;
            for (int j = 0; j < deg[v]; j++) { int u = adj[v][j]; if (ax_inS[u]) { ax_del(u); ax_age[u] = it; } }
            ax_ins(v); ax_age[v] = it;
        }
        ax_ls(it);
        if (ax_cur > best) {
            best = ax_cur;
            memcpy(bestS, ax_inS, sizeof(int) * n);
            save(out, bestS, best);
            printf("best %d at %.1fs iter %lld\n", best, now() - t0, it); fflush(stdout);
        }
        if (ax_cur < prevsz) {
            int delta = prevsz - ax_cur, dstar = best - ax_cur;
            /* accept worse with prob 1/(1 + delta*dstar) (ARW), otherwise revert */
            if (rndi(1000000) >= (int)(1000000.0 / (1.0 + (double)delta * (double)dstar))) {
                /* revert: remove vertices not in prev, then add vertices of prev not in current */
                for (int v = 0; v < n; v++) if (ax_inS[v] && !ax_prev[v]) ax_del(v);
                for (int v = 0; v < n; v++) if (!ax_inS[v] && ax_prev[v]) ax_ins(v);
            }
        }
    }
    *iters_out = it;
    return best;
}

int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: mis MODE SEED SECONDS OUTFILE [K0]\n"); return 1; }
    load(getenv("GRAPH") ? getenv("GRAPH") : "/home/user/degree-diameter/research/squads/gqd5-r1/c3/col_W11.txt");
    const char *mode = argv[1];
    rs ^= (unsigned long long)atoll(argv[2]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double secs = atof(argv[3]);
    const char *out = argv[4];
    long long iters = 0;
    int best;
    if (!strcmp(mode, "tabu")) {
        int k0 = argc > 5 ? atoi(argv[5]) : 60;
        best = run_tabu(secs, k0, out, &iters);
    } else {
        best = run_arw(secs, out, &iters);
    }
    /* verify the saved file */
    static int chk[MAXN]; memset(chk, 0, sizeof chk);
    FILE *f = fopen(out, "r"); int x, c = 0;
    while (fscanf(f, "%d", &x) == 1) { chk[x] = 1; c++; }
    fclose(f);
    printf("RESULT mode=%s seed=%s size=%d file_size=%d indep=%d iters=%lld\n", mode, argv[2], best, c, check_indep(chk), iters);
    return 0;
}
