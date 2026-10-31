/* t26.c (c26): tabu search for bipartite coset graphs of type "1,6|1,6" with ARBITRARY order-6 hub subgroups
 * (C6 or S3), so that the hub stabilisers may be non-cyclic (card c26; generalises c18's t18.c).
 * G acts by right multiplication. Vertices: A0 = G (x), A1 = G/H (coset Hx), B0 = G (y), B1 = G/K (coset Ky);
 * |H| = |K| = 6. Blocks (N = 5,1,1,0, the connected solution of the degree rule):
 *   S = {s1..s5}: A0-B0, A0 vertex x ~ B0 vertex s^-1 x (5 edges per A0 vertex);
 *   g01: A0-B1, x ~ coset K g01^-1 x (1 edge); the double coset is g01 K (6 elements);
 *   g10: A1-B0, coset Hx ~ y = (h g10)^-1 x for h in H (6 edges); the double coset is H g10;
 *   no A1-B1 block.
 * Degrees: A0 5+1, A1 6, B0 5+1, B1 6 (checked in build()). n = 2m + m/3 = 7m/3.
 * G acts transitively on each orbit, so diameter <= 5 iff the four representatives (vertex 0 of each orbit) reach all
 * vertices within 5 steps. cost = sum over the four representatives of the number of vertices at distance > 5.
 * usage: t26 TABLE SUBS HT KT SEED TLIM TENURE OUT
 *   TABLE: group table (first number m, then m rows of m entries; index 0 = identity; entry g*h).
 *   SUBS: subgroup file from c26/subs.g (first number = count, then lines "TYPE e1 .. e6").
 *   HT, KT: subgroup type of the hub stabilisers (C6 or S3). Env HIDX / KIDX: fixed start index; FIXHK=1 freezes H, K.
 *   Moves: one element of S, g01 or g10 replaced by any element; H or K replaced by another subgroup of its list.
 *   Writes OUT (edge list, n then "u v" lines) at every new best; stops when cost 0 (and prints CLAIM).
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <limits.h>

#define MAXM 1024
#define MAXS 128
#define MAXV 2600
static int m, T[MAXM * MAXM], inv_[MAXM];
#define MUL(x, y) T[(x) * m + (y)]
static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }

typedef struct { int n; int el[MAXS][6]; int cs[MAXS][MAXM]; int nc[MAXS]; int rep[MAXS][MAXM]; } SubSet;
static SubSet HS, KS;

static void coset_build(SubSet *ss, int s) {
    int *cs = ss->cs[s]; for (int x = 0; x < m; x++) cs[x] = -1;
    int c = 0;
    for (int x = 0; x < m; x++) if (cs[x] < 0) {
        ss->rep[s][c] = x;
        for (int j = 0; j < 6; j++) cs[MUL(ss->el[s][j], x)] = c;
        c++;
    }
    ss->nc[s] = c;
}
static int load_subs(const char *fn, const char *type, SubSet *ss) {
    FILE *f = fopen(fn, "r"); if (!f) { perror(fn); exit(1); }
    int cnt; if (fscanf(f, "%d", &cnt) != 1) exit(1);
    ss->n = 0;
    for (int i = 0; i < cnt; i++) {
        char tp[16]; int e[6];
        if (fscanf(f, "%15s", tp) != 1) exit(1);
        for (int j = 0; j < 6; j++) if (fscanf(f, "%d", &e[j]) != 1) exit(1);
        if (strcmp(tp, type) != 0 || ss->n >= MAXS) continue;
        /* check closure under the table */
        for (int a = 0; a < 6; a++) for (int b = 0; b < 6; b++) {
            int p = MUL(e[a], e[b]), ok = 0;
            for (int c = 0; c < 6; c++) if (e[c] == p) ok = 1;
            if (!ok) { fprintf(stderr, "subgroup not closed\n"); exit(1); }
        }
        for (int j = 0; j < 6; j++) ss->el[ss->n][j] = e[j];
        coset_build(ss, ss->n);
        ss->n++;
    }
    fclose(f);
    return ss->n;
}

/* state */
static int S[5], g01, g10, hI, kI;
static int fixhk = 0;

/* graph */
static int V, offA1, offB0, offB1, qH, qK;
static int adj[MAXV * 6], deg[MAXV], invalid;
static void add_edge(int a, int b) {
    if (deg[a] >= 6 || deg[b] >= 6) { invalid = 1; return; }
    adj[a * 6 + deg[a]++] = b; adj[b * 6 + deg[b]++] = a;
}
static int build(void) {
    qH = HS.nc[hI]; qK = KS.nc[kI];
    V = 2 * m + qH + qK; offA1 = m; offB0 = m + qH; offB1 = 2 * m + qH;
    for (int v = 0; v < V; v++) deg[v] = 0;
    invalid = 0;
    int ig = inv_[g01];
    for (int x = 0; x < m; x++) {
        for (int i = 0; i < 5; i++) add_edge(x, offB0 + MUL(inv_[S[i]], x));
        add_edge(x, offB1 + KS.cs[kI][MUL(ig, x)]);
    }
    for (int c = 0; c < qH; c++) {
        int x = HS.rep[hI][c];
        for (int j = 0; j < 6; j++) {
            int d = MUL(HS.el[hI][j], g10);
            add_edge(offA1 + c, offB0 + MUL(inv_[d], x));
        }
    }
    if (invalid) return 0;
    for (int v = 0; v < V; v++) if (deg[v] != 6) return 0;
    return 1;
}
/* all four representatives at once: bit r of mk[v] = representative r reaches v within the rounds done */
static uint8_t mkA[MAXV], mkB[MAXV];
static const int PC4[16] = {0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4};
static int eval(void) {
    if (!build()) return 1000000;
    uint8_t *cur = mkA, *nxt = mkB;
    for (int v = 0; v < V; v++) cur[v] = 0;
    cur[0] |= 1; cur[offA1] |= 2; cur[offB0] |= 4; cur[offB1] |= 8;
    for (int d = 0; d < 5; d++) {
        for (int v = 0; v < V; v++) {
            uint8_t x = cur[v];
            const int *a = &adj[v * 6];
            x |= cur[a[0]]; x |= cur[a[1]]; x |= cur[a[2]]; x |= cur[a[3]]; x |= cur[a[4]]; x |= cur[a[5]];
            nxt[v] = x;
        }
        uint8_t *t = cur; cur = nxt; nxt = t;
    }
    int c = 0;
    for (int v = 0; v < V; v++) c += 4 - PC4[cur[v]];
    return c;
}
static void write_graph(const char *fn) {
    if (!build()) { fprintf(stderr, "write: invalid state\n"); return; }
    FILE *f = fopen(fn, "w"); fprintf(f, "%d\n", V);
    for (int v = 0; v < V; v++) for (int i = 0; i < 6; i++) { int u = adj[v * 6 + i]; if (v < u) fprintf(f, "%d %d\n", v, u); }
    fclose(f);
}
static void print_state(FILE *f) {
    fprintf(f, "S");
    for (int i = 0; i < 5; i++) fprintf(f, " %d", S[i]);
    fprintf(f, " G01 %d G10 %d H %d K %d\n", g01, g10, hI, kI);
}

static int in_S(int e) { for (int i = 0; i < 5; i++) if (S[i] == e) return 1; return 0; }

/* move types: 0 = S[idx] := val, 1 = g01 := val, 2 = g10 := val, 3 = hI := val, 4 = kI := val */
static int eval_move(int type, int idx, int val) {
    int c;
    if (type == 0) { int o = S[idx]; S[idx] = val; c = eval(); S[idx] = o; }
    else if (type == 1) { int o = g01; g01 = val; c = eval(); g01 = o; }
    else if (type == 2) { int o = g10; g10 = val; c = eval(); g10 = o; }
    else if (type == 3) { int o = hI; hI = val; c = eval(); hI = o; }
    else { int o = kI; kI = val; c = eval(); kI = o; }
    return c;
}
static void apply_move(int type, int idx, int val) {
    if (type == 0) S[idx] = val; else if (type == 1) g01 = val; else if (type == 2) g10 = val;
    else if (type == 3) hI = val; else kI = val;
}

int main(int argc, char **argv) {
    if (argc < 9) { fprintf(stderr, "usage: t26 TABLE SUBS HT KT SEED TLIM TENURE OUT\n"); return 1; }
    FILE *f = fopen(argv[1], "r"); if (!f) { perror(argv[1]); return 1; }
    if (fscanf(f, "%d", &m) != 1) return 1;
    for (int i = 0; i < m * m; i++) if (fscanf(f, "%d", &T[i]) != 1) return 1;
    fclose(f);
    for (int x = 0; x < m; x++) for (int y = 0; y < m; y++) if (MUL(x, y) == 0) inv_[x] = y;
    int nh = load_subs(argv[2], argv[3], &HS);
    int nk = load_subs(argv[2], argv[4], &KS);
    if (nh == 0 || nk == 0) { fprintf(stderr, "no subgroups of the requested types\n"); return 1; }
    rs ^= (uint64_t)atoll(argv[5]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    double tlim = atof(argv[6]); int tenure = atoi(argv[7]); const char *out = argv[8];
    if (getenv("FIXHK")) fixhk = atoi(getenv("FIXHK"));
    const int PERT = 400;
    long long evals = 0;
    for (int i = 0; i < 5;) { int e = rnd() % m; if (!in_S(e)) S[i++] = e; }
    g01 = rnd() % m; g10 = rnd() % m;
    hI = rnd() % nh; kI = rnd() % nk;
    if (getenv("HIDX")) hI = atoi(getenv("HIDX")) % nh;
    if (getenv("KIDX")) kI = atoi(getenv("KIDX")) % nk;
    fprintf(stderr, "m=%d subsH=%d subsK=%d\n", m, nh, nk);
    int cur = eval(); evals++;
    int best = cur; int bS[5]; int bg01, bg10, bh, bk;
    memcpy(bS, S, sizeof S); bg01 = g01; bg10 = g10; bh = hI; bk = kI;
    long lastimp = 0;
    static long long tabS[MAXM], tab01[MAXM], tab10[MAXM], tabH[MAXS], tabK[MAXS];
    double t0 = now();
    long step;
    printf("start %d\n", cur); fflush(stdout);
    for (step = 1;; step++) {
        if (best == 0) break;
        if (now() - t0 > tlim) break;
        int bc = INT_MAX, nb = 0, mt = -1, mi = -1, mv = -1;
        for (int i = 0; i < 5; i++) {
            int old = S[i];
            for (int e = 0; e < m; e++) {
                if (e == old || in_S(e)) continue;
                int c = eval_move(0, i, e); evals++;
                int tb = (tabS[e] > step) && !(c < best);
                if (tb) continue;
                if (c < bc) { bc = c; nb = 1; mt = 0; mi = i; mv = e; }
                else if (c == bc && (rnd() % (++nb)) == 0) { mt = 0; mi = i; mv = e; }
            }
        }
        for (int e = 0; e < m; e++) {
            if (e == g01) continue;
            int c = eval_move(1, 0, e); evals++;
            if ((tab01[e] > step) && !(c < best)) continue;
            if (c < bc) { bc = c; nb = 1; mt = 1; mv = e; }
            else if (c == bc && (rnd() % (++nb)) == 0) { mt = 1; mv = e; }
        }
        for (int e = 0; e < m; e++) {
            if (e == g10) continue;
            int c = eval_move(2, 0, e); evals++;
            if ((tab10[e] > step) && !(c < best)) continue;
            if (c < bc) { bc = c; nb = 1; mt = 2; mv = e; }
            else if (c == bc && (rnd() % (++nb)) == 0) { mt = 2; mv = e; }
        }
        if (!fixhk) {
            for (int j = 0; j < nh; j++) {
                if (j == hI) continue;
                int c = eval_move(3, 0, j); evals++;
                if ((tabH[j] > step) && !(c < best)) continue;
                if (c < bc) { bc = c; nb = 1; mt = 3; mv = j; }
                else if (c == bc && (rnd() % (++nb)) == 0) { mt = 3; mv = j; }
            }
            for (int j = 0; j < nk; j++) {
                if (j == kI) continue;
                int c = eval_move(4, 0, j); evals++;
                if ((tabK[j] > step) && !(c < best)) continue;
                if (c < bc) { bc = c; nb = 1; mt = 4; mv = j; }
                else if (c == bc && (rnd() % (++nb)) == 0) { mt = 4; mv = j; }
            }
        }
        if (mt < 0) continue;
        /* apply, set tabu on the value that was removed */
        if (mt == 0) { tabS[S[mi]] = step + tenure; S[mi] = mv; }
        else if (mt == 1) { tab01[g01] = step + tenure; g01 = mv; }
        else if (mt == 2) { tab10[g10] = step + tenure; g10 = mv; }
        else if (mt == 3) { tabH[hI] = step + tenure; hI = mv; }
        else { tabK[kI] = step + tenure; kI = mv; }
        cur = eval(); evals++;
        if (cur < best) {
            best = cur; memcpy(bS, S, sizeof S); bg01 = g01; bg10 = g10; bh = hI; bk = kI; lastimp = step;
            printf("best %d step %ld t %.1f S", best, step, now() - t0);
            for (int i = 0; i < 5; i++) printf(" %d", S[i]);
            printf(" G01 %d G10 %d H %d K %d\n", g01, g10, hI, kI); fflush(stdout);
            write_graph(out);
        }
        if (step - lastimp > PERT) {
            /* perturbation: two random slot changes from the best state */
            memcpy(S, bS, sizeof S); g01 = bg01; g10 = bg10; hI = bh; kI = bk;
            for (int r = 0; r < 2; r++) {
                int i = rnd() % 5; int e = rnd() % m; if (!in_S(e)) S[i] = e;
            }
            cur = eval(); evals++;
            lastimp = step;
        }
    }
    /* final: restore best state and write */
    memcpy(S, bS, sizeof S); g01 = bg01; g10 = bg10; hI = bh; kI = bk;
    int fc = eval();
    printf("RESULT %d steps %ld evals %lld time %.1f check %d\n", best, step, evals, now() - t0, fc);
    write_graph(out);
    if (best == 0) printf("CLAIM cost 0 with n=%d\n", V);
    return 0;
}
