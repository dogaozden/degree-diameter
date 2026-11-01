/* bicos: bi-coset graphs (handsoff-49, worker w7).
 * Group table file (groups.py format): int32 N, then N*N uint16, T[a*N+b] = a*b, identity = index 0.
 * H = <GENS> a subgroup of order h. Vertices: A = right cosets Hg, B = right cosets Hk (M = N/h each).
 * S = HSH, a union of double cosets with sum of k_D = 4 (k_D = |HsH|/h). Edge: Hg ~ Hk iff k g^-1 in S.
 * Simple, 4-regular, bipartite, n = 2M. G acts on the right, transitively on each side: two BFS suffice.
 * Cost C = aFar + bFarB + 2 bFarA (far = distance > 9 or unreachable); C = 0 iff diameter <= 9.
 *
 * Usage:
 *   bicos TABLE classes                          conjugacy classes of elements of order 2 and 3
 *   bicos TABLE info GENS                        double-coset counts by k
 *   bicos TABLE exh GENS COMP [LIMIT] [OUT]      exhaustive over S with k-composition COMP (e.g. 1,1,1,1 or 1,2 or 2,2 or 1,3 or 4)
 *   bicos TABLE sa GENS COMP SECONDS SEED [OUT]  simulated annealing (env T0, T1 = start/end temperature)
 * GENS: comma list of element indices. OUT: edge list (first line n = 2M) of the best S.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define DIAM 9
static int N, M, hH;
static uint16_t *T;
static int *invE, *Hel, *cid, *crep, *dcid;
static int ndc, *dck, *dcinv, *dcsize, **dcrep;
static int *nbA, *nbB, *dist, *queue;
static int sList[8], tList[8];
static int ncand[8], *cand[8];

static uint64_t rng = 88172645463325252ULL;
static uint64_t xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }
static double urand(void) { return (xr() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }
static void die(const char *m) { fprintf(stderr, "bicos: %s\n", m); exit(1); }

static void load(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) die("cannot open table");
    int32_t n;
    if (fread(&n, 4, 1, f) != 1) die("read N");
    N = n;
    T = malloc((size_t)N * N * 2);
    if (!T || fread(T, 2, (size_t)N * N, f) != (size_t)N * N) die("short table");
    fclose(f);
    invE = malloc(N * sizeof(int));
    for (int g = 0; g < N; g++) {
        invE[g] = -1;
        for (int h = 0; h < N; h++) if (T[(size_t)g * N + h] == 0) { invE[g] = h; break; }
    }
}

static void make_H(int *gens, int ng) {
    char *in = calloc(N, 1);
    int *el = malloc(N * sizeof(int));
    int cnt = 0;
    in[0] = 1; el[cnt++] = 0;
    for (int i = 0; i < cnt; i++)
        for (int j = 0; j < ng; j++) {
            int x = T[(size_t)el[i] * N + gens[j]];
            if (!in[x]) { in[x] = 1; el[cnt++] = x; }
        }
    free(in);
    Hel = el; hH = cnt;
}

static void make_cosets(void) {
    cid = malloc(N * sizeof(int)); crep = malloc(N * sizeof(int));
    for (int i = 0; i < N; i++) cid[i] = -1;
    M = 0;
    for (int g = 0; g < N; g++) if (cid[g] < 0) {
        for (int a = 0; a < hH; a++) cid[T[(size_t)Hel[a] * N + g]] = M;
        crep[M++] = g;
    }
    if (M * hH != N) die("coset count");
}

static void make_dcosets(void) {
    dcid = malloc(N * sizeof(int));
    for (int i = 0; i < N; i++) dcid[i] = -1;
    int *mark = malloc(M * sizeof(int));
    for (int i = 0; i < M; i++) mark[i] = -1;
    int *elems = malloc(N * sizeof(int));
    dck = malloc(N * sizeof(int)); dcsize = malloc(N * sizeof(int)); dcrep = malloc(N * sizeof(int *));
    dcinv = malloc(N * sizeof(int));
    ndc = 0;
    for (int s = 0; s < N; s++) if (dcid[s] < 0) {
        int ne = 0;
        for (int a = 0; a < hH; a++) {
            int t1 = T[(size_t)Hel[a] * N + s];
            for (int b = 0; b < hH; b++) {
                int t2 = T[(size_t)t1 * N + Hel[b]];
                if (dcid[t2] < 0) { dcid[t2] = ndc; elems[ne++] = t2; }
            }
        }
        int *reps = malloc(ne * sizeof(int)); int nr = 0;
        for (int e = 0; e < ne; e++) {
            int c = cid[elems[e]];
            if (mark[c] != ndc) { mark[c] = ndc; reps[nr++] = elems[e]; }
        }
        dcsize[ndc] = ne; dck[ndc] = nr; dcrep[ndc] = reps;
        ndc++;
    }
    for (int D = 0; D < ndc; D++) dcinv[D] = dcid[invE[dcrep[D][0]]];
    free(mark); free(elems);
    for (int k = 0; k < 8; k++) { ncand[k] = 0; cand[k] = malloc(ndc * sizeof(int)); }
    for (int D = 0; D < ndc; D++) if (dck[D] < 8) cand[dck[D]][ncand[dck[D]]++] = D;
}

static void setup(int *gens, int ng) {
    make_H(gens, ng);
    make_cosets();
    make_dcosets();
    nbA = malloc(4 * (size_t)M * sizeof(int));
    nbB = malloc(4 * (size_t)M * sizeof(int));
    dist = malloc(2 * (size_t)M * sizeof(int));
    queue = malloc(2 * (size_t)M * sizeof(int));
}

/* S = union of the double cosets sel[0..ns) (k-sum must be 4). Returns the cost; nbA/nbB hold the graph. */
static int evalS(const int *sel, int ns) {
    int nsv = 0, ntv = 0;
    for (int p = 0; p < ns; p++) {
        int D = sel[p];
        for (int r = 0; r < dck[D]; r++) sList[nsv++] = dcrep[D][r];
        int E = dcinv[D];
        for (int r = 0; r < dck[E]; r++) tList[ntv++] = dcrep[E][r];
    }
    if (nsv != 4 || ntv != 4) die("k-sum must be 4");
    for (int x = 0; x < M; x++) {
        int g = crep[x];
        for (int i = 0; i < 4; i++) nbA[4 * x + i] = cid[T[(size_t)sList[i] * N + g]];
    }
    for (int y = 0; y < M; y++) {
        int k = crep[y];
        for (int j = 0; j < 4; j++) nbB[4 * y + j] = cid[T[(size_t)tList[j] * N + k]];
    }
    /* BFS from the A-root (node 0) and from the B-root (node M), counting nodes within DIAM */
    int nearA0 = 0, nearB0 = 0, nearB1 = 0;
    for (int root = 0; root < 2; root++) {
        int r0 = root == 0 ? 0 : M;
        for (int v = 0; v < 2 * M; v++) dist[v] = -1;
        int head = 0, tail = 0;
        queue[tail++] = r0; dist[r0] = 0;
        int nA = 0, nB = 0;
        while (head < tail) {
            int v = queue[head++];
            int d = dist[v];
            if (v < M) {
                nA++;
                if (d >= DIAM) continue;
                for (int i = 0; i < 4; i++) {
                    int w = M + nbA[4 * v + i];
                    if (dist[w] < 0) { dist[w] = d + 1; queue[tail++] = w; }
                }
            } else {
                nB++;
                if (d >= DIAM) continue;
                int y = v - M;
                for (int j = 0; j < 4; j++) {
                    int w = nbB[4 * y + j];
                    if (dist[w] < 0) { dist[w] = d + 1; queue[tail++] = w; }
                }
            }
        }
        if (root == 0) { nearA0 = nA; nearB0 = nB; }
        else nearB1 = nB;
    }
    int aFar = M - nearA0, bFarA = M - nearB0, bFarB = M - nearB1;
    return aFar + bFarB + 2 * bFarA;
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) die("cannot write OUT");
    fprintf(f, "%d\n", 2 * M);
    for (int x = 0; x < M; x++)
        for (int i = 0; i < 4; i++) fprintf(f, "%d %d\n", x, M + nbA[4 * x + i]);
    fclose(f);
}

static int parse_gens(const char *s, int *gens) {
    int n = 0;
    char *c = strdup(s), *tok = strtok(c, ",");
    while (tok) { gens[n++] = atoi(tok); tok = strtok(NULL, ","); }
    free(c);
    return n;
}

static int parse_comp(const char *s, int *ks) {
    int n = 0, sum = 0;
    char *c = strdup(s), *tok = strtok(c, ",");
    while (tok) { ks[n] = atoi(tok); sum += ks[n]; n++; tok = strtok(NULL, ","); }
    free(c);
    if (sum != 4) die("composition k-sum must be 4");
    return n;
}

/* ---- exhaustive ---- */
static int nslots, slotk[8], slotidx[8], bestC;
static int bestSel[8];
static long long nevals;
static void rec(int p) {
    int sel[8];
    if (p == nslots) {
        for (int i = 0; i < nslots; i++) sel[i] = cand[slotk[i]][slotidx[i]];
        int C = evalS(sel, nslots);
        nevals++;
        if (C < bestC) { bestC = C; memcpy(bestSel, sel, sizeof sel); }
        return;
    }
    int k = slotk[p];
    int start = (p > 0 && slotk[p - 1] == k) ? slotidx[p - 1] + 1 : 0;
    for (int c = start; c < ncand[k]; c++) { slotidx[p] = c; rec(p + 1); }
}

static double binom(int n, int r) {
    if (r < 0 || r > n) return 0;
    double b = 1;
    for (int i = 0; i < r; i++) b = b * (n - i) / (i + 1);
    return b;
}

static double count_comp(int nsl, const int *ks) {
    double tot = 1;
    for (int k = 1; k < 8; k++) {
        int m = 0;
        for (int i = 0; i < nsl; i++) if (ks[i] == k) m++;
        if (m) tot *= binom(ncand[k], m);
    }
    return tot;
}

static void print_sol(const char *tag, int C, const int *sel, int ns) {
    printf("%s C=%d S=", tag, C);
    for (int p = 0; p < ns; p++) {
        int D = sel[p];
        printf("[k=%d:", dck[D]);
        for (int r = 0; r < dck[D]; r++) printf(" %d", dcrep[D][r]);
        printf("]");
    }
    printf("\n");
}

/* ---- annealing ---- */
static void anneal(double secs, double T0, double T1, const int *ks, int ns) {
    int sel[8];
    for (int p = 0; p < ns; p++) {
        int ok;
        do {
            ok = 1;
            sel[p] = cand[ks[p]][xr() % ncand[ks[p]]];
            for (int q = 0; q < p; q++) if (sel[q] == sel[p]) ok = 0;
        } while (!ok);
    }
    int cur = evalS(sel, ns), best = cur;
    int bsel[8]; memcpy(bsel, sel, sizeof sel);
    double t0 = now();
    long long it = 0;
    double Tt = T0;
    while (1) {
        if ((it & 1023) == 0) {
            double el = now() - t0;
            if (el >= secs) break;
            double fr = el / secs;
            Tt = T0 * pow(T1 / T0, fr);
        }
        it++;
        int p = xr() % ns;
        int k = ks[p];
        int nc = ncand[k];
        if (nc <= 1) continue;
        int c = cand[k][xr() % nc];
        int ok = 1;
        for (int q = 0; q < ns; q++) if (sel[q] == c) { ok = 0; break; }
        if (!ok) continue;
        int old = sel[p];
        sel[p] = c;
        int C = evalS(sel, ns);
        if (C <= cur || urand() < exp(-(C - cur) / Tt)) {
            cur = C;
            if (C < best) { best = C; memcpy(bsel, sel, sizeof sel); if (best == 0) break; }
        } else sel[p] = old;
    }
    nevals = it;
    printf("SA best C=%d evals=%lld secs=%.1f\n", best, it, now() - t0);
    bestC = best; memcpy(bestSel, bsel, sizeof bsel);
}

int main(int argc, char **argv) {
    if (argc < 3) die("usage: see source header");
    load(argv[1]);
    const char *mode = argv[2];
    if (!strcmp(mode, "classes")) {
        char *seen = calloc(N, 1);
        int cnt = 0;
        for (int t = 1; t < N; t++) if (!seen[t]) {
            /* order */
            int o = 1, x = t;
            while (x != 0) { x = T[(size_t)x * N + t]; o++; }
            if (o != 2 && o != 3) continue;
            int size = 0;
            for (int g = 0; g < N; g++) {
                int c = T[(size_t)T[(size_t)g * N + t] * N + invE[g]];
                if (!seen[c]) { seen[c] = 1; size++; }
            }
            printf("class rep=%d order=%d size=%d centralizer=%d\n", t, o, size, N / size);
            cnt++;
        }
        printf("N=%d classes_of_order_2_or_3=%d\n", N, cnt);
        return 0;
    }
    if (argc < 4) die("missing GENS");
    int gens[16];
    int ng = parse_gens(argv[3], gens);
    setup(gens, ng);
    if (!strcmp(mode, "info")) {
        int cnt[8] = {0};
        for (int D = 0; D < ndc; D++) if (dck[D] < 8) cnt[dck[D]]++;
        printf("N=%d h=%d M=%d n=%d double_cosets:", N, hH, M, 2 * M);
        for (int k = 1; k <= 4; k++) printf(" k%d=%d", k, cnt[k]);
        printf("\n");
        int c1[4] = {4, 0, 0, 0};
        (void)c1;
        printf("count S: {1,1,1,1}=%.0f {1,1,2}=%.0f {2,2}=%.0f {1,3}=%.0f {4}=%.0f\n",
               count_comp(4, (int[]){1, 1, 1, 1}), count_comp(3, (int[]){1, 1, 2}), count_comp(2, (int[]){2, 2}),
               count_comp(2, (int[]){1, 3}), count_comp(1, (int[]){4}));
        return 0;
    }
    if (!strcmp(mode, "elems")) {
        /* bicos TABLE elems GENS S1,S2,...  : evaluate the S generated by these elements (writes OUT if given) */
        int sel[8], ns = 0;
        char *c = strdup(argv[4]), *tok = strtok(c, ",");
        while (tok) {
            int s = atoi(tok), D = dcid[s], dup = 0;
            for (int q = 0; q < ns; q++) if (sel[q] == D) dup = 1;
            if (!dup) sel[ns++] = D;
            tok = strtok(NULL, ",");
        }
        free(c);
        int C = evalS(sel, ns);
        printf("ELEMS C=%d n=%d\n", C, 2 * M);
        if (argc > 5) write_edges(argv[5]);
        return 0;
    }
    if (argc < 5) die("missing COMP");
    nslots = parse_comp(argv[4], slotk);
    if (!strcmp(mode, "exh")) {
        double total = count_comp(nslots, slotk);
        double limit = argc > 5 ? atof(argv[5]) : 5e6;
        if (total > limit) { printf("too many S: %.0f > %.0f\n", total, limit); return 2; }
        bestC = 1 << 30; nevals = 0;
        double t0 = now();
        rec(0);
        printf("EXH N=%d h=%d n=%d comp=%s evals=%lld best C=%d secs=%.1f\n", N, hH, 2 * M, argv[4], nevals, bestC, now() - t0);
        print_sol("EXH best", bestC, bestSel, nslots);
        if (argc > 6) { evalS(bestSel, nslots); write_edges(argv[6]); }
        return 0;
    }
    if (!strcmp(mode, "sa")) {
        if (argc < 7) die("sa needs SECONDS SEED");
        double secs = atof(argv[5]);
        rng ^= (uint64_t)atoll(argv[6]) * 0x9E3779B97F4A7C15ULL; if (!rng) rng = 1;
        for (int i = 0; i < 10; i++) xr();
        double T0 = getenv("T0") ? atof(getenv("T0")) : 10.0;
        double T1 = getenv("T1") ? atof(getenv("T1")) : 0.5;
        anneal(secs, T0, T1, slotk, nslots);
        print_sol("SA best", bestC, bestSel, nslots);
        if (argc > 7) {
            evalS(bestSel, nslots);
            write_edges(argv[7]);
        }
        return 0;
    }
    die("unknown mode");
    return 1;
}
