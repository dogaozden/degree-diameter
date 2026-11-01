/* bicos2: bi-coset graphs with two subgroups H (side A) and K (side B), |H| = |K| = h (handsoff-49, w7).
 * A = right cosets Hg, B = right cosets Kk; S = K S H (union of (K,H) double cosets), sum of k = 4 (k = |KsH|/|K|).
 * Edge: Hg ~ Kk iff k g^-1 in S. Simple, 4-regular, bipartite, n = 2N/h. Right multiplication by G is transitive on
 * each side, so two BFS suffice. Cost C as in bicos (far pairs = M*C/2). With K = H this is bicos.
 *   bicos2 TABLE subgroups H_GENS                 list the subgroups of prime order h = order of H (one generator each)
 *   bicos2 TABLE kexh H_GENS K_LIST COMP LIMIT OUT  exhaustive for each K = <k> (k in K_LIST, comma list), best over all
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#define DIAM 9
static int N, M, hH, hK;
static uint16_t *T;
static int *invE;
static int *Hel, *Kel;
static int *cidH, *crepH, *cidK, *crepK, *dcid, ndc, *dck, **kreps, **hreps;
static int *nbA, *nbB, *dist, *queue;
static int sList[8], tList[8];
static int ncand[8], *cand[8];

static void die(const char *m) { fprintf(stderr, "bicos2: %s\n", m); exit(1); }
static double now(void) { struct timespec ts; clock_gettime(CLOCK_MONOTONIC, &ts); return ts.tv_sec + ts.tv_nsec * 1e-9; }

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

static int *closure(const int *gens, int ng, int *cnt) {
    char *in = calloc(N, 1);
    int *el = malloc(N * sizeof(int));
    int c = 0;
    in[0] = 1; el[c++] = 0;
    for (int i = 0; i < c; i++)
        for (int j = 0; j < ng; j++) {
            int x = T[(size_t)el[i] * N + gens[j]];
            if (!in[x]) { in[x] = 1; el[c++] = x; }
        }
    free(in);
    *cnt = c;
    return el;
}

static int *rcosets(const int *el, int cnt, int **rep, int *Mout) {
    int *cid = malloc(N * sizeof(int));
    *rep = malloc(N * sizeof(int));
    for (int i = 0; i < N; i++) cid[i] = -1;
    int m = 0;
    for (int g = 0; g < N; g++) if (cid[g] < 0) {
        for (int a = 0; a < cnt; a++) cid[T[(size_t)el[a] * N + g]] = m;
        (*rep)[m++] = g;
    }
    if (m * cnt != N) die("coset count");
    *Mout = m;
    return cid;
}

static void setup(const int *hg, int nhg, const int *kg, int nkg) {
    Hel = closure(hg, nhg, &hH);
    Kel = closure(kg, nkg, &hK);
    if (hH != hK) die("|H| != |K|");
    int m1, m2;
    cidH = rcosets(Hel, hH, &crepH, &m1);
    cidK = rcosets(Kel, hK, &crepK, &m2);
    M = m1;
    dcid = malloc(N * sizeof(int));
    for (int i = 0; i < N; i++) dcid[i] = -1;
    int *mark = malloc(M * sizeof(int)), *mark2 = malloc(M * sizeof(int));
    for (int i = 0; i < M; i++) { mark[i] = -1; mark2[i] = -1; }
    int *elems = malloc(N * sizeof(int));
    dck = malloc(N * sizeof(int));
    kreps = malloc(N * sizeof(int *)); hreps = malloc(N * sizeof(int *));
    ndc = 0;
    for (int s = 0; s < N; s++) if (dcid[s] < 0) {
        int ne = 0;
        for (int a = 0; a < hK; a++) {
            int t1 = T[(size_t)Kel[a] * N + s];
            for (int b = 0; b < hH; b++) {
                int t2 = T[(size_t)t1 * N + Hel[b]];
                if (dcid[t2] < 0) { dcid[t2] = ndc; elems[ne++] = t2; }
            }
        }
        int *kr = malloc(ne * sizeof(int)); int nk = 0;
        int *hr = malloc(ne * sizeof(int)); int nh = 0;
        for (int e = 0; e < ne; e++) {
            int c = cidK[elems[e]];
            if (mark[c] != ndc) { mark[c] = ndc; kr[nk++] = elems[e]; }
            int ei = invE[elems[e]];
            int c2 = cidH[ei];
            if (mark2[c2] != ndc) { mark2[c2] = ndc; hr[nh++] = ei; }
        }
        if (nk != nh) die("k mismatch");
        dck[ndc] = nk; kreps[ndc] = kr; hreps[ndc] = hr;
        ndc++;
    }
    free(mark); free(mark2); free(elems);
    for (int k = 0; k < 8; k++) { ncand[k] = 0; cand[k] = malloc(ndc * sizeof(int)); }
    for (int D = 0; D < ndc; D++) if (dck[D] < 8) cand[dck[D]][ncand[dck[D]]++] = D;
    nbA = malloc(4 * (size_t)M * sizeof(int));
    nbB = malloc(4 * (size_t)M * sizeof(int));
    dist = malloc(2 * (size_t)M * sizeof(int));
    queue = malloc(2 * (size_t)M * sizeof(int));
}

static int evalS(const int *sel, int ns) {
    int nsv = 0, ntv = 0;
    for (int p = 0; p < ns; p++) {
        int D = sel[p];
        for (int r = 0; r < dck[D]; r++) sList[nsv++] = kreps[D][r];
        for (int r = 0; r < dck[D]; r++) tList[ntv++] = hreps[D][r];
    }
    if (nsv != 4 || ntv != 4) die("k-sum must be 4");
    for (int x = 0; x < M; x++) {
        int g = crepH[x];
        for (int i = 0; i < 4; i++) nbA[4 * x + i] = cidK[T[(size_t)sList[i] * N + g]];
    }
    for (int y = 0; y < M; y++) {
        int k = crepK[y];
        for (int j = 0; j < 4; j++) nbB[4 * y + j] = cidH[T[(size_t)tList[j] * N + k]];
    }
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
        if (root == 0) { nearA0 = nA; nearB0 = nB; } else nearB1 = nB;
    }
    return (M - nearA0) + (M - nearB1) + 2 * (M - nearB0);
}

static void write_edges(const char *path) {
    FILE *f = fopen(path, "w");
    if (!f) die("cannot write OUT");
    fprintf(f, "%d\n", 2 * M);
    for (int x = 0; x < M; x++)
        for (int i = 0; i < 4; i++) fprintf(f, "%d %d\n", x, M + nbA[4 * x + i]);
    fclose(f);
}

static int nslots, slotk[8], slotidx[8], bestC, bestSel[8];
static int curSel[8];
static void rec(int p) {
    int sel[8];
    if (p == nslots) {
        for (int i = 0; i < nslots; i++) sel[i] = cand[slotk[i]][slotidx[i]];
        int C = evalS(sel, nslots);
        if (C < bestC) { bestC = C; memcpy(bestSel, sel, sizeof sel); }
        return;
    }
    int k = slotk[p];
    int start = (p > 0 && slotk[p - 1] == k) ? slotidx[p - 1] + 1 : 0;
    for (int c = start; c < ncand[k]; c++) { slotidx[p] = c; rec(p + 1); }
}

static int parse_list(const char *s, int *out, int max) {
    int n = 0;
    char *c = strdup(s), *tok = strtok(c, ",");
    while (tok && n < max) { out[n++] = atoi(tok); tok = strtok(NULL, ","); }
    free(c);
    return n;
}

int main(int argc, char **argv) {
    if (argc < 4) die("usage: see header");
    load(argv[1]);
    int hg[4];
    int nhg = parse_list(argv[3], hg, 4);
    if (!strcmp(argv[2], "subgroups")) {
        /* setup only H for its order; then list elements x of order h, one per subgroup <x> (x <= x^-1 canonical) */
        int cnt; int *el = closure(hg, nhg, &cnt);
        int h = cnt;
        char *seen = calloc(N, 1);
        int nsub = 0;
        for (int x = 1; x < N; x++) {
            int o = 1, y = x;
            while (y != 0) { y = T[(size_t)y * N + x]; o++; }
            if (o != h) continue;
            int xi = invE[x];
            if (xi < x) continue;          /* keep one of x, x^-1 */
            if (seen[x]) continue;
            seen[x] = 1; seen[xi] = 1;
            printf("%d\n", x);
            nsub++;
        }
        fprintf(stderr, "subgroups of order %d generated by elements of that order: %d (H order %d)\n", h, nsub, cnt);
        free(el);
        return 0;
    }
    if (!strcmp(argv[2], "kexh")) {
        if (argc < 7) die("kexh needs H_GENS K_LIST COMP LIMIT [OUT]");
        int kl[4096];
        int nk = parse_list(argv[4], kl, 4096);
        int ks[8];
        char *c = strdup(argv[5]), *tok = strtok(c, ",");
        nslots = 0;
        int sum = 0;
        while (tok) { ks[nslots++] = atoi(tok); sum += ks[nslots - 1]; tok = strtok(NULL, ","); }
        free(c);
        if (sum != 4) die("composition k-sum must be 4");
        for (int i = 0; i < nslots; i++) slotk[i] = ks[i];
        double limit = atof(argv[6]);
        int gbest = 1 << 30; int gK = -1; int gSel[8] = {0};
        int gbestSvals[8];
        double t0 = now();
        for (int a = 0; a < nk; a++) {
            int kg[1] = {kl[a]};
            setup(hg, nhg, kg, 1);
            double total = 1;
            for (int k = 1; k < 8; k++) {
                int m = 0;
                for (int i = 0; i < nslots; i++) if (slotk[i] == k) m++;
                if (!m) continue;
                double b = 1;
                for (int i = 0; i < m; i++) b = b * (ncand[k] - i) / (i + 1);
                total *= b;
            }
            if (total > limit) { fprintf(stderr, "K=%d skipped (%g sets)\n", kl[a], total); continue; }
            bestC = 1 << 30;
            rec(0);
            printf("K=%d best=%d\n", kl[a], bestC);
            fflush(stdout);
            if (bestC < gbest) {
                gbest = bestC; gK = kl[a];
                memcpy(gSel, bestSel, sizeof gSel);
                /* keep the graph of the global best: recompute and write the edges at the end */
                memcpy(gbestSvals, gSel, sizeof gSel);
            }
            /* reset candidate lists are rebuilt per K in setup */
        }
        printf("KEXH best=%d K=%d n=%d time=%.1f\n", gbest, gK, 2 * M, now() - t0);
        if (gK >= 0 && argc > 7) {
            int kg[1] = {gK};
            setup(hg, nhg, kg, 1);
            evalS(gSel, nslots);
            write_edges(argv[7]);
            printf("wrote %s\n", argv[7]);
        }
        return 0;
    }
    die("unknown mode");
    return 1;
}
