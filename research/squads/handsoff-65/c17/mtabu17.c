/* mcos.c: annealer for bipartite multi-orbit coset graphs of a group G at degree 6, diameter 5.
 *
 * G acts on each colour class with several orbits; orbit o is the coset space G/H_o of a cyclic subgroup
 * H_o = <h_o> (cyclic, order 1..8). Edges between an A-orbit a and a B-orbit b form a union of FULL-SIZE double cosets
 * D = H_a u H_b (|D| = |H_a||H_b|): xH_a ~ yH_b iff x^-1 y in D. Each double coset adds |H_a| to the degree of
 * every a-vertex and |H_b| to the degree of every b-vertex, so the counts n_ab of double cosets per block fix the
 * degrees: sum_b n_ab |H_a| = 6 for every A-orbit a and sum_a n_ab |H_b| = 6 for every B-orbit b.
 * Families: TYPE "1|1" = Haar graphs H(G,S); "2|2" = bi-coset graphs with |H| = |K| = 2 (|G| vertices);
 * "1|2,2" = G regular on A, B = G/K1 u G/K2 (2|G| vertices; neither Haar nor bi-coset in general);
 * "2,2|2,2", "1|3,3,3", "3,3,3|3,3,3", ...
 * G acts on the graph, so diameter <= 5 iff every orbit representative reaches all of its own colour within 4
 * and (for A-orbits) all of B within 5. Cost = number of (representative, vertex) pairs violating this.
 *
 * usage: mcos GROUP          (GROUP: m, then the m x m multiplication table, element 0 = identity; extra lines ignored)
 * env: TYPE ("1|2,2"), N ("n_ab row-major over blocks, e.g. 3,3"; default: the unique or a balanced split),
 *      CLS (conjugacy-class choice per non-trivial orbit, comma list of indices into the class list printed at
 *      start; default: loop over all combinations), SECS (per combination, 20), SEED (1), ITERS (per restart, 30000),
 *      RANDCOMB (instead: this many random combinations), T0 (2.0), T1 (0.05), EDGES (write the best graph found as an edge list), MAXCOMB (cap on combinations, 1000)
 * Output: one "COMB ... best <cost>" line per combination, "SOL ..." for cost-0 graphs, "RESULT best <cost>" at the end.
 */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 2048
#define MAXO 8
#define MAXV 4096
static int m; static uint16_t *mul; static int inv_[MAXM], ord_[MAXM];
#define MUL(x, y) mul[(size_t)(x) * m + (y)]
static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }
static uint64_t rs = 88172645463325252ULL;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* orbits */
static int no, nA, side_[MAXO], sord[MAXO], stab[MAXO][8], osz[MAXO], off[MAXO], nv;
static int *cid[MAXO];                 /* cid[o][x] = index of coset x H_o */
static int *crep[MAXO];                /* representative of each coset */
/* blocks a (A-orbit) x b (B-orbit) */
static int nblk, ba[MAXO * MAXO], bb[MAXO * MAXO], nab[MAXO * MAXO];
static int *dcof[MAXO * MAXO];         /* dcof[k][g] = double coset id of g in block k */
static int ndc[MAXO * MAXO]; static int *dcrep[MAXO * MAXO]; static int *dcfull[MAXO * MAXO];
static int nfull[MAXO * MAXO]; static int *fulllist[MAXO * MAXO];
static int chosen[MAXO * MAXO][8]; static char *isch[MAXO * MAXO];

static void set_orbit_stab(int o, int gen) {
    int k = 0, x = 0;
    do { stab[o][k++] = x; x = MUL(x, gen); } while (x != 0 && k < 8);
    sord[o] = k; osz[o] = m / k;
    int *rep = malloc(sizeof(int) * m), nxt = 0;
    for (int g = 0; g < m; g++) { int r = g; for (int i = 0; i < k; i++) { int y = MUL(g, stab[o][i]); if (y < r) r = y; } rep[g] = r; }
    int *idx = malloc(sizeof(int) * m); for (int g = 0; g < m; g++) idx[g] = -1;
    crep[o] = malloc(sizeof(int) * osz[o]);
    for (int g = 0; g < m; g++) if (rep[g] == g) { idx[g] = nxt; crep[o][nxt++] = g; }
    for (int g = 0; g < m; g++) cid[o][g] = idx[rep[g]];
    free(rep); free(idx);
}
static void build_blocks(void) {
    nblk = 0;
    for (int a = 0; a < no; a++) if (side_[a] == 0) for (int b = 0; b < no; b++) if (side_[b] == 1) {
        int k = nblk++; ba[k] = a; bb[k] = b;
        int *id = dcof[k]; for (int g = 0; g < m; g++) id[g] = -1;
        ndc[k] = 0; nfull[k] = 0;
        for (int g = 0; g < m; g++) if (id[g] < 0) {
            int c = ndc[k]++, sz = 0;
            for (int i = 0; i < sord[a]; i++) for (int j = 0; j < sord[b]; j++) {
                int y = MUL(MUL(stab[a][i], g), stab[b][j]); if (id[y] < 0) { id[y] = c; sz++; } }
            dcrep[k][c] = g; dcfull[k][c] = (sz == sord[a] * sord[b]);
            if (dcfull[k][c]) fulllist[k][nfull[k]++] = c;
        }
    }
}
/* adjacency */
static int adj[MAXV][6], deg_[MAXV];
static int build_graph(void) {
    for (int v = 0; v < nv; v++) deg_[v] = 0;
    for (int k = 0; k < nblk; k++) {
        int a = ba[k], b = bb[k];
        for (int c = 0; c < nab[k]; c++) {
            int u = dcrep[k][chosen[k][c]];
            /* D = H_a u H_b; for each A-vertex xH_a: neighbours coset_b(x h u), h in H_a (|H_a| of them) */
            for (int i = 0; i < osz[a]; i++) { int x = crep[a][i], va = off[a] + i;
                for (int s = 0; s < sord[a]; s++) { int y = MUL(MUL(x, stab[a][s]), u); int vb = off[b] + cid[b][y];
                    if (deg_[va] >= 6 || deg_[vb] >= 6) return 0;
                    adj[va][deg_[va]++] = vb; adj[vb][deg_[vb]++] = va; } }
        }
    }
    for (int v = 0; v < nv; v++) if (deg_[v] != 6) return 0;
    return 1;
}
static int dist_[MAXV], q_[MAXV];
static int cost_eval(void) {
    if (!build_graph()) return 1 << 28;
    int cost = 0;
    for (int o = 0; o < no; o++) {
        int s = off[o]; for (int v = 0; v < nv; v++) dist_[v] = -1;
        int h = 0, t = 0; dist_[s] = 0; q_[t++] = s;
        while (h < t) { int v = q_[h++]; if (dist_[v] == 5) continue;
            for (int j = 0; j < 6; j++) { int w = adj[v][j]; if (dist_[w] < 0) { dist_[w] = dist_[v] + 1; q_[t++] = w; } } }
        for (int p = 0; p < no; p++) {
            if (side_[o] == 1 && side_[p] == 0) continue;
            for (int i = 0; i < osz[p]; i++) if (dist_[off[p] + i] < 0) cost++;
        }
    }
    return cost;
}
static void write_edges(const char *fn) {
    if (!build_graph()) return;
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "%d\n", nv);
    for (int v = 0; v < nv; v++) for (int j = 0; j < 6; j++) if (adj[v][j] > v) fprintf(f, "%d %d\n", v, adj[v][j]);
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: mcos GROUP\n"); return 2; }
    FILE *f = fopen(argv[1], "r"); if (!f || fscanf(f, "%d", &m) != 1 || m > MAXM) return 2;
    mul = malloc(sizeof(uint16_t) * m * m);
    for (int i = 0; i < m * m; i++) { int x; if (fscanf(f, "%d", &x) != 1) return 2; mul[i] = x; }
    fclose(f);
    for (int i = 0; i < m; i++) for (int j = 0; j < m; j++) if (MUL(i, j) == 0) inv_[i] = j;
    for (int i = 0; i < m; i++) { int k = 1, x = i; while (x != 0) { x = MUL(x, i); k++; } ord_[i] = (i == 0) ? 1 : k; }
    const char *type = getenv("TYPE") ? getenv("TYPE") : "1|2,2";
    double SECS = getenv("SECS") ? atof(getenv("SECS")) : 20; long ITERS = getenv("ITERS") ? atol(getenv("ITERS")) : 30000;
    double T0 = getenv("T0") ? atof(getenv("T0")) : 2.0, T1 = getenv("T1") ? atof(getenv("T1")) : 0.05;
    if (getenv("SEED")) { rs ^= (uint64_t)atoll(getenv("SEED")) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 20; i++) rnd(); }
    int MAXCOMB = getenv("MAXCOMB") ? atoi(getenv("MAXCOMB")) : 1000;
    /* parse TYPE */
    no = 0; int sd = 0;
    for (const char *p = type; *p; ) { if (*p == '|') { sd = 1; p++; continue; } if (*p == ',') { p++; continue; }
        side_[no] = sd; sord[no] = (int)strtol(p, (char **)&p, 10); no++; }
    nA = 0; for (int o = 0; o < no; o++) nA += side_[o] == 0;
    /* conjugacy classes of elements of order 2..8 (representatives = smallest index) */
    static int clsrep[9][MAXM]; int ncls[9] = {0}; static char seen[MAXM];
    for (int o = 2; o <= 8; o++) { memset(seen, 0, sizeof seen);
        for (int x = 1; x < m; x++) if (ord_[x] == o && !seen[x]) { clsrep[o - 1][ncls[o - 1]++] = x;
            for (int g = 0; g < m; g++) seen[MUL(MUL(g, x), inv_[g])] = 1; } }
    int nonab = 0; for (int i = 0; i < m && !nonab; i++) for (int j = 0; j < m; j++) if (MUL(i, j) != MUL(j, i)) { nonab = 1; break; }
    fprintf(stderr, "m %d nonabelian %d type %s classes of elements of order 2..8:", m, nonab, type);
    for (int o = 2; o <= 8; o++) fprintf(stderr, " %d", ncls[o - 1]); fprintf(stderr, "\n");
    for (int o = 0; o < no; o++) { cid[o] = malloc(sizeof(int) * m); }
    for (int k = 0; k < MAXO * MAXO; k++) { dcof[k] = malloc(sizeof(int) * m); dcrep[k] = malloc(sizeof(int) * m);
        dcfull[k] = malloc(sizeof(int) * m); fulllist[k] = malloc(sizeof(int) * m); isch[k] = malloc(m); }
    /* class combinations: orbits with sord 1 need none; others pick a class; orbits on the same side with the
       same order are interchangeable, so class indices are non-decreasing there */
    int nt = 0, tor[MAXO]; for (int o = 0; o < no; o++) if (sord[o] > 1) { if (sord[o] > 8 || ncls[sord[o] - 1] == 0) { printf("RESULT best -1 (no elements of order %d)\n", sord[o]); return 0; } tor[nt++] = o; }
    int fixed[MAXO], hasfixed = 0;
    if (getenv("CLS")) { hasfixed = 1; const char *p = getenv("CLS"); for (int i = 0; i < nt; i++) { fixed[i] = (int)strtol(p, (char **)&p, 10); if (*p == ',') p++; } }
    int comb[MAXO]; for (int i = 0; i < nt; i++) comb[i] = hasfixed ? fixed[i] : 0;
    int RANDCOMB = getenv("RANDCOMB") ? atoi(getenv("RANDCOMB")) : 0, nrand = 0;   /* sample this many random combinations */
    if (RANDCOMB) for (int i = 0; i < nt; i++) comb[i] = rnd() % ncls[sord[tor[i]] - 1];
    int ncomb = 0, gbest = 1 << 30; double tstart = now();
    const char *EDGES = getenv("EDGES");
    while (1) {
        /* validity: non-decreasing within (side, order) groups */
        int ok = 1;
        for (int i = 1; i < nt; i++) { int o = tor[i], p = tor[i - 1]; if (side_[o] == side_[p] && sord[o] == sord[p] && comb[i] < comb[i - 1]) ok = 0; }
        if (ok) {
            ncomb++;
            /* set up orbits */
            nv = 0;
            for (int o = 0, i = 0; o < no; o++) {
                if (sord[o] == 1) set_orbit_stab(o, 0); else set_orbit_stab(o, clsrep[sord[o] - 1][comb[i++]]);
                off[o] = nv; nv += osz[o];
            }
            build_blocks();
            /* degree split n_ab */
            if (getenv("N")) { const char *p = getenv("N"); for (int k = 0; k < nblk; k++) { nab[k] = (int)strtol(p, (char **)&p, 10); if (*p == ',') p++; } }
            else { /* balanced default: spread double cosets evenly, respecting degrees (works for the listed TYPEs) */
                for (int k = 0; k < nblk; k++) nab[k] = 0;
                int need[MAXO]; for (int o = 0; o < no; o++) need[o] = 6;
                for (int it = 0; it < 64; it++) for (int k = 0; k < nblk; k++) { int a = ba[k], b = bb[k];
                    if (need[a] >= sord[a] && need[b] >= sord[b]) { nab[k]++; need[a] -= sord[a]; need[b] -= sord[b]; } }
            }
            int bad = 0; for (int k = 0; k < nblk; k++) if (nab[k] > nfull[k] || nab[k] > 8) bad = 1;
            int best = 1 << 30; long evals = 0;
            if (!bad) {
                int cur, bestch[MAXO * MAXO][8];
                if (getenv("LNS")) {
                    int VERB = getenv("VERB") ? 1 : 0;
                    /* LNS: re-optimise ONE whole block at a time (all its slots together, exhaustively when
                       C(nfull, nab) <= NCAP, else NCAP random sets), accept plateau moves, kick after PASS stalls */
                    int NCAP = getenv("NCAP") ? atoi(getenv("NCAP")) : 20000;
                    int PASS = getenv("PASS") ? atoi(getenv("PASS")) : 3;
                    int KICK = getenv("KICK") ? atoi(getenv("KICK")) : 2;
                    double t0 = now();
                    for (int k = 0; k < nblk; k++) { memset(isch[k], 0, m);
                        for (int c = 0; c < nab[k]; c++) { int d; do d = fulllist[k][rnd() % nfull[k]]; while (isch[k][d]); isch[k][d] = 1; chosen[k][c] = d; } }
                    cur = cost_eval(); evals++;
                    int lbest = cur, stall = 0;
                    if (cur < best) { best = cur; memcpy(bestch, chosen, sizeof bestch); }
                    while (now() - t0 < SECS && best > 0) {
                        int improved = 0;
                        for (int kk = 0; kk < nblk && best > 0; kk++) {
                            int k = rnd() % nblk, s = nab[k], F = nfull[k];
                            if (s == 0) continue;
                            int oldc[8], idx[8], bidx[8], bc = 1 << 30, bn = 0;
                            for (int c = 0; c < s; c++) oldc[c] = chosen[k][c];
                            double tot = 1.0; for (int i = 0; i < s; i++) tot = tot * (F - i) / (i + 1);
                            int exhaustive = tot <= NCAP;
                            long ncomb = exhaustive ? (long)(tot + 0.5) : NCAP;
                            for (int c = 0; c < s; c++) idx[c] = c;
                            for (long t = 0; t < ncomb; t++) {
                                if (exhaustive) { if (t > 0) { int i = s - 1; while (i >= 0 && idx[i] == F - s + i) i--;
                                        if (i < 0) break; idx[i]++; for (int j = i + 1; j < s; j++) idx[j] = idx[j - 1] + 1; } }
                                else { for (int c = 0; c < s; c++) { int x; int dup; do { x = rnd() % F; dup = 0; for (int q = 0; q < c; q++) if (idx[q] == x) dup = 1; } while (dup); idx[c] = x; }
                                    for (int a = 1; a < s; a++) for (int b = a; b > 0 && idx[b - 1] > idx[b]; b--) { int tmp = idx[b]; idx[b] = idx[b - 1]; idx[b - 1] = tmp; } }
                                for (int c = 0; c < s; c++) chosen[k][c] = fulllist[k][idx[c]];
                                int v = cost_eval(); evals++;
                                if (v < bc) { bc = v; bn = 1; memcpy(bidx, idx, sizeof bidx); }
                                else if (v == bc && rnd() % (++bn) == 0) memcpy(bidx, idx, sizeof bidx);
                            }
                            if (bc <= cur) {
                                for (int c = 0; c < s; c++) chosen[k][c] = fulllist[k][bidx[c]];
                                if (bc < cur) improved = 1;
                                cur = bc;
                            } else { for (int c = 0; c < s; c++) chosen[k][c] = oldc[c]; }
                            if (cur < best) { best = cur; memcpy(bestch, chosen, sizeof bestch);
                                if (best < gbest) { gbest = best; if (EDGES) write_edges(EDGES); } }
                        }
                        if (cur < lbest) { lbest = cur; stall = 0; } else stall++;
                        if (VERB) fprintf(stderr, "pass cur %d lbest %d best %d evals %ld t %.1f\n", cur, lbest, best, evals, now() - t0);
                        if (!improved && stall >= PASS) {   /* kick: from the best state, KICK random slot changes */
                            memcpy(chosen, bestch, sizeof chosen);
                            for (int q = 0; q < KICK; q++) { int k = rnd() % nblk; if (nab[k] == 0) continue;
                                int c = rnd() % nab[k], d;
                                do { d = fulllist[k][rnd() % nfull[k]]; int in = 0; for (int e = 0; e < nab[k]; e++) if (chosen[k][e] == d) in = 1; if (!in) break; } while (1);
                                chosen[k][c] = d; }
                            cur = cost_eval(); evals++; lbest = cur; stall = 0;
                        }
                    }
                } else {
                double t0 = now();
                long TT = getenv("TT") ? atol(getenv("TT")) : 10;          /* tabu tenure: TT + rand(0..TT) steps */
                long STAG = getenv("STAG") ? atol(getenv("STAG")) : 300;   /* steps without local improvement -> kick */
                int KICK = getenv("KICK") ? atoi(getenv("KICK")) : 3;      /* random moves applied after a kick */
                int VERB = getenv("VERB") ? 1 : 0;
                static long tabu_until[MAXO * MAXO][MAXM];
                memset(tabu_until, 0, sizeof tabu_until);
                long step = 0, lastimp = 0;
                for (int k = 0; k < nblk; k++) { memset(isch[k], 0, m);
                    for (int c = 0; c < nab[k]; c++) { int d; do d = fulllist[k][rnd() % nfull[k]]; while (isch[k][d]); isch[k][d] = 1; chosen[k][c] = d; } }
                cur = cost_eval(); evals++;
                int lbest = cur;
                if (cur < best) { best = cur; memcpy(bestch, chosen, sizeof bestch); }
                while (now() - t0 < SECS && best > 0) {
                    /* full neighbourhood: every (block, slot) x every free full double coset */
                    int mk = -1, mc = -1, md = -1, mv = 1 << 30, nties = 0;
                    for (int k = 0; k < nblk; k++) for (int c = 0; c < nab[k]; c++) {
                        int old = chosen[k][c];
                        for (int j = 0; j < nfull[k]; j++) { int d = fulllist[k][j]; if (isch[k][d]) continue;
                            chosen[k][c] = d; isch[k][old] = 0; isch[k][d] = 1;
                            int v = cost_eval(); evals++;
                            chosen[k][c] = old; isch[k][d] = 0; isch[k][old] = 1;
                            if (tabu_until[k][d] > step && !(v < best)) continue;   /* aspiration on new best */
                            if (v < mv) { mv = v; nties = 1; mk = k; mc = c; md = d; }
                            else if (v == mv && rnd() % (++nties) == 0) { mk = k; mc = c; md = d; }
                        }
                    }
                    step++;
                    if (mk < 0) continue;
                    int old = chosen[mk][mc];
                    chosen[mk][mc] = md; isch[mk][old] = 0; isch[mk][md] = 1;
                    tabu_until[mk][old] = step + TT + (long)(rnd() % (TT + 1));
                    cur = mv;
                    if (cur < lbest) { lbest = cur; lastimp = step; }
                    if (cur < best) { best = cur; memcpy(bestch, chosen, sizeof bestch);
                        if (best < gbest) { gbest = best; if (EDGES) write_edges(EDGES); } }
                    if (VERB && step % 200 == 0) fprintf(stderr, "step %ld cur %d lbest %d best %d evals %ld t %.1f\n", step, cur, lbest, best, evals, now() - t0);
                    if (step - lastimp > STAG) {   /* kick: back to the best state, then KICK random moves */
                        memcpy(chosen, bestch, sizeof chosen);
                        for (int k = 0; k < nblk; k++) { memset(isch[k], 0, m); for (int c = 0; c < nab[k]; c++) isch[k][chosen[k][c]] = 1; }
                        for (int q = 0; q < KICK; q++) { int k; do k = rnd() % nblk; while (nab[k] == 0);
                            int c = rnd() % nab[k], o2 = chosen[k][c], d;
                            do d = fulllist[k][rnd() % nfull[k]]; while (isch[k][d]);
                            chosen[k][c] = d; isch[k][o2] = 0; isch[k][d] = 1; }
                        cur = cost_eval(); evals++; lbest = cur; lastimp = step;
                    }
                }
                }
                if (getenv("P2") && best > 0 && best < (1 << 28)) {   /* exhaustive two-move polish of the best state */
                    static int mk_[40000], mc_[40000], md_[40000]; int nm = 0, bestv2 = best; long p2evals = 0;
                    for (int k = 0; k < nblk; k++) for (int c = 0; c < nab[k]; c++) for (int j = 0; j < nfull[k]; j++) {
                        int d = fulllist[k][j], in = 0;
                        for (int e = 0; e < nab[k]; e++) if (bestch[k][e] == d) in = 1;
                        if (!in && nm < 40000) { mk_[nm] = k; mc_[nm] = c; md_[nm] = d; nm++; } }
                    int bi = -1, bj = -1;
                    for (int i = 0; i < nm; i++) {
                        memcpy(chosen, bestch, sizeof chosen);
                        int k1 = mk_[i], c1 = mc_[i];
                        chosen[k1][c1] = md_[i];
                        for (int j = i + 1; j < nm; j++) {
                            int k2 = mk_[j], c2 = mc_[j], d2 = md_[j];
                            if (k2 == k1 && c2 == c1) continue;
                            int in = 0; for (int e = 0; e < nab[k2]; e++) if (chosen[k2][e] == d2) in = 1;
                            if (in) continue;
                            int o2 = chosen[k2][c2]; chosen[k2][c2] = d2;
                            int v = cost_eval(); p2evals++;
                            chosen[k2][c2] = o2;
                            if (v < bestv2) { bestv2 = v; bi = i; bj = j; }
                        }
                    }
                    fprintf(stderr, "P2 moves %d pairs %ld best_before %d best_after %d\n", nm, p2evals, best, bestv2);
                    if (bi >= 0) {
                        memcpy(chosen, bestch, sizeof chosen);
                        chosen[mk_[bi]][mc_[bi]] = md_[bi];
                        chosen[mk_[bj]][mc_[bj]] = md_[bj];
                        best = bestv2; memcpy(bestch, chosen, sizeof bestch);
                        if (best < gbest) { gbest = best; if (EDGES) write_edges(EDGES); }
                    }
                }
                if (getenv("P2B") && best > 0 && best < (1 << 28)) {   /* exhaustive two-BLOCK polish of the best state */
                    static int cmb[64][4000][8]; int ncmb[64];
                    int okb = 1;
                    for (int k = 0; k < nblk; k++) {
                        int s = nab[k], F = nfull[k]; ncmb[k] = 0;
                        if (s == 0) { ncmb[k] = 1; continue; }
                        int idx[8]; for (int c = 0; c < s; c++) idx[c] = c;
                        if (F < s) { okb = 0; break; }
                        while (1) {
                            if (ncmb[k] >= 4000) { okb = 0; break; }
                            for (int c = 0; c < s; c++) cmb[k][ncmb[k]][c] = fulllist[k][idx[c]];
                            ncmb[k]++;
                            int i = s - 1; while (i >= 0 && idx[i] == F - s + i) i--;
                            if (i < 0) break;
                            idx[i]++; for (int j = i + 1; j < s; j++) idx[j] = idx[j - 1] + 1;
                        }
                        if (!okb) break;
                    }
                    int bestv2 = best, bp = -1, bq = -1, bxi = -1, bxj = -1; long p2b = 0;
                    if (okb) for (int p = 0; p < nblk; p++) for (int q = p + 1; q < nblk; q++) {
                        for (int xi = 0; xi < ncmb[p]; xi++) for (int xj = 0; xj < ncmb[q]; xj++) {
                            memcpy(chosen, bestch, sizeof chosen);
                            for (int c = 0; c < nab[p]; c++) chosen[p][c] = cmb[p][xi][c];
                            for (int c = 0; c < nab[q]; c++) chosen[q][c] = cmb[q][xj][c];
                            int v = cost_eval(); p2b++;
                            if (v < bestv2) { bestv2 = v; bp = p; bq = q; bxi = xi; bxj = xj; }
                        }
                    }
                    fprintf(stderr, "P2B blocks %d combos %d,%d pairs %ld best_before %d best_after %d\n", nblk, ncmb[0], ncmb[1], p2b, best, bestv2);
                    if (bp >= 0) {
                        memcpy(chosen, bestch, sizeof chosen);
                        for (int c = 0; c < nab[bp]; c++) chosen[bp][c] = cmb[bp][bxi][c];
                        for (int c = 0; c < nab[bq]; c++) chosen[bq][c] = cmb[bq][bxj][c];
                        best = bestv2; memcpy(bestch, chosen, sizeof bestch);
                        if (best < gbest) { gbest = best; if (EDGES) write_edges(EDGES); }
                    }
                }
                if (best == 0) { printf("SOL type %s cls", type); for (int i = 0; i < nt; i++) printf(" %d", comb[i]);
                    printf(" stabgens"); for (int o = 0; o < no; o++) printf(" %d", sord[o] > 1 ? stab[o][1] : 0);
                    for (int k = 0; k < nblk; k++) { printf(" | blk %d-%d:", ba[k], bb[k]); for (int c = 0; c < nab[k]; c++) printf(" %d", dcrep[k][bestch[k][c]]); }
                    printf("\n"); fflush(stdout); }
            }
            printf("COMB"); for (int i = 0; i < nt; i++) printf(" %d", comb[i]);
            printf(" stabgens"); for (int o = 0; o < no; o++) printf(" %d", sord[o] > 1 ? stab[o][1] : 0);
            printf(" n"); for (int k = 0; k < nblk; k++) printf(" %d", nab[k]);
            printf(" vertices %d best %d evals %ld%s\n", nv, bad ? -1 : best, evals, bad ? " (split impossible)" : ""); fflush(stdout);
            if (ncomb >= MAXCOMB || hasfixed) break;
        }
        if (hasfixed) break;
        if (RANDCOMB) { if (ok) nrand++; if (nrand >= RANDCOMB) break; for (int j = 0; j < nt; j++) comb[j] = rnd() % ncls[sord[tor[j]] - 1]; continue; }
        int i = nt - 1;
        while (i >= 0) { comb[i]++; if (comb[i] < ncls[sord[tor[i]] - 1]) break; comb[i] = 0; i--; }
        if (i < 0) break;
    }
    printf("RESULT best %d combinations %d secs %.1f\n", gbest, ncomb, now() - tstart);
    return 0;
}
