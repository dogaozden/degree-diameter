/* fibsa.c: squad round 3, card c8 (WILDCARD): penalty simulated annealing over FIBRE SETS of H(11).
   Model (checked numerically by model_check.py against the point-level B-form):
   - fibre vertex v = (s,b,c,f) in F_11^4 stands for the 11 affine points (1,a,b,c,c^2-ae-bf,e,f), a = lam,
     e = s + 9 lam, lam in F_11 (direction u = (1,0,0,9,0)); all 11 are pairwise opposite.
   - two fibres v,w are compatible iff R[v-w] = 0, where R[d] = #{delta : 9 delta^2 + ds delta + (db df - dc^2) = 0};
     each root is one conflicting point pair per point of the fibre, so the point-level conflicts are 11*R.
   - infinity points: P = (x1,x2,x3,x6) on the elliptic quadric 2x1^2 + x2 x6 - x3^2 = 0 (122 choices), with a
     level x4 = l in F_11; the point (0,x1,x2,x3,l,2x1,x6) is blocked by fibre v iff l + ell_P(v) = 0,
     ell_P(v) = x1 s + x2 f + x6 b - 2 x3 c.  Two infinity points with distinct P are opposite.
   Objective: F(K) = 11|K| + free(K), free(K) = #{P : some level is unblocked by all of K}.
   Penalty Pen(K) = sum of R over pairs in K.  Energy E = -F + Wp*Pen (simulated annealing, add/remove moves,
   candidate additions sampled among vertices with few conflicts).  Feasible states (Pen = 0) are saved.
   usage: fibsa OUT_FILE CPU_SECONDS SEED WP T0 T1 CYCLE_LEN PADD CMAX [INIT_FIBRES|-]
   OUT_FILE gets lines "F s b c f" (fibres) and "P x1 x2 x3 x6 level" (infinity points), plus a header. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define Q 11
#define NF 14641
#define NP 122

static int Pv[NP][4];
static uint8_t ell[NP][NF];
static int R[NF];
static int conf[NF];
static uint8_t inK[NF];
static int Kl[NF], Kpos[NF], kk = 0;
static int cntval[NP][Q], missing[NP], freeC = 0;
static long pen = 0;
static uint64_t rs = 0x9E3779B97F4A7C15ULL;
static inline uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double cpu(void) { return (double)clock() / CLOCKS_PER_SEC; }

static void build_tables(void) {
    int np = 0;
    for (int x1 = 0; x1 < Q; x1++) for (int x2 = 0; x2 < Q; x2++) for (int x3 = 0; x3 < Q; x3++) for (int x6 = 0; x6 < Q; x6++) {
        int v[4] = {x1, x2, x3, x6}; if (!x1 && !x2 && !x3 && !x6) continue;
        if ((2 * x1 * x1 + x2 * x6 - x3 * x3) % Q) continue;
        int nz = -1; for (int i = 0; i < 4; i++) if (v[i]) { nz = v[i]; break; }
        if (nz != 1) continue;
        if (np >= NP) { fprintf(stderr, "too many P\n"); exit(1); }
        for (int i = 0; i < 4; i++) Pv[np][i] = v[i];
        np++;
    }
    if (np != NP) { fprintf(stderr, "P count %d\n", np); exit(1); }
    for (int v = 0; v < NF; v++) {
        int s = v % Q, b = (v / Q) % Q, c = (v / (Q * Q)) % Q, f = v / (Q * Q * Q);
        for (int p = 0; p < NP; p++) {
            int x1 = Pv[p][0], x2 = Pv[p][1], x3 = Pv[p][2], x6 = Pv[p][3];
            ell[p][v] = (uint8_t)(((x1 * s + x2 * f + x6 * b - 2 * x3 * c) % Q + 2 * Q * Q) % Q);
        }
    }
    for (int d = 0; d < NF; d++) {
        int s = d % Q, b = (d / Q) % Q, c = (d / (Q * Q)) % Q, f = d / (Q * Q * Q);
        int r = 0;
        for (int dl = 0; dl < Q; dl++) if (((9 * dl * dl + s * dl + (b * f - c * c)) % Q + 2 * Q * Q) % Q == 0) r++;
        R[d] = (d == 0) ? 0 : r;
    }
}

/* conf[v] += sign * R[v - w] for all v */
static void conf_update(int w, int sign) {
    int ws = w % Q, wb = (w / Q) % Q, wc = (w / (Q * Q)) % Q, wf = w / (Q * Q * Q);
    int tS[Q], tB[Q], tC[Q], tF[Q];
    for (int i = 0; i < Q; i++) {
        tS[i] = (i - ws + Q) % Q; tB[i] = Q * ((i - wb + Q) % Q);
        tC[i] = Q * Q * ((i - wc + Q) % Q); tF[i] = Q * Q * Q * ((i - wf + Q) % Q);
    }
    int v = 0;
    for (int f = 0; f < Q; f++) for (int c = 0; c < Q; c++) for (int b = 0; b < Q; b++) for (int s = 0; s < Q; s++, v++) {
        int d = tS[s] + tB[b] + tC[c] + tF[f];
        conf[v] += sign * R[d];
    }
}

static int count_add(int v) {        /* #P that stop being free when v is added */
    int n = 0;
    for (int p = 0; p < NP; p++) if (missing[p] == 1 && cntval[p][ell[p][v]] == 0) n++;
    return n;
}
static int count_rem(int w) {        /* #P that become free when w is removed */
    int n = 0;
    for (int p = 0; p < NP; p++) if (missing[p] == 0 && cntval[p][ell[p][w]] == 1) n++;
    return n;
}
static void add_state(int v) {
    pen += conf[v];
    conf_update(v, +1);
    for (int p = 0; p < NP; p++) { int c = ell[p][v]; if (cntval[p][c]++ == 0) { if (--missing[p] == 0) freeC--; } }
    inK[v] = 1; Kpos[v] = kk; Kl[kk++] = v;
}
static void remove_state(int w) {
    int p0 = Kpos[w]; int last = Kl[--kk]; Kl[p0] = last; Kpos[last] = p0; inK[w] = 0;
    pen -= conf[w];
    conf_update(w, -1);
    for (int p = 0; p < NP; p++) { int c = ell[p][w]; if (--cntval[p][c] == 0) { if (missing[p] == 0) freeC++; missing[p]++; } }
}
static void save(const char *fn, int F) {
    FILE *f = fopen(fn, "w"); if (!f) return;
    fprintf(f, "# fibsa: %d fibres, free infinity points %d, total F = %d (pairwise opposite after lifting)\n", kk, freeC, F);
    for (int i = 0; i < kk; i++) { int v = Kl[i];
        fprintf(f, "F %d %d %d %d\n", v % Q, (v / Q) % Q, (v / (Q * Q)) % Q, v / (Q * Q * Q)); }
    for (int p = 0; p < NP; p++) if (missing[p] >= 1) {
        int c = -1; for (int l = 0; l < Q; l++) if (cntval[p][l] == 0) { c = l; break; }
        int level = (Q - c) % Q;     /* blocked iff level + ell = 0, so need ell != -level, i.e. cntval[(Q-level)%Q] == 0 */
        fprintf(f, "P %d %d %d %d %d\n", Pv[p][0], Pv[p][1], Pv[p][2], Pv[p][3], level);
    }
    fclose(f);
}

int main(int argc, char **argv) {
    if (argc < 10) { fprintf(stderr, "usage: fibsa OUT CPU SEED WP T0 T1 CYCLE PADD CMAX [INIT|-] [PREM]  (swap prob = 1-PADD-PREM)\n"); return 1; }
    const char *out = argv[1]; double secs = atof(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 0x2545F4914F6CDD1DULL; for (int i = 0; i < 20; i++) rnd64();
    double Wp = atof(argv[4]), T0 = atof(argv[5]), T1 = atof(argv[6]);
    long L = atol(argv[7]); double padd = atof(argv[8]); int cmax = atoi(argv[9]);
    double prem = (argc > 11) ? atof(argv[11]) : 0.2;
    build_tables();
    for (int p = 0; p < NP; p++) { missing[p] = Q; cntval[p][0] = 0; }
    freeC = NP;
    memset(conf, 0, sizeof conf);
    if (argc > 10 && strcmp(argv[10], "-") != 0) {
        FILE *g = fopen(argv[10], "r"); if (!g) return 1; char buf[256];
        while (fgets(buf, sizeof buf, g)) { int s, b, c, f; if (buf[0] == 'F' && sscanf(buf, "F %d %d %d %d", &s, &b, &c, &f) == 4) {
            int v = s + Q * b + Q * Q * c + Q * Q * Q * f; if (!inK[v]) add_state(v); } }
        fclose(g);
        fprintf(stderr, "init: %d fibres, pen %ld, free %d, F = %d\n", kk, pen, freeC, 11 * kk + freeC);
    }
    int bestF = -1; int bestk = 0;
    if (pen == 0 && 11 * kk + freeC > bestF) { bestF = 11 * kk + freeC; save(out, bestF); }
    long it = 0, acc = 0; double lastrep = 0;
    while (1) {
        if ((it & 1023) == 0 && cpu() > secs) break;
        it++;
        double phase = (double)(it % L) / (double)L;
        double T = T0 * pow(T1 / T0, phase);
        double r = rnd01();
        if (kk == 0 || r < padd) {
            int v = -1;
            for (int t = 0; t < 4000; t++) { int x = rndint(NF); if (!inK[x] && conf[x] <= cmax) { v = x; break; } }
            if (v < 0) { do v = rndint(NF); while (inK[v]); }
            int gain = Q - count_add(v);            /* F increases by gain */
            double dE = -(double)gain + Wp * conf[v];
            if (dE <= 0 || rnd01() < exp(-dE / T)) { add_state(v); acc++; }
        } else if (r < padd + prem) {
            int w = Kl[rndint(kk)];
            int dF = -Q + count_rem(w);             /* F changes by dF */
            double dE = -(double)dF - Wp * conf[w];
            if (dE <= 0 || rnd01() < exp(-dE / T)) { remove_state(w); acc++; }
        } else {
            int w = Kl[rndint(kk)];
            double E0 = -(double)(11 * kk + freeC) + Wp * pen;
            remove_state(w);
            int v = -1;
            for (int t = 0; t < 4000; t++) { int x = rndint(NF); if (!inK[x] && x != w && conf[x] <= cmax) { v = x; break; } }
            if (v < 0) { add_state(w); goto after; }
            add_state(v);
            double E1 = -(double)(11 * kk + freeC) + Wp * pen;
            double dE = E1 - E0;
            if (dE <= 0 || rnd01() < exp(-dE / T)) { acc++; }
            else { remove_state(v); add_state(w); }
        }
after:
        if (pen == 0) {
            int F = 11 * kk + freeC;
            if (F > bestF) { bestF = F; bestk = kk; save(out, F);
                fprintf(stderr, "[%.1fs] it %ld: feasible k=%d free=%d F=%d (T=%.3f)\n", cpu(), it, kk, freeC, F, T); }
        }
        if (cpu() - lastrep > 30) { lastrep = cpu();
            fprintf(stderr, "[%.0fs] it %ld T=%.3f k=%d free=%d pen=%ld F=%d bestF=%d acc=%ld\n", cpu(), it, T, kk, freeC, pen, 11 * kk + freeC, bestF, acc); }
    }
    fprintf(stderr, "done: it %ld acc %ld best F %d (k=%d)  final k=%d free=%d pen=%ld\n", it, acc, bestF, bestk, kk, freeC, pen);
    printf("bestF %d\n", bestF);
    return 0;
}
