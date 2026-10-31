/* grow.c (r3g): insert ONE Z5-orbit (one new base vertex w = kb) into a base of a polarity cover, keeping the
   Z_t symmetry, then SA repair with lift2's stub-preserving moves.
   Insertions (exhaustive over voltages):
     A: subdivide base edge e = (a,b,g): edges (a,w,g1), (w,b,g2), 1-stub loop at w (g=0).
     B: remove base edges e1 = (a,b), e2 = (c,d); w joined to one end of each (voltages h1, h2), the two other ends
        joined (voltage h3), 1-stub loop at w (g=0).
   Usage: grow BASE.items kb t seed topK nsa secs T0 T1 iters outprefix
   Writes outprefix_best.edges (cover, A_i = i, B_j = m + j; check with bin/score37) and outprefix_best.items.
*/
#define main lift2_main
#include "lift2.c"
#undef main

#define TOPK 48
typedef struct { int cost, n, kb; char tag[8]; Item x[MAXI]; } Cand;
static Cand top[TOPK];

static int ntop = 0;
static int minc[26] = {0};

static int eval_items(const Item *x, int n, int kb) {
    k = kb + 1; m = k * t; F = k * t; H = 0; hu = -1;
    NI = n; memcpy(it, x, sizeof(Item) * n);
    for (int i = 0; i < NI; i++) if (dup_with(i)) return -1;
    if (!stubs_ok()) return -1;
    rebuild();
    if (!deg_ok()) return -1;
    return cost_full();
}
static void offer(int cost, const Item *x, int n, int kb, const char *tag) {
    if (cost < minc[tag[0] - 'A']) minc[tag[0] - 'A'] = cost;
    if (ntop == TOPK && cost >= top[TOPK - 1].cost) return;
    int pos = (ntop < TOPK) ? ntop++ : TOPK - 1;
    while (pos > 0 && top[pos - 1].cost > cost) { top[pos] = top[pos - 1]; pos--; }
    top[pos].cost = cost; top[pos].n = n; top[pos].kb = kb;
    memcpy(top[pos].x, x, sizeof(Item) * n);
    snprintf(top[pos].tag, sizeof top[pos].tag, "%s", tag);
}

/* SA from the current state (it, NI) with lift2 moves; returns best cost, best state in bIt/bNI */
static int sa_repair(double secs, double T0, double T1, long iters, Item *bIt, int *bNI, int *bcost) {
    double t0 = now();
    rebuild();
    int best = cost_full();
    memcpy(bIt, it, sizeof(Item) * NI); *bNI = NI;
    Item sv[MAXI]; int svNI;
    double lt0 = log(T0), lt1 = log(T1);
    long total = 0, rounds = 0;
    while (best > 0 && now() - t0 < secs) {
        rounds++;
        NI = *bNI; memcpy(it, bIt, sizeof(Item) * NI); rebuild();
        int cur = best;
        for (long s = 0; s < iters && now() - t0 < secs; s++) {
            double T = exp(lt0 + (lt1 - lt0) * (double)s / (double)iters);
            svNI = NI; memcpy(sv, it, sizeof(Item) * NI);
            if (!apply_move()) { NI = svNI; memcpy(it, sv, sizeof(Item) * NI); continue; }
            total++;
            rebuild();
            int nc = cost_full();
            int d = nc - cur;
            if (d <= 0 || rndu() < exp(-d / T)) {
                cur = nc;
                if (cur < best) { best = cur; *bNI = NI; memcpy(bIt, it, sizeof(Item) * NI); }
            } else { NI = svNI; memcpy(it, sv, sizeof(Item) * NI); rebuild(); }
        }
    }
    *bcost = best;
    printf("  sa: moves=%ld rounds=%ld best=%d time=%.0f\n", total, rounds, best, now() - t0);
    fflush(stdout);
    return best;
}


/* ---- breakout (clause weighting) repair: weights W on uncovered same-side pairs, bumped when stuck ---- */
static int W[MAXM][MAXM];
static void cover6(uint64_t Cv[MAXM][2]) {
    static uint64_t Bw[MAXM][2], H2[MAXM][2];
    for (int j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (int w2 = 0; w2 < 2; w2++) { uint64_t x = adj[j][w2];
            while (x) { int tt = __builtin_ctzll(x); x &= x - 1; int kk = w2 * 64 + tt; r0 |= adj[kk][0]; r1 |= adj[kk][1]; } }
        Bw[j][0] = r0; Bw[j][1] = r1;
    }
    for (int j = 0; j < m; j++) {
        uint64_t r0 = 0, r1 = 0;
        for (int w2 = 0; w2 < 2; w2++) { uint64_t x = Bw[j][w2];
            while (x) { int tt = __builtin_ctzll(x); x &= x - 1; int kk = w2 * 64 + tt; r0 |= Bw[kk][0]; r1 |= Bw[kk][1]; } }
        H2[j][0] = r0; H2[j][1] = r1;
    }
    for (int i = 0; i < m; i++) {
        uint64_t r0 = 0, r1 = 0;
        for (int w2 = 0; w2 < 2; w2++) { uint64_t x = Bw[i][w2];
            while (x) { int tt = __builtin_ctzll(x); x &= x - 1; int kk = w2 * 64 + tt; r0 |= H2[kk][0]; r1 |= H2[kk][1]; } }
        Cv[i][0] = r0; Cv[i][1] = r1;
    }
}
static int wcost(int *real, int bump) {
    static uint64_t Cv[MAXM][2];
    cover6(Cv);
    int wsum = 0, rsum = 0;
    for (int i = 0; i < m; i++) for (int j = i + 1; j < m; j++) {
        int cov = (Cv[i][j >> 6] >> (j & 63)) & 1;
        if (!cov) { wsum += W[i][j]; rsum++; if (bump) { W[i][j]++; W[j][i] = W[i][j]; } }
    }
    *real = rsum;
    return wsum;
}
static void setW1(void) { for (int i = 0; i < MAXM; i++) for (int j = 0; j < MAXM; j++) W[i][j] = 1; }
/* breakout repair from current state; K = non-improving proposals before a weight bump; returns best real cost */
static int breakout_run(double secs, long K, Item *bIt, int *bNI, int *bcost) {
    double t0 = now();
    setW1();
    rebuild();
    int rc, wc = wcost(&rc, 0);
    int best = rc; memcpy(bIt, it, sizeof(Item) * NI); *bNI = NI;
    Item sv[MAXI]; int svNI; long stuck = 0, props = 0, bumps = 0;
    while (best > 0 && now() - t0 < secs) {
        svNI = NI; memcpy(sv, it, sizeof(Item) * NI);
        props++;
        if (!apply_move()) { NI = svNI; memcpy(it, sv, sizeof(Item) * NI); continue; }
        rebuild();
        int nrc, nwc = wcost(&nrc, 0);
        if (nwc <= wc) {
            wc = nwc; rc = nrc;
            if (rc < best) { best = rc; *bNI = NI; memcpy(bIt, it, sizeof(Item) * NI); }
            stuck = 0;
        } else {
            NI = svNI; memcpy(it, sv, sizeof(Item) * NI); rebuild();
            if (++stuck >= K) {
                /* bump weights of the currently uncovered pairs */
                wcost(&rc, 1); bumps++;
                wc = wcost(&rc, 0);
                stuck = 0;
            }
        }
    }
    *bcost = best;
    printf("  breakout: props=%ld bumps=%ld best=%d time=%.0f\n", props, bumps, best, now() - t0);
    fflush(stdout);
    return best;
}

static void write_state(const char *outp, const Item *x, int n, int kb, int cost) {
    k = kb + 1; m = k * t; F = k * t; H = 0; hu = -1;
    NI = n; memcpy(it, x, sizeof(Item) * n); rebuild();
    char fn[512];
    snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(fn);
    snprintf(fn, sizeof fn, "%s_best.items", outp); write_items(fn, cost);
}

int main(int argc, char **argv) {
    if (argc < 12) { fprintf(stderr, "usage: grow BASE.items kb t seed topK nsa secs T0 T1 iters outprefix\n"); return 2; }
    const char *basef = argv[1];
    int kb = atoi(argv[2]); t = atoi(argv[3]); H = 0;
    for (int q = 0; q < 26; q++) minc[q] = 1 << 30;
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int topk = atoi(argv[5]), nsa = atoi(argv[6]);
    double secs = atof(argv[7]), T0 = atof(argv[8]), T1 = atof(argv[9]);
    long iters = atol(argv[10]);
    const char *outp = argv[11];
    if (topk > TOPK) topk = TOPK;

    FILE *f = fopen(basef, "r");
    if (!f) { perror(basef); return 1; }
    static Item base[MAXI]; int nb = 0; char line[512];
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#') continue;
        int ty, u, v, g;
        if (sscanf(line, "%d %d %d %d", &ty, &u, &v, &g) == 4) { base[nb].type = ty; base[nb].u = u; base[nb].v = v; base[nb].g = g; nb++; }
    }
    fclose(f);
    k = kb; m = k * t; F = k * t; H = 0; hu = -1;
    NI = nb; memcpy(it, base, sizeof(Item) * nb);
    if (!stubs_ok()) { fprintf(stderr, "base: stubs not 3 per vertex\n"); return 1; }
    rebuild();
    printf("base kb=%d t=%d items=%d cost=%d deg_ok=%d\n", kb, t, nb, cost_full(), deg_ok()); fflush(stdout);

    if (getenv("SAONLY")) {  /* SA on the base itself (k = kb, no insertion); writes outp_best.* */
        static Item bIt[MAXI]; int bNI = 0, bcost = 0;
        if (getenv("RANDINIT")) { k = kb; m = k * t; F = k * t; H = 0; hu = -1; random_init(); rebuild();
            printf("random init kb=%d cost=%d\n", kb, cost_full()); }
        if (getenv("BREAK")) breakout_run(secs, atol(getenv("BREAK")), bIt, &bNI, &bcost);
        else sa_repair(secs, T0, T1, iters, bIt, &bNI, &bcost);
        k = kb; m = k * t; F = k * t; H = 0; hu = -1; NI = bNI; memcpy(it, bIt, sizeof(Item) * NI); rebuild();
        char fn[512];
        snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(fn);
        snprintf(fn, sizeof fn, "%s_best.items", outp); write_items(fn, bcost);
        printf("SAONLY kb=%d best cost=%d far=%d\n", kb, bcost, 2 * bcost);
        return 0;
    }
    int w = kb;
    static Item x[MAXI];
    int n;
    long nA = 0, vA = 0, nB = 0, vB = 0;
    /* A: subdivide an edge with w, 1-stub loop at w */
    for (int e = 0; e < nb; e++) {
        if (base[e].type != 0) continue;
        int a = base[e].u, b = base[e].v;
        for (int g1 = 0; g1 < t; g1++) for (int g2 = 0; g2 < t; g2++) {
            n = 0;
            for (int i = 0; i < nb; i++) if (i != e) x[n++] = base[i];
            x[n++] = mk_edge(a, w, g1);
            x[n++] = mk_edge(w, b, g2);
            x[n++] = mk_loop(w, 0);
            nA++;
            int c = eval_items(x, n, kb);
            if (c >= 0) { vA++; offer(c, x, n, kb, "A"); }
        }
    }
    /* B: two edges removed, w joined to one end of each, other ends joined, 1-stub loop at w */
    for (int i = 0; i < nb; i++) {
        if (base[i].type != 0) continue;
        for (int j = i + 1; j < nb; j++) {
            if (base[j].type != 0) continue;
            for (int p = 0; p < 2; p++) for (int q = 0; q < 2; q++) {
                int Wp = p ? base[i].v : base[i].u, Op = p ? base[i].u : base[i].v;
                int Wq = q ? base[j].v : base[j].u, Oq = q ? base[j].u : base[j].v;
                if (Op == Oq) continue;
                for (int h1 = 0; h1 < t; h1++) for (int h2 = 0; h2 < t; h2++) for (int h3 = 0; h3 < t; h3++) {
                    n = 0;
                    for (int l = 0; l < nb; l++) if (l != i && l != j) x[n++] = base[l];
                    x[n++] = mk_edge(Wp, w, h1);
                    x[n++] = mk_edge(Wq, w, h2);
                    x[n++] = mk_edge(Op, Oq, h3);
                    x[n++] = mk_loop(w, 0);
                    nB++;
                    int c = eval_items(x, n, kb);
                    if (c >= 0) { vB++; offer(c, x, n, kb, "B"); }
                }
            }
        }
    }

    /* C: three edges removed; w joined to one end of each (h1 = 0 WLOG), the other three ends: one gets a
       1-stub loop (g = 0), the other two are joined (voltage h4) */
    long nC = 0, vC = 0;
    if (getenv("NOC") == NULL)
    for (int i = 0; i < nb; i++) { if (base[i].type != 0) continue;
     for (int j = i + 1; j < nb; j++) { if (base[j].type != 0) continue;
      for (int l = j + 1; l < nb; l++) { if (base[l].type != 0) continue;
       int ei[3] = {i, j, l};
       for (int mask = 0; mask < 8; mask++) for (int r = 0; r < 3; r++) {
          int W[3], O[3];
          for (int q = 0; q < 3; q++) { int e = ei[q]; int bit = (mask >> q) & 1;
             W[q] = bit ? base[e].v : base[e].u; O[q] = bit ? base[e].u : base[e].v; }
          /* O[r] gets the loop; O[(r+1)%3], O[(r+2)%3] are joined */
          int s1 = (r + 1) % 3, s2 = (r + 2) % 3;
          if (O[s1] == O[s2]) continue;
          for (int h2 = 0; h2 < t; h2++) for (int h3 = 0; h3 < t; h3++) for (int h4 = 0; h4 < t; h4++) {
             n = 0;
             for (int q = 0; q < nb; q++) if (q != i && q != j && q != l) x[n++] = base[q];
             x[n++] = mk_edge(W[0], w, 0);
             x[n++] = mk_edge(W[1], w, h2);
             x[n++] = mk_edge(W[2], w, h3);
             x[n++] = mk_edge(O[s1], O[s2], h4);
             x[n++] = mk_loop(O[r], 0);
             nC++;
             int c = eval_items(x, n, kb);
             if (c >= 0) { vC++; offer(c, x, n, kb, "C"); }
          }
       }
      }
     }
    }

    /* D: w gets a 2-stub loop (g = 1 or 2) and one edge to pa; edge (pa,ob) removed; the 1-stub loop at c is replaced
       by the edge (ob,c) (voltage h2); h1 = 0 WLOG */
    long nD = 0, vD = 0;
    for (int e = 0; e < nb; e++) {
        if (base[e].type != 0) continue;
        for (int ps = 0; ps < 2; ps++) {
            int pa = ps ? base[e].v : base[e].u, ob = ps ? base[e].u : base[e].v;
            for (int L = 0; L < nb; L++) {
                if (base[L].type != 1 || !stub1(base[L].g)) continue;
                int c = base[L].u;
                if (c == ob) continue;
                for (int lg = 1; lg <= 2; lg++) for (int h2 = 0; h2 < t; h2++) {
                    n = 0;
                    for (int q = 0; q < nb; q++) if (q != e && q != L) x[n++] = base[q];
                    x[n++] = mk_edge(pa, w, 0);
                    x[n++] = mk_loop(w, lg);
                    x[n++] = mk_edge(ob, c, h2);
                    nD++;
                    int cc = eval_items(x, n, kb);
                    if (cc >= 0) { vD++; offer(cc, x, n, kb, "D"); }
                }
            }
        }
    }
    printf("insertions: A evaluated %ld valid %ld; B evaluated %ld valid %ld; C evaluated %ld valid %ld; D evaluated %ld valid %ld\n", nA, vA, nB, vB, nC, vC, nD, vD);
    for (int q = 0; q < 26; q++) if (minc[q] < (1 << 30)) printf("min cost option %c = %d\n", 'A' + q, minc[q]);
    printf("top costs:");
    for (int i = 0; i < ntop && i < 16; i++) printf(" %d%s", top[i].cost, top[i].tag);
    printf("\n"); fflush(stdout);
    if (ntop == 0) return 0;
    if (getenv("DUMP")) {  /* write the top candidates (before SA) as item files */
        for (int c = 0; c < ntop && c < topk; c++) {
            char fn[512]; snprintf(fn, sizeof fn, "%s_top%02d.items", outp, c);
            k = top[c].kb + 1; m = k * t; F = k * t; H = 0; hu = -1; NI = top[c].n; memcpy(it, top[c].x, sizeof(Item) * NI);
            write_items(fn, top[c].cost);
        }
    }

    int gbest = 1 << 30; static Item gIt[MAXI]; int gNI = 0;
    for (int c = 0; c < ntop && c < nsa && gbest > 0; c++) {
        k = top[c].kb + 1; m = k * t; F = k * t; H = 0; hu = -1;
        NI = top[c].n; memcpy(it, top[c].x, sizeof(Item) * NI);
        static Item bIt[MAXI]; int bNI = 0, bcost = 0;
        printf("cand %d (%s) start cost %d\n", c, top[c].tag, top[c].cost); fflush(stdout);
        if (getenv("BREAK")) breakout_run(secs, atol(getenv("BREAK")), bIt, &bNI, &bcost);
        else sa_repair(secs, T0, T1, iters, bIt, &bNI, &bcost);
        if (bcost < gbest) {
            gbest = bcost; gNI = bNI; memcpy(gIt, bIt, sizeof(Item) * bNI);
            write_state(outp, gIt, gNI, kb, gbest);
            printf("NEW BEST cost=%d far_bound=%d (cand %d)\n", gbest, 2 * gbest, c); fflush(stdout);
        }
    }
    printf("FINAL kb=%d n=%d best cost=%d\n", kb, 2 * (kb + 1) * t, gbest);
    return 0;
}
