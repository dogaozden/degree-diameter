/* grow2s.c (r3g): two-stage Z_t orbit insertion. Parent = zero (or low-cost) base with kb vertices (m = kb*t).
   Stage 1: insert base vertex w1 = kb (options A, B, C, D as in grow.c), keep the TOPK1 best covers at kb+1.
   Stage 2: for each of them insert w2 = kb+1 (options A, B, D; C only if env USEC2), keep the best TOPK at kb+2.
   Then breakout / SA repair of the best few kb+2 candidates.
   Usage: grow2s BASE.items kb t seed topK1 topK nrep secs T0 T1 iters outprefix   (env BREAK=K for breakout)
*/
#define main lift2_main
#include "lift2.c"
#undef main
#include "repair.h"

#define TOPK 64
typedef struct { int cost, n, kb; char tag[8]; Item x[MAXI]; } Cand;
static Cand *top;       /* sorted pool, capacity cap */
static int ntop = 0, cap = 0;
static int minc[26];

static int eval_items(const Item *x, int n, int kb) {
    k = kb + 1; m = k * t; F = k * t; H = 0; hu = -1;
    NI = n; memcpy(it, x, sizeof(Item) * n);
    for (int i = 0; i < NI; i++) if (dup_with(i)) return -1;
    if (!stubs_ok()) return -1;
    rebuild();
    if (!deg_ok()) return -1;
    return cost_full();
}
static void offer(Cand *pool, int *np, int capn, int cost, const Item *x, int n, int kb, const char *tag) {
    if (cost < minc[tag[0] - 'A']) minc[tag[0] - 'A'] = cost;
    if (*np == capn && cost >= pool[capn - 1].cost) return;
    int pos = (*np < capn) ? (*np)++ : capn - 1;
    while (pos > 0 && pool[pos - 1].cost > cost) { pool[pos] = pool[pos - 1]; pos--; }
    pool[pos].cost = cost; pool[pos].n = n; pool[pos].kb = kb;
    memcpy(pool[pos].x, x, sizeof(Item) * n);
    snprintf(pool[pos].tag, sizeof pool[pos].tag, "%s", tag);
}

/* enumerate insertions of w = kb into base (nb items, kb vertices); offers into pool */
static void enumerate_ins(const Item *base, int nb, int kb, int useC, Cand *pool, int *np, int capn, long *cnt) {
    int w = kb;
    static Item x[MAXI];
    int n;
    for (int e = 0; e < nb; e++) {               /* A */
        if (base[e].type != 0) continue;
        int a = base[e].u, b = base[e].v;
        for (int g1 = 0; g1 < t; g1++) for (int g2 = 0; g2 < t; g2++) {
            n = 0;
            for (int i = 0; i < nb; i++) if (i != e) x[n++] = base[i];
            x[n++] = mk_edge(a, w, g1); x[n++] = mk_edge(w, b, g2); x[n++] = mk_loop(w, 0);
            int c = eval_items(x, n, kb); (*cnt)++;
            if (c >= 0) offer(pool, np, capn, c, x, n, kb, "A");
        }
    }
    for (int i = 0; i < nb; i++) {               /* B */
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
                    x[n++] = mk_edge(Wp, w, h1); x[n++] = mk_edge(Wq, w, h2);
                    x[n++] = mk_edge(Op, Oq, h3); x[n++] = mk_loop(w, 0);
                    int c = eval_items(x, n, kb); (*cnt)++;
                    if (c >= 0) offer(pool, np, capn, c, x, n, kb, "B");
                }
            }
        }
    }
    for (int e = 0; e < nb; e++) {               /* D */
        if (base[e].type != 0) continue;
        for (int ps = 0; ps < 2; ps++) {
            int pa = ps ? base[e].v : base[e].u, ob = ps ? base[e].u : base[e].v;
            for (int L = 0; L < nb; L++) {
                if (base[L].type != 1 || !stub1(base[L].g)) continue;
                int c0 = base[L].u;
                if (c0 == ob) continue;
                for (int lg = 1; lg <= 2; lg++) for (int h2 = 0; h2 < t; h2++) {
                    n = 0;
                    for (int q = 0; q < nb; q++) if (q != e && q != L) x[n++] = base[q];
                    x[n++] = mk_edge(pa, w, 0); x[n++] = mk_loop(w, lg); x[n++] = mk_edge(ob, c0, h2);
                    int c = eval_items(x, n, kb); (*cnt)++;
                    if (c >= 0) offer(pool, np, capn, c, x, n, kb, "D");
                }
            }
        }
    }
    if (useC) {                                  /* C */
        for (int i = 0; i < nb; i++) { if (base[i].type != 0) continue;
         for (int j = i + 1; j < nb; j++) { if (base[j].type != 0) continue;
          for (int l = j + 1; l < nb; l++) { if (base[l].type != 0) continue;
           int ei[3] = {i, j, l};
           for (int mask = 0; mask < 8; mask++) for (int r = 0; r < 3; r++) {
              int W[3], O[3];
              for (int q = 0; q < 3; q++) { int e = ei[q]; int bit = (mask >> q) & 1;
                 W[q] = bit ? base[e].v : base[e].u; O[q] = bit ? base[e].u : base[e].v; }
              int s1 = (r + 1) % 3, s2 = (r + 2) % 3;
              if (O[s1] == O[s2]) continue;
              for (int h2 = 0; h2 < t; h2++) for (int h3 = 0; h3 < t; h3++) for (int h4 = 0; h4 < t; h4++) {
                 n = 0;
                 for (int q = 0; q < nb; q++) if (q != i && q != j && q != l) x[n++] = base[q];
                 x[n++] = mk_edge(W[0], w, 0); x[n++] = mk_edge(W[1], w, h2); x[n++] = mk_edge(W[2], w, h3);
                 x[n++] = mk_edge(O[s1], O[s2], h4); x[n++] = mk_loop(O[r], 0);
                 int c = eval_items(x, n, kb); (*cnt)++;
                 if (c >= 0) offer(pool, np, capn, c, x, n, kb, "C");
              }
           }
          }
         }
        }
    }
}

static int sa_or_break(double secs, double T0, double T1, long iters, Item *bIt, int *bNI, int *bcost);

int main(int argc, char **argv) {
    if (argc < 13) { fprintf(stderr, "usage: grow2s BASE.items kb t seed topK1 topK nrep secs T0 T1 iters outprefix\n"); return 2; }
    const char *basef = argv[1];
    int kb = atoi(argv[2]); t = atoi(argv[3]); H = 0;
    rs ^= (uint64_t)atoll(argv[4]) * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rnd();
    int topk1 = atoi(argv[5]), topk = atoi(argv[6]), nrep = atoi(argv[7]);
    double secs = atof(argv[8]), T0 = atof(argv[9]), T1 = atof(argv[10]);
    long iters = atol(argv[11]);
    const char *outp = argv[12];
    for (int q = 0; q < 26; q++) minc[q] = 1 << 30;
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
    if (!stubs_ok()) { fprintf(stderr, "base: stubs bad\n"); return 1; }
    rebuild();
    printf("parent kb=%d t=%d cost=%d\n", kb, t, cost_full()); fflush(stdout);

    /* stage 1 */
    cap = topk1; top = calloc(topk1, sizeof(Cand));
    long cnt1 = 0; int np1 = 0;
    enumerate_ins(base, nb, kb, 1, top, &np1, topk1, &cnt1);
    printf("stage1: %ld evaluated, kept %d (min cost %d)\n", cnt1, np1, np1 ? top[0].cost : -1); fflush(stdout);
    static Cand mid[64]; int nmid = np1;
    memcpy(mid, top, sizeof(Cand) * np1);
    free(top);

    /* stage 2 */
    Cand *pool2 = calloc(topk, sizeof(Cand));
    int np2 = 0; long cnt2 = 0;
    for (int c = 0; c < nmid; c++) {
        static Item mb[MAXI];
        int mn = mid[c].n; memcpy(mb, mid[c].x, sizeof(Item) * mn);
        enumerate_ins(mb, mn, kb + 1, 0, pool2, &np2, topk, &cnt2);
    }
    printf("stage2: %ld evaluated (from %d stage-1 covers), kept %d, min cost %d\n", cnt2, nmid, np2, np2 ? pool2[0].cost : -1);
    printf("min per option:"); for (int q = 0; q < 26; q++) if (minc[q] < (1 << 30)) printf(" %c=%d", 'A' + q, minc[q]);
    printf("\nstage2 top costs:"); for (int i = 0; i < np2 && i < 16; i++) printf(" %d%s", pool2[i].cost, pool2[i].tag); printf("\n"); fflush(stdout);

    /* repair of the best few */
    int gbest = 1 << 30; static Item gIt[MAXI]; int gNI = 0;
    for (int c = 0; c < np2 && c < nrep && gbest > 0; c++) {
        k = pool2[c].kb + 1; m = k * t; F = k * t; H = 0; hu = -1;
        NI = pool2[c].n; memcpy(it, pool2[c].x, sizeof(Item) * NI);
        static Item bIt[MAXI]; int bNI = 0, bcost = 0;
        printf("cand %d (%s) start %d\n", c, pool2[c].tag, pool2[c].cost); fflush(stdout);
        sa_or_break(secs, T0, T1, iters, bIt, &bNI, &bcost);
        if (bcost < gbest) {
            gbest = bcost; gNI = bNI; memcpy(gIt, bIt, sizeof(Item) * bNI);
            k = kb + 2; m = k * t; F = k * t; H = 0; hu = -1; NI = gNI; memcpy(it, gIt, sizeof(Item) * NI); rebuild();
            char fn[512];
            snprintf(fn, sizeof fn, "%s_best.edges", outp); write_cover(fn);
            snprintf(fn, sizeof fn, "%s_best.items", outp); write_items(fn, gbest);
            printf("NEW BEST cost=%d\n", gbest); fflush(stdout);
        }
    }
    printf("FINAL n=%d best cost=%d\n", 2 * (kb + 2) * t, gbest);
    return 0;
}
/* repair dispatcher: breakout if BREAK is set, else lift2-style SA */
static int sa_or_break(double secs, double T0, double T1, long iters, Item *bIt, int *bNI, int *bcost) {
    if (getenv("BREAK")) return breakout_run(secs, atol(getenv("BREAK")), bIt, bNI, bcost);
    return sa_repair(secs, T0, T1, iters, bIt, bNI, bcost);
}
