/* wanti.c (card c7): colour-swapping Haar graphs with pi(x) = beta(x)^-1 w, w in G (not only w = e).
 *
 * H(G,S): vertices (g,A), (g,B); (g,A) ~ (s g, B) for s in S, |S| = 7.
 * For an automorphism beta and w in G, let pi(x) = beta(x)^-1 w. If pi(S) = S, the map
 *   (g,A) -> (beta(g) a, B),  (h,B) -> (w^-1 beta(h) a, A)     (a in G arbitrary, take a = e)
 * is a colour-swapping automorphism: edge (g,A)-(h,B) (h g^-1 in S) maps to an edge iff
 * beta(g) beta(h)^-1 w in S, i.e. pi(h g^-1) in S. Hence diam <= 5 iff X X = G, X = S^-1 S (A-side distance <= 4).
 * Normal form: S -> d S c^-1 is an isomorphism; it maps (beta, w) to (beta, w') with w' = beta^2(c) w c^-1, so w is
 * taken over orbit representatives of that action. w = e is the family of haar75 anti; for beta^2 = 1 the w != e
 * classes are genuinely new.
 * Enumeration: for each (beta, w) the cycles of pi of length <= 7; S = union of cycles of total size 7 (all
 * partitions of 7); exhaustive if the number of combinations <= CAP, else CAP random combinations.
 * Score: cost = |G \ X X| (0 = valid).
 * usage: wanti FILE.ht [CAP=400] [SEED=1] [PMAX=7]     env EDGES=path writes the first valid S as an edge list.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int n, ninv;
static uint16_t *mul;
static int *inv;
static int nal; static int alp[64]; static int *aperm[64];
static uint32_t *stamp; static uint32_t stv = 0;
static uint32_t *stamp2; static uint32_t stv2 = 0;
static long long evals = 0;
static const char *edges_out = NULL; static int wrote = 0;
static uint64_t rng = 88172645463325252ULL;
static unsigned rnd(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return (unsigned)(rng >> 11); }

#define M(a,b) mul[(size_t)(a) * n + (b)]

static int rdint(FILE *f) { int x; if (fscanf(f, "%d", &x) != 1) { fprintf(stderr, "read error\n"); exit(1); } return x; }

static void load(const char *path) {
    FILE *f = fopen(path, "r"); if (!f) { perror(path); exit(1); }
    n = rdint(f); ninv = rdint(f);
    mul = malloc(sizeof(uint16_t) * (size_t)n * n); inv = malloc(sizeof(int) * n);
    for (size_t i = 0; i < (size_t)n * n; i++) mul[i] = rdint(f);
    for (int i = 0; i < n; i++) inv[i] = rdint(f);
    char w[32];
    while (fscanf(f, "%31s", w) == 1) {
        if (!strcmp(w, "ALPHA")) {
            int p = rdint(f); alp[nal] = p; aperm[nal] = malloc(sizeof(int) * n);
            for (int i = 0; i < n; i++) aperm[nal][i] = rdint(f);
            if (fscanf(f, "%31s", w) != 1 || strcmp(w, "CENT")) { fprintf(stderr, "format\n"); exit(1); }
            int k = rdint(f);
            for (int j = 0; j < k; j++) for (int i = 0; i < n; i++) rdint(f);
            nal++; if (nal >= 64) break;
        }
    }
    fclose(f);
    stamp = calloc(n, sizeof(uint32_t)); stamp2 = calloc(n, sizeof(uint32_t));
}

/* cycles of pi of length <= 7 */
#define MAXL 7
static int *cyc_el; static int cyc_off[4 * 1024 * 16]; static int cyc_len[4 * 1024 * 16]; static int ncyc;
static int *bylen[MAXL + 1]; static int nbylen[MAXL + 1];

static long long nsol_total = 0;

static int eval_set(const int *S) {
    /* X = S^-1 S, then X X; return number of uncovered elements */
    static int X[64]; int nx = 0;
    stv++;
    for (int i = 0; i < 7; i++) for (int j = 0; j < 7; j++) {
        int x = M(inv[S[i]], S[j]);
        if (stamp[x] != stv) { stamp[x] = stv; X[nx++] = x; }
    }
    stv2++;
    int cov = 0;
    for (int a = 0; a < nx; a++) for (int b = 0; b < nx; b++) {
        int y = M(X[a], X[b]);
        if (stamp2[y] != stv2) { stamp2[y] = stv2; cov++; }
    }
    evals++;
    return n - cov;
}

/* partition of 7 given as (len, mult) pairs */
static int parts[16][8][2]; static int npart[16]; static int nparts = 0;
static void gen_parts(int rem, int maxp, int *cur, int depth) {
    if (rem == 0) {
        int k = 0; for (int i = 0; i < depth; i += 0) break;
        /* convert cur (non-increasing list of lengths) to (len,mult) */
        int idx = nparts; npart[idx] = 0;
        for (int i = 0; i < depth;) {
            int j = i; while (j < depth && cur[j] == cur[i]) j++;
            parts[idx][npart[idx]][0] = cur[i]; parts[idx][npart[idx]][1] = j - i; npart[idx]++;
            i = j;
        }
        (void)k; nparts++; return;
    }
    for (int p = (rem < maxp ? rem : maxp); p >= 1; p--) { cur[depth] = p; gen_parts(rem - p, p, cur, depth + 1); }
}

static double binom(int a, int b) { if (b < 0 || b > a) return 0; double r = 1; for (int i = 1; i <= b; i++) r = r * (a - b + i) / i; return r; }

static int cur_S[7];
static int cur_alpha, cur_w, cur_part;
static int bestc_here; static long long hits_here;

static void report(const int *S, int cost, int part_id) {
    if (cost == 0) {
        nsol_total++; hits_here++;
        printf("SOL alpha %d w %d part %d S", cur_alpha, cur_w, part_id);
        for (int i = 0; i < 7; i++) printf(" %d", S[i]);
        printf("\n");
        if (edges_out && !wrote) {
            FILE *f = fopen(edges_out, "w");
            if (f) {
                fprintf(f, "%d\n", 2 * n);
                for (int g = 0; g < n; g++) for (int i = 0; i < 7; i++) fprintf(f, "%d %d\n", g, n + M(S[i], g));
                fclose(f); wrote = 1;
            }
        }
    }
    if (cost < bestc_here) bestc_here = cost;
}

/* recursive choice of cycles for part p (groups g = 0..npart-1), cycle lists chosen from bylen */
static void choose_rec(int part_id, int g, int start_in_group, int *pick_stack, int depth, int lim_mode) {
    (void)lim_mode;
    if (g == npart[part_id]) {
        int pos = 0;
        for (int d = 0; d < depth; d++) {
            int c = pick_stack[d];
            for (int t = 0; t < cyc_len[c]; t++) cur_S[pos++] = cyc_el[cyc_off[c] + t];
        }
        int cost = eval_set(cur_S);
        report(cur_S, cost, part_id);
        return;
    }
    int L = parts[part_id][g][0], mlt = parts[part_id][g][1];
    /* choose mlt distinct cycles from bylen[L] (indices >= start_in_group, increasing) */
    int need = mlt;
    /* recursion over sorted index combos */
    int idx[7]; int avail = nbylen[L];
    if (avail < need) return;
    for (int i = 0; i < need; i++) idx[i] = i;
    for (;;) {
        for (int i = 0; i < need; i++) pick_stack[depth + i] = bylen[L][idx[i]];
        choose_rec(part_id, g + 1, 0, pick_stack, depth + need, 0);
        int i = need - 1;
        while (i >= 0 && idx[i] == avail - need + i) i--;
        if (i < 0) break;
        idx[i]++;
        for (int j = i + 1; j < need; j++) idx[j] = idx[j - 1] + 1;
    }
}

static void random_rec(int part_id, int *pick_stack) {
    int depth = 0;
    for (int g = 0; g < npart[part_id]; g++) {
        int L = parts[part_id][g][0], mlt = parts[part_id][g][1];
        int avail = nbylen[L];
        /* partial Fisher-Yates on a copy of indices */
        int tmp[64]; int m = avail < 64 ? avail : 64;
        if (avail > 64) { /* fallback: rejection sampling */
            for (int t = 0; t < mlt; t++) {
                int ok; int c;
                do { c = bylen[L][rnd() % avail]; ok = 1;
                    for (int u = 0; u < depth; u++) if (pick_stack[u] == c) ok = 0; } while (!ok);
                pick_stack[depth++] = c;
            }
            continue;
        }
        for (int t = 0; t < m; t++) tmp[t] = bylen[L][t];
        for (int t = 0; t < mlt; t++) { int r = t + rnd() % (m - t); int x = tmp[t]; tmp[t] = tmp[r]; tmp[r] = x; pick_stack[depth++] = tmp[t]; }
    }
    int pos = 0;
    for (int d = 0; d < depth; d++) { int c = pick_stack[d]; for (int t = 0; t < cyc_len[c]; t++) cur_S[pos++] = cyc_el[cyc_off[c] + t]; }
    int cost = eval_set(cur_S);
    /* part id is set by caller through cur_part */
    report(cur_S, cost, cur_part);
}


/* simulated annealing over cycle choices of partition pp (replace one cycle by another of the same length) */
static int sa_run(int pp, long iters, int restarts) {
    int slotlen[8]; int ns = 0;
    for (int g = 0; g < npart[pp]; g++) for (int t = 0; t < parts[pp][g][1]; t++) slotlen[ns++] = parts[pp][g][0];
    int state[8]; int best = 1 << 30;
    for (int rs = 0; rs < restarts; rs++) {
        int ok = 1;
        for (int i = 0; i < ns && ok; i++) {
            int L = slotlen[i];
            int tries = 0; int c;
            do { if (nbylen[L] == 0) { ok = 0; break; } c = bylen[L][rnd() % nbylen[L]];
                 int dup = 0; for (int j = 0; j < i; j++) if (state[j] == c) dup = 1;
                 if (!dup) break; } while (++tries < 100);
            if (!ok) break;
            state[i] = c;
        }
        if (!ok) return best;
        int pos = 0;
        #define BUILD { pos = 0; for (int i2 = 0; i2 < ns; i2++) { int c2 = state[i2]; for (int t2 = 0; t2 < cyc_len[c2]; t2++) cur_S[pos++] = cyc_el[cyc_off[c2] + t2]; } }
        BUILD;
        int cost = eval_set(cur_S);
        int bcost = cost; int bstate[8]; memcpy(bstate, state, sizeof(state));
        for (long it = 0; it < iters && cost > 0; it++) {
            double T = 3.0 * (1.0 - (double)it / iters) + 0.05;
            int i = rnd() % ns; int L = slotlen[i]; int old = state[i];
            int c = bylen[L][rnd() % nbylen[L]];
            int dup = 0; for (int j = 0; j < ns; j++) if (state[j] == c) dup = 1;
            if (dup || c == old) continue;
            state[i] = c; BUILD; int nc = eval_set(cur_S);
            int d = nc - cost;
            if (d <= 0 || (double)(rnd() % 1000000) / 1e6 < __builtin_exp(-d / T)) {
                cost = nc;
                if (cost < bcost) { bcost = cost; memcpy(bstate, state, sizeof(state)); }
            } else state[i] = old;
        }
        memcpy(state, bstate, sizeof(state)); BUILD;
        cost = eval_set(cur_S);
        if (cost == 0) report(cur_S, 0, pp);
        if (cost < best) best = cost;
        if (cost < bestc_here) bestc_here = cost;
    }
    return best;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: wanti FILE.ht [CAP] [SEED] [PMAX]\n"); return 1; }
    long CAP = argc > 2 ? atol(argv[2]) : 400;
    rng ^= (uint64_t)(argc > 3 ? atol(argv[3]) : 1) * 0x9E3779B97F4A7C15ULL;
    int PMAX = argc > 4 ? atoi(argv[4]) : 7;
    edges_out = getenv("EDGES");
    long sa_iters = getenv("SA") ? atol(getenv("SA")) : 0;
    int sa_restarts = getenv("SAR") ? atoi(getenv("SAR")) : 2;
    load(argv[1]);
    /* partitions of 7 */
    int cur[8]; gen_parts(7, 7, cur, 0);
    cyc_el = malloc(sizeof(int) * (size_t)n * 8);
    int *cyc_el_tmp = cyc_el; (void)cyc_el_tmp;
    int *seen = malloc(sizeof(int) * n);
    int *pick = malloc(sizeof(int) * 64);
    int *wrep = malloc(sizeof(int) * n);
    int *beta2 = malloc(sizeof(int) * n);
    int *pi = malloc(sizeof(int) * n);
    char *mark = malloc(n);
    for (int L = 1; L <= MAXL; L++) bylen[L] = malloc(sizeof(int) * (n + 1));
    for (int a = 0; a < nal; a++) {
        int p = alp[a]; if (p > PMAX) continue;
        int *beta = aperm[a];
        for (int x = 0; x < n; x++) beta2[x] = beta[beta[x]];
        /* orbit representatives of w under w -> beta2(c) w c^-1 */
        memset(mark, 0, n); int nreps = 0;
        for (int w = 0; w < n; w++) {
            if (mark[w]) continue;
            wrep[nreps++] = w;
            for (int c = 0; c < n; c++) mark[M(M(beta2[c], w), inv[c])] = 1;
        }
        int alpha_best = 1 << 30; long long alpha_hits = 0;
        for (int r = 0; r < nreps; r++) {
            int w = wrep[r];
            for (int x = 0; x < n; x++) pi[x] = M(inv[beta[x]], w);
            /* cycles of pi with length <= 7 */
            memset(seen, 0, sizeof(int) * n);
            ncyc = 0; for (int L = 1; L <= MAXL; L++) nbylen[L] = 0;
            int *tmpbuf = malloc(sizeof(int) * (n + 1));
            int ptotal = 0;
            for (int x = 0; x < n; x++) {
                if (seen[x]) continue;
                int L = 0, y = x;
                do { if (L < n) tmpbuf[L] = y; L++; seen[y] = 1; y = pi[y]; } while (y != x);
                if (L > MAXL) continue;
                int c = ncyc++;
                cyc_off[c] = ptotal; cyc_len[c] = L;
                for (int t = 0; t < L; t++) cyc_el[ptotal++] = tmpbuf[t];
                nbylen[L]++;
            }
            free(tmpbuf);
            for (int L = 1; L <= MAXL; L++) nbylen[L] = 0;
            for (int c = 0; c < ncyc; c++) bylen[cyc_len[c]][nbylen[cyc_len[c]]++] = c;
            (void)ptotal;
            /* enumerate partitions of 7 */
            bestc_here = 1 << 30; hits_here = 0;
            if (sa_iters > 0) {
                for (int pp = 0; pp < nparts; pp++) {
                    cur_alpha = p; cur_w = w; cur_part = pp;
                    int bc = sa_run(pp, sa_iters, sa_restarts);
                    if (bc < bestc_here) bestc_here = bc;
                }
            } else
            for (int pp = 0; pp < nparts; pp++) {
                double count = 1;
                int ok = 1;
                for (int g = 0; g < npart[pp]; g++) {
                    int L = parts[pp][g][0], mlt = parts[pp][g][1];
                    if (L > MAXL || nbylen[L] < mlt) { ok = 0; break; }
                    count *= binom(nbylen[L], mlt);
                }
                if (!ok) continue;
                cur_alpha = p; cur_w = w; cur_part = pp;
                if (count <= CAP) {
                    choose_rec(pp, 0, 0, pick, 0, 0);
                } else {
                    for (long t = 0; t < CAP; t++) { cur_part = pp; random_rec(pp, pick); }
                }
            }
            if (bestc_here < alpha_best) alpha_best = bestc_here;
            alpha_hits += hits_here;
            if (getenv("VERB")) printf("ALPHA_W p %d a %d w %d cycles %d best %d hits %lld\n", p, a, w, ncyc, bestc_here, hits_here);
        }
        printf("ALPHA p %d idx %d reps %d best_cost %d hits %lld evals %lld\n", p, a, nreps, alpha_best, alpha_hits, evals);
        fflush(stdout);
    }
    printf("DONE n %d total_hits %lld\n", n, nsol_total);
    return 0;
}
