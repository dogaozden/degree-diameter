/* relaxed_bb.c: exact search for relaxed sets T in W(q) (fact 12), using the regular-spread group structure.
   Input (relax_groups_W<q>.txt): n, then per point "g k nb1 ... nbk" where g = index of its regular spread line.
   T must satisfy: (a) at most one point per spread line (automatic from the spread-line constraint), (b) every point
   of T has at most one collinear neighbour in T. (Pairs on a spread line are forbidden; every other collinear pair
   is allowed, exactly as in relaxed.c.)
   Branch and bound over the groups g = 0..G-1 in order: choose none or one of the group's points.
   Bound: current size + number of undecided groups that still contain a feasible point (feasibility is monotone).
   usage: relaxed_bb FILE TARGET [SYM]
     Searches for a relaxed set of size >= TARGET. Prints "FOUND size ..." with the set, or "NONE target ..." when the
     search space is exhausted (so max < TARGET). Prints the node count and time. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static int n, G, *grp, *deg, **nb, *cnt, *chosen, *gfirst, *gsize, *gpts;
static int target, found = 0;
static long long nodes = 0;
static int bestset[1024], bestsz = 0, cur = 0;


static int feasible(int p) {
    if (cnt[p] > 1) return 0;
    for (int k = 0; k < deg[p]; k++) {
        int x = nb[p][k];
        if (chosen[x] && cnt[x] != 0) return 0;
    }
    return 1;
}

static void add(int p, int sgn) {
    chosen[p] = sgn > 0;
    for (int k = 0; k < deg[p]; k++) cnt[nb[p][k]] += sgn;
}

static int decided[1024];
static int skipbudget;
static int undecided;

static void rec2(void) {
    if (found) return;
    nodes++;
    if (cur >= target) {
        found = 1;
        int m = 0; for (int i = 0; i < n; i++) if (chosen[i]) bestset[m++] = i;
        bestsz = m; return;
    }
    /* bound: undecided groups that still contain a feasible point; pick the group with fewest options */
    int avail = 0, bestg = -1, bestc = 1 << 30;
    for (int h = 0; h < G; h++) {
        if (decided[h]) continue;
        int c = 0;
        for (int j = 0; j < gsize[h]; j++) if (feasible(gpts[gfirst[h] + j])) c++;
        if (c > 0) avail++;
        if (c < bestc || (c == bestc && c > 0 && gsize[h] < gsize[bestg])) { bestc = c; bestg = h; }
    }
    if (cur + avail < target) return;
    if (bestg < 0) return;                       /* no undecided group left */
    int h = bestg;
    decided[h] = 1;
    for (int j = 0; j < gsize[h] && !found; j++) {
        int p = gpts[gfirst[h] + j];
        if (!feasible(p)) continue;
        add(p, +1); cur++;
        rec2();
        add(p, -1); cur--;
    }
    if (!found && skipbudget > 0) {              /* leave group h empty (at most G - target groups may be empty) */
        skipbudget--;
        rec2();
        skipbudget++;
    }
    decided[h] = 0;
}

int main(int argc, char **argv) {
    FILE *f = fopen(argv[1], "r");
    target = atoi(argv[2]);
    if (fscanf(f, "%d", &n) != 1) return 1;
    grp = malloc(n * sizeof(int)); deg = malloc(n * sizeof(int)); nb = malloc(n * sizeof(int *));
    cnt = calloc(n, sizeof(int)); chosen = calloc(n, sizeof(int));
    G = 0;
    for (int i = 0; i < n; i++) {
        if (fscanf(f, "%d %d", &grp[i], &deg[i]) != 2) return 1;
        nb[i] = malloc((deg[i] + 1) * sizeof(int));
        for (int k = 0; k < deg[i]; k++) if (fscanf(f, "%d", &nb[i][k]) != 1) return 1;
        if (grp[i] + 1 > G) G = grp[i] + 1;
    }
    gsize = calloc(G, sizeof(int)); gfirst = calloc(G, sizeof(int)); gpts = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++) gsize[grp[i]]++;
    int off = 0;
    for (int g = 0; g < G; g++) { gfirst[g] = off; off += gsize[g]; }
    int *fill = calloc(G, sizeof(int));
    for (int i = 0; i < n; i++) gpts[gfirst[grp[i]] + fill[grp[i]]++] = i;
    clock_t t0 = clock();
    skipbudget = G - target; if (skipbudget < 0) skipbudget = 0;
    rec2();
    double secs = (double)(clock() - t0) / CLOCKS_PER_SEC;
    if (found) {
        printf("FOUND size %d nodes %lld time %.2fs\n", bestsz, nodes, secs);
        for (int i = 0; i < bestsz; i++) printf("%d ", bestset[i]);
        printf("\n");
    } else {
        printf("NONE target %d nodes %lld time %.2fs (no relaxed set of size >= %d)\n", target, nodes, secs, target);
    }
    return 0;
}
