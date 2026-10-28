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
static int stack_sel[1024];

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

static void rec(int g) {
    if (found) return;
    nodes++;
    if (cur >= target) {
        found = 1; bestsz = cur;
        int m = 0; for (int i = 0; i < n; i++) if (chosen[i]) bestset[m++] = i;
        bestsz = m; return;
    }
    /* bound: groups g..G-1 that still have a feasible point */
    int avail = 0;
    for (int h = g; h < G; h++) {
        for (int j = 0; j < gsize[h]; j++) if (feasible(gpts[gfirst[h] + j])) { avail++; break; }
    }
    if (cur + avail < target) return;
    if (g == G) return;
    /* try points of group g (most constrained first is not needed for correctness) */
    for (int j = 0; j < gsize[g] && !found; j++) {
        int p = gpts[gfirst[g] + j];
        if (!feasible(p)) continue;
        add(p, +1); cur++;
        rec(g + 1);
        add(p, -1); cur--;
    }
    if (!found) rec(g + 1);   /* group g left empty */
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
    rec(0);
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
