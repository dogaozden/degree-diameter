# Makes a copy of the shared lift3.c that keeps annealing after a sampled zero (SRC>0) until an all-source check passes.
import sys
src = open("/home/user/degree-diameter/research/d10D8/hex/lift3.c").read()
def rep(s, a, b):
    assert s.count(a) == 1, a[:60]
    return s.replace(a, b)
src = rep(src, "    for (long it = 0; it < iters && best > 0 && nv_tot > 0; it++) {",
               "    for (long it = 0; it < iters && nv_tot > 0; it++) {")
src = rep(src, "static void save(const char *fn, const char *gspec, long cost) {",
"""static long full_cost(void) {   /* cost over all V sources, restores the sampled source list */
    int sn = nsrc; int *sv = malloc(sizeof(int) * sn); memcpy(sv, srcs, sizeof(int) * sn);
    nsrc = V; for (int i = 0; i < V; i++) srcs[i] = i;
    long c = total_cost(1L << 60);
    nsrc = sn; memcpy(srcs, sv, sizeof(int) * sn); free(sv); return c;
}
static void save(const char *fn, const char *gspec, long cost) {""")
src = rep(src, """                fprintf(stderr, "it %ld temp %.3f best %ld\\n", it, temp, best); }
        } else {""",
"""                fprintf(stderr, "it %ld temp %.3f best %ld\\n", it, temp, best); }
            if (cur == 0) {   /* sampled zero: accept only if the all-source check is also 0, else resample and go on */
                int ok = 1;
                if (SRC > 0 && SRC < V) { ok = (full_cost() == 0);
                    if (!ok) { for (int i = 0; i < nsrc; i++) srcs[i] = rnd() % V; cur = total_cost(1L << 60); } }
                if (ok) { if (out) save(out, gspec, 0); fprintf(stderr, "it %ld sampled+full zero\\n", it); break; }
            }
        } else {""")
open(sys.argv[1], "w").write(src)
print("patched copy written:", sys.argv[1])
