src = open('/home/user/degree-diameter/research/squads/d10D7-r4/c6/ls6.c').read()
old = """static void perturb(void) {
    for (int t = 0; t < PERT_SWAPS; t++) {
        int u = Sarr[rndn(k)];
        int v; do { v = rndn(N); } while (inS[v]);
        remv(u); addv(v);
    }
    F = recountF();
}"""
new = """/* perturbation: swap out a random member and add the least-conflicting outside vertex from a random sample */
static void perturb(void) {
    for (int t = 0; t < PERT_SWAPS; t++) {
        int u = Sarr[rndn(k)];
        remv(u);
        int bv = -1, bc = INT_MAX;
        for (int s = 0; s < 300; s++) {
            int v = rndn(N);
            if (inS[v] || v == u) continue;
            if (cnt[v] < bc) { bc = cnt[v]; bv = v; }
        }
        if (bv < 0) bv = u;
        addv(bv);
    }
    F = recountF();
}"""
assert src.count(old) == 1, "pattern not found"
open('/home/user/degree-diameter/research/squads/d10D7-r4/c6/ls6.c', 'w').write(src.replace(old, new))
print("patched")
