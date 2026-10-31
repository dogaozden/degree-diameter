import sys
p = '/home/user/degree-diameter/research/squads/sd5c-r1/c7/fsd_focus.c'
src = open(p).read()
def rep(old, new):
    global src
    assert src.count(old) == 1, ("count", src.count(old), old[:70])
    src = src.replace(old, new)

# 1. focus helpers before run()
helpers = r'''
/* ---------- c7 FOCUS: focused neighbourhood (env FOCUS=percent) ----------
 * For a random uncovered element z of G (not in X X), propose s' with z = s_i^-1 s_j s'^-1 s_l or
 * z = s_i^-1 s_j s_l^-1 s' (i, j, l random indices of the current S), i.e. a new element that would create a
 * product covering z.  The proposal replaces a random item of the same type (fixed / orbit); exact energy decides. */
static int *flpos_ = NULL, FOCUS_ = 0, fk_;
static uint32_t *xmk2_ = NULL, *cvm_ = NULL, xs2_ = 0, cs2_ = 0; static int *unc_, nunc_;
static void setup_flpos(void) {
    if (!flpos_) flpos_ = malloc(sizeof(int) * n);
    for (int i = 0; i < n; i++) flpos_[i] = -1;
    for (int x = 0; x < nfl; x++) flpos_[fl[x]] = x;
}
static int focus_prepare(void) {
    if (!xmk2_) { xmk2_ = calloc(n, 4); cvm_ = calloc(n, 4); unc_ = malloc(sizeof(int) * n); }
    fk_ = build(); int X[512], nx = 0; xs2_++;
    for (int i = 0; i < fk_; i++) for (int j = 0; j < fk_; j++) { int x = gmul(inv[S[i]], S[j]); if (xmk2_[x] != xs2_) { xmk2_[x] = xs2_; X[nx++] = x; } }
    cs2_++; for (int a = 0; a < nx; a++) for (int b = 0; b < nx; b++) cvm_[gmul(X[a], X[b])] = cs2_;
    nunc_ = 0; for (int z = 0; z < n; z++) if (cvm_[z] != cs2_) unc_[nunc_++] = z;
    return nunc_ > 0;
}
static int focus_cand(int *isfix) {   /* item proposed for a random uncovered element, or -1 */
    for (int t = 0; t < 8; t++) {
        int z = unc_[rnd() % nunc_];
        int i = (int)(rnd() % fk_), j = (int)(rnd() % fk_), l = (int)(rnd() % fk_), sp;
        if (rnd() & 1) sp = gmul(gmul(gmul(S[l], inv[z]), inv[S[i]]), S[j]);   /* s' = s_l z^-1 s_i^-1 s_j */
        else sp = gmul(gmul(gmul(S[l], inv[S[j]]), S[i]), z);                   /* s' = s_l s_j^-1 s_i z */
        if (sp == 0) continue;
        int item;
        if (psi[sp] == sp) { if (flpos_[sp] < 0) continue; item = flpos_[sp]; *isfix = 1; }
        else { if (orbof[sp] < 0 || orbof[sp] == fixed0) continue; item = nfl + orbof[sp]; *isfix = 0; }
        if (!used(item)) return item;
    }
    return -1;
}
'''
rep("static const char *edges_out; static int nsol = 0;", helpers + "static const char *edges_out; static int nsol = 0;")

# 2. call setup_flpos after setup in run()
rep("    setup(r);\n    if (rkind[r]) { fixed0 = orbof[0]", "    setup(r); setup_flpos();\n    if (rkind[r]) { fixed0 = orbof[0]")

# 3. focus-aware candidate generation
rep("        for (int t = 0; t < NB && t < 256; t++) { int i = (int)(rnd() % nit), isfix = it[i] < nfl; int x = rand_item(isfix); if (x < 0) continue; ci[nc] = i; cx[nc] = x; nc++; }",
"""        int fready = 0;
        for (int t = 0; t < NB && t < 256; t++) {
            if (FOCUS_ && (int)(rnd() % 100) < FOCUS_) {
                if (!fready) fready = focus_prepare() ? 1 : 2;
                if (fready == 1) { int isf = 0, x = focus_cand(&isf);
                    if (x >= 0) { int i = -1; for (int a = 0; a < 50 && i < 0; a++) { int q = (int)(rnd() % nit); if ((it[q] < nfl) == isf) i = q; }
                        if (i >= 0) { ci[nc] = i; cx[nc] = x; nc++; continue; } } }
            }
            int i = (int)(rnd() % nit), isfix = it[i] < nfl; int x = rand_item(isfix); if (x < 0) continue; ci[nc] = i; cx[nc] = x; nc++;
        }""")

# 4. env
rep('    if (getenv("MAXREC")) MAXREC_ = atoi(getenv("MAXREC"));', '    if (getenv("MAXREC")) MAXREC_ = atoi(getenv("MAXREC"));\n    if (getenv("FOCUS")) FOCUS_ = atoi(getenv("FOCUS"));')
open(p, 'w').write(src)
print("patched")
