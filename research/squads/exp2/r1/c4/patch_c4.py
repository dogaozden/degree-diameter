# c4 patch: skip the 2N+2K full BFS check at the end (about 132K BFS on 398K vertices, hours at q=9).
# The solution is written as soon as the search reaches cost 0; the all-pairs apsp run is the verifier.
src = open("d7hex_src_orig.c").read()
old = """    if (cost == 0) {
        int diam, bad = full_check(&diam);
        int maxdeg = 0, nb[64]; for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); if (c > maxdeg) maxdeg = c; }
        printf("RESULT q=%d K=%d n=%d maxdeg=%d diameter=%d badsources=%d %s\\n", q, K, NV, maxdeg, diam, bad,
               (bad == 0 && diam <= 7 && maxdeg <= q + 2) ? "VALID" : "INVALID");
        if (out && bad == 0 && diam <= 7) write_sol(out);
    } else printf("RESULT q=%d K=%d unsolved cost %d\\n", q, K, cost);"""
new = """    if (cost == 0) {
        int maxdeg = 0, nb[64]; for (int v = 0; v < NV; v++) { int c = nbrs(v, nb); if (c > maxdeg) maxdeg = c; }
        printf("RESULT q=%d K=%d n=%d maxdeg=%d cost0 full_check_skipped (verify with apsp)\\n", q, K, NV, maxdeg);
        if (out) write_sol(out);
    } else printf("RESULT q=%d K=%d unsolved cost %d\\n", q, K, cost);"""
assert src.count(old) == 1, src.count(old)
open("d7hex.c", "w").write(src.replace(old, new))
print("patched d7hex.c")
