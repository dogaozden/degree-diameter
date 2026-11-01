import sys
src = open('growb_src.c').read()
def rep(old, new):
    global src
    assert src.count(old) == 1, old[:60]
    src = src.replace(old, new)
# 1. blame accumulators and blame flag
rep("static int npool = 0;\n",
    "static int npool = 0;\nstatic int BLAME = 0; static double blame[MAXC]; static long bl_free = 0, bl_tot = 0;\n")
# 2. step-1 compat check: full blocker list in blame mode
rep("""            int good = 1;
            for (int q2 = 0; q2 < npool && good; q2++) if (isCur[q2] && !(compat(p, q2) && compat(q2, p))) good = 0;
            if (!good) continue;
            cnt_good++;""",
"""            int good = 1;
            if (BLAME) { int nbl = 0; int bl_[64];
                for (int q2 = 0; q2 < npool; q2++) if (isCur[q2] && !(compat(p, q2) && compat(q2, p))) { if (nbl < 64) bl_[nbl] = q2; nbl++; }
                bl_tot++; if (nbl == 0) bl_free++;
                for (int a = 0; a < nbl && a < 64; a++) blame[bl_[a]] += 1.0 / nbl;
                continue; }
            for (int q2 = 0; q2 < npool && good; q2++) if (isCur[q2] && !(compat(p, q2) && compat(q2, p))) good = 0;
            if (!good) continue;
            cnt_good++;""")
# 3. blame mode: stop after sampling, write blame table
rep("        /* 2. compat graph among alive and max clique",
"""        if (BLAME) {
            FILE *fb = fopen(getenv("BLAME_OUT"), "w");
            /* one line per fixed orbit: index blame(total weight over key-free self-compatible blocked covers) */
            for (int p = 0; p < npool; p++) if (isCur[p]) fprintf(fb, "%d %.4f\\n", p, blame[p]);
            fclose(fb);
            fprintf(stderr, "blame: sampled self-ok key-free covers %ld, free (addable) %ld, blocked %ld\\n", bl_tot, bl_free, bl_tot - bl_free);
            printf("%ld %ld\\n", bl_tot, bl_free);
            return 0;
        }
        /* 2. compat graph among alive and max clique""")
# 4. enable blame mode through env var BLAME_OUT (set -> blame mode)
rep("    if (argc < 6) {", "    if (getenv(\"BLAME_OUT\")) BLAME = 1;\n    if (argc < 6) {")
open('growb_f02.c', 'w').write(src)
print('ok')
