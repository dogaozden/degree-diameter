import sys
src = open('mlift_src.c').read()
anchor = '    if (getenv("INIT_VOLT")) {'
assert src.count(anchor) == 1
block = r'''    if (getenv("EXH")) {   /* c4 addition: exhaustive over the free voltages (k = 1: three free edges), exact min for this chart */
        int fr[64], nf2 = 0; for (int i = 0; i < ne; i++) { if (istree[i]) volt[i] = e_id; else fr[nf2++] = i; }
        if (nf2 != 3) { printf("EXH needs exactly 3 free edges\n"); return 9; }
        int bestc = 1 << 30, bcnt = 0, bvv[64]; long tot = 0;
        for (int x0 = 0; x0 < n; x0++) for (int x1 = 0; x1 < n; x1++) for (int x2 = 0; x2 < n; x2++) {
            volt[fr[0]] = x0; volt[fr[1]] = x1; volt[fr[2]] = x2;
            if (!parallel_ok()) continue;
            int cc = cost(); tot++;
            if (cc < bestc) { bestc = cc; bcnt = 1; memcpy(bvv, volt, sizeof volt); }
            else if (cc == bestc) bcnt++;
        }
        memcpy(volt, bvv, sizeof volt);
        printf("EXH n=%d m=%d FAKE=%d DIAGBT=%d tuples=%ld min_cost=%d count_at_min=%d volt=", n, k * n, FAKE, DIAGBT, tot, bestc, bcnt);
        for (int i = 0; i < ne; i++) printf("%d%c", bvv[i], i + 1 < ne ? ',' : '\n');
        if (out && (bestc == 0 || getenv("WRITEBEST"))) {
            char fn[1024]; snprintf(fn, sizeof fn, "%s.edges", out); FILE *g = fopen(fn, "w");
            for (int i = 0; i < ne; i++) for (int x = 0; x < n; x++) fprintf(g, "%d %d %d\n", EA[i] * n + x, EB[i] * n + mul(bvv[i], x), i);
            fclose(g); snprintf(fn, sizeof fn, "%s.echart", out); write_echart(fn, A, b); }
        return 0;
    }
'''
open('mlift_exh.c', 'w').write(src.replace(anchor, block + anchor))
print('patched')
