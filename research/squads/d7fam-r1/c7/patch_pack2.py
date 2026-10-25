import re
src = open('/home/user/degree-diameter/research/squads/d7fam-r1/c7/pack.c').read()
old_pert = src[src.index('        /* perturbation: force-insert one element'):src.index('        run_queue();\n        if (ns > best)')]
new_pert = r'''        /* perturbation v2: force-insert a base element (low tightness); with prob 1/2 the forced set is a cluster of
           2-3 elements, each at collinearity distance 2 from the previous one (so the forced region is local); then
           refill every element freed by the removals (maximality repair: pack v1 never re-added freed free elements) */
        nrl = 0;
        int clustered = (rnd() % 2 == 0);
        int kk = clustered ? 2 + (int)(rnd() % 2) : ((rnd() % 8 == 0) ? 2 : 1);
        int prev = -1;
        for (int r = 0; r < kk; r++) {
            int x = -1;
            if (r > 0 && clustered) {
                int L = EC[prev * Q1 + rnd() % Q1];
                int z = CE[L * Q1 + rnd() % Q1];
                int M = (z == prev) ? -1 : EC[z * Q1 + rnd() % Q1];
                if (M >= 0 && M != L) { int y = CE[M * Q1 + rnd() % Q1]; if (y != z && y != prev) x = y; }
            }
            if (x < 0) {
                do { x = rnd() % N; } while (in[x]);
                for (int tr = 0; tr < 3 && tight[x] > 1; tr++) { int y = rnd() % N; if (!in[y] && tight[y] < tight[x]) x = y; }
            }
            if (in[x]) continue;
            for (int i = 0; i < Q1; i++) { int c = EC[x * Q1 + i]; if (owner[c] >= 0) { rl[nrl++] = owner[c]; rem(owner[c]); } }
            add(x); push(x); prev = x;
        }
        for (int i = 0; i < nrl; i++) {
            int y = rl[i];
            for (int j = 0; j < Q1; j++) { int c = EC[y * Q1 + j];
                for (int t = 0; t < Q1; t++) { int f = CE[c * Q1 + t]; if (!in[f] && tight[f] == 0) { add(f); push(f); } } }
        }
'''
src = src.replace(old_pert, new_pert)
src = src.replace('static int pick[64];', 'static int pick[64];\nstatic int rl[1 << 16], nrl;   /* elements removed by the current perturbation */')
src = src.replace('/* pack.c:', '/* pack2.c (card c7 variant of pack.c: clustered distance-2 forced insertions + maximality refill): ', 1)
open('/home/user/degree-diameter/research/squads/d7fam-r1/c7/pack2.c', 'w').write(src)
print('ok', len(old_pert), len(new_pert))
