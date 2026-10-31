import sys
src = open(sys.argv[1]).read()
a = src.index("            if (!bad) {\n")
b = src.index('            printf("COMB");')
new = r'''            if (!bad) {
                int cur, bestch[MAXO * MAXO][8];
                double t0 = now();
                int TT = getenv("TT") ? atoi(getenv("TT")) : 12;
                long STAG = getenv("STAG") ? atol(getenv("STAG")) : 3000;
                int KICK = getenv("KICK") ? atoi(getenv("KICK")) : 3;
                static long tabu_until[MAXO * MAXO][MAXM];
                memset(tabu_until, 0, sizeof tabu_until);
                for (int k = 0; k < nblk; k++) { memset(isch[k], 0, m);
                    for (int c = 0; c < nab[k]; c++) { int d; do d = fulllist[k][rnd() % nfull[k]]; while (isch[k][d]); isch[k][d] = 1; chosen[k][c] = d; } }
                cur = cost_eval(); evals++;
                best = cur; memcpy(bestch, chosen, sizeof bestch);
                long stag = 0, tit = 0, steps = 0;
                while (now() - t0 < SECS && best > 0) {
                    int mk = -1, mc = -1, md = -1, mv = 1 << 30, nties = 0;
                    for (int k = 0; k < nblk; k++) for (int c = 0; c < nab[k]; c++) {
                        int old = chosen[k][c];
                        for (int i = 0; i < nfull[k]; i++) {
                            int d = fulllist[k][i]; if (isch[k][d]) continue;
                            int istabu = tabu_until[k][d] > tit;
                            chosen[k][c] = d; isch[k][old] = 0; isch[k][d] = 1;
                            int v = cost_eval(); evals++;
                            chosen[k][c] = old; isch[k][d] = 0; isch[k][old] = 1;
                            if (istabu && !(v < best)) continue;
                            if (v < mv) { mv = v; mk = k; mc = c; md = d; nties = 1; }
                            else if (v == mv) { nties++; if (rnd() % nties == 0) { mk = k; mc = c; md = d; } }
                        }
                    }
                    steps++;
                    if (mk < 0) { continue; }
                    int old = chosen[mk][mc];
                    chosen[mk][mc] = md; isch[mk][old] = 0; isch[mk][md] = 1;
                    cur = mv; tabu_until[mk][old] = tit + TT + (long)(rnd() % (TT + 1));
                    tit++;
                    if (cur < best) { best = cur; memcpy(bestch, chosen, sizeof bestch); stag = 0;
                        if (best < gbest) { gbest = best; if (EDGES) write_edges(EDGES); } }
                    else stag++;
                    if (stag > STAG) { /* restart from the best of this combination with a few random kicks */
                        memcpy(chosen, bestch, sizeof chosen);
                        for (int k = 0; k < nblk; k++) { memset(isch[k], 0, m); for (int c = 0; c < nab[k]; c++) isch[k][chosen[k][c]] = 1; }
                        for (int q = 0; q < KICK; q++) { int k; do k = rnd() % nblk; while (nab[k] == 0);
                            int c = rnd() % nab[k], old2 = chosen[k][c], d; do d = fulllist[k][rnd() % nfull[k]]; while (isch[k][d]);
                            chosen[k][c] = d; isch[k][old2] = 0; isch[k][d] = 1; }
                        cur = cost_eval(); evals++; stag = 0;
                    }
                }
                if (getenv("VERB")) fprintf(stderr, "steps %ld\n", steps);
                if (best == 0) { printf("SOL type %s cls", type); for (int i = 0; i < nt; i++) printf(" %d", comb[i]);
                    printf(" stabgens"); for (int o = 0; o < no; o++) printf(" %d", sord[o] > 1 ? stab[o][1] : 0);
                    for (int k = 0; k < nblk; k++) { printf(" | blk %d-%d:", ba[k], bb[k]); for (int c = 0; c < nab[k]; c++) printf(" %d", dcrep[k][bestch[k][c]]); }
                    printf("\n"); fflush(stdout); }
                /* nothing else */
            }
'''
src = src[:a] + new + src[b:]
open(sys.argv[2], 'w').write(src)
