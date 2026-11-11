import sys
p = sys.argv[1]
src = open(p).read()
def rep(old, new, count=1):
    global src
    n = src.count(old)
    assert n == count, (n, old[:80])
    src = src.replace(old, new)

# A. clocks, improvement log, abort policy (after now())
rep("static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }\n",
"static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }\n"
"/* c7-throughput: CPUCLOCK=1 runs schedule, budget and chain times in process CPU seconds (contention-free).\n"
" * IMLOG=1 records every new chain minimum (chain time, energy) and prints one IM line per chain.\n"
" * ABORTPOL=\"t:thr,...\": a chain whose chain minimum is above thr at chain time t is ended (live early abort). */\n"
"static int CPUCLK = 0, IMLOG = 0, NAP = 0; static double APT[16], APTHR[16];\n"
"static double tcpu(void) { struct timespec t; clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &t); return t.tv_sec + 1e-9 * t.tv_nsec; }\n"
"static double tclk(void) { return CPUCLK ? tcpu() : now(); }\n"
"static double IMT[20000], IME[20000]; static int NIM = 0;\n"
"static void imp_push(double t, long long e) { if (NIM < 20000) { IMT[NIM] = t; IME[NIM] = (double)e; NIM++; } }\n")

# B. setup at start of orbit_main
rep("static int orbit_main(ctx **C, int nth, int K, double secs, const char *out) {\n",
"static int orbit_main(ctx **C, int nth, int K, double secs, const char *out) {\n"
"    CPUCLK = getenv(\"CPUCLOCK\") ? atoi(getenv(\"CPUCLOCK\")) : 0;\n"
"    IMLOG = getenv(\"IMLOG\") ? atoi(getenv(\"IMLOG\")) : 0;\n"
"    if (getenv(\"ABORTPOL\")) { char *s = strdup(getenv(\"ABORTPOL\")); for (char *tok = strtok(s, \",\"); tok; tok = strtok(NULL, \",\"))\n"
"        if (NAP < 16 && sscanf(tok, \"%lf:%lf\", &APT[NAP], &APTHR[NAP]) == 2) NAP++; free(s); }\n"
"    fprintf(stderr, \"c7: CPUCLOCK=%d IMLOG=%d ABORTPOL pairs=%d\\n\", CPUCLK, IMLOG, NAP);\n")

# C. timing in orbit_main
rep("    double chain_t0 = now(); long long chain_e0 = 0;\n", "    double chain_t0 = tclk(); long long chain_e0 = 0;\n")
rep("    double cE = (double)ce / OK_, t0 = now(), T = TMAX, lastimp = t0, lastprint = t0, lastheat = t0;\n",
    "    double cE = (double)ce / OK_, t0 = tclk(), T = TMAX, lastimp = t0, lastprint = t0, lastheat = t0;\n")
rep("#define ONOW (OVCLOCK > 0 ? t0 + steps * OVCLOCK : now())\n", "#define ONOW (OVCLOCK > 0 ? t0 + steps * OVCLOCK : tclk())\n")
rep("    long long evals = 1 + evals0, steps = 0, lastimpstep = 0;\n",
    "    long long evals = 1 + evals0, steps = 0, lastimpstep = 0;\n    NIM = 0; imp_push(0, ce);\n")
rep("    printf(\"RESULT d=%d D=%d group=%s x Z_%d N=%d best=%lld evals=%lld time=%.1f orbit k=%d m=%d f=%d fix=%lld\\n\", d, D, Q->spec, ncyc, N, best, evals, now() - t0, OK_, OM, OF, NFIX);",
    "    printf(\"RESULT d=%d D=%d group=%s x Z_%d N=%d best=%lld evals=%lld time=%.1f orbit k=%d m=%d f=%d fix=%lld\\n\", d, D, Q->spec, ncyc, N, best, evals, ONOW - t0, OK_, OM, OF, NFIX);")

# D. improvement events
rep("        if (RA >= 0 && ce < lbestE) { lbestE = ce; memcpy(lbestS, S, sizeof(int) * d); lastimp = ONOW; lastimpstep = steps; nfail = 0; }\n",
    "        if (RA >= 0 && ce < lbestE) { lbestE = ce; memcpy(lbestS, S, sizeof(int) * d); lastimp = ONOW; lastimpstep = steps; nfail = 0;\n"
    "            if (IMLOG) imp_push(ONOW - chain_t0, ce); }\n")

# E. stall / abort branch
rep("        if (ONOW - lastimp > REHEAT && steps - lastimpstep > REHEATSTEPS) {\n            lastheat = ONOW; T = TMAX; memcpy(S, RA >= 0 ? lbestS : bestS2, sizeof(int) * d);\n",
    "        int c7stall = ONOW - lastimp > REHEAT && steps - lastimpstep > REHEATSTEPS, c7ab = 0;\n"
    "        if (RA >= 0) for (int q = 0; q < NAP; q++) if (ONOW - chain_t0 >= APT[q] && (double)lbestE > APTHR[q]) c7ab = 1;\n"
    "        if (c7stall || c7ab) {\n            lastheat = ONOW; T = TMAX; memcpy(S, RA >= 0 ? lbestS : bestS2, sizeof(int) * d);\n")
rep("                fprintf(stderr, \"CHAIN %d min %lld secs %.0f evals %lld S\", nchains, lbestE, now() - chain_t0, evals - chain_e0);\n",
    "                if (IMLOG) { fprintf(stderr, \"IM %d end %.3f min %lld ev %lld ab %d n %d\", nchains, ONOW - chain_t0, lbestE, evals - chain_e0, c7ab && !c7stall, NIM);\n"
    "                    for (int q = 0; q < NIM; q++) fprintf(stderr, \" %.3f:%.0f\", IMT[q], IME[q]); fprintf(stderr, \"\\n\"); }\n"
    "                fprintf(stderr, \"CHAIN %d min %lld secs %.0f evals %lld S\", nchains, lbestE, ONOW - chain_t0, evals - chain_e0);\n")
rep("                chain_t0 = now(); chain_e0 = evals; lbestE = (1LL << 60); nchains++;\n",
    "                chain_t0 = ONOW; chain_e0 = evals; lbestE = (1LL << 60); nchains++;\n")
rep("            cE = (double)ce / OK_; collect(C[0]); lastimp = ONOW; lastimpstep = steps;\n        }\n",
    "            cE = (double)ce / OK_; collect(C[0]); lastimp = ONOW; lastimpstep = steps; NIM = 0; imp_push(0, ce);\n        }\n")
open(p, "w").write(src)
print("patched", p)
