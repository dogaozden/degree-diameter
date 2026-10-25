# exp/: haar_sym screening and anneal runs of BEYOND_RANDOM.md (§4.3, §4.5)

haar_sym and haar_fast were built from `research/structured/haar_sym.c` on branch `claude/structured-haar-search-ws7bet`
(commit c8e7452), unchanged: `gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm`. Every run used THREADS=1 on
the 4-core cloud container (Xeon 2.8 GHz). `B` below is the directory that holds the binary.

Random symmetric S (RANDORB) against random S (RANDSAMPLE):
```
ORBIT="3 2 2" RANDORB=1000 LEVELS=1000 $B/haar_sym 8 7 60 1 8 /dev/null sl 8 43            > lv_87_sl8_43_conj.txt
ORBIT="3 2 2" AFROB=1 RANDORB=1000 LEVELS=1000 $B/haar_sym 8 7 60 1 8 /dev/null sl 8 43   > lv_87_sl8_43_frob.txt
RANDSAMPLE=1000 LEVELS=1000 $B/haar_sym 8 7 60 1 8 /dev/null sl 8 43                     > lv_87_sl8_43_rand.txt
ORBIT="3 4 1" RANDORB=150 $B/haar_sym 13 8 60 1 8 /dev/null sl 64 13                     > ro_138_sl64_conj.txt
ORBIT="3 4 1" AFROB=2 RANDORB=150 $B/haar_sym 13 8 60 1 8 /dev/null sl 64 13             > ro_138_sl64_frob.txt
RANDSAMPLE=150 $B/haar_sym 13 8 60 1 8 /dev/null sl 64 13                                > ro_138_sl64_rand.txt
ORBIT="3 2 3" / "3 3 0" RANDORB=400, RANDSAMPLE=400 ... 9 8 60 2 8 /dev/null sl 27 13     > ro_98_f3_f0.txt (seed 2)
```
(`ro_98_sl27_*.txt`: the same at 200 samples, seed 1.)

Anneals (k = 3 orbit search):
```
ORBIT="3 4 1"          $B/haar_sym 13 8 2400 1 8 sol_138_sl64_conj.txt sl 64 13   > an_138_sl64_conj.log
ORBIT="3 4 1" AFROB=2  $B/haar_sym 13 8 2400 1 8 sol_138_sl64_frob.txt sl 64 13   > an_138_sl64_frob.log
ORBIT="3 3 0"          $B/haar_sym 9 8 600 1 8 sol_98_sl27_f0.txt sl 27 13        > an_98_sl27_f0.log
ORBIT="3 3 0"          $B/haar_sym 9 8 1200 1 8 sol_98_sl64_conj_f0.txt sl 64 1   > an_98_sl64_conj_f0.log
ORBIT="3 3 0" AFROB=2  $B/haar_sym 9 8 1200 1 8 sol_98_sl64_frob_f0.txt sl 64 1   > an_98_sl64_frob_f0.log
```
Solution files (`sol_*.txt`, haar_gen3 format) are kept for runs that reached cost 0 and passed haar_sym's full
diameter check. `check_*.txt` holds the output of `../../../frontier/build_haar2.py` on them.
