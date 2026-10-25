#!/bin/bash
# B7 (short version): census for three alpha choices, then RANDORB=60 for AFROBH with AR=2 (control) and AR=3 (test).
B=/home/user/degree-diameter/research/squads/d11D10-r2/B7/haar_sym_B7
run() { echo "=== $1"; shift; env CENSUS=1 "$@" $B 11 10 60 5 8 /dev/null psl 243 11 2>&1 | grep -E "CENSUS|alpha:|ORBIT|group " ; }
rnd() { echo "=== RANDORB $1"; shift; env RANDORB=60 "$@" $B 11 10 60 7 8 /dev/null psl 243 11 2>&1 | grep -E "RANDORB d=|hist|group |alpha:|ORBIT|cost0" ; }
run "k10 AFROB=1 AFROBH AR=2"  ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2
run "k10 AFROB=1 AFROBD AR=2"  ORBIT="10 1 1" AFROB=1 AFROBD=1 AR=2
run "k10 AFROB=1 AFROBH AR=3"  ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=3
rnd "k10 AFROBH AR=3 (60 samples)" ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=3
rnd "k10 AFROBH AR=2 (60 samples, control)" ORBIT="10 1 1" AFROB=1 AFROBH="0 1 2 0" AR=2
