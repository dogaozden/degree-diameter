#!/bin/bash
# wave 3: 10-min single-thread k=2 orbit runs, one seed, on ten more candidates from the 15841-22000 screen (4 at a time)
cd /home/user/degree-diameter/research/structured
R=/home/user/degree-diameter/research/squads/raise-d6D8
cat > $R/wave3_groups.txt <<'LIST'
psl_17_7|psl 17 7
psl_23_3|psl 23 3
sl_11_13|sl 11 13
psl_11_26|psl 11 26
prod_sl3_sl9_1|prod sl 3 sl 9 1
psl_9_48|psl 9 48
prod_psl3_sl7_4|prod psl 3 sl 7 4
prod_psl3_psl7_9|prod psl 3 psl 7 9
sl_9_24|sl 9 24
prod_psl3_sl4_23|prod psl 3 sl 4 23
LIST
run() { tag=$1; shift; ORBIT="2 3 0" THREADS=1 nice -n 5 timeout 700 ./haar_sym 6 8 600 1 8 $R/sols_tmp/d6D8_${tag}_orb2f0_s1.txt $* > $R/runs/d6D8_${tag}_orb2f0_s1.log 2>&1; }
export -f run; export R
cut -d'|' -f1,2 $R/wave3_groups.txt | tr '|' ' ' | xargs -P 4 -L 1 bash -c 'run "$0" "${@:1}"'
echo WAVE3_DONE >> $R/runs/wave3.out
