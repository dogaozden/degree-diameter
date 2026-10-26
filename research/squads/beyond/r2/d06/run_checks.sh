#!/bin/bash
# d06: build MDM lifts and check each with apsp (single thread). Output: checks/*.txt
cd /home/user/degree-diameter/research/squads/beyond/r2/d06
mkdir -p checks edges
# q=13, k=1: positive (valid nu) and negative control (nu with exactly one failing opposite pair)
python3 build_mdm.py gq/gq_q13.bin nu_q13_valid.txt 1 1 edges/pos_q13_k1.edges > checks/build_pos_q13_k1.txt
timeout 900 nice -n 10 ./apsp edges/pos_q13_k1.edges 16 5 > checks/apsp_pos_q13_k1.txt 2>&1
python3 build_mdm.py gq/gq_q13.bin neg_q13_k1.txt 1 1 edges/neg_q13_k1.edges > checks/build_neg_q13_k1.txt
timeout 900 nice -n 10 ./apsp edges/neg_q13_k1.edges 16 5 > checks/apsp_neg_q13_k1.txt 2>&1
# small q with the best (not condition-(A)) labellings from the anneal: apsp exact diameter
for q in 3 4 5 7; do for k in 1 2 3; do
  python3 build_mdm.py gq/gq_q$q.bin nu_q$q.txt $k 1 edges/best_q${q}_k$k.edges > checks/build_best_q${q}_k$k.txt
  timeout 900 nice -n 10 ./apsp edges/best_q${q}_k$k.edges $((q+1+2*k)) 5 > checks/apsp_best_q${q}_k$k.txt 2>&1
done; done
echo ALLDONE > checks/done.txt
