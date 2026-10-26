#!/bin/bash
# sweep: BASE m k r ; 60000 iters, 1 restart, D=10
cd /home/user/degree-diameter/research/squads/table-audit-r2/c2
run() { timeout 900 nice -n 10 ../bin/lift_sa "$1" "$2" "$3" "$4" 10 60000 1 $RANDOM 2.0 "out/$5.edges" 2>/dev/null | tr '\n' ' '; echo; }
run bases/desargues.txt 5 8 2 des_Z5x8_2
run bases/desargues.txt 20 2 19 des_D20
run bases/desargues.txt 20 2 1 des_Z20xZ2
run bases/desargues.txt 10 4 3 des_Z10x4_3
run bases/dyck.txt 5 5 1 dyck_Z5xZ5
run bases/dyck.txt 13 2 12 dyck_D13
run bases/mobius_kantor.txt 25 2 24 mk_D25
run bases/mobius_kantor.txt 5 10 4 mk_Z5x10_4
run bases/mobius_kantor.txt 5 10 1 mk_Z5xZ10
run bases/q3.txt 25 4 7 q3_Z25x4_7
run bases/q3.txt 25 4 18 q3_Z25x4_18
run bases/q3.txt 20 5 1 q3_Z20xZ5
run bases/q3.txt 50 2 49 q3_D50
run bases/q3.txt 10 10 1 q3_Z10xZ10
