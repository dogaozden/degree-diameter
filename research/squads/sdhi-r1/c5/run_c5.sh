#!/bin/bash
# card c5: self-dual haar_sd (ORBIT 2 3 0, SDUAL tw) vs plain haar_sym (ORBIT 3 2 0) at (6,8), 100 s each
C=/home/user/degree-diameter/research/squads/sdhi-r1/c5
SD=/home/user/degree-diameter/research/selfdual-hi/src/haar_sd
cd $C
export THREADS=1
rm -f $C/progress.txt
SDUAL="tw 1 0" ORBIT="2 3 0" timeout 300 nice -n 10 $SD 6 8 100 1 8 $C/sol_sd_psl11_25_tw1.txt psl 11 25 > $C/log_sd_psl11_25_tw1.txt 2>&1; echo "done sd_psl11_25_tw1 rc=$?" >> $C/progress.txt
ORBIT="3 2 0" timeout 300 nice -n 10 $C/haar_sym 6 8 100 1 8 $C/sol_plain_psl11_25.txt psl 11 25 > $C/log_plain_psl11_25.txt 2>&1; echo "done plain_psl11_25 rc=$?" >> $C/progress.txt
SDUAL="tw -1 0" ORBIT="2 3 0" timeout 300 nice -n 10 $SD 6 8 100 1 8 $C/sol_sd_psl11_25_twm1.txt psl 11 25 > $C/log_sd_psl11_25_twm1.txt 2>&1; echo "done sd_psl11_25_twm1 rc=$?" >> $C/progress.txt
SDUAL="tw 1 0" ORBIT="2 3 0" timeout 300 nice -n 10 $SD 6 8 100 1 8 $C/sol_sd_sl7_49_tw1.txt sl 7 49 > $C/log_sd_sl7_49_tw1.txt 2>&1; echo "done sd_sl7_49_tw1 rc=$?" >> $C/progress.txt
ORBIT="3 2 0" timeout 300 nice -n 10 $C/haar_sym 6 8 100 1 8 $C/sol_plain_sl7_49.txt sl 7 49 > $C/log_plain_sl7_49.txt 2>&1; echo "done plain_sl7_49 rc=$?" >> $C/progress.txt
echo ALLDONE >> $C/progress.txt
