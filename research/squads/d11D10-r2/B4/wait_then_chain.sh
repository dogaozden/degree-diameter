#!/bin/bash
# B4: wait for both haar_sym gate calls to finish, make the corrupted copies, then run the small checks through the gate.
B=/home/user/degree-diameter/research/squads/d11D10-r2/B4
G=/home/user/degree-diameter/research/squads/d11D10-r2/gate.sh
while ! grep -q '^exit=' $B/hs_valid1.log 2>/dev/null; do sleep 5; done
while ! grep -q '^exit=' $B/hs_valid2.log 2>/dev/null; do sleep 5; done
cd $B || exit 1
python3 -I $B/mkcases.py repeat $B/d16D8_psl_243_1_orb5_frob1_s1.txt $B/corrupt_repeat_from_s1.txt
python3 -I $B/mkcases.py breakdet $B/d16D8_psl_243_1_plain_s2.txt $B/corrupt_breakdet_from_s2.txt
echo "mkcases done $(date -u +%T)" >> $B/logs/chain_small.status
$G 400 $B/chain_small.sh $B/corrupt_repeat_from_s1.txt $B/corrupt_breakdet_from_s2.txt $B/d16D8_psl_243_1_orb5_frob1_s1.txt > $B/logs/chain_small.out 2>&1
echo "gate chain exit=$?" >> $B/logs/chain_small.status
