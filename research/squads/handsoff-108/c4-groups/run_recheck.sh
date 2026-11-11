#!/bin/bash
# c4: sequential (one heavy process at a time): pilot big-n (100 samples), pilot meta (100 samples), recheck top 30 at 1000 samples
cd /home/user/degree-diameter/research/squads/handsoff-108/c4-groups
FAMS=sl,pgl,psl,prod,agl1,meta python3 screen.py candidates.tsv pilot_big.tsv 100 - pilot_big_specs.txt > pilot_big.log 2>&1
FAMS=meta python3 screen.py candidates.tsv pilot_meta.tsv 100 - pilot_meta_specs.txt > pilot_meta.log 2>&1
FAMS=sl,pgl,psl,prod,agl1 python3 screen.py candidates.tsv recheck1000.tsv 1000 - top30_specs.txt > recheck.log 2>&1
echo done > run_recheck.done
