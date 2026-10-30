#!/bin/bash
# usage: chunk.sh N  -- export ids (N-1)*40+1 .. N*40 from r6_c.txt into d/ (fresh) and anneal them
cd /home/user/degree-diameter/research/squads/s65r6/c3
N=$1
IDS=$(sed -n "$(( (N-1)*40+1 )),$(( N*40 ))p" /home/user/degree-diameter/research/s65/c3p256/r6_c.txt | paste -sd, -)
[ -z "$IDS" ] && { echo "no ids for chunk $N" >> progress.txt; exit 0; }
rm -rf d && mkdir -p d
echo "$(date +%H:%M:%S) chunk $N ids $(sed -n "$(( (N-1)*40+1 ))p" /home/user/degree-diameter/research/s65/c3p256/r6_c.txt)..$(sed -n "$(( N*40 ))p" /home/user/degree-diameter/research/s65/c3p256/r6_c.txt) export" >> progress.txt
timeout 600 nice -n 10 gap -q -c "PORD:=256; IDS:=[$IDS]; OUTDIR:=\"d\";" c3p_export.g > gap_$(printf %03d $N).log 2>&1
echo "$(date +%H:%M:%S) chunk $N exported $(ls d | wc -l) dc2 files" >> progress.txt
./run_dir.sh $(printf %03d $N)
