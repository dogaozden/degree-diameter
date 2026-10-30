#!/bin/bash
# export all 158 semidirect ids in chunks of 20 (one GAP process at a time)
cd /home/user/degree-diameter/research/squads/s65r5/c8
split -l 20 -d ids158.txt chunk_
for c in chunk_*; do
  IDS=$(paste -sd, "$c")
  echo "chunk $c start $(date +%T)" >> export_progress.txt
  timeout 900 nice -n 10 gap -q -c "PORD:=256; IDS:=[$IDS]; OUTDIR:=\"d\";" sdp_export.g > gap_$c.log 2>&1
  echo "chunk $c rc=$? files=$(ls d | wc -l) end $(date +%T)" >> export_progress.txt
done
echo ALLDONE >> export_progress.txt
