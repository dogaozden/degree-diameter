#!/bin/bash
# sequential all-pairs checks (single thread, wall-clock timeout 3600 s each)
cd /home/user/degree-diameter/research/squads/polylev/r2/e10
APSP=/home/user/degree-diameter/research/theorems/polylev/bin/apsp
run() { # $1 edges, $2 Delta, $3 D, $4 log
  echo "start $(date -u +%FT%TZ)" > "$4"
  timeout 3600 nice -n 10 $APSP "$1" "$2" "$3" >> "$4" 2>&1
  echo "exit=$? end=$(date -u +%FT%TZ)" >> "$4"
}
run bal_r1.edges 5 10 apsp_r1_D10.log
run bal_r2.edges 6 11 apsp_r2_D11.log
run bal_r2.edges 6 10 apsp_r2_D10.log
echo ALLDONE > run_apsp_rest.done
