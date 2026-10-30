#!/bin/bash
for qk in "97 12" "293 4" "61 20" "289 4"; do set -- $qk
  ./run_group2.sh aff1_$1_$2 "AffSub($1,$2)" 2 7 60 > /dev/null
done
echo BATCH5_DONE
