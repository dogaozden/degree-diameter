#!/bin/bash
# Repeat step.sh until the 45-min time box ends; save best_sideB_<count>.txt on each improvement.
cd "$(dirname "$0")"
end=$(( $(date +%s) + 45*60 ))
last=$(wc -l < best_B.txt)
while [ "$(date +%s)" -lt "$end" ]; do
  ./step.sh > /dev/null 2>&1
  c=$(wc -l < best_B.txt)
  if [ "$c" -gt "$last" ]; then cp best_B.txt best_sideB_$c.txt; last=$c; echo "IMPROVED $c $(date +%T)" >> improve_g08.log; fi
  if [ "$c" -ge 48 ]; then break; fi
done
echo "DONE $(date +%T) final $(wc -l < best_B.txt)" >> loop_g08.done
