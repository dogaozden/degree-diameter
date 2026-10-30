#!/bin/bash
# stop the queues whose best costs stayed far from 0 (C_k x 2-group sweeps for (6,5)/(7,5), product sweeps), with their
# children; run from coset/
cd "$(dirname "$0")"
for q in queue_dp6.sh queue_codd.sh queue_codd6.sh queue_prod7.sh queue_prodh7.sh; do
  for p in $(pgrep -f "[.]/$q"); do pkill -P $p; kill $p; done
done
sleep 1
for pat in "sweep_dp.sh" "sweep_diag.sh" "prod_sweep.sh" "prodh_sweep.sh"; do
  for p in $(pgrep -f "[.]/$pat"); do pkill -P $p; kill $p; done
done
sleep 2
rm -rf tmpdp_* tmpd_* tmpp_* tmpq_*
echo "$(date -u +%H:%M) stopped the C_k x 2-group and product-group queues (best costs 34+ for (7,5), 144+ for (6,5))" >> logs/queue75.log
