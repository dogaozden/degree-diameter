#!/bin/bash
# Director's bi-Cayley campaign over all exported groups of order 344-360 (run from research/s65).
# Waits for each order's export to finish (export_all.sh writes groups/bc/export_<N>.log), then runs bc_campaign.sh.
for N in 344 346 348 350 352 354 356 358 360; do
  while [ ! -e groups/bc/export_$((N+2)).log ] && [ $N -ne 360 ] && pgrep -f export_all.sh > /dev/null; do sleep 20; done
  while [ $N -eq 360 ] && pgrep -f export_all.sh > /dev/null; do sleep 20; done
  SECS=${SECS:-600} nice -n 5 bash tools/bc_campaign.sh bc_campaign/O$N groups/bc/bc_${N}_*.txt
done
echo CAMPAIGN_DONE
