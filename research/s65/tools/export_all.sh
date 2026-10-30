#!/bin/bash
# exports for round s65r1 (run from research/s65)
for N in 344 346 348 350 354 356 358 352 360; do
  gap -q -c "ORDER:=$N; OUTDIR:=\"groups/bc\"; CAP:=3000;" tools/bicay_export.g > groups/bc/export_$N.log 2>&1
done
