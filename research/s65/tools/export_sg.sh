#!/bin/bash
for N in 172 174 175 176 177 178 180 115 116 117 118 119 120; do
  gap -q -c "ORDER:=$N; OUTDIR:=\"groups/sg\";" tools/gap_tables.g > groups/sg/export_$N.log 2>&1
done
