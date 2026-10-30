#!/bin/bash
# tables for mcos (all groups of the given orders), run from research/s65/tools
for N in "$@"; do gap -q -c "ORDER:=$N; OUTDIR:=\"../groups/mc\";" gap_tables.g > ../groups/mc/export_$N.log 2>&1; done
