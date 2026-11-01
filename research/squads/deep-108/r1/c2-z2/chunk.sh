#!/bin/bash
# usage: chunk.sh START  -> exhaustive scanLR of pair (a) D5e x D5et, step 24 (resumable chunk START of 0..23)
cd "$(dirname "$0")"
. ./classes.sh
timeout 100 nice -n 10 ../../cq/cq2 181 1 2 $D5e $D5et scanLR scan_D5e_D5et.tsv 300 $1 24 2>> scan_D5e_D5et.log
echo "chunk $1: $(tail -1 scan_D5e_D5et.log)"
