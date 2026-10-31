#!/bin/bash
# haar_record.sh ORD ID EXPORT OUTDIR s1 .. s6: record check of a Haar graph H(SmallGroup(ORD,ID), S) found by haarex
# (S as 0-based element indices of the export EXPORT). Builds the edge list twice (from the export table with
# src/haar_table_edges.py, and independently from GAP's arithmetic with haar_gap_edges.g), compares the
# sorted edge sets (sha256), and runs research/lifts/coordinator_check/apsp.c at d = 6, D = 5 and D = 4.
# Env: GAP, APSP (compiled apsp.c). Writes OUTDIR/haar_<ORD>_<ID>.edges, .sha256, .check.
set -eu
o=$1; i=$2; ex=$3; out=$4; shift 4; S="$*"; R=$(cd "$(dirname "$0")/../../.." && pwd)
mkdir -p $out; base=$out/haar_${o}_$i
python3 $R/research/six-five-384/src/haar_table_edges.py $ex $base.edges $S
$GAP -q -c "ORD:=$o;; ID:=$i;; SIDX:=[$(echo $S | tr ' ' ',')];; FN:=\"$base.gap.edges\";;" $R/research/six-five-384/src/haar_gap_edges.g > $base.gap.log 2>&1
a=$(tail -n +2 $base.edges | sort | sha256sum | cut -c1-64); b=$(tail -n +2 $base.gap.edges | sort | sha256sum | cut -c1-64)
{ echo "S indices: $S"; cat $base.gap.log | grep "^S ="; echo "sorted edge sha256 (table): $a"; echo "sorted edge sha256 (GAP):   $b";
  [ "$a" = "$b" ] && echo "builders agree" || echo "BUILDERS DIFFER";
  echo "apsp d=6 D=5: $($APSP $base.edges 6 5 | grep RESULT)"; echo "apsp d=6 D=4: $($APSP $base.edges 6 4 | grep RESULT)"; } > $base.check
sha256sum $base.edges > $base.sha256; rm -f $base.gap.edges $base.gap.log
cat $base.check
