#!/bin/bash
# Save a verified find: self-contained builder, gzipped edge list, check file.
# usage: save_find.sh BASE CTRL.edges CHART n NAME "provenance"     (NAME like d12D5_n9720_k33m_z20)
set -e
D=$(cd "$(dirname "$0")" && pwd); BASE=$1; CTRL=$2; CHART=$3; NN=$4; NAME=$5; PROV=$6
NV=$(echo $NAME | sed 's/^d12D5_n\([0-9]*\)_.*/\1/')
python3 $D/make_builder.py $BASE $CTRL $CHART $NN $D/graphs/build_d12D5_n$NV.py "$PROV"
python3 $D/graphs/build_d12D5_n$NV.py $D/runs/self_n$NV.edges
python3 $D/gf3.py lift $CTRL $CHART $D/runs/pipe_n$NV.edges > /dev/null
A=$(sort $D/runs/self_n$NV.edges | sha256sum | cut -d' ' -f1); B=$(sort $D/runs/pipe_n$NV.edges | sha256sum | cut -d' ' -f1)
[ "$A" = "$B" ] || { echo "builder and pipeline differ"; exit 1; }
cp $D/runs/self_n$NV.edges $D/graphs/$NAME.edges; SHA=$(sha256sum $D/graphs/$NAME.edges | cut -d' ' -f1); gzip -9 -f $D/graphs/$NAME.edges
cp $CTRL $D/graphs/${NAME}_controller.txt; cp $CHART $D/graphs/${NAME}_chart.txt
{ echo "Check of the (12,5) graph on $NV vertices (job cell-12-5, $(date -u +%Y-%m-%dT%H:%MZ)). $PROV"
  echo "Builder: research/d12D5/graphs/build_d12D5_n$NV.py (self-contained). Edge list: graphs/$NAME.edges.gz"
  echo "Controller (a b colour): graphs/${NAME}_controller.txt; chart: graphs/${NAME}_chart.txt"
  echo "Uncompressed edge list sha256 $SHA (identical, after sorting, to gf3.py lift of the search output)."
  echo; echo "\$ apsp $NAME.edges 12 5   (research/lifts/coordinator_check/apsp.c, all pairs, no symmetry)"
  $D/apsp $D/runs/self_n$NV.edges 12 5
  echo; echo "\$ bfs_all $NAME.edges   (plain BFS from every vertex)"
  $D/bfs_all $D/runs/self_n$NV.edges
  $D/bfs_all $D/runs/self_n$NV.edges | awk -v n=$NV '/dist/ {s+=$3} END {print "sum of ordered pairs = " s " ; n^2 = " n*n}'
} > $D/graphs/${NAME}_check.txt
cat $D/graphs/${NAME}_check.txt
