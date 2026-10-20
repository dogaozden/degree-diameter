#!/usr/bin/env bash
# Merge the (3,8) chunks: count distinct connected cubic bipartite graphs on 15+15 (|RB(3,8)|)
# and distinct LBM(3,8) graphs with their girth vectors.
set -eu
W=/Users/dogaozden/AI_Projects/p12-work/cubic38
R=/Users/dogaozden/AI_Projects/degree-diameter/research/p12
mkdir -p $W/tmp
export LC_ALL=C
cat $W/canon_*.g6 | sort -u -S 4G -T $W/tmp > $W/rb38_distinct.g6
echo "RB(3,8) distinct plain graphs: $(wc -l < $W/rb38_distinct.g6)"
cat $W/hits_*.txt | sort -u > $R/lbm38_distinct.tsv
echo "LBM(3,8) distinct graphs: $(wc -l < $R/lbm38_distinct.tsv)"
echo "girth-vector classes (count, vector):"
cut -f2 $R/lbm38_distinct.tsv | sort | uniq -c | sort -k1,1nr
echo "closest to Moore (sorted by S1, S2, S3; S1 = 0 is the Moore graph):"
sort -t$'\t' -k3,3n -k4,4n -k5,5n $R/lbm38_distinct.tsv | head -20
