#!/bin/bash
# run_shard.sh K SHARD MOD: one shard of the p = 7 joint search (D = 7), cut depth 24 edges.
cd "$(dirname "$0")/../.."
SHARD=$2/$3 SHARDDEPTH=24 nice -n 5 ./bin/jsearch3 7 $1 7 1000 > runs/js/js_p7_k$1_s$2of$3.out 2> runs/js/js_p7_k$1_s$2of$3.err
