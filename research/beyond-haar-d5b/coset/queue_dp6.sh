#!/bin/bash
# (6,5): bi-coset graphs (H = K of order 2) of C_k x P (P a 2-group), 800-880 vertices
cd "$(dirname "$0")"
./sweep_dp.sh 55 16 "[1..14]" 6 3;  echo "55x16 done $(date -u +%H:%M)" >> logs/queue_dp6.log
./sweep_dp.sh 25 32 "[1..51]" 6 3;  echo "25x32 done $(date -u +%H:%M)" >> logs/queue_dp6.log
./sweep_dp.sh 27 32 "[1..51]" 6 3;  echo "27x32 done $(date -u +%H:%M)" >> logs/queue_dp6.log
./sweep_dp.sh 13 64 "[1..100]" 6 3; echo "13x64 done $(date -u +%H:%M)" >> logs/queue_dp6.log
