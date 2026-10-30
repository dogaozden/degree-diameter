#!/bin/bash
# (6,5): bi-coset graphs (H = K of order 2) of the direct products C_k x P (P a 2-group) of order 688, 720, 704
./sweep_diag.sh 688 2 6 3 "[ 2, 19, 20, 21, 22, 23, 24, 25, 26, 37, 38, 39, 40, 42 ]"; echo "688 direct done $(date -u +%H:%M)" >> logs/queue_codd.log
./sweep_diag.sh 720 2 6 3 ""; echo "720 direct done $(date -u +%H:%M)" >> logs/queue_codd.log
./sweep_diag.sh 704 2 6 3 "[ 2, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, "; echo "704 direct done $(date -u +%H:%M)" >> logs/queue_codd.log
