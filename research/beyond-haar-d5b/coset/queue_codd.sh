#!/bin/bash
# (7,5): bi-coset graphs (H = K of order 2) of the direct products C_k x P (P a 2-group) of order 1312 and 1248
./sweep_diag.sh 1312 2 7 5 "[ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, "; echo "1312 direct done $(date -u +%H:%M)" >> logs/queue_codd.log
./sweep_diag.sh 1248 2 7 5 "[ 6, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, "; echo "1248 direct done $(date -u +%H:%M)" >> logs/queue_codd.log
