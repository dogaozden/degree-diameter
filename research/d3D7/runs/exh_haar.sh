#!/bin/bash
# every cubic Haar graph of every group of order 85..127 (n = 170..254), D = 7
cd "$(dirname "$0")/.."
for N in $(seq 85 127); do ./bin/liftx bases/haar.txt groups/g$N.txt 7; done > runs/exh_haar.out
echo DONE >> runs/exh_haar.out
