#!/bin/bash
# A8: twisted affine orbit family on psl 243 x Z11 (one gate slot): 120 random samples
cd /home/user/degree-diameter/research/squads/d11D10-r2/A8
echo "start $(date -u +%T)"
env -u THREADS TWISTORB=120 ./haar_sym_A8 11 10 0 1 8 /dev/null psl 243 11
echo "rc=$? end $(date -u +%T)"
