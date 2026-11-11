#!/bin/bash
# usage: screen.sh tag  <group args...>  -- random (no orbit) cost screen
tag=$1; shift
THREADS=1 RANDSAMPLE=4 nice -n 10 timeout 600 /home/user/degree-diameter/research/frontier/beyond13/bin/haar_sym 5 13 30 1 3 scr_$tag.sol "$@" 2>&1 | grep -v wide > scr_$tag.log
