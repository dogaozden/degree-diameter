#!/bin/bash
# (5,5): h=2 coset graphs of groups of order 2 x odd (orbit-type Haar graphs of the odd-order index-2 subgroup)
for o in 358 362 366 370 374 378; do ./sweep.sh $o 2 5 > /dev/null 2>&1; echo "done $o" >> logs/batch8.out; done
echo BATCH8_DONE >> logs/batch8.out
