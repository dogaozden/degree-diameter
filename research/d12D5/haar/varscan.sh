#!/bin/bash
# exhaustive Haar cost for every k=1 chart variant pattern file on the given group tables
for t in "$@"; do for p in k1var/*.pat; do echo "$(basename $t) $(basename $p) $(./exh_k1r $t $p 1 | tail -2 | tr '\n' ' ')"; done; done
