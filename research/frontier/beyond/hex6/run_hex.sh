#!/bin/bash
for q in 16 17 19; do
  d=$((q+1))
  ( time ./hexgen2 $q ) > gen_q$q.log 2>&1
  ./hexauto $q >> gen_q$q.log 2>&1
  { echo "H($q) incidence graph: research/frontier/beyond/hex6/hexgen2 $q; ./hexauto $q (job beyond-small, $(date -u +%FT%TZ))";
    echo "edge list sha256: $(sha256sum hex_q$q.edges | cut -c1-64)";
    echo "aut file sha256:  $(sha256sum hex_q$q.aut | cut -c1-64)";
    ( time ./apsp_auto hex_q$q.edges hex_q$q.aut $d 6 2 ) 2>&1; } > check_d${d}D6_H$q.auto.txt
done
echo done > run_hex.done
