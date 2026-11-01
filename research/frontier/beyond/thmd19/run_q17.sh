#!/bin/bash
./thmd_auto ../hex6/hex/hex_q17.bin 0 1 thmd_q17.edges thmd_q17.aut > build_q17.log 2>&1
{ echo "Theorem D, q = 17, m = 2: research/frontier/beyond/thmd19/thmd_auto ../hex6/hex/hex_q17.bin 0 1 thmd_q17.edges thmd_q17.aut (job beyond-small, $(date -u +%FT%TZ))";
  grep -E "levels|doubled|degrees|generator|torus" build_q17.log;
  echo "edge list sha256: $(sha256sum thmd_q17.edges | cut -c1-64)";
  ( time ../hex6/apsp_auto thmd_q17.edges thmd_q17.aut 19 6 3 ) 2>&1; } > check_d19D6_thmD_q17.auto.txt
echo done > run_q17.done
