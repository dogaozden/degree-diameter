#!/bin/bash
# re-certify every D = 11 set used in the note (run from research/theorems/polylev)
for q in 7 11 13 16; do echo "=== q=$q"; python3 d11cert.py hex/hex_q$q.bin certs/q${q}_lines.txt certs/q${q}_points.txt; done
echo "=== q=8"; python3 d11cert.py hex/hex_q8.bin certs/q8_lines.txt certs/q8_points.txt
echo "=== q=9"; python3 d11cert.py hex/hex_q9.bin certs/q9_lines.txt DUAL parts/dual_q9.phi
