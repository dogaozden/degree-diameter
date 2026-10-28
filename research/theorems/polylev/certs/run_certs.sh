#!/bin/bash
# re-certify every D = 11 set used in the note (run from research/theorems/polylev)
for q in 7 11 13; do echo "=== q=$q"; python3 d11cert.py hex/hex_q$q.bin certs/q${q}_lines.txt certs/q${q}_points.txt; done
echo "=== q=8 (orbit construction)"; python3 d11cert.py hex/hex_q8.bin certs/q8_lines.txt certs/q8_points.txt
echo "=== q=8 (plus local search)"; python3 d11cert.py hex/hex_q8.bin certs/q8_lines_3292.txt certs/q8_points.txt
echo "=== q=8 stand-alone"; python3 certs/verify_q8.py certs/q8_h.txt certs/q8_point_reps.txt certs/q8_line_reps.txt; python3 certs/verify_q8.py certs/q8_h.txt certs/q8_point_reps.txt certs/q8_lines_3292_span.txt.gz certs/identity7.txt
echo "=== q=9 (5,021 lines)"; python3 d11cert.py hex/hex_q9.bin certs/q9_lines.txt DUAL parts/dual_q9.phi
echo "=== q=16 (points from the order-255 quotient)"; python3 d11cert.py hex/hex_q16.bin certs/q16_lines.txt certs/q16_points_o255.txt
