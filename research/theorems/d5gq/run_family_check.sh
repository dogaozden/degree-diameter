#!/bin/bash
# explicit families of Corollaries 10.1-10.4, built independently (scripts written by the referee agent), all-pairs checked
cd "$(dirname "$0")"
{
echo "== (10,5) q=7 HHDHD"; python3 family_check.py 7 HHDHD 22 22 3
echo "== (13,5) q=9 HHHDHHD"; python3 family_check.py 9 HHHDHHD 42 30 4
echo "== (14,5) q=9 HHHHDHHHD"; python3 family_check.py 9 HHHHDHHHD 26 26 3
echo "== (11,5) q=8 r=2 duality"; python3 family_check_even.py 8 2 120 3 1
echo "== (12,5) q=8 r=3 duality"; python3 family_check_even.py 8 3 120 3 1
echo "== (15,5) q=11 HHHDHHD"; python3 family_check.py 11 HHHDHHD 66 36 4
} > family_check_out.txt 2>&1
echo DONE >> family_check_out.txt
