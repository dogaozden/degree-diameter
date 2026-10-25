#!/bin/sh
# Delta=4 Haar scans over Z_p x| Z_k (p prime), exhaustive in normal form, quotient filter on; N above the table.
cd "$(dirname "$0")/.."
nice -n 5 python3 frob_scan.py 4 7 421 1093 --threads 3 --maxsets 4e7 > runs/frob_d4D7.txt
nice -n 5 python3 frob_scan.py 4 8 1093 2000 --threads 3 --maxsets 4e7 > runs/frob_d4D8.txt
nice -n 5 python3 frob_scan.py 4 9 2486 3600 --threads 3 --maxsets 4e7 > runs/frob_d4D9.txt
echo ALLDONE >> runs/frob_d4D9.txt
