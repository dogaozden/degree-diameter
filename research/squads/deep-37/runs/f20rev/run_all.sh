#!/bin/bash
for b in "$@"; do MAXSOL=1000 SOLPREFIX=sol_b$b ../../bin/orbdfs f20rev_b$b.txt 7 > out_b$b.txt 2> err_b$b.txt; echo "b=$b $(tail -1 out_b$b.txt)"; done
