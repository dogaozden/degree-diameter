#!/bin/bash
# final_check.sh PARAMS M : rebuild the B-level base graph of a Singer-invariant design (sym_1.npz, seed 1) and check
# COST on all 1332 point-orbit representatives with the independent checker lifteval (exact by Sigma-invariance).
set -e
D=/home/user/degree-diameter/research/squads/r1_d14D8/c4
cd "$D"
python3 mkbase.py "$1" "base_m$2.txt" 1 "$2"
REPS=$(python3 -c "import numpy as np; r=np.load('sym_1.npz')['repP']; print(','.join(str(int(x)) for x in r))")
/home/user/degree-diameter/research/squads/cells/d14D8_work/lifteval "base_m$2.txt" 8 "i:$REPS"
