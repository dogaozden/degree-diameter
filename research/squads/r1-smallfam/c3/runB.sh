#!/bin/bash
# chain B: (4,9) affine candidates
cd /home/user/degree-diameter/research/theorems/smallfam
OUT=/home/user/degree-diameter/research/squads/r1-smallfam/c3
exprs=(
'Aff(2,5,SL(2,5))'
'Aff(2,4,GL(2,4))'
'Aff(3,5,Group([ImmutableMatrix(GF(5),[[0,1,0],[0,0,1],[1,0,0]]),ImmutableMatrix(GF(5),[[0,1,0],[1,0,0],[0,0,4]]),ImmutableMatrix(GF(5),[[4,0,0],[0,4,0],[0,0,1]])]))'
'Aff(2,8,Filtered(List(ConjugacyClassesSubgroups(GL(2,8)),Representative),H->Size(H)=42)[1])'
)
for e in "${exprs[@]}"; do
  echo "### $e"
  timeout 900 nice -n 10 python3 named.py 4 9 "$e" --threads 1 --outdir "$OUT"
  echo "### exit $?"
done
echo CHAIN_B_DONE
