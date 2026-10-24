#!/bin/bash
# chain A: (4,8) affine candidates, one named.py call per expression (threads 1, nice 10)
cd /home/user/degree-diameter/research/theorems/smallfam
OUT=/home/user/degree-diameter/research/squads/r1-smallfam/c3
exprs=(
'Aff(2,5,Filtered(List(ConjugacyClassesSubgroups(GL(2,5)),Representative),H->Size(H)=48)[2])'
'Aff(2,7,Filtered(List(ConjugacyClassesSubgroups(GL(2,7)),Representative),H->Size(H)=24)[2])'
'Aff(3,3,Group([DiagonalMat([-One(GF(3)),One(GF(3)),One(GF(3))]),PermutationMat((1,2),3,GF(3)),PermutationMat((1,2,3),3,GF(3))]))'
'Aff(4,2,Group(Concatenation(List(GeneratorsOfGroup(GL(2,2)),A->DirectSumMat(A,IdentityMat(2,GF(2)))),List(GeneratorsOfGroup(GL(2,2)),A->DirectSumMat(IdentityMat(2,GF(2)),A)),[PermutationMat((1,3)(2,4),4,GF(2))])))'
'Aff(2,5,Filtered(List(ConjugacyClassesSubgroups(GL(2,5)),Representative),H->Size(H)=48)[1])'
'Aff(2,7,Filtered(List(ConjugacyClassesSubgroups(GL(2,7)),Representative),H->Size(H)=24)[5])'
'Aff(2,7,Filtered(List(ConjugacyClassesSubgroups(GL(2,7)),Representative),H->Size(H)=24)[1])'
'Aff(2,7,Filtered(List(ConjugacyClassesSubgroups(GL(2,7)),Representative),H->Size(H)=24)[6])'
)
for e in "${exprs[@]}"; do
  echo "### $e" 
  timeout 900 nice -n 10 python3 named.py 4 8 "$e" --threads 1 --outdir "$OUT"
  echo "### exit $?"
done
echo CHAIN_A_DONE
