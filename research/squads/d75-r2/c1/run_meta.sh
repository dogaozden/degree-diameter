#!/bin/bash
# run_meta.sh M K R: metacyclic G = C_M : C_K, y x y^-1 = x^R (order M*K); export, all automorphisms, self-dual bi-coset search.
C=/home/user/degree-diameter/research/squads/d75-r2/c1; T=$C/tmp; mkdir -p $T $C/out
EX=/home/user/degree-diameter/research/d75-raise/src
M=$1; K=$2; R=$3; NAME=meta_${M}_${K}_${R}; t0=$(date +%s)
G=$T/$NAME.grp.g
cat > $G << GEOF
Cm := CyclicGroup(IsPcGroup, $M);;
Ck := CyclicGroup(IsPcGroup, $K);;
au := GroupHomomorphismByImages(Cm, Cm, [Cm.1], [Cm.1^$R]);;
hom := GroupHomomorphismByImages(Ck, AutomorphismGroup(Cm), [Ck.1], [au]);;
S := SemidirectProduct(Ck, hom, Cm);;
G := Range(IsomorphismPcGroup(S));;
N := Size(G);;
GEOF
cat > $T/$NAME.exp.g << GEOF
Read("$G");;
OUT:="$T/$NAME.ht";; NOAUT:=true;; INVS:=true;;
Read("$EX/export.g");;
GEOF
timeout 200 gap -q $T/$NAME.exp.g > $T/$NAME.gaplog 2>&1 < /dev/null
if [ ! -s $T/$NAME.ht ]; then echo "$NAME GAPFAIL" >> $C/out/summary.txt; exit 0; fi
cat > $T/$NAME.aut.g << GEOF
Read("$G");;
OUT:="$T/$NAME.aut.txt";;
Read("$EX/allaut.g");;
GEOF
timeout 300 gap -q $T/$NAME.aut.g > $T/$NAME.autlog 2>&1 < /dev/null
t1=$(date +%s)
timeout ${BST:-400} nice -n 15 $C/bsd75 $T/$NAME.ht $T/$NAME.aut.txt > $C/out/$NAME.out 2>&1
rc=$?
sols=$(grep -c "^SOL" $C/out/$NAME.out); yyf=$(grep -c "^YYFAIL" $C/out/$NAME.out)
echo "$NAME rc=$rc sols=$sols yyfail=$yyf gapsecs=$((t1-t0)) searchsecs=$(( $(date +%s) - t1 )) capped=$(grep -c CAPPED $C/out/$NAME.out); $(grep "^GROUP\|^CLASS\|^DONE" $C/out/$NAME.out | tr '\n' ';' | cut -c1-300)" >> $C/out/summary.txt
if [ "$sols" -gt 0 ]; then echo "HIT $NAME $(grep -m1 '^SOL' $C/out/$NAME.out)" >> $C/out/HITS.txt; fi
