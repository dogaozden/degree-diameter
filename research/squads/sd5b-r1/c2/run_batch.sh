#!/bin/bash
# c2 batch: direct products G1 x G2 (G1 non-metacyclic, so the product is non-metacyclic: quotient/subgroup argument)
cd /home/user/degree-diameter
C2=/home/user/degree-diameter/research/squads/sd5b-r1/c2
export TMPDIR=$C2/tmp
H3='SmallGroup(27,First([1..5], i -> not IsAbelian(SmallGroup(27,i)) and Exponent(SmallGroup(27,i))=3))'
run() {  # name, GAP expression for G
  local name=$1 expr=$2
  echo "== $name $(date +%T)"
  timeout 300 nice -n 15 gap -q -c "G:=$expr;; Print(\"order \", Size(G), \" center \", Size(Centre(G)), \" inv \", Number(Elements(G), x->Order(x)=2), \"\n\");; OUT:=\"$C2/$name.ht\";; NOEXT:=1;;" research/selfdual-d5/src/export_sd.g
  echo "export rc $?"
  K=9 SECS=3 NB=48 STALL=1000 TYPES=1,3,5 NOID=1 SEED=1 EDGES=$C2/sol_$name.edges \
    timeout 900 nice -n 15 research/selfdual-d5/src/sdtabu2 $C2/$name.ht all > $C2/$name.out 2>&1
  echo "screen rc $? $(date +%T)"
  grep -c '^TABU' $C2/$name.out
  grep '^TABU' $C2/$name.out | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1)}' | sort -n | head -1
}
run a_h3_d29 "DirectProduct($H3, DihedralGroup(58))"
run b_a4_d65 "DirectProduct(AlternatingGroup(4), DihedralGroup(130))"
run c_a4_d67 "DirectProduct(AlternatingGroup(4), DihedralGroup(134))"
run d_s4_d33 "DirectProduct(SymmetricGroup(4), DihedralGroup(66))"
run h_h3_a5 "DirectProduct($H3, AlternatingGroup(5))"
echo "BATCH DONE $(date +%T)"
