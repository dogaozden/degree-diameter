#!/bin/bash
# c2 batch 2: products of two small Frobenius-type factors (C_p:C_a) x (C_r:C_2), and (C7:C3) x (C13:C3) x C2.
# Non-metacyclic: G' = C_pr is the only cyclic normal subgroup containing G' that could work, and the top
# (C_a x C_2, or C3 x C3 x C2) is not cyclic because its elements act non-trivially on C_pr.
cd /home/user/degree-diameter
C2=/home/user/degree-diameter/research/squads/sd5b-r1/c2
export TMPDIR=$C2/tmp
frob() { echo "SmallGroup($1,First([1..NrSmallGroups($1)], i -> Size(Centre(SmallGroup($1,i)))=1 and not IsAbelian(SmallGroup($1,i))))"; }
run() {
  local name=$1 expr=$2
  echo "== $name $(date +%T)"
  timeout 300 nice -n 15 gap -q -c "G:=$expr;; Print(\"order \", Size(G), \" center \", Size(Centre(G)), \" inv \", Number(Elements(G), x->Order(x)=2), \"\n\");; OUT:=\"$C2/$name.ht\";; NOEXT:=1;;" research/selfdual-d5/src/export_sd.g 2>/dev/null
  echo "export rc $?"
  K=9 SECS=3 NB=48 STALL=1000 TYPES=1,3,5 NOID=1 SEED=1 EDGES=$C2/sol_$name.edges \
    timeout 600 nice -n 15 research/selfdual-d5/src/sdtabu2 $C2/$name.ht all > $C2/$name.out 2>&1
  echo "screen rc $? $(date +%T) $(head -1 $C2/$name.out | grep -o 'records [0-9]*')"
  grep '^TABU' $C2/$name.out | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1)}' | sort -n | head -1
}
run e_f20_d41 "DirectProduct($(frob 20), DihedralGroup(82))"
run f_f116_d7 "DirectProduct($(frob 116), DihedralGroup(14))"
run g_f164_d5 "DirectProduct($(frob 164), DihedralGroup(10))"
run i_f52_d15 "DirectProduct($(frob 52), DihedralGroup(30))"
run j_f21_f39_c2 "DirectProduct(SmallGroup(21,1), SmallGroup(39,1), CyclicGroup(2))"
echo "BATCH2 DONE $(date +%T)"
