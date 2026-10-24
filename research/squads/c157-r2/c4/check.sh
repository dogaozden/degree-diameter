#!/bin/bash
# check.sh Q K KIND SOLFILE: for k = 1,2,3 run kcopy_hub check, kcopy_hub edges + apsp (DELTA = q+1+k, D = 7)
# and apsp_sym (B = 2N, r = 2k+1). Appends one row per case to cases.md and results.tsv.
cd /home/user/degree-diameter/research/squads/c157-r2/c4 || exit 1
Q=$1; K=$2; KIND=$3; SOL=$4
case $Q in 3) N=364;; 5) N=3906;; *) echo "bad q"; exit 1;; esac
HEX=hex/hex_q$Q.bin; B=$((2*N))
KC=/home/user/degree-diameter/research/d15D7/kcopy_hub
SYM=/home/user/degree-diameter/research/d15D7/apsp_sym
[ -f cases.md ] || printf '| case | q | K | k | kind | maxdeg (Delta) | kcopy: max ecc, bad src -> verdict | apsp: diameter -> verdict | apsp_sym: diameter -> verdict | all three agree | lemma (ecc<=7 iff diam<=7) |\n|---|---|---|---|---|---|---|---|---|---|---|\n' > cases.md
[ -f results.tsv ] || printf 'case\tq\tK\tk\tkind\tkc\tapsp\tapsym\tagree\tlemma\tecc\tdiam\tmaxdeg\n' > results.tsv
for k in 1 2 3; do
  tag=q${Q}_K${K}_${KIND}_k${k}; DELTA=$((Q+1+k)); R=$((2*k+1))
  kc_out=$($KC check $HEX $SOL $k 2>&1); kc_rc=$?
  kc_md=$(echo "$kc_out" | sed -n 's/.*maxdeg=\([0-9]*\) (Delta.*/\1/p')
  kc_line=$(echo "$kc_out" | grep 'freed sources and hubs')
  kc_ecc=$(echo "$kc_line" | sed -n 's/.*max eccentricity \([0-9]*\).*/\1/p')
  kc_bad=$(echo "$kc_line" | sed -n 's/.*bad sources \([0-9]*\).*/\1/p')
  kc_v=$(echo "$kc_line" | sed -n 's/.* -> \(OK\|FAIL\)$/\1/p'); [ -z "$kc_v" ] && kc_v="ERR$kc_rc"
  $KC edges $HEX $SOL $k edges/$tag.txt 2>/dev/null
  ap_out=$(timeout 900 nice -n 10 ./apsp edges/$tag.txt $DELTA 7 2>&1)
  ap_diam=$(echo "$ap_out" | sed -n 's/.*diameter=\([0-9]*\).*/\1/p')
  ap_v=$(echo "$ap_out" | grep -o 'RESULT [A-Z]*' | head -1 | awk '{print $2}'); [ -z "$ap_v" ] && ap_v="ERR"
  sy_out=$(timeout 900 nice -n 10 $SYM edges/$tag.txt $DELTA 7 $B $R 1 2>&1)
  sy_diam=$(echo "$sy_out" | sed -n 's/.*diameter=\([0-9]*\).*/\1/p')
  sy_v=$(echo "$sy_out" | grep -o 'RESULT [A-Z]*' | head -1 | awk '{print $2}'); [ -z "$sy_v" ] && sy_v="ERR"
  case $kc_v in OK) kcx=VALID;; FAIL) kcx=INVALID;; *) kcx=ERR;; esac
  agree=no; [ "$kcx" = "$ap_v" ] && [ "$ap_v" = "$sy_v" ] && [ "$ap_v" != ERR ] && agree=yes
  ecc7=no; [ -n "$kc_ecc" ] && [ "$kc_ecc" -le 7 ] && [ "$kc_bad" = 0 ] && ecc7=yes
  diam7=no; [ -n "$ap_diam" ] && [ "$ap_diam" -le 7 ] && diam7=yes
  lem=no; [ "$ecc7" = "$diam7" ] && lem=yes
  echo "| $tag | $Q | $K | $k | $KIND | $kc_md ($DELTA) | $kc_ecc, $kc_bad -> $kc_v | ${ap_diam:-n/a} -> $ap_v | ${sy_diam:-n/a} -> $sy_v | $agree | $lem |" >> cases.md
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$tag" $Q $K $k $KIND "$kc_v" "$ap_v" "$sy_v" $agree $lem "$kc_ecc" "${ap_diam:-n/a}" "$kc_md" >> results.tsv
  rm -f edges/$tag.txt
done
