#!/bin/bash
# run_groups.sh: for each "n id ninv ..." line of list.txt: export the group (d75 export.g, with Aut classes), run haar6 (exh,
# p = 3 and 5), and apsp-check any solution.  Summary lines go to summary.txt.
D=/home/user/degree-diameter/research/squads/sd5-r1/c6
export TMPDIR=$D/tmp
cd $D
while read n id ninv rest; do
  base=g${n}_${id}
  timeout 150 nice -n 15 gap -q -c "N:=$n;; ID:=$id;; OUT:=\"$D/tmp/$base.ht\";;" /home/user/degree-diameter/research/d75-raise/src/export.g < /dev/null > /dev/null 2>&1
  if [ ! -s tmp/$base.ht ]; then echo "$n $id ninv $ninv EXPORT_FAIL_OR_TIMEOUT" >> summary.txt; continue; fi
  EDGES=$D/tmp/$base EDGESMAX=3 timeout 300 nice -n 15 ./haar6 tmp/$base.ht > runs/$base.out 2>&1
  best=$(grep '^DONE' runs/$base.out | sed 's/.*best_cost \([0-9]*\).*/\1/')
  nsol=$(grep -c '^SOL' runs/$base.out)
  alphas=$(grep -c '^ALPHA' runs/$base.out)
  valid=NONE
  for f in tmp/${base}_*.el; do [ -f "$f" ] || continue
    r=$(timeout 200 /home/user/degree-diameter/research/selfdual-d5/src/apsp "$f" 6 5 | tail -1)
    case "$r" in *"RESULT VALID"*) valid="$f:$r";; esac
  done
  echo "$n $id ninv $ninv alphas(3,5) $alphas sols $nsol best_cost ${best:-NA} apsp $valid" >> summary.txt
  rm -f tmp/$base.ht
done < list_rest.txt
echo ALLDONE >> summary.txt
