#!/bin/bash
# usage: screen.sh START END  (1-based lines of jobs.txt); sym (Haar-type mirrored) tabu, 6 s per run
C=/home/user/degree-diameter/research/squads/deep-65b/round1/c2
G=/home/user/degree-diameter/research/squads/deep-65b/groups
S=/home/user/degree-diameter/research/squads/deep-65b/shared
cd $C
sed -n "$1,$2p" jobs.txt | while read o id a; do
  name=$(cut -d'|' -f1 $G/sg_${o}_${id}.name | sed 's/ |Aut.*//')
  out=screen/o${o}_${id}_a${a}
  line=$(timeout 20 nice -n 15 ./lift2 $G/sg_${o}_${id}.tab $a tabu 1 6 $out 10 100 0 1 | head -1)
  best=$(echo "$line" | sed -n 's/.* best=\([0-9]*\).*/\1/p')
  tsol=$(echo "$line" | sed -n 's/.*t_solution=\([^ ]*\).*/\1/p')
  it=$(echo "$line" | sed -n 's/.* iters=\([0-9]*\).*/\1/p')
  echo -e "$o\t$id\t$name\ta=$a\tbest=$best\tt=$tsol\titers=$it" | tee -a screen/results.tsv
  if [ "$best" = "0" ]; then
    echo "  FOUND cost 0 at order $o id $id a=$a: $(timeout 60 nice -n 15 $S/score65 $out.edges)  $(timeout 60 nice -n 15 $S/apsp $out.edges 6 5 | tail -1)"
  fi
done
