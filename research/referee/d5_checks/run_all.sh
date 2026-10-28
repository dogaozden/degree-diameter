#!/bin/sh
# Reruns every referee check; output in checks.log.  Usage: ./run_all.sh BRANCH_CHECKOUT SCRATCH
#   BRANCH_CHECKOUT = a checkout of claude/gq-diameter-5-xa5d3d (for the solution files and the c4 example)
#   SCRATCH = a directory for temporary edge lists
B=$1; S=$2
G=$B/research/theorems/d5gq/graphs
gcc -O2 -fopenmp -o bfs bfs.c && gcc -O2 -o tourn tourn.c && gcc -O2 -o clique clique.c 2>/dev/null
echo "== GQ constructions and the Klein correspondence (sec. 1.2)"; python3 gq.py
echo "== small lemmas (1.2(c) exhaustive triads, 1.3, 1.4; hub structure of the record)"; python3 small_lemmas.py $G/d13D5_q9_relaxed66_n11636.json
echo "== numbers (sec. 0, 7, 8, 9, 10, 11, 12, 14)"; python3 nums.py
echo "== typings of regular tournaments (sec. 8)"
./tourn 5 > $S/t5.txt; ./tourn 7 > $S/t7.txt; ./tourn 9 1 > $S/t9.txt; head -1 $S/t5.txt $S/t7.txt $S/t9.txt
python3 layouts_eval.py $S/t5.txt $S/t7.txt $S/t9.txt
echo "== two-level tests: Theorems E, B, Prop. 6.4, 7.1, 7.2"; python3 test_theorems.py 1; python3 test_E_split.py 3
echo "== Computer-checked 6.5 (card c4)"
(cd $B/research/theorems/d5gq && python3 -c "import gqlib, json; json.dump([list(l) for l in gqlib.Q4(5).lines], open('$S/q45_lines.json','w'))")
python3 check_c4.py $S/q45_lines.json $B/research/squads/gqd5-r1/c4/best.json
echo "== largest partial ovoid of W(3), W(5) (pair fixed; clique number + 2)"
python3 w5_ovoid.py 3 | ./clique; python3 w5_ovoid.py 5 | ./clique
echo "== (13,5) 11,636 rebuilt from its solution file"
python3 rebuild_record.py $G/d13D5_q9_relaxed66_n11636.json $S/rec.edges && ./bfs 5 < $S/rec.edges
python3 - $S/rec.edges $G/d13D5_q9_relaxed66_n11636.edges.gz <<'PY'
import gzip, sys
def es(f):
    it = iter(f); n = int(next(it)); return n, {tuple(sorted(map(int, l.split()))) for l in it if l.strip()}
a = es(open(sys.argv[1])); b = es(gzip.open(sys.argv[2], 'rt'))
print("identical to the writer's edge list:", a == b)
PY
echo "== §12 remark: one more freed element on the D->D arc 3->6 of the 11,636 graph (report point 2)"
for sd in 1 2 3; do python3 arc36.py $G/d13D5_q9_relaxed66_n11636.json $S/rec.edges $S/a36.edges $sd; ./bfs 5 list < $S/a36.edges 2> $S/a36.bad
  python3 -c "import sys; from collections import Counter; N=820; P=[tuple(map(int,l.split())) for l in open(sys.argv[1])]; lev=lambda v: str(v//(2*N)) if v < 14*N else 'hub'; print('whole-graph bad pairs by levels:', dict(Counter(tuple(sorted((lev(a),lev(b)))) for a,b in P)))" $S/a36.bad; done
rm -f $S/a36.edges $S/a36.bad
echo "== (15,5)-type 20,713 rebuilt from its solution file"
python3 rebuild_record.py $G/d15D5type_q11_relaxed87_n20713.json $S/rec.edges && ./bfs 5 < $S/rec.edges
echo "== explicit families (Cor. 10.1-10.4), built from the printed ingredients"; ./run_families.sh $S
echo "== relaxed pair meeting in the ovoid (sec. 7, 'The hubs exist')"
for qq in 5 7 9; do python3 z_in_O.py $qq $S/z.edges && ./bfs 5 < $S/z.edges; python3 z_in_O.py $qq $S/z.edges break && ./bfs 5 < $S/z.edges; done
rm -f $S/rec.edges $S/z.edges
