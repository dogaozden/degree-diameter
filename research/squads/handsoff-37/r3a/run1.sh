#!/bin/bash
# usage: run1.sh NAME M K ALPHA SIGA SIGB SECS SEED T0 T1     (env BIN = symloc binary, default ./symloc)
# one symmetric SA run (group Z_M x| <sigma,alpha>, lift of K+K base, n = 2*K*M).
# The start graph (degree-only SAT) is redrawn with new SAT seeds until it is connected (max 8 tries).
# Results appended to out/results.tsv: name M K alpha sA sB seed group n best(symloc cost) scoreboard-far line
set -u
name=$1; m=$2; k=$3; al=$4; sa=$5; sb=$6; secs=$7; seed=$8; T0=$9; T1=${10}
BIN=${BIN:-./symloc}
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
d=out/$name/s$seed
mkdir -p $d
ok=0
for try in $(seq 0 7); do
  sd=$((seed + 1000 * try))
  if ! timeout 60 nice -n 10 python3 mkgroup.py $m $k $al "$sa" "$sb" $d/grp.txt $d/start.txt $sd > $d/mk.log 2>&1; then
    continue
  fi
  if ../bin/score37 $d/start.txt | grep -q "connected=yes"; then ok=1; break; fi
done
if [ $ok -ne 1 ]; then
  echo "NOCONN $name seed=$seed (start graph never connected; running on last start)"
  if [ ! -s $d/grp.txt ] || [ ! -s $d/start.txt ]; then echo -e "$name\t$m\t$k\t$al\t$sa\t$sb\t$seed\tMKFAIL" >> out/results.tsv; echo "MKFAIL $name $seed"; exit 0; fi
fi
go=$(head -1 $d/mk.log | awk '{print $3}')
n=$((2*k*m))
timeout 100 nice -n 10 $BIN $d/grp.txt $d/start.txt $((secs*40000)) $T0 $T1 $secs $seed $d/sa > $d/sa.out 2> $d/sa.log
far=$(grep "done best" $d/sa.log | awk '{print $3}')
bf=$(../bin/score37 $d/sa_best.edges 2>/dev/null | tail -1)
echo -e "$name\t$m\t$k\t$al\t$sa\t$sb\t$seed\tgroup=$go\tn=$n\tbin=$BIN\tcost=$far\ttry=$try\t$bf" >> out/results.tsv
echo "$name seed=$seed group=$go n=$n cost=$far | $bf"
