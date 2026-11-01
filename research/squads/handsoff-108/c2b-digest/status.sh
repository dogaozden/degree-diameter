#!/bin/bash
# Read-only status for the digest: live processes by worker folder, chain histograms, scan progress, scoreboard tail.
S=/home/user/degree-diameter/research/squads/handsoff-108
cd $S || exit 1
date -u +"now %F %T UTC"; uptime | sed 's/^.*load/load/'
echo "== live processes (pid etime cpu% folder :: command)"
for p in $(pgrep -f . 2>/dev/null); do
  c=$(readlink /proc/$p/cwd 2>/dev/null); case "$c" in *handsoff-108/*)
    comm=$(ps -o comm= -p $p 2>/dev/null | tr -d ' '); args=$(tr '\0' ' ' < /proc/$p/cmdline 2>/dev/null)
    case "$comm" in haar*|exh|hexeval|timeout) ;; *) case "$args" in "/bin/bash ./"*) ;; *) continue;; esac;; esac
    echo "$p $(ps -o etime= -p $p | tr -s ' ') $(ps -o pcpu= -p $p | tr -d ' ')% ${c#*handsoff-108/} :: $(echo "$args" | cut -c1-100)";;
  esac
done
echo "== chain histograms (fields: chains min median <=12 <=9 <=6)"
$S/c2b-digest/hist.sh c1-grind/g1.log c1-grind/g2.log c1b-structure/ab.log c3b-sl23x49/d1.log c3b-sl23x49/d2.log c3b-sl23x49/d3.log c4-groups/d1.log c4-groups/d2.log c8c-smooth/ab_base.log c8c-smooth/ab_s1.log c7-throughput/*.log c3-twist/sl23_49.log 2>/dev/null | grep -v 'chains=0'
echo "== scan progress"
for f in c5c-scanC/out/C_scanA.tsv c6b-exhaust/out/K_scanA.tsv c6c-h12/out/A4_scanA.tsv c6c-h12/out/D6nsq_scanA.tsv; do echo "$f lines=$(wc -l < $f 2>/dev/null)"; done
for fam in "c5c-scanC C" "c6b-exhaust K"; do set -- $fam; (cd $S/$1 && timeout 120 python3 -I summ.py $2 2>&1 | grep -E 'classes scanned|^P =|exact full C|exact C over' | cut -c1-160); done
echo "== scoreboard: $(($(wc -l < $S/scoreboard.tsv)-1)) lines; last 4 (time worker cost)"
tail -n 4 $S/scoreboard.tsv | awk -F'\t' '{print substr($1,6,11), $2, $5}'
echo "== c7b hz summary"; cut -c1-90 $S/c7b-design/runs/hz_summary_q3.txt 2>/dev/null | tail -n 3
echo "== records/: $(ls $S/records | wc -l) files"
