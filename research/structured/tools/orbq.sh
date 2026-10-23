#!/bin/bash
# Sequential job queue for haar_sym.  Each line:  ORBIT_SPEC | d D seconds seed K GROUP... n
# e.g.  3 2 2 | 8 7 600 1 8 psl 13 19
# Solutions go to OUTDIR/d<d>D<D>_<group>_orb<k>_s<seed>.txt, logs next to them; a solved job is checked with
# build_haar2.py (verdict appended to the log).  Lines starting with # are skipped; a job whose log already has
# RESULT is skipped (restartable).  usage: orbq.sh JOBFILE OUTDIR [BIN]
JOBS=$1; OUT=$2; BIN=${3:-$(dirname "$0")/../haar_sym}
HERE=$(cd "$(dirname "$0")" && pwd); CHECK=$HERE/../../frontier/build_haar2.py
mkdir -p "$OUT"
while IFS= read -r line; do
  [[ -z "$line" || "$line" =~ ^# ]] && continue
  spec=$(echo "${line%%|*}" | xargs); rest=$(echo "${line#*|}" | xargs)
  set -- $rest; d=$1; D=$2; secs=$3; seed=$4; K=$5; shift 5; grp="$*"
  k=${spec%% *}; tag="d${d}D${D}_$(echo $grp | tr ' ' '_')_orb${k}_s${seed}"
  log=$OUT/$tag.log; sol=$OUT/$tag.txt
  grep -q RESULT "$log" 2>/dev/null && continue
  echo "$(date +%H:%M:%S) start $tag" >&2
  ORBIT="$spec" timeout $((secs + 60)) "$BIN" $d $D $secs $seed $K "$sol" $grp > "$log" 2>&1
  if [ -s "$sol" ]; then
    read -r _ _ fam p _ n _ NN < <(head -1 "$sol")
    big=0; [[ "$NN" =~ ^[0-9]+$ ]] && [ "$NN" -gt 10000000 ] && big=1
    if [ $big = 1 ] && [ "$fam" = sl ] && [ -x "$HERE/hcsl" ] && [ -x "$HERE/hc2" ]; then
      # > 20M vertices, SL(2,p) x Z_n: the two independent low-memory checkers (build_haar2 needs hours and > 7 GB)
      "$HERE/hcsl" "$sol" 2>&1 | tail -1 >> "$log"; "$HERE/hc2" "$sol" 2>&1 | tail -1 >> "$log"
    elif [ $big = 1 ] && [ "$fam" = psl ] && [ -x "$HERE/haarcheck_psl" ]; then
      "$HERE/haarcheck_psl" "$sol" 2>&1 | tail -1 >> "$log"            # > 20M vertices, PSL(2,p) x Z_n
    elif [ $big = 1 ]; then echo "UNCHECKED: > 20M vertices and no low-memory checker for $fam" >> "$log"
    else python3 "$CHECK" "$sol" 2>&1 | tail -3 >> "$log"; fi
  fi
  echo "$(date +%H:%M:%S) done  $tag: $(grep -h 'RESULT\|VALID' "$log" | tr '\n' ' ')" >&2
done < "$JOBS"
