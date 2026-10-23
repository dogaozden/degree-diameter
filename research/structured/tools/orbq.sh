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
  if [ -s "$sol" ]; then python3 "$CHECK" "$sol" 2>&1 | tail -3 >> "$log"; fi
  echo "$(date +%H:%M:%S) done  $tag: $(grep -h 'RESULT\|VALID' "$log" | tr '\n' ' ')" >&2
done < "$JOBS"
