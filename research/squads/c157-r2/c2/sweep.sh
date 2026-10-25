#!/bin/bash
# c2 sweep runner (squad c157-r2, parameter sweep of the finishing local search).
# Usage: bash sweep.sh NAME BIN K INIT SECS BESTK [T0]
#   BIN = ./d7hexr (research/d15D7) or the round-1 d7hexs binary (research/squads/c157-r1/c5/d7hexs)
# Same command as the brief: search hex/hex_q11.bin K 1 SECS DONE 3 2, env INIT/NOTRUE=1/SKIPFULL=1/BESTK (T0 for d7hexs),
# THREADS=1, nice -n 10, one process at a time, wall cap 200 s.
# Difference: the process is stopped as soon as it prints "fast search done". The BFS phase after the fast search never
# changes the proxy, and it would otherwise run up to SECS more CPU seconds (so each run would last ~250 s, not 150 s).
# The proxy is read from that line: "proxy" = the proxy at the end of the 0.9*SECS CPU-second anneal, "best" = lowest seen.
# Wall cap: the budget is CPU seconds (clock()), and the machine is shared (load 6 on 4 cores), so one run needs
# ~270-300 s of wall time; the cap is WALLCAP (default 600). A cap of 200 s stopped runs at about 100 CPU seconds.
NAME=$1; BIN=$2; K=$3; INIT=$4; SECS=$5; BK=$6; T0V=${7:-}
CAP=${WALLCAP:-600}
CARD=/home/user/degree-diameter/research/squads/c157-r2/c2
SCR=/tmp/claude-0/-home-user-degree-diameter/07637e37-13ff-5912-bf46-48e7ca07985c/scratchpad
mkdir -p "$SCR"
ERR=$CARD/$NAME.err
DONE=$SCR/${NAME}_done.sol
cd /home/user/degree-diameter/research/d15D7 || exit 1
ENVS=(THREADS=1 INIT=$INIT NOTRUE=1 SKIPFULL=1 BESTK=$BK)
[ -n "$T0V" ] && ENVS+=(T0=$T0V)
START=$(date +%s)
env "${ENVS[@]}" nice -n 10 "$BIN" search hex/hex_q11.bin "$K" 1 "$SECS" "$DONE" 3 2 2> "$ERR" > "$SCR/${NAME}.stdout" &
PID=$!
STATUS=process_exited
while kill -0 "$PID" 2>/dev/null; do
  if grep -q "fast search done" "$ERR" 2>/dev/null; then kill -9 "$PID" 2>/dev/null; STATUS=stopped_after_fast_search; break; fi
  if [ $(( $(date +%s) - START )) -ge "$CAP" ]; then kill -9 "$PID" 2>/dev/null; STATUS=wall_cap_${CAP}s; break; fi
  sleep 1
done
wait "$PID" 2>/dev/null
WALL=$(( $(date +%s) - START ))
LINE=$(grep "fast search done" "$ERR" | tail -1)
PROXY=$(echo "$LINE" | sed -n 's/.* proxy \([0-9]*\).*/\1/p')
BEST=$(grep -o 'best [0-9]*' "$ERR" | awk '{print $2}' | sort -n | head -1)
IT=$(echo "$LINE" | sed -n 's/.*done: it \([0-9]*\).*/\1/p')
echo "$NAME K=$K BESTK=$BK T0=${T0V:-default} proxy_end=${PROXY:-NA} best_seen=${BEST:-NA} it=${IT:-NA} status=$STATUS wall=${WALL}s"
echo "  last line: $LINE"
rm -f "$DONE"
