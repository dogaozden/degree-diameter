#!/bin/bash
# usage: run.sh SEED K P KK R SECS
B=/home/user/degree-diameter/research/squads/beyond11b/bin
cd /home/user/degree-diameter/research/squads/beyond11b/r3/i14
SEED=$1; K=$2; P=$3; KK=$4; R=$5; SECS=${6:-65}
OUT=sol_p${P}_k${KK}_s${SEED}_K${K}.txt
THREADS=1 timeout 105 nice -n 10 bash -c "$B/haar_gen3 8 11 $SECS $SEED $K $OUT meta $P $KK $R 1 > run_p${P}_k${KK}_s${SEED}_K${K}.out 2>&1 & pid=\$!; peak=0; while kill -0 \$pid 2>/dev/null; do r=\$(awk '/VmHWM/{print \$2}' /proc/\$pid/status 2>/dev/null); [ -n \"\$r\" ] && [ \"\$r\" -gt \"\$peak\" ] && peak=\$r; sleep 2; done; echo PEAK_KB \$peak >> run_p${P}_k${KK}_s${SEED}_K${K}.out; wait \$pid"
echo "--- p=$P k=$KK r=$R seed=$SEED K=$K secs=$SECS $(date +%T)"; cat run_p${P}_k${KK}_s${SEED}_K${K}.out
