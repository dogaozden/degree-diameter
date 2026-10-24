#!/bin/bash
# usage: run_job.sh VARIANT SEED   (sl 53 x Z91, ORBIT="3 5 1", deterministic schedule VCLOCK=0.01 COOL=2, MAXSTEPS=800)
cd /home/user/degree-diameter/research/squads/d16D10-r1/c8 || exit 1
T=/tmp/claude-0/-home-user-degree-diameter/4ce63409-b0f8-5c33-8f23-00173ad34031/scratchpad/tools/research/structured
v=$1; s=$2; mkdir -p logs
case $v in
  base)  BIN=$T/haar_sym; EXTRA="" ;;
  L30)   BIN=./mysym; EXTRA="LOCALP=30 LOCALL=1" ;;
  L100)  BIN=./mysym; EXTRA="LOCALP=100 LOCALL=1" ;;
  *) echo "unknown variant $v"; exit 2 ;;
esac
env ORBIT="3 5 1" VCLOCK=0.01 COOL=2 MAXSTEPS=800 $EXTRA timeout 200 nice -n 10 $BIN 16 8 300 "$s" 8 /dev/null sl 53 91 > logs/${v}_s$s.out 2> logs/${v}_s$s.err
echo "$v $s rc=$?"
