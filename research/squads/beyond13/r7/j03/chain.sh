#!/bin/bash
# chain.sh SECS SEED0 "m k r" ... : one hmeta run per group (START from the group's best file if present)
cd "$(dirname "$0")"; secs=$1; s0=$2; shift 2
for g in "$@"; do set -- $g; base=rec/g_$1_$2_$3; S=""
  [ -f $base.best ] && S=$base.best
  env ${S:+START=$S} T0=8 T1=1 REHEAT=400 THREADS=1 timeout 100 nice -n 10 ./hmeta 4 10 $secs $((s0 + $1 % 97)) 8 $base $1 $2 $3 2>&1 | grep RESULT | sed "s/^/$1 $2 $3 /"
  case "$(cat /dev/null)" in esac
done
