#!/bin/bash
# chain.sh base.in prefix [seed]: wpo (if structural cost > 0) -> nujoint TARGET=1 from a random nu -> finish.sh (z6 lift + apsp)
cd /tmp/claude-0/-home-user-degree-diameter/468680c1-3e6e-599d-b1ca-881241eddc40/scratchpad/w
b=$1; P=$2; seed=${3:-1}
cost() { SCORE=1 /tmp/po7 $1 | tail -1 | grep -oE "cost=[0-9]+" | cut -d= -f2; }
c=$(cost $b); echo "start cost $c"
if [ "$c" != "0" ]; then
  SECS=${WSECS:-900} SEED=$seed OUT=$P.w.in OUT0=$P.w0.in nice /tmp/wpo $b > $P.w.log 2>&1
  [ -f $P.w0.in ] || { echo "wpo did not reach 0: $(cost $P.w.in)"; exit 1; }
  b=$P.w0.in
fi
echo "structural 0: $b"
n=$(head -1 $b | cut -d' ' -f1)
python3 -c "import random; r=random.Random($seed); print('\n'.join(str(r.randrange(2)) for _ in range($n*9)))" > $P.nu0
TARGET=1 SECS=${NSECS:-1200} SEED=$seed T0=0.4 T1=0.05 PS=0.02 WS=50 NU=$P.nu0 OUTNU=$P.nu OUT=$P.final.in nice /tmp/nuj7 $b > $P.nuj.log 2>&1
tail -n 1 $P.nuj.log
grep -q "violated=0 " $P.nuj.log && cd /home/user/degree-diameter/research/d11D5/inc && ./finish.sh /tmp/claude-0/-home-user-degree-diameter/468680c1-3e6e-599d-b1ca-881241eddc40/scratchpad/w/$P.final.in /tmp/claude-0/-home-user-degree-diameter/468680c1-3e6e-599d-b1ca-881241eddc40/scratchpad/w/$P.nu /tmp/claude-0/-home-user-degree-diameter/468680c1-3e6e-599d-b1ca-881241eddc40/scratchpad/w/$P.lift 11 5
