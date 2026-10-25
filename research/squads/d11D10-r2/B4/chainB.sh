#!/bin/bash
# waits (outside the gate) for the valid2 haar_sym run, then checks breakdet copy and valid2 through the gate
while ! grep -q '^exit=' /home/user/degree-diameter/research/squads/d11D10-r2/B4/hs_valid2.log 2>/dev/null; do sleep 5; done
cd /home/user/degree-diameter/research/squads/d11D10-r2/B4 || exit 1
python3 -I /home/user/degree-diameter/research/squads/d11D10-r2/B4/mkcases.py breakdet /home/user/degree-diameter/research/squads/d11D10-r2/B4/d16D8_psl_243_1_plain_s2.txt /home/user/degree-diameter/research/squads/d11D10-r2/B4/corrupt_breakdet_from_s2.txt || exit 1
/home/user/degree-diameter/research/squads/d11D10-r2/gate.sh 400 /home/user/degree-diameter/research/squads/d11D10-r2/B4/chain_small.sh /home/user/degree-diameter/research/squads/d11D10-r2/B4/corrupt_breakdet_from_s2.txt /home/user/degree-diameter/research/squads/d11D10-r2/B4/d16D8_psl_243_1_plain_s2.txt > /home/user/degree-diameter/research/squads/d11D10-r2/B4/logs/chainB.out 2>&1
echo "chainB gate exit=$?" >> /home/user/degree-diameter/research/squads/d11D10-r2/B4/logs/chain_small.status
