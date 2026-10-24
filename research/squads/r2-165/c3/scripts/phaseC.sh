#!/bin/bash
# wait (bounded) for the reduced screen to finish, pick the best candidate per target, then run phase C with 2 workers
timeout 900 bash -c 'until [ "$(wc -l < /tmp/claude-0/r2c3/res_screen.txt)" -ge 120 ]; do sleep 3; done'
/tmp/claude-0/r2c3/make_phaseC.sh
cat /tmp/claude-0/r2c3/jobs_phaseC.txt | xargs -P 2 -L 1 /tmp/claude-0/r2c3/run1.sh > /tmp/claude-0/r2c3/res_phaseC.txt
echo "PHASEC_DONE $(wc -l < /tmp/claude-0/r2c3/res_phaseC.txt) lines"
