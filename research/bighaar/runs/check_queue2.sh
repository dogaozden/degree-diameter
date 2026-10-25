#!/bin/bash
# Sequential checks on one core (after the running hcheckpsl of 151 x 1331): hcheckpsl cross-checks, then haarcheck_psl on the best.
B=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin
while pgrep -f 'hcheckpsl ../../frontier/sols/d16D10_psl_151_1331' > /dev/null; do sleep 10; done
for g in 151_1321_orb5f_s1 191_661_orb5g_s12; do
  t=${g%_orb*}; THREADS=1 nice -n 5 timeout 2h ../check_one.sh hcheckpsl check_hcheckpsl_d16D10_psl_$t.txt $B/hcheckpsl ../../frontier/sols/d16D10_psl_$g.txt
done
nice -n 5 timeout 3h ../check_one.sh haarcheck_psl check_haarcheck_psl_d16D10_psl_191_671.txt $B/hcpsl ../../frontier/sols/d16D10_psl_191_671_orb5g_s23.txt
