#!/bin/bash
# Sequential independent checks of the (16,10) PSL finds on one core.
B=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin
for g in 151_1331_orb5f_s1 151_1321_orb5f_s1 191_661_orb5g_s12; do
  t=${g%_orb*}; THREADS=1 nice -n 5 timeout 2h ../check_one.sh hcheckpsl check_hcheckpsl_d16D10_psl_$t.txt $B/hcheckpsl ../../frontier/sols/d16D10_psl_$g.txt
done
nice -n 5 timeout 3h ../check_one.sh haarcheck_psl check_haarcheck_psl_d16D10_psl_181_781.txt $B/hcpsl ../../frontier/sols/d16D10_psl_181_781_orb5g_s14.txt
