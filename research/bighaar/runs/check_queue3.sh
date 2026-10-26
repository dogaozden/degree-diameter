#!/bin/bash
B=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin
THREADS=1 nice -n 5 timeout 1h ../check_one.sh hcheckpsl check_hcheckpsl_d16D10_psl_179_821.txt $B/hcheckpsl ../../frontier/sols/d16D10_psl_179_821_orb5g_s41.txt
nice -n 5 timeout 2h ../check_one.sh haarcheck_psl check_haarcheck_psl_d16D10_psl_179_821.txt $B/hcpsl ../../frontier/sols/d16D10_psl_179_821_orb5g_s41.txt
