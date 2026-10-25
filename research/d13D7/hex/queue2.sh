#!/bin/bash
cd /home/user/degree-diameter/research/d13D7
while kill -0 27487 2>/dev/null; do sleep 10; done
OMP_NUM_THREADS=4 nice -n 2 ./apsp_src hex/d12D7_dual_R1953.edges 12 7 multi_t/src12.txt > hex/d12D7_dual_R1953.apsp_src.txt 2> hex/d12D7_dual_R1953.apsp_src.err
OMP_NUM_THREADS=4 nice -n 2 ./apsp_src hex/d16D7_R168.edges 16 7 multi_t/src16_partial.txt > hex/d16D7_R168.apsp_partial.txt 2> hex/d16D7_R168.apsp_partial.err
OMP_NUM_THREADS=4 nice -n 2 ./apsp_src hex/d15D7_R397.edges 15 7 multi_t/src15.txt > hex/d15D7_R397.apsp_src.txt 2> hex/d15D7_R397.apsp_src.err
