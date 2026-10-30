#!/bin/bash
cd /home/user/degree-diameter/research/squads/s65r2/c8
run() { name=$1; grp=$2; typ=$3; shift 3
  env TYPE="$typ" SECS=8 SEED=1 EDGES=edges/$name.edges "$@" timeout 600 nice -n 10 /home/user/degree-diameter/research/s65/tools/mcos $grp > logs/$name.log 2>&1
  echo "== $name: $(grep -E '^COMB|^SOL|^RESULT' logs/$name.log | tr '\n' ' ')"
}
run C_174_1_a /home/user/degree-diameter/research/s65/groups/sg/sg_174_1.txt "1,1|2,2,2,2"
run C_180_31_a /home/user/degree-diameter/research/s65/groups/sg/sg_180_31.txt "1,1|2,2,2,2"
run C_180_8_a /home/user/degree-diameter/research/s65/groups/sg/sg_180_8.txt "1,1|2,2,2,2"
run C_174_1_b /home/user/degree-diameter/research/s65/groups/sg/sg_174_1.txt "2,2,2,2|2,2,2,2"
run C_180_31_b /home/user/degree-diameter/research/s65/groups/sg/sg_180_31.txt "2,2,2,2|2,2,2,2"
