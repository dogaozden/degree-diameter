#!/bin/bash
# sequential queue: waits for the running annealer (pid 1290, run 1) then runs the remaining three 600 s anneals one at a time
while kill -0 1290 2>/dev/null; do sleep 2; done
cd /home/user/degree-diameter/research/squads/r2
ORBIT="2 4 0" timeout 900 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym 8 8 600 1 8 /home/user/degree-diameter/research/squads/r2/c6/d8D8_240_psl7sl9_s1.txt prod psl 7 sl 9 1 > /home/user/degree-diameter/research/squads/r2/c6/d8D8_240_psl7sl9_s1.log 2>&1
ORBIT="4 2 0" timeout 900 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym 8 8 600 1 8 /home/user/degree-diameter/research/squads/r2/c6/d8D8_420_sl7psl9_s1.txt prod sl 7 psl 9 1 > /home/user/degree-diameter/research/squads/r2/c6/d8D8_420_sl7psl9_s1.log 2>&1
ORBIT="4 2 0" timeout 900 nice -n 10 /tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin/haar_sym 8 8 600 1 8 /home/user/degree-diameter/research/squads/r2/c6/d8D8_420_psl7sl9_s1.txt prod psl 7 sl 9 1 > /home/user/degree-diameter/research/squads/r2/c6/d8D8_420_psl7sl9_s1.log 2>&1
echo QUEUE_DONE > /home/user/degree-diameter/research/squads/r2/c6/queue.done
