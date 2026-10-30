#!/bin/bash
# waits for the haar5x queue to finish, then runs a third b4a2y worker on the remaining order-96 groups (from the end)
while pgrep -f "joblist_h.txt" > /dev/null; do sleep 20; done
cat joblist_c.txt | xargs -P 1 -L 1 ./run_one.sh
