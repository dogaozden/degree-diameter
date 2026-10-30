#!/bin/bash
# after the order-96 b4a2y queues end: b4a2y over orders 111..127 (3 workers)
cd "$(dirname "$0")"
while pgrep -f "[j]oblist_b.txt|[j]oblist_c.txt|[a]fter_haar.sh" > /dev/null; do sleep 30; done
cat joblist_d.txt | xargs -P 3 -L 1 ./run_one.sh
