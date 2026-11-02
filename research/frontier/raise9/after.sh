#!/bin/bash
# after.sh PID QUEUEFILE: start dq.sh QUEUEFILE once process PID has exited
cd "$(dirname "$0")"; while kill -0 $1 2>/dev/null; do sleep 10; done; ./dq.sh $2
