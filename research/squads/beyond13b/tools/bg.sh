#!/bin/bash
# bg.sh TAG cmd args... : start one long run in the background (environment variables pass through), in the current
# directory: log out/TAG.log, pid out/TAG.pid, start time out/TAG.t0. Returns at once. Then call poll.sh TAG.
mkdir -p out; tag=$1; shift
nohup "$@" > out/$tag.log 2>&1 &
echo $! > out/$tag.pid; date +%s > out/$tag.t0
echo "started $tag (pid $(cat out/$tag.pid)) at $(date -u +%T)"
