#!/bin/bash
# bg.sh TAG cmd args... : start one long run in the background, in the current directory, at nice 10 and ONE thread
# (THREADS=1, OMP_NUM_THREADS=1 are forced; the director sets DIRECTOR=1 to keep its own values). Log out/TAG.log,
# pid out/TAG.pid, start time out/TAG.t0. Refuses to start while another run of this folder is alive (MAXRUNS, 1).
mkdir -p out; tag=$1; shift
if [ -z "$DIRECTOR" ]; then export THREADS=1 OMP_NUM_THREADS=1; fi
alive=0; for f in out/*.pid; do [ -f "$f" ] && kill -0 $(cat "$f") 2>/dev/null && alive=$((alive + 1)); done
if [ $alive -ge ${MAXRUNS:-1} ]; then echo "REFUSED: $alive run(s) of this folder still alive; poll until FINISHED or kill it first"; exit 1; fi
nohup nice -n 10 "$@" > out/$tag.log 2>&1 &
echo $! > out/$tag.pid; date +%s > out/$tag.t0
# autogroup scheduling is on here: each run is its own scheduling group and plain nice has no effect against other
# groups, so set the group's nice too (AGNICE, default 10; the director's own runs keep 0)
[ -z "$DIRECTOR" ] && echo ${AGNICE:-10} > /proc/$!/autogroup 2>/dev/null
echo "started $tag (pid $(cat out/$tag.pid)) at $(date -u +%T)"
