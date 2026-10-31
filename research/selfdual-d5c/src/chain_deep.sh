#!/bin/bash
# chain_deep.sh: after probes.sh ends, deep runs (600 s) on the 4 best screened K = 13 groups
R0="$(cd "$(dirname "$0")/.." && pwd)"
while pgrep -x probes.sh > /dev/null; do sleep 30; done
$R0/src/deep.sh 13 24 4 600
