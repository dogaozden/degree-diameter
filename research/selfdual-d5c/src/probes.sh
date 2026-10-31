#!/bin/bash
# probes.sh: one group just above each target of (14,5), (15,5), (16,5), 60 s per record and type, 1200 s budget each
R0="$(cd "$(dirname "$0")/.." && pwd)"
K=14 TYPES=2,x SHUFFLE=1 STOPFIRST=1 SECS=60 TBUDGET=1200 MAXSOL=1 SEED=1 TAG=probe NICE=0 $R0/src/run1.sh meta 163 54 23 1
K=15 TYPES=1,3 SHUFFLE=1 STOPFIRST=1 SECS=60 TBUDGET=1200 MAXSOL=1 SEED=1 TAG=probe NICE=0 $R0/src/run1.sh meta 433 24 64 1
K=16 TYPES=2,x SHUFFLE=1 STOPFIRST=1 SECS=60 TBUDGET=1200 MAXSOL=1 SEED=1 TAG=probe NICE=0 $R0/src/run1.sh meta 353 48 70 1
