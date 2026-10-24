#!/bin/bash
# Reads speed_summary.tsv (written by speed.sh) and prints, per group, the speedup of every setting over the default
# (FAST=2, HWMIN=64, HWMAX=256, PFD=8).  Default time = mean of the default run and its drift-check repeat when both ran.
# Hash/best columns are compared with the default run of the same group (the trajectory must be identical).
B=/home/user/degree-diameter/research/squads/d11D10-r1/B5
awk -F'\t' '
NR == 1 { next }
{
  n = $1; ORD[++c] = n
  G[n] = $2; FA[n] = $3; HM[n] = $4; HX[n] = $5; PF[n] = $6; SU[n] = $7; WD[n] = $8
  EV[n] = $9; TM[n] = $10; US[n] = $11; RT[n] = $12; HS[n] = $13; BS[n] = $14; ST[n] = $16
}
END {
  for (i = 1; i <= c; i++) {
    n = ORD[i]; g = G[n]
    if (ST[n] != "ok") { printf "%-14s %-4s %s\n", n, g, ST[n]; continue }
    ref = g "_def"; ref2 = g "_def2"
    base = US[ref] + 0
    if (ST[ref2] == "ok") base = (US[ref] + US[ref2]) / 2
    wide = WD[n]; hw = "none"
    if (match(wide, /HW order [0-9]+/)) hw = substr(wide, RSTART + 9, RLENGTH - 9)
    if (wide ~ /no cyclic/) hw = "fallback"
    same = (HS[n] == HS[ref] && BS[n] == BS[ref] && EV[n] == EV[ref]) ? "same" : "DIFFERENT"
    printf "%-14s %-4s fast=%s hwmin=%-3s hwmax=%-3s pfd=%-3s HW=%-8s setup=%-6s evals=%-4s time=%-5s us/eval=%-6s evals/s=%-7s speedup_vs_default=%.3f trace=%s best=%s\n", \
      n, g, FA[n], HM[n], HX[n], PF[n], hw, SU[n], EV[n], TM[n], US[n], RT[n], base / US[n], same, BS[n]
  }
}' "$B/speed_summary.tsv"
