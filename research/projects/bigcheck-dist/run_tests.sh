#!/bin/bash
# Tests for apsp_shard: a sharded run must agree with apsp.c (the reference all-pairs check) on every graph, a rerun of a
# shard must give the same bytes, and merge must refuse incomplete, mismatched or truncated report sets.
# Usage: run_tests.sh [WORKDIR]     (WORKDIR defaults to a fresh temp directory; prints ok/FAIL lines, exit 1 on any FAIL)
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../.." && pwd)
W=${1:-$(mktemp -d)}
mkdir -p "$W"
cc -O2 -o "$W/apsp" "$REPO/research/lifts/coordinator_check/apsp.c" 2>/dev/null || { echo "FAIL: build apsp.c"; exit 1; }
cc -O2 -pthread -Wall -o "$W/apsp_shard" "$HERE/apsp_shard.c" || { echo "FAIL: build apsp_shard.c"; exit 1; }
fail=0
ok()   { echo "ok: $1"; }
bad()  { echo "FAIL: $1"; fail=1; }

# Reference diameter from apsp.c (empty if the graph is disconnected).
ref_diam() { "$W/apsp" "$1" "$2" 99 | sed -n 's/.*diameter=\([0-9]*\).*/\1/p'; }

# Runs K shards (T threads each) and merges them. Prints the merge output, and sets MERGE_RC in this shell (so call it
# directly, not inside $(...)).
shard_all() { # EDGES d D K LAYOUT T TAG
    local g=$1 d=$2 D=$3 K=$4 lay=$5 T=$6 tag=$7 i reps=()
    for ((i = 0; i < K; i++)); do
        "$W/apsp_shard" shard "$g" "$d" "$D" "$K" "$i" "$T" "$lay" > "$W/$tag.$i.T$T.rep" || true
        reps+=("$W/$tag.$i.T$T.rep")
    done
    "$W/apsp_shard" merge "$g" "$d" "$D" "$K" "$lay" "${reps[@]}" > "$W/$tag.merge"; MERGE_RC=$?
    cat "$W/$tag.merge"
}
verdict() { sed -n 's/^RESULT \([A-Z]*\).*/\1/p' <<< "$1"; }

# case NAME EDGES d LAYOUT K: sharded verdicts with D = reference diameter (must be VALID) and D - 1 (must be INVALID).
case_graph() {
    local name=$1 g=$2 d=$3 lay=$4 K=$5 R out rc i
    R=$(ref_diam "$g" "$d")
    if [ -z "$R" ]; then bad "$name: apsp.c gives no diameter (graph not valid)"; return; fi
    shard_all "$g" "$d" "$R" "$K" "$lay" 1 "$name" > "$W/out.txt"; out=$(cat "$W/out.txt"); rc=$MERGE_RC
    if [ "$(verdict "$out")" = VALID ] && grep -q "diameter $R" <<< "$out" && [ "$rc" -eq 0 ]; then ok "$name (layout $lay, K=$K): diameter $R, merge VALID"
    else bad "$name (layout $lay, K=$K): expected VALID diameter $R; got rc $rc: $out"; fi
    shard_all "$g" "$d" $((R - 1)) "$K" "$lay" 1 "$name.below" > "$W/out.txt"; out=$(cat "$W/out.txt"); rc=$MERGE_RC
    if [ "$(verdict "$out")" = INVALID ] && [ "$rc" -ne 0 ]; then ok "$name (layout $lay, K=$K): D=$((R - 1)) merge INVALID"
    else bad "$name (layout $lay, K=$K): D=$((R - 1)) should be INVALID, got rc $rc"; fi
    # Threads do not change the reports: the 2-thread run must match the 1-thread run byte for byte.
    shard_all "$g" "$d" "$R" "$K" "$lay" 3 "$name.mt" > "$W/out.txt"; out=$(cat "$W/out.txt"); rc=$MERGE_RC
    for ((i = 0; i < K; i++)); do
        cmp -s "$W/$name.$i.T1.rep" "$W/$name.mt.$i.T3.rep" || bad "$name: shard $i differs between 1 and 3 threads"
    done
    [ "$rc" -eq 0 ] && ok "$name: 3-thread reports identical to 1-thread reports"
}

# Haar graph (research/lifts builder): diameter 10, degree 4, 12,416 vertices, 194 batches.
python3 "$REPO/research/lifts/coordinator_check/build.py" meta 97 64 19 0,0 74,51 30,20 47,1 "$W/haar.e" >/dev/null
case_graph haar "$W/haar.e" 4 full 3

# Level covers with the shift automorphism: both the full source set and the "L,B" source set must agree with apsp.c.
python3 "$HERE/level_graph.py" 8 12 0,1 "$W/lvl8.e" >/dev/null
python3 "$HERE/level_graph.py" 12 30 0,1,4 "$W/lvl12.e" >/dev/null
case_graph lvl8full "$W/lvl8.e" 4 full 3
case_graph lvl8 "$W/lvl8.e" 4 8,12 3
case_graph lvl8k5 "$W/lvl8.e" 4 8,12 5          # K larger than the number of batches: some shards are empty
case_graph lvl12 "$W/lvl12.e" 6 12,30 4
case_graph lvl12full "$W/lvl12.e" 6 full 2

# Negative graphs: odd L (not bipartite), and offsets {0} (disconnected: one cycle per position).
python3 "$HERE/level_graph.py" 9 12 0,1 "$W/odd.e" >/dev/null
python3 "$HERE/level_graph.py" 8 12 0 "$W/disc.e" >/dev/null
shard_all "$W/odd.e" 4 99 3 full 1 odd.full > "$W/out.txt"; out=$(cat "$W/out.txt"); [ "$(verdict "$out")" = INVALID ] && ok "odd L: merge INVALID (not bipartite)" || bad "odd L: expected INVALID"
shard_all "$W/disc.e" 4 99 3 full 1 disc > "$W/out.txt"; [ "$MERGE_RC" -ne 0 ] && ok "disconnected: merge refuses" || bad "disconnected: merge should refuse"
"$W/apsp_shard" shard "$W/lvl8.e" 4 99 1 0 1 8,11 | grep -q 'not an automorphism' && ok "wrong level size 8,11: shard rejects the shift" || bad "wrong level size accepted"

# Merge must refuse bad report sets: a truncated report, a report from another graph, a repeated shard, a short list.
shard_all "$W/lvl8.e" 4 99 3 8,12 1 neg >/dev/null
head -n 3 "$W/neg.1.T1.rep" > "$W/trunc.rep"
"$W/apsp_shard" merge "$W/lvl8.e" 4 99 3 8,12 "$W/neg.0.T1.rep" "$W/trunc.rep" "$W/neg.2.T1.rep" | grep -q REJECT && ok "truncated report refused" || bad "truncated report accepted"
shard_all "$W/haar.e" 4 99 3 full 1 otherg >/dev/null
"$W/apsp_shard" merge "$W/lvl8.e" 4 99 3 8,12 "$W/neg.0.T1.rep" "$W/neg.1.T1.rep" "$W/otherg.2.T1.rep" | grep -q 'another graph' && ok "report from another graph refused" || bad "foreign report accepted"
"$W/apsp_shard" merge "$W/lvl8.e" 4 99 3 8,12 "$W/neg.0.T1.rep" "$W/neg.1.T1.rep" "$W/neg.0.T1.rep" | grep -q 'given twice' && ok "repeated shard refused" || bad "repeated shard accepted"
"$W/apsp_shard" merge "$W/lvl8.e" 4 99 3 8,12 "$W/neg.0.T1.rep" "$W/neg.1.T1.rep" | grep -q 'expected 3' && ok "missing shard refused" || bad "missing shard accepted"
"$W/apsp_shard" merge "$W/lvl8.e" 4 99 3 full "$W/neg.0.T1.rep" "$W/neg.1.T1.rep" "$W/neg.2.T1.rep" | grep -q 'parameters differ' && ok "layout mismatch refused" || bad "layout mismatch accepted"

[ "$fail" -eq 0 ] && echo "ALL PASS" || echo "SOME TESTS FAILED"
exit $fail
