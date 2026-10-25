#!/bin/sh
# Rebuild and check every table cell below ~150,000 vertices (table-audit). Writes ../checks/{moore_pg_w,moore_h_small,small}.txt.
# Usage: sh rebuild_small.sh WORKDIR      (WORKDIR gets bin/, g/, t/; needs gcc, python3, numpy)
set -e
T=$(cd "$(dirname "$0")" && pwd); P=$(dirname "$T"); R=$(cd "$P/../../.." && pwd); W=${1:-/tmp/table-audit}
mkdir -p "$W/bin" "$W/g" "$W/t"; cd "$W"
gcc -O2 -o bin/moore_build "$T/moore_build.c"
gcc -O2 -o bin/apsp "$R/research/lifts/coordinator_check/apsp.c" 2>/dev/null
gcc -O2 -pthread -o bin/apsp_orb "$R/research/lifts/coordinator_check/apsp_orb.c" 2>/dev/null
export BIN="$W/bin" G="$W/g"
chk() { # name file d D
  printf '%s: ' "$1"; bin/apsp "$2" "$3" "$4" | tr '\n' ' '; echo; }
{
  for q in 2 3 4 5 7 8 9 11 13; do
    bin/moore_build pg $q g/pg_$q.txt g/pg_$q.crd >/dev/null; chk "PG(2,$q) (Delta,D)=($((q+1)),3)" g/pg_$q.txt $((q+1)) 3
    bin/moore_build w $q g/w_$q.txt g/w_$q.crd >/dev/null; chk "W($q) (Delta,D)=($((q+1)),4)" g/w_$q.txt $((q+1)) 4
  done
} > "$P/checks/moore_pg_w.txt"
{
  for q in 2 3 4 5 7 8; do
    bin/moore_build h $q g/h_$q.txt g/h_$q.crd >/dev/null; chk "H($q) (Delta,D)=($((q+1)),6)" g/h_$q.txt $((q+1)) 6
  done
} > "$P/checks/moore_h_small.txt"
{
  python3 "$T/small_builders.py" bye 28 4 12,0,8,20 t/bye56.txt >/dev/null; chk "(3,5)=56 Bar-Yehuda-Etzion" t/bye56.txt 3 5
  chk "(3,5)=56 annealed (graphs/d3D5_n56_anneal.edges.txt)" "$P/graphs/d3D5_n56_anneal.edges.txt" 3 5
  for f in 7.3:7:3 4.5:4:5 4.7:4:7 mdec3.7:3:7; do
    n=${f%%:*}; r=${f#*:}; python3 -I "$T/adjlist2edges.py" "$P/lit/hafner_bipartite/$n" t/hafner_$n.txt >/dev/null
    chk "Hafner file $n" t/hafner_$n.txt ${r%%:*} ${r#*:}
  done
  python3 "$R/research/frontier/build_haar2.py" "$P/graphs/d7D3_n80_meta_5_8_2_x1.sol" t/h80.txt >/dev/null; chk "(7,3)=80 Haar Z5:Z8" t/h80.txt 7 3
  chk "(3,7)=168 Conder C168.1" "$P/graphs/d3D7_n168_conder_C168.1.edges.txt" 3 7
  for A in 4,7,16,27,38,52,62,81 4,16,30,43,51,62,71,89 11,15,21,28,37,40,45,63; do
    python3 "$T/small_builders.py" phi 95 $A t/phi.txt >/dev/null; chk "(11,3)=190 FMP Phi_95($A)" t/phi.txt 11 3
  done
  for q in 9 11 13; do python3 "$T/al_build.py" $q t/al.txt >/dev/null; chk "($((q+2)),3) Araujo-Pardo-Lopez R_$q" t/al.txt $((q+2)) 3; done
  python3 "$T/delorme.py" d3 13 t/d3.txt >/dev/null; chk "(16,3)=394 PG(2,13) + conic/tangent copies" t/d3.txt 16 3
  for q in 5 9 11 13; do python3 "$T/delorme.py" d4 $q 2 t/d4.txt >/dev/null; chk "($((q+2)),4) Delorme 8(a) W($q) doubling" t/d4.txt $((q+2)) 4; done
  python3 "$T/delorme.py" d4 13 3 t/d4.txt >/dev/null; chk "(16,4) Delorme 8(a) W(13) tripling" t/d4.txt 16 4
  python3 "$T/delorme.py" d6 5 2 t/d6.txt >/dev/null; chk "(7,6) Delorme 8(b) H(5) doubling" t/d6.txt 7 6
  for q in 5 7; do python3 "$T/delorme.py" d7 $q t/d7.txt >/dev/null; chk "($((q+1)),7) Delorme Sec. 9 H($q)" t/d7.txt $((q+1)) 7; done
  for s in 10:7:2 11:8:2 12:9:2 13:9:3 14:9:4 15:11:3; do
    d=${s%%:*}; r=${s#*:}; q=${r%%:*}; j=${r#*:}
    python3 "$T/xt_build.py" g/w_$q.txt $j t/x5.txt >/dev/null; chk "($d,5) $((2*j+1)) copies of W($q)" t/x5.txt $d 5
  done
  python3 "$T/xt_build.py" g/h_5.txt 1 t/x7.txt >/dev/null
  printf '(7,7) 3 copies of H(5): '; bin/apsp_orb t/x7.txt 7 7 1 3 7812 | tr '\n' ' '; echo
  for f in "$P"/graphs/*_x1.sol; do
    case $f in *d7D3*) continue;; esac
    b=$(basename $f); d=$(echo $b | sed 's/^d\([0-9]*\)D.*/\1/'); D=$(echo $b | sed 's/^d[0-9]*D\([0-9]*\)_.*/\1/')
    python3 "$R/research/frontier/build_haar2.py" $f t/hs.txt >/dev/null; chk "($d,$D) Haar $b" t/hs.txt $d $D
  done
} > "$P/checks/small.txt"
grep -c "RESULT VALID" "$P/checks/moore_pg_w.txt" "$P/checks/moore_h_small.txt" "$P/checks/small.txt"
