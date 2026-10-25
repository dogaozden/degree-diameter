#!/bin/bash
# record.sh OUT_PREFIX "FDSET" NAME: file a verified FLAGDEL graph: OUT_PREFIX.sol (dmhub2_f output, H=3 numbering) ->
# ../hubs/graphs/NAME.sol (+ FDSET line), NAME.edges.gz (independent rebuild by build_fd.py), apsp to ../hubs/checks/NAME_apsp.txt
set -e
O=$1; FS=$2; NAME=$3; G=../hubs/graphs; C=../hubs/checks
cp "$O.sol" "$G/$NAME.sol"; echo "fdset $FS" >> "$G/$NAME.sol"
python3 build_fd.py gq/gq_q7.bin "$G/$NAME.sol" "$FS" "/tmp/claude-0/$NAME.edges"
./apsp "/tmp/claude-0/$NAME.edges" 10 5 | tee "$C/${NAME}_apsp.txt" | tail -n 2
./apsp "/tmp/claude-0/$NAME.edges" 10 4 | tail -n 1 | sed 's/^/D=4: /' >> "$C/${NAME}_apsp.txt"
sha256sum "/tmp/claude-0/$NAME.edges" | awk '{print $1}' > "$C/${NAME}_sha256.txt"
gzip -c "/tmp/claude-0/$NAME.edges" > "$G/$NAME.edges.gz"
cat "$C/${NAME}_sha256.txt"; tail -n 1 "$C/${NAME}_apsp.txt"
