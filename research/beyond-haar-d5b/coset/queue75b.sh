#!/bin/bash
# (7,5) |H| = 2 annealing sweep upward from 1220 (orders with at most ~60 groups), 5 CPU-seconds per (group, H, K)
cd "$(dirname "$0")"
for o in 1220 1222 1226 1228 1230 1234 1236 1238 1240 1242 1244 1246 1250 1252 1254 1256 1258 1262 1264 1266 1268 1270 1272 1274 1276 1278 1282 1284 1286 1288 1290 1292 1294 1298 1300 1302 1304 1306 1308 1310 1314; do
  ./sweep.sh $o 2 7 5 "[1..NrSmallGroups($o)]" 1; echo "$o (7,5) done $(date -u +%H:%M)" >> logs/queue75b.log
done
