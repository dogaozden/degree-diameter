#!/bin/bash
# (7,5) |H| = 2 screening sweep over the orders 1202..1320 with at most ~60 groups (orders 1204, 1210, 1228, 1244,
# 1252 were swept by the previous job), SECS seconds of annealing per (group, H, K).
SECS=${1:-30}
for o in 1202 1206 1208 1212 1214 1218 1220 1222 1226 1230 1234 1236 1238 1240 1242 1246 1250 1254 1256 1258 1262 1264 1266 1268 1270 1272 1274 1276 1278 1282 1284 1286 1288 1290 1292 1294 1298 1300 1302 1304 1306 1308 1310 1314 1316 1318; do
  ./sweep.sh $o 2 7 $SECS "[1..NrSmallGroups($o)]" 1
  echo "$o done $(date -u +%H:%M)" >> logs/queue75.log
done
