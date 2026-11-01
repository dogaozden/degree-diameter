#!/bin/bash
# topN.sh SCREEN.tsv K : print the K best groups (by 1.5 s cost, ties by ab) as "N m k r ab cost" lines
sort -t$'\t' -k6,6n -k5,5n "$1" | awk -F'\t' '$6!="NA"' | head -n "$2" | awk -F'\t' '{print $1, $2, $3, $4, $5, $6}'
