#!/bin/bash
# usage: run_meta.sh jobs.txt seconds seed out.log
while read -r spec; do
  timeout $(( $2 + 60 )) nice -n 5 python3 controller.py search "$spec" $2 $3 >> $4 2>&1
done < $1
