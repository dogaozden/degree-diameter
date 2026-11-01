#!/bin/bash
# map spec lines to tables/ names: spaces and * to underscores
sed -e 's/ /_/g' -e 's/\*/x/g' "$1"
