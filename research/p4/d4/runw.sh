#!/bin/bash
PY=/private/tmp/claude-501/-Users-dogaozden-AI-Projects-degree-diameter/d6bfe58f-ec9f-4fe8-a39d-9588c6bb9afc/scratchpad/venv/bin/python
while read -r line; do [ -z "$line" ] && continue; $PY cp_w.py $line; done
