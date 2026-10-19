#!/usr/bin/env bash
# Autopilot stop switch. Prints STOP and exits 0 when the branch `autopilot-stop` exists on origin; exits 1 otherwise.
# Anyone can create that branch on GitHub (also from a phone) to stop all autopilot work; delete it to allow work again.
if git ls-remote --exit-code --heads origin autopilot-stop >/dev/null 2>&1; then echo STOP; exit 0; fi
exit 1
