#!/usr/bin/env python3
"""How much has this Claude Code session spent? A budget meter for experiments (stdlib only).

  python3 tools/session_usage.py [--since ISO8601] [--log research/squads/usage/<arm>.jsonl --arm NAME]

Reads the Claude Code transcripts on this machine (~/.claude/projects/**/*.jsonl, which includes subagents' transcripts),
keeps assistant messages newer than --since (default: the start of the oldest transcript touched in the last 24 h),
deduplicates them by message id, and sums tokens by model family. It prints one JSON line:
  {"budget_units": .., "by_model": {"opus": {...}, "haiku": {...}}, ...}
budget_units is a price-weighted token count in "Opus output M-token equivalents": each token is weighted by its list
price relative to Opus output (cache reads 0.1x input, cache writes 1.25x input). It is a way to compare arms of an
experiment on one scale. It is NOT a measurement of the subscription allowance.
"""
import argparse, glob, json, os, time, datetime as dt

# list prices per million tokens (input, output); only the ratios matter
PRICE = {'opus': (4.0, 20.0), 'sonnet': (2.0, 10.0), 'haiku': (0.10, 0.50), 'fable': (10.0, 50.0)}
REF = PRICE['opus'][1]


def family(model):
    m = (model or '').lower()
    return next((f for f in PRICE if f in m), None)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--since'); ap.add_argument('--log'); ap.add_argument('--arm', default='')
    ap.add_argument('--root', default=os.path.expanduser('~/.claude/projects'))
    a = ap.parse_args()
    files = glob.glob(os.path.join(a.root, '**', '*.jsonl'), recursive=True)
    if a.since:
        since = dt.datetime.fromisoformat(a.since.replace('Z', '+00:00')).timestamp()
    else:
        recent = [os.path.getmtime(f) for f in files if time.time() - os.path.getmtime(f) < 86400]
        since = 0.0 if not recent else min(os.stat(f).st_birthtime if hasattr(os.stat(f), 'st_birthtime') else os.path.getctime(f)
                                            for f in files if time.time() - os.path.getmtime(f) < 86400)
    seen, tot = set(), {}
    for f in files:
        if os.path.getmtime(f) < since:
            continue
        with open(f, errors='replace') as fh:
            for line in fh:
                if '"usage"' not in line:
                    continue
                try:
                    m = json.loads(line)
                except ValueError:
                    continue
                msg = m.get('message') or {}
                u, fam = msg.get('usage'), family(msg.get('model'))
                if not u or not fam:
                    continue
                ts = m.get('timestamp')
                if ts and dt.datetime.fromisoformat(ts.replace('Z', '+00:00')).timestamp() < since:
                    continue
                key = msg.get('id') or (f, m.get('uuid'))
                if key in seen:
                    continue
                seen.add(key)
                t = tot.setdefault(fam, {'input': 0, 'output': 0, 'cache_read': 0, 'cache_write': 0, 'messages': 0})
                t['input'] += u.get('input_tokens', 0) or 0
                t['output'] += u.get('output_tokens', 0) or 0
                t['cache_read'] += u.get('cache_read_input_tokens', 0) or 0
                t['cache_write'] += u.get('cache_creation_input_tokens', 0) or 0
                t['messages'] += 1
    units = 0.0
    for fam, t in tot.items():
        pin, pout = PRICE[fam]
        cost = (t['input'] * pin + t['cache_write'] * pin * 1.25 + t['cache_read'] * pin * 0.1 + t['output'] * pout) / 1e6
        t['units'] = round(cost / REF, 4)
        units += cost / REF
    out = {'at': dt.datetime.now(dt.timezone.utc).isoformat(timespec='seconds'), 'arm': a.arm,
           'since': dt.datetime.fromtimestamp(since, dt.timezone.utc).isoformat(timespec='seconds'),
           'budget_units': round(units, 4), 'by_model': tot}
    print(json.dumps(out))
    if a.log:
        os.makedirs(os.path.dirname(a.log), exist_ok=True)
        with open(a.log, 'a') as fh:
            fh.write(json.dumps(out) + '\n')


if __name__ == '__main__':
    main()
