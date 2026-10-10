"""Stand-in for the `claude` CLI, used by tests. Prints stream-json lines.

Mode comes from the env var FAKE_CLAUDE_MODE:
  apikey       init event reports apiKeySource=ANTHROPIC_API_KEY
  limit90      adds a rate_limit_event at 95% utilization
  usage_limit  result is an error: "You've hit your limit"
  transient    first call (tracked by $FAKE_CLAUDE_COUNTER) is a 529 error, then normal
  (unset)      normal successful reply
"""
import json
import os
import sys


def emit(event):
    print(json.dumps(event), flush=True)


def main():
    sys.stdin.read()
    mode = os.environ.get("FAKE_CLAUDE_MODE", "")
    emit({"type": "system", "subtype": "init",
          "apiKeySource": "ANTHROPIC_API_KEY" if mode == "apikey" else "none"})
    if mode == "limit90":
        emit({"type": "rate_limit_event",
              "rate_limit_info": {"unifiedWindows": {"five_hour": {"utilization": 0.95}}}})
    if mode == "usage_limit":
        emit({"type": "result", "is_error": True, "result": "You've hit your limit"})
        return
    if mode == "transient":
        counter = os.environ["FAKE_CLAUDE_COUNTER"]
        if not os.path.exists(counter):
            with open(counter, "w") as f:
                f.write("1")
            emit({"type": "result", "is_error": True, "api_error_status": 529,
                  "result": "Overloaded"})
            return
    emit({"type": "result", "is_error": False,
          "result": "Here:\n```python\ndef build(d, D, seed, time_limit):\n    return 1, []\n```",
          "usage": {"input_tokens": 10, "output_tokens": 5}, "total_cost_usd": 0.001,
          "duration_api_ms": 50, "modelUsage": {"claude-haiku-5-5": {"outputTokens": 5}},
          "session_id": "s"})


if __name__ == "__main__":
    main()
