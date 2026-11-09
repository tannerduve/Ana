import json, sys
from inventory import summarize
try: result = summarize(json.load(sys.stdin))
except (ValueError, TypeError, KeyError):
    print("invalid inventory", file=sys.stderr)
    sys.exit(2)
print(json.dumps(result))
