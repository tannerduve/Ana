import json, sys
from inventory import summarize
print(json.dumps(summarize(json.load(sys.stdin))))
