import json,sys
from report import report
print(json.dumps(report(sys.stdin.read())))
