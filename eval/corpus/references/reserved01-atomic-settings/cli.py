import json,sys
from transactions import apply
try:
    j=json.load(sys.stdin);result=apply(j['settings'],j['operations'])
except (ValueError,KeyError,TypeError):
    print('invalid transaction',file=sys.stderr);sys.exit(2)
print(json.dumps(result))
