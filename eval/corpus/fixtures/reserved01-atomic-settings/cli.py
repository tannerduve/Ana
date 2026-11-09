import json,sys
from transactions import apply
j=json.load(sys.stdin);print(json.dumps(apply(j['settings'],j['operations'])))
