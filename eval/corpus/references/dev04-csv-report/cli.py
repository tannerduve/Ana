import argparse,json,sys
from report import report
parser=argparse.ArgumentParser(); parser.add_argument("--min-total",type=int)
options=parser.parse_args()
try: rows=report(sys.stdin.read())
except ValueError:
    print("invalid CSV",file=sys.stderr); sys.exit(2)
if options.min_total is not None: rows=[r for r in rows if r["total"]>=options.min_total]
print(json.dumps(rows))
