import re
def compare(left,right):
    def parse(x):
        if type(x) is not str or not re.fullmatch(r"[0-9]+(?:\.[0-9]+)*",x): raise ValueError("invalid version")
        return [int(p) for p in x.split(".")]
    a,b=parse(left),parse(right)
    n=max(len(a),len(b));a += [0]*(n-len(a));b += [0]*(n-len(b))
    return (a>b)-(a<b)
