from copy import deepcopy
def apply(settings,operations):
    if type(settings) is not dict or type(operations) is not list: raise ValueError("invalid transaction")
    out=deepcopy(settings)
    for op in operations:
        if type(op) is not dict or op.get('op') not in ('set','delete'): raise ValueError("bad operation")
        path=op.get('path')
        if type(path) is not list or not path or any(type(x) is not str or not x for x in path): raise ValueError("bad path")
        parent=out
        for part in path[:-1]:
            if type(parent) is not dict or part not in parent: raise ValueError("missing object")
            parent=parent[part]
        if type(parent) is not dict: raise ValueError("not an object")
        if op['op']=='set':
            if 'value' not in op: raise ValueError("missing value")
            parent[path[-1]]=deepcopy(op['value'])
        else:
            if path[-1] not in parent: raise ValueError("missing key")
            del parent[path[-1]]
    return out
