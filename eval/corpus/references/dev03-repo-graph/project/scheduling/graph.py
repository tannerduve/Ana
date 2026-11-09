def plan(graph):
    remaining = {k:set(v) for k,v in graph.items()}
    for value in graph.values():
        for name in value: remaining.setdefault(name,set())
    order=[]
    while remaining:
        ready=sorted(k for k,v in remaining.items() if not v)
        if not ready: raise ValueError("cycle")
        name=ready[0]; order.append(name); del remaining[name]
        for deps in remaining.values(): deps.discard(name)
    return order
