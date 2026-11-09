from copy import deepcopy
def overlay(base, patch):
    if type(base) is not dict or type(patch) is not dict: raise ValueError("objects required")
    out = deepcopy(base)
    for key, value in patch.items():
        out[key] = overlay(base[key], value) if key in base and type(base[key]) is dict and type(value) is dict else deepcopy(value)
    return out
