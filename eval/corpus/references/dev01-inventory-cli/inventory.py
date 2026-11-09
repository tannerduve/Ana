def summarize(rows):
    if type(rows) is not list: raise ValueError("rows must be a list")
    result = {}
    for r in rows:
        if type(r) is not dict or type(r.get("sku")) is not str or not r["sku"] or type(r.get("quantity")) is not int or type(r.get("unit_cents")) is not int or r["unit_cents"] < 0:
            raise ValueError("invalid row")
        item = result.setdefault(r["sku"], {"sku":r["sku"],"quantity":0,"value_cents":0})
        item["quantity"] += r["quantity"]
        item["value_cents"] += r["quantity"] * r["unit_cents"]
    return [result[k] for k in sorted(result)]
