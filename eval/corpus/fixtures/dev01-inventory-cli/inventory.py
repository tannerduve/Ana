def summarize(rows):
    return [{"sku":r["sku"],"quantity":r["quantity"],"value_cents":r["unit_cents"]} for r in rows]
