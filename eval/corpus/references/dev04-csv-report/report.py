import csv,io,re
def report(text):
    try: rows=list(csv.reader(io.StringIO(text),strict=True))
    except csv.Error as error: raise ValueError("bad CSV") from error
    if not rows or len(rows[0]) != 2 or set(rows[0]) != {"category","amount"}: raise ValueError("bad header")
    cat=rows[0].index("category"); amt=rows[0].index("amount"); result={}
    for row in rows[1:]:
        if not row: continue
        if len(row)!=2 or not row[cat] or not re.fullmatch(r"[+-]?[0-9]+",row[amt]): raise ValueError("bad row")
        item=result.setdefault(row[cat], {"category":row[cat],"total":0,"count":0})
        item["total"]+=int(row[amt]); item["count"]+=1
    return [result[k] for k in sorted(result)]
