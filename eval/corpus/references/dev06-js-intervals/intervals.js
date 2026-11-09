exports.mergeIntervals = function(intervals) {
  if (!Array.isArray(intervals)) throw new RangeError('intervals required');
  const rows=intervals.map(row=>{
    if (!Array.isArray(row)||row.length!==2||!row.every(Number.isSafeInteger)||row[0]>row[1]) throw new RangeError('invalid interval');
    return row.slice();
  }).filter(([a,b])=>a!==b).sort((a,b)=>a[0]-b[0]||a[1]-b[1]);
  const out=[];
  for (const row of rows) {
    if (out.length && row[0]<=out[out.length-1][1]) out[out.length-1][1]=Math.max(out[out.length-1][1],row[1]);
    else out.push(row);
  }
  return out;
};
