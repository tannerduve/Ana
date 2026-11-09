exports.report=function(events){
 const rows=new Map();
 for(const e of events){const r=rows.get(e.account)||{account:e.account,balance:0,events:0};r.balance+=e.delta;r.events++;if(!Number.isSafeInteger(r.balance))throw new RangeError('overflow');rows.set(e.account,r);}
 return [...rows.values()].filter(r=>r.balance!==0).sort((a,b)=>a.account<b.account?-1:a.account>b.account?1:0);
};
