exports.normalize=function(events){
 if(!Array.isArray(events))throw new RangeError('events required');
 const seen=new Map(),out=[];
 for(const e of events){
  if(!e||typeof e.account!=='string'||!e.account||typeof e.id!=='string'||!e.id||!Number.isSafeInteger(e.delta))throw new RangeError('invalid event');
  if(seen.has(e.id)){const old=seen.get(e.id);if(old.account!==e.account||old.delta!==e.delta)throw new RangeError('conflict');continue;}
  const copy={id:e.id,account:e.account,delta:e.delta};seen.set(e.id,copy);out.push(copy);
 }
 return out;
};
