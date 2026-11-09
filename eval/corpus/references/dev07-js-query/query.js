exports.parseQuery = function(text) {
 const out={}; const decode=s=>decodeURIComponent(s.replace(/\+/g,' '));
 for(const part of text.replace(/^\?/,'').split('&')) {
  if(!part) continue;
  const at=part.indexOf('='); const key=decode(at<0?part:part.slice(0,at)); const value=decode(at<0?'':part.slice(at+1));
  if(!Object.hasOwn(out,key)) Object.defineProperty(out,key,{value:[],enumerable:true,writable:true,configurable:true});
  out[key].push(value);
 }
 return out;
};
