exports.windowSums=function(values,width){
 if(!Number.isInteger(width)||width<=0||!Array.isArray(values)||!values.every(v=>typeof v==='number'&&Number.isFinite(v))) throw new RangeError('invalid input');
 if(width>values.length)return [];
 const out=[];let sum=0;
 for(let i=0;i<values.length;i++){sum+=values[i];if(i>=width)sum-=values[i-width];if(i>=width-1)out.push(sum);}
 return out;
};
