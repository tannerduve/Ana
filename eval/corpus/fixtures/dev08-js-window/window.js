exports.windowSums=(values,width)=>values.slice(0,Math.max(0,values.length-width)).map((_,i)=>values.slice(i,i+width).reduce((a,b)=>a+b,0));
