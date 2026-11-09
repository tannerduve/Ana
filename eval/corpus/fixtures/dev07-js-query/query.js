exports.parseQuery = function(text) {
 const out={}; for(const part of text.replace(/^\?/,'').split('&')) {if(part){const [k,v='']=part.split('=');out[k]=[v];}} return out;
};
