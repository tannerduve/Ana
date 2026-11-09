pub fn normalize(text:&str)->Result<String,String>{
 if text.starts_with('/')||text.contains('\\')||text.contains('\0'){return Err("invalid path".into());}
 let mut parts=Vec::new();for part in text.split('/') {match part {""|"."=>{},".."=>{if parts.pop().is_none(){return Err("escape".into());}},other=>parts.push(other)}}
 Ok(if parts.is_empty(){".".into()}else{parts.join("/")})
}
