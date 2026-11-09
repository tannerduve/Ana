pub fn decode(text: &str) -> Result<String,String> {
 let input=text.as_bytes();let mut out=Vec::new();let mut i=0;
 while i<input.len(){match input[i]{b'+' => out.push(b' '),b'%' => {
  if i+2>=input.len(){return Err("incomplete escape".into());}
  let hi=(input[i+1] as char).to_digit(16).ok_or("invalid escape")?;
  let lo=(input[i+2] as char).to_digit(16).ok_or("invalid escape")?;
  out.push((hi*16+lo) as u8);i+=2;
 },value=>out.push(value)};i+=1;}
 String::from_utf8(out).map_err(|_| "invalid UTF-8".into())
}
