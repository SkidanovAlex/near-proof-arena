// Lossless transport only. The native verifier must still check reconstructed bytes.
fn decode_digest_dictionary(input:&[u8])->Result<Vec<u8>,String> {
    fn take<'a>(input:&mut &'a [u8],n:usize)->Result<&'a [u8],String> {
        if n>input.len(){return Err("truncated dictionary stream".into());}
        let (a,b)=input.split_at(n);*input=b;Ok(a)
    }
    fn u32le(input:&mut &[u8])->Result<usize,String> {
        Ok(u32::from_le_bytes(take(input,4)?.try_into().unwrap()) as usize)
    }
    let mut input=input;
    if take(&mut input,8)?!=b"NPDICT01" {return Err("dictionary version".into());}
    let size=u32le(&mut input)?;
    if size>16*1024*1024 {return Err("decoded size limit".into());}
    let count=u32le(&mut input)?;
    if count>65536 {return Err("dictionary index width".into());}
    let dictionary=take(&mut input,count*48)?;
    let mut output=Vec::with_capacity(size);
    while !input.is_empty() {
        let tag=take(&mut input,1)?[0];
        let bytes=match tag {
            0=> {let n=u32le(&mut input)?; if n==0 {return Err("empty literal".into());} take(&mut input,n)?},
            1=> {let index=u16::from_le_bytes(take(&mut input,2)?.try_into().unwrap()) as usize;
                if index>=count {return Err("dictionary index".into());}
                &dictionary[index*48..(index+1)*48]},
            _=>return Err("dictionary tag".into()),
        };
        if bytes.len()>size-output.len() {return Err("decoded length overflow".into());}
        output.extend_from_slice(bytes);
    }
    if output.len()!=size {return Err("decoded length mismatch".into());}
    Ok(output)
}
