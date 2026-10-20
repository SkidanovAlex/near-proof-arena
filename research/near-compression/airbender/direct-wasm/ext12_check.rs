use p3_baby_bear::BabyBear as F;
use p3_field::{extension::BinomialExtensionField, BasedVectorSpace, Field, PrimeCharacteristicRing, PrimeField32, TwoAdicField};
type E = BinomialExtensionField<F,12>;
fn read(v:&serde_json::Value)->E {
    E::new(std::array::from_fn(|i|F::from_u32(v[i].as_u64().unwrap().try_into().unwrap())))
}
fn pow(mut x:E, mut n:u64)->E {
    let mut out=E::ONE;
    while n>0 {if n&1==1 {out*=x;} x=x.square();n>>=1;}
    out
}
fn main() {
    let path=std::env::args().nth(1).unwrap();
    let c:serde_json::Value=serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
    assert_eq!(E::GENERATOR,read(&c["generator"]));
    assert_eq!(E::TWO_ADICITY,29);
    for bits in 0..=29 {
        let root=E::two_adic_generator(bits);
        assert_eq!(pow(root,1u64<<bits),E::ONE);
        if bits>0 {assert_ne!(pow(root,1u64<<(bits-1)),E::ONE);
            assert_eq!(root.square(),E::two_adic_generator(bits-1));}
    }
    assert_eq!(E::ZERO.try_inverse(),None);
    for v in c["vectors"].as_array().unwrap() {
        let a=read(&v["a"]);let b=read(&v["b"]);
        assert_eq!(a*b,read(&v["product"]));
        assert_eq!(a.inverse(),read(&v["inverse"]));
        assert_eq!(a*a.inverse(),E::ONE);
        assert_eq!(pow(a,2013265921),read(&v["frobenius"]));
        assert_eq!(a.square(),a*a);
        assert_eq!((a+b)-b,a);
        // Canonical coefficient serialization, used by the native proof codec.
        let bytes:Vec<u8>=a.as_basis_coefficients_slice().iter()
            .flat_map(|x: &F|x.as_canonical_u32().to_le_bytes()).collect();
        assert_eq!(bytes.len(),48);
        let back=E::new(std::array::from_fn(|i|F::from_u32(u32::from_le_bytes(bytes[4*i..4*i+4].try_into().unwrap()))));
        assert_eq!(a,back);
    }
    println!("EXT12_PASS vectors={} roots=30 zero_inverse_rejected=true canonical_bytes=48",c["vectors"].as_array().unwrap().len());
}
