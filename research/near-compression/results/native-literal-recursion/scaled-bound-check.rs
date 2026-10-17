struct LinearConstraint {coefficients:Vec<u32>,threshold:u32}
impl LinearConstraint {
    /// Returns true if `self` is logically implied by `other`, i.e.,
    /// whenever `other` is satisfied, `self` is also satisfied.
    pub fn is_implied_by(&self, other: &LinearConstraint) -> bool {
        if self.coefficients.len() != other.coefficients.len() {
            return false;
        }
        // For nonnegative heights h: self.dot(h) <= scale * other.dot(h).
        // Positive scale preserves the strict bound; u32 products fit in u64.
        let mut scale = 1u64;
        for (&a, &b) in self.coefficients.iter().zip(&other.coefficients) {
            if b == 0 {
                if a != 0 { return false; }
            } else {
                scale = scale.max(u64::from(a).div_ceil(u64::from(b)));
            }
        }
        scale * u64::from(other.threshold) <= u64::from(self.threshold)
    }
}

fn main() {
 let mut checked=0u64;
 for a in 0..4 { for b in 0..4 { for c in 0..4 { for d in 0..4 {
 for t in 0..7 { for u in 0..7 {
  let x=LinearConstraint{coefficients:vec![a,b],threshold:t};
  let y=LinearConstraint{coefficients:vec![c,d],threshold:u};
  if x.is_implied_by(&y) {
   for h in 0..6 {for k in 0..6 {
    if c*h+d*k<u {assert!(a*h+b*k<t);}
    checked+=1;
   }}
  }
 }}}}}}
 let x=LinearConstraint{coefficients:vec![1,511],threshold:2013265921};
 assert!(x.is_implied_by(&LinearConstraint{coefficients:vec![198,2],threshold:1<<20}));
 assert!(!x.is_implied_by(&LinearConstraint{coefficients:vec![198,2],threshold:1<<30}));
 assert!(!x.is_implied_by(&LinearConstraint{coefficients:vec![198],threshold:1<<20}));
 let large=LinearConstraint{coefficients:vec![u32::MAX],threshold:u32::MAX};
 assert!(large.is_implied_by(&large));
 assert!(!large.is_implied_by(&LinearConstraint{coefficients:vec![1],threshold:u32::MAX}));
 println!("{}",checked);
}
