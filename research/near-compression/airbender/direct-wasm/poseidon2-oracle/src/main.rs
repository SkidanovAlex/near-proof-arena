use std::io::{self, BufRead};
use p3_baby_bear::{BabyBear, default_babybear_poseidon2_32};
use p3_field::PrimeField32;
use p3_symmetric::Permutation;

fn main() {
    let permutation = default_babybear_poseidon2_32();
    for line in io::stdin().lock().lines() {
        let values: Vec<u32> = line.unwrap().split_whitespace()
            .map(|x| x.parse().unwrap()).collect();
        assert_eq!(values.len(), 32);
        assert!(values.iter().all(|&x| x < 2013265921));
        let mut state = BabyBear::new_array(values.try_into().unwrap());
        permutation.permute_mut(&mut state);
        println!("{}", state.iter().map(|x| x.as_canonical_u32().to_string())
            .collect::<Vec<_>>().join(" "));
    }
}
