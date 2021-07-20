extern crate miracl_core;

use miracl_core::rand::{RAND_impl, RAND};
use miracl_core::bls12381::big::BIG;

use functional_encryption_schemes::quadratic_sgp::*;
use num_bigint::BigInt;

fn main() {
    let sgp = Sgp::new(2);
    let mut raw: [u8; 100] = [0; 100];
    let mut rng = RAND_impl::new();
    rng.clean();
    for i in 0..100 {
        raw[i] = i as u8
    }
    rng.seed(100, &raw);

    let (msk, pk) = sgp.generate_sec_key(&mut rng);
     

    let mut x: Vec<BigInt> = Vec::with_capacity(2);
    let mut y: Vec<BigInt> = Vec::with_capacity(2);
    for i in 0..2 {
        x.push(BigInt::from(i));
        y.push(BigInt::from(i+1));
    }

    let cipher = sgp.encrypt(&x, &y, &pk, &mut rng);

    let a: [i64; 4] = [10, 20, 30, 40];
    let f = BigNumMatrix::new_ints(&a[..], 2, 2);
    let dk = sgp.derive_fe_key(&msk, f);

    let result = sgp.decrypt(&cipher, &dk, &BigInt::from(100)); 
    println!("result {:?}", result);

}
