use crate::rand_chacha::rand_core::{RngCore, SeedableRng};
use lazy_static::lazy_static;
use miracl_core::bls12381::big;
use miracl_core::bls12381::big::BIG;
use miracl_core::bls12381::ecp;
use miracl_core::bls12381::ecp::ECP;
use miracl_core::bls12381::ecp2::ECP2;
use miracl_core::bls12381::fp12::FP12;
use miracl_core::bls12381::pair;
use miracl_core::bls12381::rom;
/* use  miracl_core::bn254::big;
use miracl_core::bn254::big::BIG;
use miracl_core::bn254::ecp;
use miracl_core::bn254::ecp::ECP;
use miracl_core::bn254::ecp2::ECP2;
use miracl_core::bn254::fp12::FP12;
use miracl_core::bn254::pair;
use miracl_core::bn254::rom; */
use miracl_core::hash256::HASH256;
use miracl_core::rand::RAND;
use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use num_traits::Num;
//use rand::prelude::*;
use rand_chacha::ChaCha20Rng;
use std::collections::HashMap;
use std::convert::TryInto;

pub type BigNum = BIG;
pub type G1 = ECP;
pub type G2 = ECP2;
pub type GT = FP12;

pub const MB: usize = big::MODBYTES as usize;

pub type G2Vector = Vec<G2>;

#[derive(Debug)]
struct BigIntMatrix2x2 {
    data: Vec<BigInt>,
}

impl BigIntMatrix2x2 {
    pub fn new() -> Self {
        Self {
            data: vec![BigInt::from(0); 2 * 2],
        }
    }

    pub fn new_random_deterministic(seed: &[u8; 32]) -> Self {
        let mut rand_bytes: [u8; 32] = [0; 32];
        let mut rng = ChaCha20Rng::from_seed(*seed);
        rng.fill_bytes(&mut rand_bytes);
        let mut temp = BigIntMatrix2x2::new();
        for i in 0..2 {
            for j in 0..2 {
                //temp.data[i*2+j] = BigInt::from_bytes_be(Sign::Plus, &rand_bytes);
                //temp.data[i*2+j] = BigInt::from_signed_bytes_be(&rand_bytes);
                temp.data[i * 2 + j] = BigInt::from(1); //FIXME
            }
        }
        temp
    }

    pub fn get_element(&self, i: usize, j: usize) -> &BigInt {
        &self.data[i * 2 + j]
    }

    pub fn add(&mut self, rhs: &BigIntMatrix2x2) {
        for i in 0..2 {
            for j in 0..2 {
                self.data[i * 2 + j] += &rhs.data[i * 2 + j];
            }
        }
    }

    pub fn sub(&mut self, rhs: &BigIntMatrix2x2) {
        for i in 0..2 {
            for j in 0..2 {
                self.data[i * 2 + j] -= &rhs.data[i * 2 + j];
            }
        }
    }

    pub fn modp(&mut self, p: &BigInt) {
        for i in 0..2 {
            for j in 0..2 {
                self.data[i * 2 + j] = self.data[i * 2 + j].mod_floor(p);
            }
        }
    }
}

#[derive(Debug)]
pub struct Dmcfe {
    index: usize,
    pub client_pub_key: G1,
    client_sec_key: BigNum,
    share: BigIntMatrix2x2,
    s: [BigNum; 2],
}

lazy_static! {
    pub static ref CURVE_ORDER: BigNum = BigNum::new_ints(&rom::CURVE_ORDER);
}

impl Dmcfe {
    pub fn new(rng: &mut impl RAND, index: usize) -> Dmcfe {
        let client_sec_key = BigNum::randtrunc(&(CURVE_ORDER), 16 * ecp::AESKEY, rng);

        let client_pub_key = G1::generator();
        client_pub_key.mul(&client_sec_key);

        let share = BigIntMatrix2x2::new();
        let s = [
            BigNum::randtrunc(&(CURVE_ORDER), 16 * ecp::AESKEY, rng),
            BigNum::randtrunc(&(CURVE_ORDER), 16 * ecp::AESKEY, rng),
        ];

        Dmcfe {
            index,
            client_pub_key,
            client_sec_key,
            share,
            s,
        }
    }

    pub fn set_share(&mut self, pub_keys: &[G1]) {
        let mut shared_g1: G1 = G1::new();
        let mut t: [u8; MB + 1] = [0; MB + 1];
        let p =
            BigInt::from_str_radix(&BigNum::new_ints(&rom::CURVE_ORDER).tostring(), 16).unwrap();

        for i in 0..pub_keys.len() {
            if i == self.index {
                continue;
            }

            shared_g1.copy(&pub_keys[i]);
            shared_g1 = shared_g1.mul(&self.client_sec_key);
            shared_g1.tobytes(&mut t, true);

            let mut hash256 = HASH256::new();
            hash256.process_array(&t);
            let digest = hash256.hash();

            let mut add = BigIntMatrix2x2::new_random_deterministic(&digest);
            add.modp(&p);

            if i < self.index {
                self.share.add(&add);
            } else {
                self.share.sub(&add);
            }
            self.share.modp(&p);
        }
    }

    pub fn encrypt(&self, x: &BigInt, label: &str) -> G1 {
        let x = BigNum::fromstring(x.to_str_radix(16));
        let mut cipher: G1 = G1::new();
        cipher.inf();

        for i in 0..2 {
            let ex_label = format!("{} {}", i.to_string(), label);
            let mut h = hash_to_g1(&ex_label);
            h = h.mul(&self.s[i]);
            cipher.add(&h);
        }
        let mut g = G1::generator();
        g = g.mul(&x);
        cipher.add(&g);

        cipher
    }

    pub fn derive_fe_key_share(&self, y: &[BigInt]) -> G2Vector {
        let mut fe_key_share: G2Vector = vec![G2::new(); 2];
        let mut hs: G2Vector = vec![G2::new(); 2];
        let mut y_str = "".to_string();
        for yi in y.iter() {
            y_str = y_str + " " + &yi.to_str_radix(16);
        }

        for i in 0..2 {
            let ex_label = format!("{} {}", i.to_string(), y_str);
            hs[i] = hash_to_g2(&ex_label);
        }

        let mut h = G2::generator();
        for i in 0..2 {
            fe_key_share[i].inf();
            for j in 0..2 {
                h.copy(&hs[j]);
                let share_i = BigNum::fromstring(self.share.get_element(i, j).to_str_radix(16));
                let temp = h.mul(&share_i);
                fe_key_share[i].add(&temp);
            }

            let temp = BigNum::fromstring(y[self.index].to_str_radix(16));
            let temp = BigNum::modmul(&temp, &self.s[i], &CURVE_ORDER);
            h = G2::generator();
            h = h.mul(&temp);
            fe_key_share[i].add(&h);
        }
        fe_key_share
    }

    pub fn decrypt(
        ciphers: &[G1],
        y: &[BigInt],
        key_shares: &[G2Vector],
        label: &str,
        bound: &BigInt,
    ) -> Option<BigInt> {
        let mut keys_sum: G2Vector = vec![G2::new(); 2];
        let ylen: isize = y.len().try_into().unwrap();

        for i in 0..2 {
            keys_sum[i].inf();
        }

        for i in 0..y.len() {
            for j in 0..2 {
                keys_sum[j].add(&key_shares[i][j]);
            }
        }

        let (g1, mut ciphers_sum, mut cipher_i) = (G1::generator(), G1::new(), G1::new());
        let g2 = G2::generator();

        ciphers_sum.inf();

        for i in 0..y.len() {
            let mut temp = BigNum::fromstring(y[i].to_str_radix(16));
            cipher_i.copy(&ciphers[i]);
            temp.rmod(&CURVE_ORDER);
            cipher_i = cipher_i.mul(&temp);
            ciphers_sum.add(&cipher_i);
        }

        let mut s = pair::ate(&g2, &ciphers_sum);
        s = pair::fexp(&s);

        let mut t = GT::new();
        let mut pair: GT;
        t.one();
        for i in 0..2 {
            let ex_label = format!("{} {}", i.to_string(), label);
            let h = hash_to_g1(&ex_label);
            pair = pair::ate(&keys_sum[i], &h);
            pair = pair::fexp(&pair);
            t.mul(&pair);
        }
        t.inverse();
        s.mul(&t);

        pair = pair::ate(&g2, &g1);
        pair = pair::fexp(&pair);

        //dlog
        let mut result_bound = BigNum::fromstring(bound.to_str_radix(16));
        result_bound = result_bound.powmod(&BigNum::new_int(2), &CURVE_ORDER);
        result_bound = BigNum::modmul(&result_bound, &BigNum::new_int(ylen), &CURVE_ORDER);

        baby_step_giant_step(&s, &pair, &result_bound)
    }
}

fn hash_to_g1(data: &str) -> G1 {
    let mut hash256 = HASH256::new();
    hash256.process_array(data.as_bytes());
    let digest = hash256.hash();
    G1::mapit(&digest)
}

fn hash_to_g2(data: &str) -> G2 {
    let mut hash256 = HASH256::new();
    hash256.process_array(data.as_bytes());
    let digest = hash256.hash();
    G2::mapit(&digest)
}

use std::ops::Add;
fn baby_step_giant_step(h: &GT, g: &GT, bound: &BigNum) -> Option<BigInt> {
    let mut table = HashMap::new();
    let mut pow_zero = GT::new();
    pow_zero.one();
    if pow_zero.equals(&h) {
        return Some(BigInt::from(0));
    }

    let b = BigInt::from_str_radix(&bound.tostring(), 16).unwrap();
    let b_sqrt = b.sqrt();
    let temp: BigInt = b_sqrt.add(1);
    let m = BigNum::fromstring(temp.to_str_radix(16));

    // precompute the table
    let (mut x, mut z) = (GT::new(), GT::new_copy(&g));
    let mut i = BigNum::new_int(0);
    x.one();
    x.reduce();
    while BigNum::comp(&i, &m) <= 0 {
        table.insert(x.tostring(), i);
        x.mul(&g);
        x.reduce();
        i.inc(1);
    }

    // search for solution
    z.inverse();
    z = z.pow(&m);
    x = GT::new_copy(&h);
    let mut x_neg = GT::new_copy(&h);
    x_neg.inverse();
    i.zero();
    while BigNum::comp(&i, &m) <= 0 {
        // positive solution
        match table.get(&x.tostring()) {
            Some(value) => {
                let mut temp = BigNum::modmul(&i, &m, &CURVE_ORDER);
                temp = BigNum::modadd(&value, &temp, &CURVE_ORDER);
                let temp = BigInt::from_str_radix(&temp.tostring(), 16).unwrap();
                return Some(temp);
            }
            None => {
                x.mul(&z);
                x.reduce();
            }
        }
        // negative solution
        match table.get(&x_neg.tostring()) {
            Some(value) => {
                let mut temp = BigNum::modmul(&i, &m, &CURVE_ORDER);
                temp = BigNum::modadd(&value, &temp, &CURVE_ORDER);
                temp = BigNum::modneg(&temp, &CURVE_ORDER);
                let temp = BigInt::from_str_radix(&temp.tostring(), 16).unwrap();
                return Some(temp);
            }
            None => {
                x_neg.mul(&z);
                x_neg.reduce();
            }
        }
        i.inc(1);
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_baby_step_giant_step() {
        let g1 = G1::generator();
        let g2 = G2::generator();

        let mut g = pair::ate(&g2, &g1);
        g = pair::fexp(&g);

        let bound = BigNum::new_int(10024);
        let x = BigNum::new_int(1335);

        let h = g.pow(&x);
        if let Some(res) = baby_step_giant_step(&h, &g, &bound) {
            println!("res={}", res);
        }
        println!("g={}", g.tostring());
        println!("x={}", x.tostring());
    }

    #[test]
    fn test_bigint_bignum_conversion() {
        let a = BigNum::new_int(25500);
        println!("{:?} => {}", a, a.tostring());
        let a = BigInt::from_str_radix(&a.tostring(), 16);
        let aa = BigInt::from(25500);
        println!("{:?} => {:?}", a, aa);

        let b = BigInt::from(15500);
        println!("{:?} => {}", b, b.to_str_radix(16));
        let b = BigNum::fromstring(b.to_str_radix(16));
        let bb = BigNum::new_int(15500);
        println!("{:?} => {:?}", b, bb);
    }

}
