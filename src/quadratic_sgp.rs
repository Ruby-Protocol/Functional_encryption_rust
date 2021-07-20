use crate::rand_chacha::rand_core::{RngCore, SeedableRng};
use lazy_static::lazy_static;
use miracl_core::bls12381::big;
use miracl_core::bls12381::big::BIG;
use miracl_core::bls12381::dbig::DBIG;
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
pub type DBigNum = DBIG;
pub type G1 = ECP;
pub type G2 = ECP2;
pub type GT = FP12;

pub const MB: usize = big::MODBYTES as usize;

pub type G1Vector = Vec<G1>;
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
pub struct BigIntMatrix {
    data: Vec<BigInt>,
    n_rows: usize,
    n_cols: usize
}

impl BigIntMatrix {
    pub fn new(n_rows: usize, n_cols: usize) -> Self {
        Self {
            data: vec![BigInt::from(0); n_rows * n_cols],
            n_rows,
            n_cols,
        }
    }

    pub fn new_ints(a: &[i64], n_rows: usize, n_cols: usize) -> Self {
        let mut data: Vec<BigInt> = Vec::with_capacity(n_rows * n_cols);
        for i in 0..n_rows {
            for j in 0..n_cols {
                data[i * n_cols + j] = BigInt::from(a[i * n_cols + j]);
            }
        }
        Self {
            data,
            n_rows,
            n_cols,
        }
    }

    pub fn get_element(&self, i: usize, j: usize) -> &BigInt {
        &self.data[i * self.n_cols + j]
    }

}


#[derive(Debug)]
pub struct BigNumMatrix {
    data: Vec<BigNum>,
    n_rows: usize,
    n_cols: usize
}

impl BigNumMatrix {
    pub fn new(n_rows: usize, n_cols: usize) -> Self {
        Self {
            data: vec![BigNum::new(); n_rows * n_cols],
            n_rows,
            n_cols,
        }
    }

    pub fn new_ints(a: &[i64], n_rows: usize, n_cols: usize) -> Self {
        let mut data: Vec<BigNum> = Vec::with_capacity(n_rows * n_cols);
        for i in 0..n_rows {
            for j in 0..n_cols {
                data.push(BigNum::new_int(a[i * n_cols + j].try_into().unwrap()));
            }
        }
        Self {
            data,
            n_rows,
            n_cols,
        }
    }

    pub fn get_element(&self, i: usize, j: usize) -> &BigNum {
        &self.data[i * self.n_cols + j]
    }

}


#[derive(Debug)]
pub struct BigNumMatrix2x2 {
    data: Vec<BigNum>,
}

impl BigNumMatrix2x2 {
    pub fn new() -> Self {
        Self {
            data: vec![BigNum::new(); 2 * 2],
        }
    }

    pub fn new_with_data(data: &[BigNum]) -> Self {
        Self {
            data: data.to_vec(),
        }
    }

    pub fn new_random(modulus: &BigNum, rng: &mut impl RAND) -> Self {
        Self {
            data: uniform_sample_vec(2 * 2, modulus, rng),
        }
    }

    pub fn get_element(&self, i: usize, j: usize) -> &BigNum {
        &self.data[i * 2 + j]
    }

    pub fn determinant(&self) -> DBigNum {
        let a: &BigNum = self.get_element(0, 0);
        let b: &BigNum = self.get_element(0, 1);
        let c: &BigNum = self.get_element(1, 0);
        let d: &BigNum = self.get_element(1, 1);
        let mut ad = BigNum::mul(a, d);
        let bc = BigNum::mul(b, c);
        ad.sub(&bc);
        ad
    }

    pub fn invmod(&self, modulus: &BigNum) -> Self {
        let mut det: DBigNum = self.determinant();
        let mut det: BigNum = det.dmod(modulus);
        if det.iszilch() {
            panic!("Matrix determinant is zero");
        }
        det.invmodp(modulus); 
        let det_inv = det;
        let e00 = BigNum::modmul(self.get_element(1, 1), &det_inv, modulus);
        let e01 = BigNum::modmul(&(BigNum::modneg(self.get_element(0, 1), modulus)), &det_inv, modulus);
        let e10 = BigNum::modmul(&(BigNum::modneg(self.get_element(1, 0), modulus)), &det_inv, modulus);
        let e11 = BigNum::modmul(self.get_element(0, 0), &det_inv, modulus);
        Self {
            data: vec![e00, e01, e10, e11],
        }
    }

    pub fn transpose(&mut self) {
        self.data.swap(1, 2); 
    }
}


#[derive(Debug)]
pub struct Sgp {
    n: usize,
}

#[derive(Debug)]
pub struct SgpSecKey {
    s: Vec<BigNum>, 
    t: Vec<BigNum>,
}

#[derive(Debug)]
pub struct SgpPubKey {
    g1s: G1Vector,
    g2t: G2Vector,
}

#[derive(Debug)]
pub struct SgpCipher {
    g1MulGamma: G1,
    a: G1Vector,
    b: G2Vector,
    n: usize,
}

#[derive(Debug)]
pub struct SgpDecKey {
    key: G2,
    f: BigNumMatrix,
}

lazy_static! {
    pub static ref CURVE_ORDER: BigNum = BigNum::new_ints(&rom::CURVE_ORDER);
}

impl Sgp {
    pub fn new(n: usize) -> Sgp {
        Sgp {
            n
        }
    }

    pub fn generate_sec_key(&self, rng: &mut impl RAND) -> (SgpSecKey, SgpPubKey) {
        let msk = SgpSecKey {
            s: uniform_sample_vec(self.n, &(CURVE_ORDER), rng),
            t: uniform_sample_vec(self.n, &(CURVE_ORDER), rng),
        };
        let mut pk = SgpPubKey {
            g1s: vec![G1::generator(); self.n],
            g2t: vec![G2::generator(); self.n],
        };
        println!("pk.g1s len: {}", pk.g1s.len());
        println!("msk.s len: {}", msk.s.len());
        for i in 0..self.n {
            pk.g1s[i] = pk.g1s[i].mul(&(msk.s[i]));
            pk.g2t[i] = pk.g2t[i].mul(&(msk.t[i]));
        }
        (msk, pk)
    }

    pub fn encrypt(&self, x: &[BigInt], y: &[BigInt], pk: &SgpPubKey, rng: &mut impl RAND) -> SgpCipher {
        if x.len() != self.n ||  y.len() != self.n {
            panic!("Malformed input: x.len ({}), y.len ({}), expected len ({})", x.len(), y.len(), self.n);
        }

        let W = BigNumMatrix2x2::new_random(&(CURVE_ORDER), rng);
        let mut W_inv = W.invmod(&(CURVE_ORDER));
        W_inv.transpose();

        let gamma = uniform_sample(&(CURVE_ORDER), rng);
        let mut g1MulGamma = G1::generator();
        g1MulGamma = g1MulGamma.mul(&gamma);

        let mut a: G1Vector = vec![G1::generator(); self.n * 2];
        let mut b: G2Vector = vec![G2::generator(); self.n * 2];

        for i in 0..self.n {
            let xi = BigNum::fromstring(x[i].to_str_radix(16));
            let yi = BigNum::fromstring(y[i].to_str_radix(16));

            let w00_mul_xi = BigNum::modmul(W_inv.get_element(0, 0), &xi, &CURVE_ORDER);
            let w01_mul_gamma = BigNum::modmul(W_inv.get_element(0, 1), &gamma, &CURVE_ORDER);
            let w10_mul_xi = BigNum::modmul(W_inv.get_element(1, 0), &xi, &CURVE_ORDER);
            let w11_mul_gamma = BigNum::modmul(W_inv.get_element(1, 1), &gamma, &CURVE_ORDER);

            a[i*2] = a[i*2].mul(&w00_mul_xi);
            a[i*2].add(&(pk.g1s[i].mul(&w01_mul_gamma)));

            a[i*2+1] = a[i*2+1].mul(&w10_mul_xi);
            a[i*2+1].add(&(pk.g1s[i].mul(&w11_mul_gamma)));


            let w00_mul_yi = BigNum::modmul(W.get_element(0, 0), &yi, &CURVE_ORDER);
            let w01_neg = BigNum::modneg(W.get_element(0, 1), &CURVE_ORDER);
            let w10_mul_yi = BigNum::modmul(W.get_element(1, 0), &yi, &CURVE_ORDER);
            let w11_neg = BigNum::modneg(W.get_element(1, 1), &CURVE_ORDER);

            b[i*2] = b[i*2].mul(&w00_mul_yi);
            b[i*2].add(&(pk.g2t[i].mul(&w01_neg)));

            b[i*2+1] = b[i*2+1].mul(&w10_mul_yi);
            b[i*2+1].add(&(pk.g2t[i].mul(&w11_neg)));
        }
        SgpCipher {
            g1MulGamma,
            a,
            b,
            n: self.n
        }
    }

    pub fn derive_fe_key(&self, msk: &SgpSecKey, f: BigNumMatrix) -> SgpDecKey {
        let mut exp = BigNum::new();
        for i in 0..msk.s.len() {
            for j in 0..msk.t.len() {
                let fij = f.get_element(i, j);

                let si_tj = BigNum::modmul(&(msk.s[i]), &(msk.t[j]), &CURVE_ORDER);
                let fij_si_tj = BigNum::modmul(&fij, &si_tj, &CURVE_ORDER);
                exp.add(&fij_si_tj);
            }
        }
        SgpDecKey {
            key: (G2::generator()).mul(&exp),
            f: f 
        }
    }

    pub fn decrypt(&self, ct: &SgpCipher, dk: &SgpDecKey, bound: &BigInt) -> Option<BigInt> {
        if ct.a.len() != dk.f.n_rows * 2 || ct.b.len() != dk.f.n_cols * 2 {
            panic!("Malformed input: a.len ({}), b.len ({}), f dimension ({} x {}).", ct.a.len() / 2, ct.b.len() / 2, dk.f.n_rows, dk.f.n_cols);
        }

        let mut out: GT = pair::ate(&dk.key, &ct.g1MulGamma);
        out = pair::fexp(&out);
        let (mut proj0, mut proj1): (GT, GT);
        for i in 0..dk.f.n_rows {
            for j in 0..dk.f.n_cols {
                //for k in 0..2 {
                    //proj[k] = pair::ate(&ct.b[j*2 + k], &ct.a[i*2 + k]);
                    //proj[k] = pair::fexp(&proj[k]);
                //}
                proj0 = pair::ate(&ct.b[j*2], &ct.a[i*2]);
                proj0 = pair::fexp(&proj0);
                proj1 = pair::ate(&ct.b[j*2 + 1], &ct.a[i*2 + 1]);
                proj1 = pair::fexp(&proj1);
                
                proj0.mul(&proj1);
                proj0 = proj0.pow(dk.f.get_element(i, j));
                out.mul(&proj0);
            }
        }
        println!("after loop");

        let g1 = G1::generator();
        let g2 = G2::generator();
        let pair = pair::ate(&g2, &g1);
        let pair = pair::fexp(&pair);

        //dlog
        let mut result_bound = BigNum::fromstring(bound.to_str_radix(16));
        result_bound = result_bound.powmod(&BigNum::new_int(3), &CURVE_ORDER);
        result_bound = BigNum::modmul(&result_bound, &BigNum::new_int((dk.f.n_rows * dk.f.n_cols) as isize), &CURVE_ORDER);

        println!("before bsgs");

        baby_step_giant_step(&out, &pair, &result_bound)
    }
}

fn uniform_sample(modulus: &BigNum, rng: &mut impl RAND) -> BigNum {
    BigNum::randomnum(modulus, rng)
}

fn uniform_sample_vec(len: usize, modulus: &BigNum, rng: &mut impl RAND) -> Vec<BigNum> {
    let mut v: Vec<BigNum> = Vec::with_capacity(len);
    for i in 0..len {
        v.push(uniform_sample(modulus, rng));
    }
    v 
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
