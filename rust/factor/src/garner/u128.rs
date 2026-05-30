use crate::modint::u128::{DynamicModInt, StaticModInt};

pub struct Garner3 {
    mo: DynamicModInt,
    m1: u128,
    m2: u128,
}

// M1 < M2 < M3
pub const M1: u128 = 7 << 120 | 1;
pub const M2: u128 = 51 << 119 | 1;
pub const M3: u128 = 71 << 119 | 1;
pub type Mint1 = StaticModInt<M1>;
pub type Mint2 = StaticModInt<M2>;
pub type Mint3 = StaticModInt<M3>;

const M1_INV_M2: Mint2 = match Mint2::new_const(M1).inv_const() {
    Ok(e) => e,
    Err(_) => panic!(),
};
const M1M2_INV_M3: Mint3 = match Mint3::new_const(M1)
    .mul_const(Mint3::new_const(M2))
    .inv_const()
{
    Ok(e) => e,
    Err(_) => panic!(),
};

impl Garner3 {
    pub const fn new(mo: DynamicModInt) -> Self {
        Self {
            mo,
            m1: mo.mr_const(M1),
            m2: mo.mr_const(M2),
        }
    }

    /// min x s.t. x mod Mi = ci に対する x mod m.
    ///
    /// 入力は Montgomery 表現ではない．
    /// 出力は Montgomery 表現である．
    pub fn reconstruct(&self, c1: u128, c2: u128, c3: u128) -> u128 {
        let x1 = c1;
        let x2 = ((Mint2::new(c2) - Mint2::new(x1)) * M1_INV_M2).val();
        let x3 = ((Mint3::new(c3) - Mint3::new(x1) - Mint3::new(x2) * Mint3::new(M1))
            * M1M2_INV_M3)
            .val();
        let Self { mo, m1, m2 } = self;
        let (x1, x2, x3) = (mo.mr(x1), mo.mr(x2), mo.mr(x3));
        mo.add(mo.add(x1, mo.mul(*m1, x2)), mo.mul(*m1, mo.mul(*m2, x3)))
    }

    pub fn reconstruct_vector(&self, c1: Vec<u128>, c2: Vec<u128>, c3: Vec<u128>) -> Vec<u128> {
        c1.into_iter()
            .zip(c2)
            .zip(c3)
            .map(|((c1, c2), c3)| self.reconstruct(c1, c2, c3))
            .collect()
    }
}
