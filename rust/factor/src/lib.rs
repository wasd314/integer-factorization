pub mod ecm;
pub mod convolution;
pub mod modint;
pub mod fps;
pub mod multipoint_evaluation;
pub mod pollard_rho;
pub mod primality;
pub mod utility;
pub mod wrapper;

pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
