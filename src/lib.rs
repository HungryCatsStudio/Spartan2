//! This library implements Spartan, a high-speed SNARK.
#![deny(
  warnings,
  unused,
  future_incompatible,
  nonstandard_style,
  rust_2018_idioms,
  missing_docs
)]
#![allow(non_snake_case)]
#![allow(clippy::type_complexity)]
#![forbid(unsafe_code)]

// private modules
mod bellpepper;
mod constants;
mod digest;
mod r1cs;

// public modules
pub mod errors;
pub mod provider;
pub mod spartan;
pub mod traits;

use bellpepper_core::Circuit;
use core::marker::PhantomData;
use errors::SpartanError;
use ff::PrimeField;
use serde::{Deserialize, Serialize};
use traits::{
  commitment::{CommitmentEngineTrait, CommitmentTrait},
  snark::RelaxedR1CSSNARKTrait,
  Group,
};

/// A type that holds the prover key
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct ProverKey<G, S>
where
  G: Group,
  S: RelaxedR1CSSNARKTrait<G>,
{
  pk: S::ProverKey,
}

/// A type that holds the verifier key
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct VerifierKey<G, S>
where
  G: Group,
  S: RelaxedR1CSSNARKTrait<G>,
{
  vk: S::VerifierKey,
}

/// A SNARK proving a circuit expressed with bellperson
/// This module provides interfaces to directly prove a step circuit by using Spartan SNARK.
/// In particular, it supports any SNARK that implements RelaxedR1CSSNARK trait
/// (e.g., with the SNARKs implemented in ppsnark.rs or snark.rs).
#[derive(Clone, Serialize, Deserialize)]
#[serde(bound = "")]
pub struct SNARK<G, S, C>
where
  G: Group,
  S: RelaxedR1CSSNARKTrait<G>,
  C: Circuit<G::Scalar>,
{
  snark: S, // snark proving the witness is satisfying
  _p: PhantomData<G>,
  _p2: PhantomData<C>,
}

impl<G: Group, S: RelaxedR1CSSNARKTrait<G>, C: Circuit<G::Scalar>> SNARK<G, S, C> {
  /// Produces prover and verifier keys for the direct SNARK
  pub fn setup(circuit: C) -> Result<(ProverKey<G, S>, VerifierKey<G, S>), SpartanError> {
    let (pk, vk) = S::setup(circuit)?;

    Ok((ProverKey { pk }, VerifierKey { vk }))
  }

  /// Produces a proof of satisfiability of the provided circuit
  pub fn prove(pk: &ProverKey<G, S>, circuit: C) -> Result<Self, SpartanError> {
    // prove the instance using Spartan
    let snark = S::prove(&pk.pk, circuit)?;

    Ok(SNARK {
      snark,
      _p: Default::default(),
      _p2: Default::default(),
    })
  }

  /// Verifies a proof of satisfiability
  pub fn verify(&self, vk: &VerifierKey<G, S>, io: &[G::Scalar]) -> Result<(), SpartanError> {
    // verify the snark using the constructed instance
    self.snark.verify(&vk.vk, io)
  }
}

type CommitmentKey<G> = <<G as traits::Group>::CE as CommitmentEngineTrait<G>>::CommitmentKey;
type Commitment<G> = <<G as Group>::CE as CommitmentEngineTrait<G>>::Commitment;
type CompressedCommitment<G> = <<<G as Group>::CE as CommitmentEngineTrait<G>>::Commitment as CommitmentTrait<G>>::CompressedCommitment;
type CE<G> = <G as Group>::CE;

#[cfg(test)]
mod tests {
  use super::*;
  use crate::provider::{bn256_grumpkin::bn256, secp_secq::secp256k1};
  use bellpepper_core::{
    boolean::AllocatedBit, num::AllocatedNum, ConstraintSystem, LinearCombination, SynthesisError,
  };
  use ff::PrimeFieldBits;

  #[derive(Clone, Debug, Default)]
  struct CubicCircuit {}

  impl<F> Circuit<F> for CubicCircuit
  where
    F: PrimeField,
  {
    fn synthesize<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
      // Consider a cubic equation: `x^3 + x + 5 = y`, where `x` and `y` are respectively the input and output.
      let x = AllocatedNum::alloc(cs.namespace(|| "x"), || Ok(F::ONE + F::ONE))?;
      let x_sq = x.square(cs.namespace(|| "x_sq"))?;
      let x_cu = x_sq.mul(cs.namespace(|| "x_cu"), &x)?;
      let y = AllocatedNum::alloc(cs.namespace(|| "y"), || {
        Ok(x_cu.get_value().unwrap() + x.get_value().unwrap() + F::from(5u64))
      })?;

      cs.enforce(
        || "y = x^3 + x + 5",
        |lc| {
          lc + x_cu.get_variable()
            + x.get_variable()
            + CS::one()
            + CS::one()
            + CS::one()
            + CS::one()
            + CS::one()
        },
        |lc| lc + CS::one(),
        |lc| lc + y.get_variable(),
      );

      let _ = y.inputize(cs.namespace(|| "output"));

      Ok(())
    }
  }

  // Range check: constrains input < `bound`. The bound must fit into
  // `num_bits` bits (this is asserted in the circuit constructor).
  // Important: it must be checked elsewhere that the input fits into
  // `num_bits` bits - this is NOT constrained by this circuit in order to
  // avoid duplications
  #[derive(Clone, Debug)]
  struct UnsignedRangeCircuit {
    bound: u64,
    num_bits: u8,
  }

  impl UnsignedRangeCircuit {
    fn new(bound: u64, num_bits: u8) -> Self {
      assert!(bound < (1 << num_bits));
      Self { bound, num_bits }
    }
  }

  fn num_to_bits_le_bounded<F: PrimeField + PrimeFieldBits, CS: ConstraintSystem<F>>(
    cs: &mut CS,
    n: AllocatedNum<F>,
    num_bits: u8,
  ) -> Result<Vec<AllocatedBit>, SynthesisError> {
    let opt_bits = match n.get_value() {
      Some(v) => v
        .to_le_bits()
        .into_iter()
        .take(num_bits as usize)
        .map(|b| Some(b))
        .collect::<Vec<Option<bool>>>(),
      None => vec![None; num_bits as usize],
    };

    // Add one witness per input bit in little-endian bit order
    let bits_circuit = opt_bits.into_iter()
      .enumerate()
      // AllocateBit enforces the value to be 0 or 1 at the constraint level
      .map(|(i, b)| AllocatedBit::alloc(cs.namespace(|| format!("b_{}", i)), b).unwrap())
      .collect::<Vec<AllocatedBit>>();

    let mut weighted_sum_lc = LinearCombination::zero();
    let mut pow2 = F::ONE;

    for bit in bits_circuit.iter() {
      weighted_sum_lc = weighted_sum_lc + (pow2, bit.get_variable());
      pow2 = pow2.double();
    }

    cs.enforce(
      || "bit decomposition check",
      |lc| lc + &weighted_sum_lc,
      |lc| lc + CS::one(),
      |lc| lc + n.get_variable(),
    );

    // Ok(bits_circuit.into_iter().map(Boolean::from).collect())
    Ok(bits_circuit)
  }

  impl<F: PrimeField + PrimeFieldBits> Circuit<F> for UnsignedRangeCircuit {
    fn synthesize<CS: ConstraintSystem<F>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
      /**** Change here ****/
      let input_value = 9;
      /*********************/

      assert!(F::NUM_BITS > self.num_bits as u32 + 1);

      let input = AllocatedNum::alloc(cs.namespace(|| "input"), || Ok(F::from(input_value)))?;
      let shifted_diff = AllocatedNum::alloc(cs.namespace(|| "shifted_diff"), || {
        Ok(F::from(input_value + (1 << self.num_bits) - self.bound))
      })?;

      cs.enforce(
        || "shifted_diff_computation",
        |lc| lc + input.get_variable() + (F::from((1 << self.num_bits) - self.bound), CS::one()),
        |lc| lc + CS::one(),
        |lc| lc + shifted_diff.get_variable(),
      );

      //let shifted_diff_bits = num_to_bits_le_bounded::<F, CS, {UnsignedRangeCircuit::<B, N>::N_PLUS_1}>(cs, shifted_diff)?;
      let shifted_diff_bits = num_to_bits_le_bounded::<F, CS>(cs, shifted_diff, self.num_bits + 1)?;

      for bit in &shifted_diff_bits {
        print!(
          "{}",
          if let Some(b) = bit.get_value() {
            if b {
              "1"
            } else {
              "0"
            }
          } else {
            "x"
          }
        );
      }

      println!("");

      // Check that the last (i.e. most sifnificant) bit is 0
      cs.enforce(
        || "bound_check",
        |lc| lc + shifted_diff_bits[self.num_bits as usize].get_variable(),
        |lc| lc + CS::one(),
        |lc| lc + (F::ZERO, CS::one()),
      );

      println!(
        "KEY BIT: {}",
        if let Some(b) = shifted_diff_bits[self.num_bits as usize].get_value() {
          if b {
            "1"
          } else {
            "0"
          }
        } else {
          "x"
        }
      );

      /*       // TODO remove
      (11..16).for_each(|i| {
        cs.enforce(|| format!("row_padding_{i}"), |lc| lc, |lc| lc, |lc| lc);
      });

      // TODO remove
      (10..16).for_each(|i| {
        let _ =
          AllocatedNum::alloc(cs.namespace(|| format!("col_padding_{i}")), || Ok(F::ZERO)).unwrap();
      }); */

      // No need to inputize is needed, as V is not meant to learn the output
      // bit: they just know that, if all constraints are satisfied (and the
      // secret input fits into `num_bits` bits), the input is less than
      // `bound`
      Ok(())
    }
  }

  #[test]
  fn test_snark() {
    type G = pasta_curves::pallas::Point;
    type EE = crate::provider::ipa_pc::EvaluationEngine<G>;
    type S = crate::spartan::snark::RelaxedR1CSSNARK<G, EE>;
    type Spp = crate::spartan::ppsnark::RelaxedR1CSSNARK<G, EE>;
    test_snark_with::<G, S>();
    test_snark_with::<G, Spp>();

    type G2 = bn256::Point;
    type EE2 = crate::provider::ipa_pc::EvaluationEngine<G2>;
    type S2 = crate::spartan::snark::RelaxedR1CSSNARK<G2, EE2>;
    type S2pp = crate::spartan::ppsnark::RelaxedR1CSSNARK<G2, EE2>;
    test_snark_with::<G2, S2>();
    test_snark_with::<G2, S2pp>();

    type G3 = secp256k1::Point;
    type EE3 = crate::provider::ipa_pc::EvaluationEngine<G3>;
    type S3 = crate::spartan::snark::RelaxedR1CSSNARK<G3, EE3>;
    type S3pp = crate::spartan::ppsnark::RelaxedR1CSSNARK<G3, EE3>;
    test_snark_with::<G3, S3>();
    test_snark_with::<G3, S3pp>();
  }

  fn test_snark_with<G: Group, S: RelaxedR1CSSNARKTrait<G>>() {
    let circuit = CubicCircuit::default();

    // produce keys
    let (pk, vk) = SNARK::<G, S, CubicCircuit>::setup(circuit.clone()).unwrap();

    // produce a SNARK
    let res = SNARK::prove(&pk, circuit);
    assert!(res.is_ok());
    let snark = res.unwrap();

    // verify the SNARK
    let res = snark.verify(&vk, &[<G as Group>::Scalar::from(15u64)]);
    assert!(res.is_ok());
  }

  #[test]
  fn test_unsigned_range_snark_with() {
    type G = pasta_curves::pallas::Point;
    type EE = crate::provider::ipa_pc::EvaluationEngine<G>;
    type S = crate::spartan::snark::RelaxedR1CSSNARK<G, EE>;

    let circuit = UnsignedRangeCircuit::new(16, 7);

    // produce keys
    let (pk, vk) = SNARK::<G, S, UnsignedRangeCircuit>::setup(circuit.clone()).unwrap();

    // produce a SNARK
    let snark = SNARK::prove(&pk, circuit).unwrap();

    // verify the SNARK
    let _ = snark.verify(&vk, &[]).unwrap();
  }
}
