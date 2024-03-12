//! Support for generating R1CS using bellperson.

#![allow(non_snake_case)]

use super::{shape_cs::ShapeCS, solver::SatisfyingAssignment, test_shape_cs::TestShapeCS};
use crate::{
  errors::SpartanError,
  r1cs::{R1CSInstance, R1CSShape, R1CSWitness, R1CS},
  traits::Group,
  CommitmentKey,
};
use bellpepper_core::{Index, LinearCombination};
use ff::PrimeField;

/// `SpartanWitness` provide a method for acquiring an `R1CSInstance` and `R1CSWitness` from implementers.
pub trait SpartanWitness<G: Group> {
  /// Return an instance and witness, given a shape and ck.
  fn r1cs_instance_and_witness(
    &self,
    shape: &R1CSShape<G>,
    ck: &CommitmentKey<G>,
  ) -> Result<(R1CSInstance<G>, R1CSWitness<G>), SpartanError>;
}

/// `SpartanShape` provides methods for acquiring `R1CSShape` and `CommitmentKey` from implementers.
pub trait SpartanShape<G: Group> {
  /// Return an appropriate `R1CSShape` and `CommitmentKey` structs.
  fn r1cs_shape(&self) -> (R1CSShape<G>, CommitmentKey<G>);
}

impl<G: Group> SpartanWitness<G> for SatisfyingAssignment<G>
where
  G::Scalar: PrimeField,
{
  fn r1cs_instance_and_witness(
    &self,
    shape: &R1CSShape<G>,
    ck: &CommitmentKey<G>,
  ) -> Result<(R1CSInstance<G>, R1CSWitness<G>), SpartanError> {
    // TODO remove
    println!("Getting here 1");
    println!("shape.num_vars: {:?}", shape.num_vars);
    println!("Aux_assignment: {:?}", self.aux_assignment.len());

    let W = R1CSWitness::<G>::new(shape, &self.aux_assignment)?;
    
    // TODO remove
    println!("Getting here 2");
    
    let X = &self.input_assignment[1..];

    let comm_W = W.commit(ck);

    // TODO remove
    println!("Getting here 3");

    let instance = R1CSInstance::<G>::new(shape, &comm_W, X)?;

    // TODO remove
    println!("Getting here 4");

    Ok((instance, W))
  }
}

macro_rules! impl_spartan_shape {
  ( $name:ident) => {
    impl<G: Group> SpartanShape<G> for $name<G>
    where
      G::Scalar: PrimeField,
    {
      fn r1cs_shape(&self) -> (R1CSShape<G>, CommitmentKey<G>) {
        let mut A: Vec<(usize, usize, G::Scalar)> = Vec::new();
        let mut B: Vec<(usize, usize, G::Scalar)> = Vec::new();
        let mut C: Vec<(usize, usize, G::Scalar)> = Vec::new();

        let mut num_cons_added = 0;
        let mut X = (&mut A, &mut B, &mut C, &mut num_cons_added);

        let num_inputs = self.num_inputs();
        let num_constraints = self.num_constraints();
        let num_vars = self.num_aux();

        for constraint in self.constraints.iter() {
          add_constraint(
            &mut X,
            num_vars,
            &constraint.0,
            &constraint.1,
            &constraint.2,
          );
        }

        assert_eq!(num_cons_added, num_constraints);

        let S: R1CSShape<G> = {
          // Don't count One as an input for shape's purposes.
          let res = R1CSShape::new(num_constraints, num_vars, num_inputs - 1, &A, &B, &C);
          res.unwrap()
        }
        .pad();

        let ck = R1CS::<G>::commitment_key(&S);

        (S, ck)
      }
    }
  };
}

impl_spartan_shape!(ShapeCS);
impl_spartan_shape!(TestShapeCS);

fn add_constraint<S: PrimeField>(
  X: &mut (
    &mut Vec<(usize, usize, S)>,
    &mut Vec<(usize, usize, S)>,
    &mut Vec<(usize, usize, S)>,
    &mut usize,
  ),
  num_vars: usize,
  a_lc: &LinearCombination<S>,
  b_lc: &LinearCombination<S>,
  c_lc: &LinearCombination<S>,
) {
  let (A, B, C, nn) = X;
  let n = **nn;
  let one = S::ONE;

  let add_constraint_component = |index: Index, coeff, V: &mut Vec<_>| {
    match index {
      Index::Input(idx) => {
        // Inputs come last, with input 0, reprsenting 'one',
        // at position num_vars within the witness vector.
        let i = idx + num_vars;
        V.push((n, i, one * coeff))
      }
      Index::Aux(idx) => V.push((n, idx, one * coeff)),
    }
  };

  for (index, coeff) in a_lc.iter() {
    add_constraint_component(index.0, coeff, A);
  }
  for (index, coeff) in b_lc.iter() {
    add_constraint_component(index.0, coeff, B)
  }
  for (index, coeff) in c_lc.iter() {
    add_constraint_component(index.0, coeff, C)
  }

  **nn += 1;
}
