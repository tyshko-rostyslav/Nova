#![allow(unused)]
//! Poseidon Transcript for the TranscriptEngineTrait

use crate::errors::NovaError;
use crate::traits::PrimeFieldExt;
use crate::traits::{Group, TranscriptEngineTrait, TranscriptReprTrait};
use core::marker::PhantomData;
use digest::typenum::Unsigned;
use ff::{Field, PrimeField, PrimeFieldBits};

use generic_array::{sequence::GenericSequence, typenum::U24, GenericArray};
use neptune::{
  circuit2::Elt,
  poseidon::{Poseidon, PoseidonConstants},
  sponge::{
    api::{IOPattern, SpongeAPI, SpongeOp},
    circuit::SpongeCircuit,
    vanilla::{Direction, Mode, Sponge, SpongeTrait},
  },
  Strength,
};
use std::collections::VecDeque;

use bellperson::{
  gadgets::{
    boolean::{AllocatedBit, Boolean},
    num::AllocatedNum,
  },
  ConstraintSystem, SynthesisError,
};

// WARNING: all this is WIP. Current version is just to have something to use in SumCheck & Spartan
// that fullfills Nova's TranscriptEngineTrait with Poseidon.
/// Implements the Poseidon Transcript.
pub struct PoseidonTranscript<'a, G: Group> {
  sponge: Sponge<'a, G::Scalar, U24>,
}
impl<'a, G: Group> PoseidonTranscript<'a, G> {
  // impl<'a, G: Group> TranscriptEngineTrait<G> for PoseidonTranscript<'a, G> {

  // NOTE: to fullfill the TranscriptEngineTrait, the 'new' method should not have the 'constants'
  // parameter as input.
  fn new(label: &'static [u8], constants: &'a PoseidonConstants<G::Scalar, U24>) -> Self {
    let mut sponge: Sponge<'_, G::Scalar, U24> =
      Sponge::<G::Scalar, U24>::new_with_constants(&constants, Mode::Duplex);
    Self { sponge }
  }
  fn squeeze(&mut self, label: &'static [u8]) -> Result<G::Scalar, NovaError> {
    let acc = &mut ();
    let hash = SpongeAPI::squeeze(&mut self.sponge, 1, acc);
    Ok(hash[0])
  }
  fn absorb<T: TranscriptReprTrait<G>>(&mut self, label: &'static [u8], o: &T) {
    let mut elements: Vec<G::Scalar> = Vec::with_capacity(1);
    // NOTE: this is failing since o.to_transcript_bytes() is returning 32 bytes, but
    // G::Scalar::from_uniform() is expecting 64 bytes
    elements.push(G::Scalar::from_uniform(&o.to_transcript_bytes()));
    let acc = &mut ();
    SpongeAPI::absorb(&mut self.sponge, elements.len() as u32, &elements, acc);
  }
  fn dom_sep(&mut self, bytes: &'static [u8]) {
    unimplemented!();
  }
}

/// Implements Poseidon Transcript in Bellperson gadget system
pub struct PoseidonTranscriptCircuit<'a, G: Group, CS: ConstraintSystem<G::Scalar>> {
  sponge: SpongeCircuit<'a, G::Scalar, U24, CS>,
}
impl<'a, G: Group, CS: 'a + ConstraintSystem<G::Scalar, Root = CS>>
  PoseidonTranscriptCircuit<'a, G, CS>
{
  // for the TranscriptCircuit, since there is no trait already defined in Nova's codebase, we can
  // initiate it by passing the PoseidonConstants.
  fn new(constants: &'a PoseidonConstants<G::Scalar, U24>) -> Self {
    let sponge = SpongeCircuit::new_with_constants(&constants, Mode::Duplex);
    Self { sponge }
  }
  fn squeeze(&mut self, mut cs: &'a mut CS) -> AllocatedNum<G::Scalar> {
    let mut ns = cs.namespace(|| "ns");
    let hash = SpongeAPI::squeeze(&mut self.sponge, 1, &mut ns);
    // let hash = self.sponge.squeeze();
    let hash =
      Elt::ensure_allocated(&hash[0], &mut ns.namespace(|| "ensure allocated"), true).unwrap();
    hash
  }

  fn absorb(&mut self, mut cs: &'a mut CS, element: AllocatedNum<G::Scalar>) {
    let mut ns = cs.namespace(|| "ns");

    let mut allocated_elements = Vec::with_capacity(1);
    allocated_elements.push(Elt::Allocated(element));

    neptune::sponge::api::SpongeAPI::absorb(
      &mut self.sponge,
      32,
      allocated_elements.as_slice(),
      &mut ns,
    );
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::provider::bn256_grumpkin::bn256;
  use crate::{
    bellperson::solver::SatisfyingAssignment, constants::NUM_CHALLENGE_BITS,
    gadgets::utils::le_bits_to_num, traits::Group,
  };
  use ff::Field;
  use rand::rngs::OsRng;

  /*
  // NOTE: this test follows the test from `src/provider/poseidon.rs` but using
  // `PoseidonTranscript` instead of `PoseidonRO`
  fn test_poseidon_transcript_with<G: Group>()
  where
    // we can print the field elements we get from G's Base & Scalar fields,
    // and compare their byte representations
    <<G as Group>::Base as PrimeField>::Repr: std::fmt::Debug,
    <<G as Group>::Scalar as PrimeField>::Repr: std::fmt::Debug,
    <<G as Group>::Base as PrimeField>::Repr: PartialEq<<<G as Group>::Scalar as PrimeField>::Repr>,
  {
    // Check that the value computed inside the circuit is equal to the value computed outside the circuit
    let mut csprng: OsRng = OsRng;
    let constants: PoseidonConstants<G::Scalar, U24> = Sponge::<G::Scalar, U24>::duplex_constants();
    let constants2: PoseidonConstants<G::Scalar, U24> =
      Sponge::<G::Scalar, U24>::duplex_constants();
    let num_absorbs = 32;
    let mut transcript: PoseidonTranscript<'_, G> =
      PoseidonTranscript::new(b"poseidontranscript", &constants2);
    let mut transcript_gadget: PoseidonTranscriptCircuit<'_, G, SatisfyingAssignment<G>> =
      PoseidonTranscriptCircuit::new(&constants2);

    let mut cs: SatisfyingAssignment<G> = SatisfyingAssignment::new();
    for i in 0..num_absorbs {
      let num = G::Scalar::random(&mut csprng);
      transcript.absorb(b"test", &num);
      let allocated_num =
        AllocatedNum::alloc(cs.namespace(|| format!("data {i}")), || Ok(num)).unwrap();
      allocated_num
        .inputize(&mut cs.namespace(|| format!("input {i}")))
        .unwrap();
      transcript_gadget.absorb(&mut cs, allocated_num);
    }
    let num = transcript.squeeze(b"test");
    let num2: AllocatedNum<G::Scalar> = transcript_gadget.squeeze(&mut cs);
    assert_eq!(num.unwrap(), num2.get_value().unwrap());
  }

  #[test]
  fn test_poseidon_ro() {
    test_poseidon_transcript_with::<pasta_curves::pallas::Point>();
    // test_poseidon_ro_with::<bn256::Point>();
  }
  */
}
