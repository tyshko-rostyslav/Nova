#![allow(unused)]
//! Poseidon Transcript for the TranscriptEngineTrait

use crate::errors::NovaError;
use crate::traits::PrimeFieldExt;
use crate::traits::{Group, TranscriptEngineTrait, TranscriptReprTrait};
use core::marker::PhantomData;
use digest::typenum::Unsigned;
use ff::{Field, PrimeField, PrimeFieldBits};

use generic_array::typenum::U24;
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
pub struct PoseidonTranscript<G: Group> {
  state: Vec<G::Scalar>,
  constants: PoseidonConstants<G::Scalar, U24>,
}
impl<G: Group> TranscriptEngineTrait<G> for PoseidonTranscript<G> {
  fn new(label: &'static [u8]) -> Self {
    let constants: PoseidonConstants<G::Scalar, U24> = Sponge::<G::Scalar, U24>::duplex_constants();
    Self {
      state: Vec::new(),
      constants,
    }
  }
  fn absorb<T: TranscriptReprTrait<G>>(&mut self, label: &'static [u8], o: &T) {
    // NOTE: this is failing since o.to_transcript_bytes() is returning 32 bytes, but
    // G::Scalar::from_uniform() is expecting 64 bytes
    self
      .state
      .push(G::Scalar::from_uniform(&o.to_transcript_bytes()));
  }
  fn squeeze(&mut self, label: &'static [u8]) -> Result<G::Scalar, NovaError> {
    let acc = &mut ();

    let mut sponge = Sponge::new_with_constants(&self.constants, Mode::Duplex);

    SpongeAPI::absorb(&mut sponge, self.state.len() as u32, &self.state, acc);

    let hash = SpongeAPI::squeeze(&mut sponge, 1, acc);

    Ok(hash[0])
  }
  fn dom_sep(&mut self, bytes: &'static [u8]) {
    unimplemented!();
  }
}

// WIP version
/// Implements Poseidon Transcript in Bellperson gadget system
pub struct PoseidonTranscriptCircuit<G: Group> {
  state: Vec<AllocatedNum<G::Scalar>>,
  constants: PoseidonConstants<G::Scalar, U24>,
}

impl<G: Group> PoseidonTranscriptCircuit<G> {
  // note: for the TranscriptCircuit, since there is no trait already defined in Nova's codebase, we can
  // initiate it by passing the PoseidonConstants.
  fn new(constants: PoseidonConstants<G::Scalar, U24>) -> Self {
    Self {
      state: Vec::new(),
      constants,
    }
  }

  fn absorb(&mut self, element: AllocatedNum<G::Scalar>) {
    self.state.push(element);
  }

  fn squeeze<CS>(&mut self, mut cs: CS) -> AllocatedNum<G::Scalar>
  where
    CS: ConstraintSystem<G::Scalar>,
  {
    let mut ns = cs.namespace(|| "ns");
    let acc = &mut ns;

    let mut sponge = SpongeCircuit::new_with_constants(&self.constants, Mode::Duplex);
    let hash = neptune::sponge::api::SpongeAPI::squeeze(&mut sponge, 1, acc);
    // TODO absorb
    let hash =
      Elt::ensure_allocated(&hash[0], &mut ns.namespace(|| "ensure allocated"), true).unwrap();
    hash
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
    let mut transcript: PoseidonTranscript<G> = PoseidonTranscript::new(b"poseidontranscript");
    let mut transcript_gadget: PoseidonTranscriptCircuit<G> =
      PoseidonTranscriptCircuit::new(constants2);

    let mut cs: SatisfyingAssignment<G> = SatisfyingAssignment::new();
    let num_absorbs = 32;
    for i in 0..num_absorbs {
      let num = G::Scalar::random(&mut csprng);
      dbg!(&num);
      transcript.absorb(b"test", &num);
      let allocated_num =
        AllocatedNum::alloc(cs.namespace(|| format!("data {i}")), || Ok(num)).unwrap();
      allocated_num
        .inputize(&mut cs.namespace(|| format!("input {i}")))
        .unwrap();
      transcript_gadget.absorb(allocated_num);
    }
    let num = transcript.squeeze(b"test");
    let num2: AllocatedNum<G::Scalar> = transcript_gadget.squeeze(cs);
    // let num2: AllocatedNum<G::Scalar> =
    //   transcript_gadget.squeeze(&mut cs.namespace(|| format!("squeze")));
    assert_eq!(num.unwrap(), num2.get_value().unwrap());
  }

  #[test]
  fn test_poseidon_ro() {
    test_poseidon_transcript_with::<pasta_curves::pallas::Point>();
    // test_poseidon_ro_with::<bn256::Point>();
  }
}
