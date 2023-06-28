#![allow(unused)]
use crate::traits::Group;
use bellperson::{
  gadgets::{
    boolean::{AllocatedBit, Boolean},
    num::{AllocatedNum, Num},
    Assignment,
  },
  ConstraintSystem, LinearCombination, SynthesisError,
};
use ff::{Field, PrimeField, PrimeFieldBits};

pub fn verify<Scalar, CS>(
  mut cs: CS,
  claim: AllocatedNum<Scalar>,
  num_rounds: usize,
  degree_bound: usize,
  polys: Vec<Vec<AllocatedNum<Scalar>>>,
  challenges: Vec<AllocatedNum<Scalar>>, // this is while Transcript circuit is not ready
) -> Result<(AllocatedNum<Scalar>, Vec<AllocatedNum<Scalar>>), SynthesisError>
where
  Scalar: PrimeField + PrimeFieldBits,
  CS: ConstraintSystem<Scalar>,
{
  let mut e = claim;
  for (i, poly) in polys.iter().enumerate() {
    // TODO verify poly degree
    if poly.len() != degree_bound {
      panic!("TODO: constraint");
    }

    // eval at zero
    let eval_0 = poly[0].clone();
    // eval at one
    let eval_1 = eval_at_one(cs.namespace(|| format!("sc_eval_at_one {}", i)), poly)?;

    let r_i = challenges[i].clone(); // this is while Transcript circuit is not ready

    e = uni_evaluate(
      cs.namespace(|| format!("sc_unieval {}", i)),
      poly.clone(),
      r_i,
    )?;

    cs.enforce(
      || "s(0)+s(1)=s(r)",
      |lc| lc + eval_0.get_variable() + eval_1.get_variable(),
      |lc| lc,
      |lc| lc + e.get_variable(),
    );
  }

  // note: challenges will be replaced by r vector once the Transcript circuit is ready
  Ok((e, challenges))
}

pub fn eval_at_one<Scalar, CS>(
  mut cs: CS,
  poly: &Vec<AllocatedNum<Scalar>>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
  Scalar: PrimeField + PrimeFieldBits,
  CS: ConstraintSystem<Scalar>,
{
  let mut eval: Num<Scalar> = Num::<Scalar>::from(poly[0].clone());
  for (i, coeff) in poly.iter().enumerate().skip(1) {
    eval = eval.add(&Num::<Scalar>::from(coeff.clone()));
  }
  let allocated_eval: AllocatedNum<Scalar> =
    AllocatedNum::<Scalar>::alloc(&mut cs, || Ok(eval.get_value().unwrap()))?;

  Ok(allocated_eval)
}

// method compatible with src/spartan/sumcheck.rs > UniPoly::evaluate()
pub fn uni_evaluate<Scalar, CS>(
  mut cs: CS,
  coeffs: Vec<AllocatedNum<Scalar>>,
  r: AllocatedNum<Scalar>,
) -> Result<AllocatedNum<Scalar>, SynthesisError>
where
  Scalar: PrimeField + PrimeFieldBits,
  CS: ConstraintSystem<Scalar>,
{
  let mut eval: Num<Scalar> = Num::<Scalar>::from(coeffs[0].clone());
  let mut power = r.clone();
  for (i, coeff) in coeffs.iter().enumerate().skip(1) {
    eval = eval.add(&Num::<Scalar>::from(
      power.mul(cs.namespace(|| format!("mul {}", i)), &coeff)?,
    ));
    power = power.mul(cs.namespace(|| format!("mul2 {}", i)), &r)?;
  }
  let allocated_eval: AllocatedNum<Scalar> =
    AllocatedNum::<Scalar>::alloc(&mut cs, || Ok(eval.get_value().unwrap()))?;

  Ok(allocated_eval)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::bellperson::{
    r1cs::{NovaShape, NovaWitness},
    {shape_cs::ShapeCS, solver::SatisfyingAssignment},
  };
  use crate::spartan::sumcheck::UniPoly;
  use pasta_curves::{
    arithmetic::CurveAffine,
    group::{Curve, Group},
    pallas,
    pallas::Scalar,
    vesta,
  };

  fn synthetize_uni_evaluate<Scalar, CS>(
    mut cs: CS,
    coeffs: Vec<Scalar>,
    r: Scalar,
  ) -> AllocatedNum<Scalar>
  where
    Scalar: PrimeField + PrimeFieldBits,
    CS: ConstraintSystem<Scalar>,
  {
    // prepare inputs
    let r_var = AllocatedNum::<Scalar>::alloc(cs.namespace(|| "alloc r"), || Ok(r)).unwrap();
    let mut coeffs_var: Vec<AllocatedNum<Scalar>> = Vec::new();
    for (i, coeff) in coeffs.iter().enumerate() {
      coeffs_var.push(
        AllocatedNum::<Scalar>::alloc(cs.namespace(|| format!("alloc coeffs {}", i)), || {
          Ok(*coeff)
        })
        .unwrap(),
      );
    }

    // define inputs
    // let _ = r_var.inputize(cs.namespace(|| "Input r"));
    // for (i, coeff) in coeffs_var.iter().enumerate() {
    //   let _ = coeff.inputize(cs.namespace(|| format!("Input coeffs {}", i)));
    // }

    // evaluate in-circuit (synthetize)
    let res = uni_evaluate(cs.namespace(|| "uni_evaluate"), coeffs_var, r_var).unwrap();
    // let _ = res.inputize(cs.namespace(|| "Output res"));

    res
  }

  #[test]
  fn test_uni_evaluate() {
    let evals = vec![
      Scalar::from(1_u64),
      Scalar::from(2_u64),
      Scalar::from(3_u64),
    ];
    let p = UniPoly::<pallas::Point>::from_evals(&evals);
    let r = Scalar::from(5_u64);

    // let's test it against the CS
    let mut cs: ShapeCS<pallas::Point> = ShapeCS::new();
    let _ = synthetize_uni_evaluate(&mut cs, p.coeffs.clone(), r);

    println!("Number of constraints: {}", cs.num_constraints());

    let (shape, ck) = cs.r1cs_shape();

    let mut cs: SatisfyingAssignment<pallas::Point> = SatisfyingAssignment::new();
    let res = synthetize_uni_evaluate(&mut cs, p.coeffs.clone(), r);
    println!("circ res {:?}", res.get_value());
    assert_eq!(res.get_value().unwrap(), p.evaluate(&r));

    let (inst, witness) = cs.r1cs_instance_and_witness(&shape, &ck).unwrap();
    assert!(shape.is_sat(&ck, &inst, &witness).is_ok());
  }

  #[test]
  fn test_sumcheck_verify() {}
}
