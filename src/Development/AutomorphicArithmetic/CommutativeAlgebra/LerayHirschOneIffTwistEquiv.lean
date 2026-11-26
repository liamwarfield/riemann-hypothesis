module

public import Development.AutomorphicArithmetic.BlowupCategories.AffC
public import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedComm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClasses
public import Development.EtaleCohomology.EtaleSheaves.EtStagePf
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.NoetherCharP

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOneIffTwistEquiv
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

namespace UpperTheory.LHOne

variable {q : ℕ} {X : Spc}

private theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'')
    (x : Ht q X n i) : (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4
  rfl

private theorem cup_one' [NeZero q] (hX : Inv q X) {n i : ℤ} (x : Ht q X n i) :
    cup q x (one q X) = x.cast (by ring) (by ring) := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q X x (one q X), (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 X hX x, cast_cast, mul_zero, Int.negOnePow_zero, one_smul]

private theorem bij_iff [NeZero q] {E : Spc} (π : X ⟶ E) (hX : Inv q X) {n i n' i' : ℤ} (hn : n' = n) (hi : i' = i)
    (h1 : n' + 0 = n) (h2 : i' + 0 = i) :
    Function.Bijective (fun a : Fin 1 → Ht q E n' i' =>
        ∑ j, ((cup q (pull _ π _ _ (a j)) (one q X)).cast h1 h2 : Ht q X n i)) ↔
      Function.Bijective (pull _ π (tw q i) n) := by
  subst hn hi
  have key : (fun a : Fin 1 → Ht q E n' i' =>
      ∑ j, ((cup q (pull _ π _ _ (a j)) (one q X)).cast h1 h2 : Ht q X n' i')) =
      (pull _ π (tw q i') n') ∘ (Equiv.funUnique (Fin 1) (Ht q E n' i')) := by
    funext a
    simp only [Fin.sum_univ_one, Function.comp_apply, Equiv.funUnique_apply]
    rw [cup_one' hX, cast_cast]
    rfl
  rw [key, Equiv.bijective_comp]

end UpperTheory.LHOne

theorem UpperTheory.lerayHirsch_one_iff_twist_equiv :
    ∀ (q : ℕ) [NeZero q] {X E : Spc} (π : X ⟶ E), Inv q X →
        (LH q π (fun _ : Fin 1 => (0 : ℤ)) (fun _ : Fin 1 => (0 : ℤ)) (fun _ => one q X) ↔ ∀ i, Eqv _ π (tw q i)) := by
  intro q _ X E π hX
  constructor
  · intro h i n
    exact (UpperTheory.LHOne.bij_iff π hX (sub_zero n) (sub_zero i) _ _).1 (h n i)
  · intro h n i
    exact (UpperTheory.LHOne.bij_iff π hX (sub_zero n) (sub_zero i) _ _).2 (h i n)
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.IntegralClosureFiniteOfFiniteTypeDomain
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem UpperTheory.integralClosure_finite_of_finiteType_domain :
    LateralTheory.E.LeafIntClosureAlgPf.LeafIntClFinite := by
  intro Ω L _ _ _ u _ hfd
  have : Algebra.FiniteType Ω (Algebra.adjoin Ω {u}) :=
    .adjoin_of_finite (Set.finite_singleton u)
  refine GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_of_forall_mvPolynomial
    Ω (Algebra.adjoin Ω {u}) (IntermediateField.adjoin Ω {u}) L ?_
  intro s L' _ _ _ _ _
  obtain ⟨p, hp⟩ := CharP.exists Ω
  rcases CharP.char_is_prime_or_zero Ω p with hpr | rfl
  · haveI : Fact p.Prime := ⟨hpr⟩
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charP Ω p s L'
  · haveI : CharZero Ω := CharP.charP_to_charZero Ω
    exact GroundTheory.Heights₂.Heights.FieldNumbers.finite_integralClosure_mvPolynomial_of_charZero Ω s L'
end
