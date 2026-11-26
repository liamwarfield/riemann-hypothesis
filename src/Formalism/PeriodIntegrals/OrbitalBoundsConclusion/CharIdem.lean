module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Scalar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CauchyBinet.WwCauchyBinetMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.RaisingLoweringSplit
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.BlockDiagonalPreservesDegree

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharIdem
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.Central
open CategoryTheory

namespace PI.CharIdemW

open PI.CharIdem

variable {G : Type} [Group G] [Fintype G]

theorem coeff_charIdem (V : FDRep ℂ G) (g : G) :
    (charIdem V).coeff g =
      ((Module.finrank ℂ V : ℂ) / (Fintype.card G : ℂ)) * V.character g⁻¹ := by
  classical
  unfold PI.CharIdem.charIdem
  simp [Finsupp.single_apply]

private theorem charIdem_mul_single_one_comm (V : FDRep ℂ G) (h : G) :
    PI.CharIdem.charIdem V * MonoidAlgebra.single h (1 : ℂ) = MonoidAlgebra.single h (1 : ℂ) * PI.CharIdem.charIdem V := by
  unfold PI.CharIdem.charIdem
  rw [Finset.sum_mul, Finset.mul_sum]
  simp only [MonoidAlgebra.single_mul_single, mul_one, one_mul]
  let e : G ≃ G := ⟨fun g => h⁻¹ * g * h, fun g => h * g * h⁻¹, fun g => by group, fun g => by group⟩
  refine Fintype.sum_equiv e _ _ (fun g => ?_)
  have he : h * e g = g * h := by
    show h * (h⁻¹ * g * h) = g * h
    group
  have hi : (e g)⁻¹ = h⁻¹ * g⁻¹ * h⁻¹⁻¹ := by
    show (h⁻¹ * g * h)⁻¹ = h⁻¹ * g⁻¹ * h⁻¹⁻¹
    group
  rw [he, hi, FDRep.char_conj]

theorem idempotent_mul_comm (V : FDRep ℂ G) (x : MonoidAlgebra ℂ G) :
    charIdem V * x = x * charIdem V := by
  refine MonoidAlgebra.induction_on (motive := fun y => PI.CharIdem.charIdem V * y = y * PI.CharIdem.charIdem V) x ?_ ?_ ?_
  · intro g
    simpa [MonoidAlgebra.of_apply] using charIdem_mul_single_one_comm V g
  · intro a b ha hb
    rw [mul_add, add_mul, ha, hb]
  · intro r a ha
    rw [mul_smul_comm, smul_mul_assoc, ha]

theorem central : Central := by
  intro G _ _ V x
  exact idempotent_mul_comm V x

end PI.CharIdemW
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CharacterIdempotents.CoeffMulCharIdem
open CategoryTheory

namespace PI.CharIdemW

open PI.CharIdem

variable {G : Type} [Group G] [Fintype G]

theorem coeff_mul_charIdem (W : FDRep ℂ G) (x : MonoidAlgebra ℂ G) (h : G) :
    (x * charIdem W).coeff h =
      ((Module.finrank ℂ W : ℂ) / (Fintype.card G : ℂ)) *
        LinearMap.trace ℂ W (W.ρ h⁻¹ * act W x) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    rw [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply, coeff_charIdem, act_single]
    simp only [one_smul, mul_inv_rev, inv_inv, one_mul]
    rw [← map_mul, FDRep.character]
  | add x y hx hy =>
    rw [add_mul, map_add (f := _), mul_add, map_add (f := _), mul_add, ← hx, ← hy]
    rfl
  | smul r x hx =>
    rw [smul_mul_assoc, map_smul, mul_smul_comm, map_smul, smul_eq_mul, mul_left_comm, ← hx]
    rfl

theorem mulEq_of (hS : Scalar) : MulEq := by
  intro G _ _ V W hV hW
  constructor
  · intro hVW
    have h1 : act W (charIdem V) = 1 := ((hS G V W hV hW).1 hVW)
    ext h
    rw [coeff_mul_charIdem, h1, mul_one, coeff_charIdem, FDRep.character]
  · intro hVW
    have h0 : act W (charIdem V) = 0 := ((hS G V W hV hW).2 hVW)
    ext h
    rw [coeff_mul_charIdem, h0, mul_zero, map_zero, mul_zero]
    rfl

end PI.CharIdemW
end

theorem orthogonalCentral : PI.CharIdem.CharIdem :=
  PI.CharIdemW.charIdem_of PI.CharIdemW.central PI.CharIdemW.scalar
    (PI.CharIdemW.mulEq_of PI.CharIdemW.scalar)
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WwCauchyBinet
theorem cauchy_binet_minors : PI.WwCauchyBinet.WwCauchyBinet := PI.WwCauchyBinetWork.wwCauchyBinet_main
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FockRaiseLow
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.GradedOscillatorPropertyOf
namespace FockRL

theorem gradedOscillatorProperty_of (hK : KCStep) (hP : PCStep) (hA : AdjStep) (hM : MatStep) : FockH1Action.H1 := by
  intro p q r s
  obtain ⟨e1, e2, k1, k2, o1, o2, c1, c2, a1, a2⟩ := hM p q r s
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ d P hP'
    rw [e1]; exact hK p q r s _ (k1 Z hZ) d P hP'
  · intro Z hZ d P hP'
    rw [e2]; exact hK p q r s _ (k2 Z hZ) d P hP'
  · intro Z hZ P
    rw [e1]; exact hP p q r s _ (o1 Z hZ) P
  · intro Z hZ P
    rw [e2]; exact hP p q r s _ (o2 Z hZ) P
  · intro Z hZ P Q
    rw [e1, e1]; exact hA p q r s _ _ (o1 Z hZ) (o1 _ (c1 Z hZ)) (a1 Z) P Q
  · intro Z hZ P Q
    rw [e2, e2]; exact hA p q r s _ _ (o2 Z hZ) (o2 _ (c2 Z hZ)) (a2 Z) P Q

end FockRL
end

theorem gradedOscillatorProperty : FockH1Action.H1 :=
  FockRL.gradedOscillatorProperty_of FockRL.blockDiagonalPreservesDegree
    (FockRL.pcStep_of FockRaiseLowGrade.raisingLoweringSplit)
    (FockRL.adjStep_of FockRaiseLowGrade.raisingLoweringSplit FockRaiseLowInner.fischerConjLinearLeft
      FockRaiseLowInner.fischerLinearRight FockRaiseLowInner.fischerXAdjoint)
    FockRL.kroneckerProperties
end
