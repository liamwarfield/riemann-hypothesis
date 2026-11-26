module

public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.FixedBaseSurjectivity.GaloisPeriodCyclotomic
public import Development.WeilBound.RepresentationTheoryGL.PeriodRingBases.BaseThetaVanishing.BaseThZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.CoeUntiltIterateLFlat

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TiltedDrinfeld.TieQB
noncomputable section

namespace period_ring_base.DualB

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime]

theorem qB_eq (q : ℚ_[l]) : PositivityTheory.LocInh.qB l q = period_ring_base.qB l q :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (S := ℚ_[l])
    (j := PositivityTheory.LocInh.qB l) (k := period_ring_base.qB l)
    (RingHom.ext fun z => by
      simp only [RingHom.comp_apply]
      rw [show (algebraMap ℤ_[l] ℚ_[l] z) = (z : ℚ_[l]) from rfl, PositivityTheory.LocInh.qB_coe]
      exact (IsLocalization.lift_eq (M := nonZeroDivisors ℤ_[l]) (isUnit_zB l) z).symm)) q

variable {P : LocPrime l} {AI : LocAinf l P} (T : LocTied6 l P AI)

theorem tie_qB (q : ℚ_[l]) : T.eB (algebraMap ℚ_[l] P.R.B q) = period_ring_base.qB l q :=
  (PositivityTheory.LocInh.tie_q T q).trans (qB_eq q)

theorem tie_σB (g : GQ l) (b : P.R.B) : T.eB (P.actQ g b) = period_ring_base.σB g (T.eB b) := T.actB g b

end period_ring_base.DualB
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace UpperTheory.Lit.Drps

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GroundTheory.PAdicHodge DeRhamPotentiallySemistable.DRPst

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem exists_beta (T : LocTied6 l P AI) : ∃ β : ℚ_[l], ∀ g : GQ l,
    T.eB ((GlobalTheory.Pst.kummer P g : ℚ_[l]) • P.tB) =
      period_ring_base.qB l (period_ring_base.κ g) * period_ring_base.t l +
        (period_ring_base.σB g (period_ring_base.qB l β * period_ring_base.t l) - period_ring_base.qB l β * period_ring_base.t l) := by
  obtain ⟨a, b, ht, hr⟩ := Kum.exists_rel AI T
  have h1 : T.eB P.tB = period_ring_base.qB l (a : ℚ_[l]) * period_ring_base.t l := by
    apply period_ring_base.base_ι_inj l
    rw [map_mul, period_ring_base.base_ι_q, period_ring_base.period_image_eq, period_ring_base.BaseA.ι_eq, ← PositivityTheory.LocInh.tie_ι T, ht, map_mul,
      DeRhamTwist.Twist.tQ_eq]
    rfl
  refine ⟨(b : ℚ_[l]), fun g => ?_⟩
  have h2 : period_ring_base.κ g + period_ring_base.χ g * (b : ℚ_[l]) = b + a * (GlobalTheory.Pst.kummer P g : ℚ_[l]) := by
    have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) (hr g)
    simp only [PadicInt.coe_add, PadicInt.coe_mul] at this
    exact this
  have h3 := congrArg (period_ring_base.qB l) h2
  simp only [map_add (f := _), map_mul] at h3
  rw [Algebra.smul_def, map_mul, period_ring_base.DualB.tie_qB T, h1, map_mul, period_ring_base.base_σ_q, period_ring_base.galois_period_cyclotomic]
  linear_combination (-(period_ring_base.t l)) * h3

end UpperTheory.Lit.Drps
