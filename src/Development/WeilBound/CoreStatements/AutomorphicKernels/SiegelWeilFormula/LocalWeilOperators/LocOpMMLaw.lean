module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocForm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.ChiWPf

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryMultiplicativeEqArgPow
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryMultiplicativeEqArgPow
namespace GlobalTheory.CompanionTheory.KlocOp

theorem cstar_char_eq_zpow : ∀ φ : ℂ → ℂ, (∀ z w : ℂ, z ≠ 0 → w ≠ 0 → φ (z * w) = φ z * φ w) →
    ContinuousOn φ {z : ℂ | z ≠ 0} → (∀ z : ℂ, z ≠ 0 → ‖φ z‖ = 1) →
    (∀ r : ℝ, 0 < r → φ (r : ℂ) = 1) →
    ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → φ z = (z / (‖z‖ : ℂ)) ^ k := by
  intro φ hmul hc hn h1
  have hmem : ∀ z : ℂˣ, φ (z : ℂ) ∈ Submonoid.unitSphere ℂ := fun z => by
    simpa [Submonoid.unitSphere] using hn z z.ne_zero
  let f : ℂˣ → Circle := fun z => ⟨φ (z : ℂ), hmem z⟩
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact hc.comp_continuous Units.continuous_val fun z => z.ne_zero
  have hf1 : f 1 = 1 := by
    apply Circle.ext
    have := h1 1 one_pos
    simpa [f] using this
  have hfm : ∀ a b : ℂˣ, f (a * b) = f a * f b := fun a b => by
    apply Circle.ext
    rw [Circle.coe_mul]
    change φ ((a * b : ℂˣ) : ℂ) = φ (a : ℂ) * φ (b : ℂ)
    rw [Units.val_mul]
    exact hmul a b a.ne_zero b.ne_zero
  let χ : ℂˣ →ₜ* Circle :=
    { toFun := f, map_one' := hf1, map_mul' := hfm, continuous_toFun := hfc }
  obtain ⟨⟨m, τ⟩, hp, -⟩ := GroundTheory.Global.existsUnique_complexUnits_circle χ
  have hp' : ∀ z : ℂˣ, φ (z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ m *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := hp
  have hr : ∀ r : ℝ, 0 < r → (r : ℂ) ^ ((τ : ℂ) * Complex.I) = 1 := by
    intro r hr0
    have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have h := hp' (Units.mk0 (r : ℂ) hne)
    rw [Units.val_mk0, h1 r hr0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_self hne, one_zpow, one_mul] at h
    exact h.symm
  refine ⟨m, fun z hz => ?_⟩
  have h := hp' (Units.mk0 z hz)
  rw [Units.val_mk0, hr _ (norm_pos_iff.mpr hz), mul_one] at h
  exact h

end GlobalTheory.CompanionTheory.KlocOp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryMultiplicativeEqArgPowStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_unitary_multiplicative_eq_arg_pow : ∀ φ : ℂ → ℂ, (∀ z w : ℂ, z ≠ 0 → w ≠ 0 → φ (z * w) = φ z * φ w) → ContinuousOn φ {z : ℂ | z ≠ 0} → (∀ z : ℂ, z ≠ 0 → ‖φ z‖ = 1) → (∀ r : ℝ, 0 < r → φ (r : ℂ) = 1) → ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → φ z = (z / (‖z‖ : ℂ)) ^ k := by
  first | exact @GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow | exact GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow | (intros; apply GlobalTheory.CompanionTheory.KlocOp.cstar_char_eq_zpow <;> assumption)
end
end

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace SD

variable (d : SD σ)

theorem chiW_mul (w : InfinitePlace F) : ∀ z z' : ℂ, z ≠ 0 → z' ≠ 0 → d.chiW w (z * z') = d.chiW w z * d.chiW w z' :=
  d.chiW_mul_pf w

theorem chiW_cont (w : InfinitePlace F) : ContinuousOn (d.chiW w) {z : ℂ | z ≠ 0} :=
  d.chiW_cont_pf w

theorem chiW_norm (w : InfinitePlace F) : ∀ z : ℂ, z ≠ 0 → ‖d.chiW w z‖ = 1 := by
  intro z _
  by_cases h : IsUnit (d.uW w z)
  · rw [SD.chiW, dite_eq_left h]
    exact Circle.norm_coe _
  · rw [SD.chiW, dite_eq_right h, norm_one]

theorem chiW_pos (w : InfinitePlace F) : ∀ r : ℝ, 0 < r → d.chiW w (r : ℂ) = 1 :=
  d.chiW_pos_pf w

theorem chiW_form (w : InfinitePlace F) : ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → d.chiW w z = (z / (‖z‖ : ℂ)) ^ k :=
  GlobalTheory.T.continuous_unitary_multiplicative_eq_arg_pow (d.chiW w) (d.chiW_mul w) (d.chiW_cont w) (d.chiW_norm w) (d.chiW_pos w)

end SD

namespace RD

variable {d : SD σ} (R : RD d) (w : InfinitePlace F)

theorem stepM_val (hT : TAll) : ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a →
    R.StepOK w (R.ι w y) (fun f u => (d.chiW w a.det * (‖a.det‖ : ℂ) ^ d.m) * f (Matrix.of u * a)) id :=
  R.stepM_val_pf w hT

variable {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}

theorem locOp_mM_law (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∃ k : ℤ, ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a → ∀ f, IsSw f →
      L y f = fun u => (a.det / (‖a.det‖ : ℂ)) ^ k * (‖a.det‖ : ℂ) ^ d.m * f (Matrix.of u * a) := by
  obtain ⟨k, hk⟩ := d.chiW_form w
  refine ⟨k, fun y a ha hy f hf => ?_⟩
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := ((R.stepM_val w hT y a ha hy).2 Ψ hΨ.1).2 f hf Φ hΦ hT'
  rw [R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2), hk _ ha.ne_zero]
  rfl

end RD

end PositivityTheory.SiegelWeilFormula

end
