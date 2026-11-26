module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsIsCayleyUIff
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue

@[expose] public section

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_isLowUnitH_of_isDSHpk {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Mx k r → (H →L[ℂ] H)}
    (hσ : PI.UpqRep.IsDSHpk k r ε mu σ) : ∃ w, ‖w‖ = 1 ∧ PI.UpqRep.IsLowUnitH k r ε mu σ w := by
  unfold PI.UpqRep.IsDSHpk at hσ
  obtain ⟨P, hP, hds⟩ := hσ
  unfold PI.UpqRep.IsDS at hds
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, -⟩ := hds
  have hS' := hS
  unfold PI.UpqRep.IsKTypeOf at hS'
  obtain ⟨v, hvS, hv0, -⟩ := hS'.2.2.2.1
  have hle : S ≤ PI.UpqRep.lowKSub ε mu (fun g => σ (P⁻¹ * g * P)) := le_sSup hS
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, norm_smul_inv_norm hv0, ?_⟩
  unfold PI.UpqRep.IsLowUnitH PI.UpqRep.IsLowUnit
  exact ⟨P, hP, norm_smul_inv_norm hv0, Submodule.smul_mem _ _ (hle hvS)⟩

theorem rep_basic_of_isDS : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → (∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) ∧ (∀ v, R.σ 1 v = v) ∧ (∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm) ∧ (∀ v ∈ R.TK, v ∈ R.sm) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.TK, R.σ g v ∈ R.TK) ∧ (∀ v, R.KFin v → v ∈ R.TK) ∧ (∃ w, ‖w‖ = 1 ∧ R.KFin w ∧ PI.UpqRep.IsLowUnitH k r ε mu R.σ w) ∧ (∀ v, ContinuousOn (fun g => R.σ g v) (GG k r)) := by
  intro hK k r ε mu R hDG
  have hds : PI.UpqRep.IsDSHpk k r ε mu R.σ := hDG.ds
  have hc : PI.UpqRep.IsHCParam mu := hDG.hc
  have toPI : ∀ g, g ∈ GG k r → g ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r) := by
    intro g hg
    rw [← Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_eq]
    exact hg
  have ofPI : ∀ g, g ∈ PI.UpqRep.UH (PI.UpqRep.Hpk k r) → g ∈ GG k r := by
    intro g hg
    show g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
    rw [Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_eq]
    exact hg
  have hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v) := by
    intro g hg h hh v
    have e := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hds (toPI g hg) (toPI h hh)
    exact congrArg (fun T => T v) e
  have hone : ∀ v, R.σ 1 v = v := by
    intro v
    have e := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hds).1
    simpa using congrArg (fun T : R.H →L[ℂ] R.H => T v) e
  have hsmooth : ∀ v, R.KFin v → v ∈ R.sm := fun v hv => hK k r ε mu R.H R.σ hc hds v hv
  have hsm : ∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm := by
    intro g hg v hv
    exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_translate hds hv (toPI g hg)
  refine ⟨hmul, hone, ?_, hsm, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg v w
    have hinv := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    have e1 := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_inner hds hg (R.σ g v) w
    have e2 := hmul g⁻¹ hinv.1 g hg v
    rw [hinv.2.2, hone] at e2
    rw [e1, ← e2]
  · intro v hv
    unfold BranchingSupport.Rep.TK at hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, v₀, hv₀, rfl⟩ := hx
      exact hsm g hg v₀ (hsmooth v₀ hv₀)
    | zero => exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_zero
    | add x y _ _ hx hy => exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_add hx hy
    | smul a x _ hx => exact Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_smul a hx
  · intro g hg v hv
    unfold BranchingSupport.Rep.TK at hv ⊢
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, v₀, hv₀, rfl⟩ := hx
      refine Submodule.subset_span ⟨g * h, ?_, v₀, hv₀, (hmul g hg h hh v₀).symm⟩
      exact ofPI _ (Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul (toPI g hg) (toPI h hh))
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · intro v hv
    unfold BranchingSupport.Rep.TK
    refine Submodule.subset_span ⟨1, ?_, v, hv, (hone v).symm⟩
    exact ofPI _ (by simp [PI.UpqRep.UH])
  · obtain ⟨w, hw1, hw⟩ := exists_isLowUnitH_of_isDSHpk hds
    exact ⟨w, hw1, PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hw, hw⟩
  · intro v
    exact Formalism.FourierDecayAlt.P.S3dx4.sigma_contOn hds v

end GlobalTheory
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasicStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.discreteSeries_unitary_smooth_basic : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → (∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v)) ∧ (∀ v, R.σ 1 v = v) ∧ (∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.sm, R.σ g v ∈ R.sm) ∧ (∀ v ∈ R.TK, v ∈ R.sm) ∧ (∀ g ∈ GG k r, ∀ v ∈ R.TK, R.σ g v ∈ R.TK) ∧ (∀ v, R.KFin v → v ∈ R.TK) ∧ (∃ w, ‖w‖ = 1 ∧ R.KFin w ∧ PI.UpqRep.IsLowUnitH k r ε mu R.σ w) ∧ (∀ v, ContinuousOn (fun g => R.σ g v) (GG k r)) := by
  first | exact @GlobalTheory.rep_basic_of_isDS | exact GlobalTheory.rep_basic_of_isDS | (intros; apply GlobalTheory.rep_basic_of_isDS <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SumNonneg
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselDecay

theorem gN_mul_le' {k r : ℕ} (a b : Mx k r) : B.gN (a * b) ≤ B.gN a * B.gN b := by
  exact PI.PolynomialProperness.GN.gN_mul_le a b

theorem gN_pos' {k r : ℕ} {a : Mx k r} (ha : a ∈ GG k r) : 0 < B.gN a := by
  exact PI.PolynomialProperness.GN.gN_pos ha

theorem sum_nonneg' {α : Type} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (L : List α) : 0 ≤ (L.map f).sum := by
  apply List.sum_nonneg
  intro a ha
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp ha
  exact hf w

theorem one_le_aOf {k r : ℕ} {h : ℝ} (hg : GapOK k r h) : 1 ≤ aOf r h := by
  have h4 := hg.2.2.2
  have : 0 ≤ AG k r := by unfold AG; positivity
  have : 0 ≤ 9 * ((r : ℝ) + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  linarith

theorem decay_TK : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r), R.IsDG ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → ∀ v ∈ R.TK, ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧ ∀ w ∈ R.sm, ∀ x ∈ GG k r, ‖⟪v, R.σ x w⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum * B.gN x ^ (1 - aOf r h) := by
  intro H k r ε mu h R hR hgap hok v hv
  have hdec : DecInf := H.1.2.1
  have ha := one_le_aOf hok
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨g, hg, v₀, hv₀, rfl⟩ := hv
    obtain ⟨C, Ws, hWs, hb⟩ := hdec k r ε mu h R.H R.σ hR.1 hR.2 hgap hok v₀ hv₀
    refine ⟨|C| * B.gN g ^ (aOf r h - 1), Ws, hWs, fun w hw x hx => ?_⟩
    obtain ⟨hi, hgi, hig⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uh_inv hg
    have hy : g⁻¹ * x ∈ GG k r := Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul hi hx
    have hx' : x = g * (g⁻¹ * x) := by rw [← Matrix.mul_assoc, hgi, Matrix.one_mul]
    have hunit := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2
    have hiso : ∀ a b, ⟪R.σ g a, R.σ g b⟫_ℂ = ⟪a, b⟫_ℂ :=
      (LinearMap.norm_map_iff_inner_map_map ((R.σ g : R.H →L[ℂ] R.H) : R.H →ₗ[ℂ] R.H)).1 (hunit g hg)
    have e : ⟪R.σ g v₀, R.σ x w⟫_ℂ = ⟪v₀, R.σ (g⁻¹ * x) w⟫_ℂ := by
      rw [← hiso v₀]
      congr 1
      conv_lhs => rw [hx', Formalism.FourierDecayAlt.P.TranslationBesselVanishing.sigma_mul hR.2 hg hy]
      rfl
    rw [e]
    have h1 := hb w hw _ hy
    set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS
    have hS0 : 0 ≤ S := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have pg := gN_pos' hg
    have px := gN_pos' hx
    have py := gN_pos' hy
    have hle : B.gN x ≤ B.gN g * B.gN (g⁻¹ * x) := by
      conv_lhs => rw [hx']
      exact gN_mul_le' _ _
    have h2 : (B.gN g * B.gN (g⁻¹ * x)) ^ (1 - aOf r h) ≤ B.gN x ^ (1 - aOf r h) :=
      Real.rpow_le_rpow_of_nonpos px hle (by linarith)
    rw [Real.mul_rpow pg.le py.le] at h2
    have h3 : B.gN g ^ (aOf r h - 1) * B.gN g ^ (1 - aOf r h) = 1 := by
      rw [← Real.rpow_add pg]; simp
    have pg' : 0 < B.gN g ^ (aOf r h - 1) := Real.rpow_pos_of_pos pg _
    have h4 : B.gN (g⁻¹ * x) ^ (1 - aOf r h) ≤ B.gN g ^ (aOf r h - 1) * B.gN x ^ (1 - aOf r h) := by
      calc B.gN (g⁻¹ * x) ^ (1 - aOf r h)
          = B.gN g ^ (aOf r h - 1) * (B.gN g ^ (1 - aOf r h) * B.gN (g⁻¹ * x) ^ (1 - aOf r h)) := by
            rw [← mul_assoc, h3, one_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 pg'.le
    calc _ ≤ C * S * B.gN (g⁻¹ * x) ^ (1 - aOf r h) := h1
      _ ≤ |C| * S * B.gN (g⁻¹ * x) ^ (1 - aOf r h) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hS0)
            (Real.rpow_pos_of_pos py _).le
      _ ≤ |C| * S * (B.gN g ^ (aOf r h - 1) * B.gN x ^ (1 - aOf r h)) :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg (abs_nonneg C) hS0)
      _ = _ := by ring
  | zero => exact ⟨0, [], by simp, fun w _ x _ => by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨C, Ws, hWs, hb⟩ := hu
    obtain ⟨C', Ws', hWs', hb'⟩ := hv
    refine ⟨|C| + |C'|, Ws ++ Ws', fun W hW => (List.mem_append.1 hW).elim (hWs W) (hWs' W),
      fun w hw x hx => ?_⟩
    have h1 := hb w hw x hx
    have h2 := hb' w hw x hx
    rw [List.map_append, List.sum_append, inner_add_left]
    set S := (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS
    set S' := (Ws'.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W w‖).sum with hS'
    have hS0 : 0 ≤ S := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have hS0' : 0 ≤ S' := sum_nonneg' _ (fun _ => norm_nonneg _) _
    have px : 0 ≤ B.gN x ^ (1 - aOf r h) := (Real.rpow_pos_of_pos (gN_pos' hx) _).le
    have h3 : C * S + C' * S' ≤ (|C| + |C'|) * (S + S') := by
      have a1 := mul_le_mul_of_nonneg_right (le_abs_self C) hS0
      have a2 := mul_le_mul_of_nonneg_right (le_abs_self C') hS0'
      have a3 := mul_nonneg (abs_nonneg C) hS0'
      have a4 := mul_nonneg (abs_nonneg C') hS0
      nlinarith
    calc _ ≤ ‖⟪u, R.σ x w⟫_ℂ‖ + ‖⟪v, R.σ x w⟫_ℂ‖ := norm_add_le _ _
      _ ≤ (C * S + C' * S') * B.gN x ^ (1 - aOf r h) := by rw [add_mul]; exact add_le_add h1 h2
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 px
  | smul c v _ hv =>
    obtain ⟨C, Ws, hWs, hb⟩ := hv
    refine ⟨‖c‖ * C, Ws, hWs, fun w hw x hx => ?_⟩
    rw [inner_smul_left, norm_mul, RCLike.norm_conj, mul_assoc, mul_assoc, ← mul_assoc C]
    exact mul_le_mul_of_nonneg_left (hb w hw x hx) (norm_nonneg c)

end GlobalTheory.BesselDecay
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsKTypeNonzeroBessel
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsKTypeNonzeroBessel
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem bessel_nonzero_on_translates : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), R.IsDG ε mu → IsBes R z π l → NzOn R l → ∃ v ∈ R.TK, l v ≠ 0 := by
  intro hH k r ε mu R Wp _ _ _ _ z π l hds hB hnz
  obtain ⟨⟨-, -, hKF, -⟩, hCyc, -⟩ := hH
  have hex : ∃ w0, PI.UpqRep.IsLowUnitH k r ε mu R.σ w0 := by
    obtain ⟨P, hP, -, -, -, -, -, ⟨S, hS⟩, -⟩ := hds.2
    obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, P, hP, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · exact Submodule.smul_mem _ _ (Submodule.mem_sSup.mpr fun N hN => hN S hS hvS)
  obtain ⟨w0, hlow⟩ := hex
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  by_contra hcon
  push_neg at hcon
  obtain ⟨w, hw, hlw⟩ := hnz
  refine hlw (Formalism.FourierDecayAlt.P.bessel_ne_zero_of_cyclic_orbit hCyc hKF k r ε mu R.H R.σ w0 Wp z Formalism.QuantumDeterminants.cStd π hds.1 hds.2 hlow
    l hB (fun x hx => hcon x ?_) w hw)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hg, w0, hwK, rfl⟩

end GlobalTheory
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ExistsKTypeNonzeroBesselStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.exists_K_type_nonzero_bessel : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), R.IsDG ε mu → IsBes R z π l → NzOn R l → ∃ v ∈ R.TK, l v ≠ 0 := by
  first | exact @GlobalTheory.bessel_nonzero_on_translates | exact GlobalTheory.bessel_nonzero_on_translates | (intros; apply GlobalTheory.bessel_nonzero_on_translates <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrepDiscreteSeriesSum
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrepDiscreteSeriesSum
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensAdj

section
variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_left (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (y : ι → R.H) :
    hh Γ R (fun c => ∑ I, f I c) y = ∑ I, hh Γ R (f I) y := by
  simp only [hh, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (x : ι → R.H) :
    hh Γ R x (fun c => ∑ I, f I c) = ∑ I, hh Γ R x (f I) := by
  simp only [hh, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem sum_sm (R : Rep k r) (x : ι → R.H) (hx : ∀ c, x c ∈ R.sm) : ∑ c, x c ∈ R.sm :=
  R.smSub.sum_mem (t := univ) (f := x) fun c _ => hx c

omit [DecidableEq ι] in
theorem hh_tm (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) (v : R.H) :
    hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ := by
  simp only [hh, tm, ev, inner_sum, inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

theorem norm_sq_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Γ : Matrix ι ι ℂ}
    (h : Γᴴ * Γ = 1) (x : ι → H) : ∑ i, ‖∑ j, Γ i j • x j‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := _root_.GlobalTheory.TensAdj.norm_sq_mul (H := H) (Γ := Γ) h x

theorem norm_hh_le {Γ : Matrix ι ι ℂ} (h : Γᴴ * Γ = 1) (R : Rep k r) (x : ι → R.H) :
    ‖hh Γ R x x‖ ≤ ∑ c, ‖x c‖ ^ 2 := by
  have e : hh Γ R x x = ∑ i, ⟪x i, ∑ j, Γ i j • x j⟫_ℂ := by
    simp only [hh, inner_sum, inner_smul_right]
  have h1 := norm_sq_mul h x
  have h2 : ‖hh Γ R x x‖ ≤ ∑ i, (‖x i‖ ^ 2 + ‖∑ j, Γ i j • x j‖ ^ 2) / 2 := by
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    nlinarith [sq_nonneg (‖x i‖ - ‖∑ j, Γ i j • x j‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib, h1] at h2
  linarith

variable {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
  {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} {ep : κ → ℝ}

theorem proj_sm (hT : TensH ρ Γ R RI io pr ep) (I : κ) {x : ι → R.H} (hx : ∀ c, x c ∈ R.sm) :
    ∑ c, pr I c (x c) ∈ (RI I).sm :=
  sum_sm (RI I) _ fun c => (hT.raw.pr_sm I c).mem _ (hx c)

theorem adj (hT : TensH ρ Γ R RI io pr ep) (I : κ) (y : (RI I).H) (hy : y ∈ (RI I).sm) (x : ι → R.H)
    (hx : ∀ c, x c ∈ R.sm) :
    hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ := by
  have e : (fun c => ∑ J, io J c (∑ d, pr J d (x d))) = x := funext (hT.raw.sum_io_pr x hx)
  conv_lhs => rw [← e]
  rw [hh_sum_right Γ R (fun J c => io J c (∑ d, pr J d (x d))), Finset.sum_eq_single I]
  · exact hT.iso I y hy _ (proj_sm hT I hx)
  · intro J _ hJ
    exact hT.orth I J hJ.symm y hy _ (proj_sm hT J hx)
  · simp

theorem parseval (hT : TensH ρ Γ R RI io pr ep) (x x' : ι → R.H) (hx : ∀ c, x c ∈ R.sm)
    (hx' : ∀ c, x' c ∈ R.sm) :
    hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ := by
  have e : (fun c => ∑ J, io J c (∑ d, pr J d (x d))) = x := funext (hT.raw.sum_io_pr x hx)
  conv_lhs => rw [← e]
  rw [hh_sum_left Γ R (fun J c => io J c (∑ d, pr J d (x d)))]
  exact Finset.sum_congr rfl fun I _ => adj hT I _ (proj_sm hT I hx) x' hx'

end

theorem tens_adj : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ I, ∀ y ∈ (RI I).sm, ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) → hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ) ∧ (∀ x x' : ι → R.H, (∀ c, x c ∈ R.sm) → (∀ c, x' c ∈ R.sm) → hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ) ∧ (∀ (a : ι → ℂ) (x : ι → R.H) (v : R.H), hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ) ∧ (∀ I, ∀ y ∈ (RI I).sm, ‖y‖ ^ 2 ≤ ∑ c, ‖io I c y‖ ^ 2) ∧ ∀ (a a' : ι → ℂ), ∀ v ∈ R.sm, ∀ v' ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a') a * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R a v c), (RI I).σ g (∑ c, pr I c (tm R a' v' c))⟫_ℂ := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI hR _ hF hT
  refine ⟨fun I y hy x hx => adj hT I y hy x hx, fun x x' hx hx' => parseval hT x x' hx hx',
    fun a x v => hh_tm Γ R a x v, ?_, ?_⟩
  · intro I y hy
    have h1 := norm_hh_le (Γ := Γ) (by rw [hF.1, hF.2.1]) R (fun c => io I c y)
    rw [hT.iso I y hy y hy, norm_mul, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖(ep I : ℂ)‖ = 1 := by rcases hT.ep_sq I with h | h <;> simp [h]
    rw [h2] at h1
    simpa using h1
  · intro a a' v hv v' hv' g hg
    have ht : ∀ (b : ι → ℂ) (w : R.H), w ∈ R.sm → ∀ c, tm R b w c ∈ R.sm := fun b w hw c =>
      R.smSub.smul_mem (b c) hw
    have hact : ∀ c, act ρ R g (tm R a' v') c ∈ R.sm := fun c =>
      sum_sm R _ fun j => R.smSub.smul_mem _
        (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 _ (ht a' v' hv' j) g hg)
    have hp := parseval hT _ _ hact (ht a v hv)
    simp only [hT.raw.pr_eq _ g hg _ (ht a' v' hv')] at hp
    rw [← hp]
    simp only [hh, act, tm, Formalism.QuantumDeterminants.herm, inner_sum, inner_smul_left, inner_smul_right, map_smul, smul_smul,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.star_apply, RCLike.star_def]
    ring

end GlobalTheory.TensAdj
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FrepDiscreteSeriesSumStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.frep_discrete_series_sum : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ I, ∀ y ∈ (RI I).sm, ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) → hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ) ∧ (∀ x x' : ι → R.H, (∀ c, x c ∈ R.sm) → (∀ c, x' c ∈ R.sm) → hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ) ∧ (∀ (a : ι → ℂ) (x : ι → R.H) (v : R.H), hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ) ∧ (∀ I, ∀ y ∈ (RI I).sm, ‖y‖ ^ 2 ≤ ∑ c, ‖io I c y‖ ^ 2) ∧ ∀ (a a' : ι → ℂ), ∀ v ∈ R.sm, ∀ v' ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a') a * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R a v c), (RI I).σ g (∑ c, pr I c (tm R a' v' c))⟫_ℂ := by
  first | exact @GlobalTheory.TensAdj.tens_adj | exact GlobalTheory.TensAdj.tens_adj | (intros; apply GlobalTheory.TensAdj.tens_adj <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionParameters
section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionParameters
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensForm

theorem common_bound {ι α β : Type} [DecidableEq ι] (P : α → Prop) (S : Set β) (n : α → β → ℝ)
    (hn : ∀ a v, 0 ≤ n a v) (f : ι → β → ℝ)
    (h : ∀ c, ∃ (C : ℝ) (L : List α), (∀ a ∈ L, P a) ∧ ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum)
    (s : Finset ι) :
    ∃ (C : ℝ) (L : List α), 0 ≤ C ∧ (∀ a ∈ L, P a) ∧
      ∀ c ∈ s, ∀ v ∈ S, f c v ≤ C * (L.map fun a => n a v).sum := _root_.GlobalTheory.TensForm.common_bound (ι := ι) (α := α) (β := β) P S n hn f h s

variable {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem hh_act (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (R : Rep k r) (g : Mx k r)
    (hρ : (ρ g)ᴴ * Γ * ρ g = Γ) (hσ : ∀ v, ‖R.σ g v‖ = ‖v‖) (x y : ι → R.H) :
    hh Γ R (act ρ R g x) (act ρ R g y) = hh Γ R x y := _root_.GlobalTheory.TensForm.hh_act ρ Γ R g hρ hσ x y


omit [DecidableEq ι] in
theorem norm_hh_le (Γ : Matrix ι ι ℂ) (R : Rep k r) (x y : ι → R.H) (A B : ℝ)
    (hx : ∀ c, ‖x c‖ ≤ A) (hy : ∀ c, ‖y c‖ ≤ B) :
    ‖hh Γ R x y‖ ≤ (∑ i, ∑ j, ‖Γ i j‖) * (A * B) := by
  rw [hh, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans ?_) (norm_nonneg _)
  rw [mul_comm A B]
  exact mul_le_mul (hy i) (hx j) (norm_nonneg _) ((norm_nonneg _).trans (hy i))

theorem family_bound (R R' : Rep k r) (T : ι → R.H → R'.H) (hT : ∀ c, SmMap R R' (T c)) :
    ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) ∧
      ∀ c, ∀ v ∈ R.sm, ‖T c v‖ ≤ C * (Ws.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖).sum := by
  obtain ⟨C, L, -, hL, hb⟩ := common_bound (fun W : List (Mx k r) => ∀ X ∈ W, PI.UpqRep.InLieHpk k r X) R.sm
    (fun W v => ‖PI.UpqRep.dsigW (k := k) (r := r) R.σ W v‖) (fun _ _ => norm_nonneg _)
    (fun c v => ‖T c v‖) (fun c => (hT c).cont [] (by simp)) Finset.univ
  exact ⟨C, L, hL, fun c => hb c (Finset.mem_univ c)⟩

theorem pulledBack_isInvForm : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∀ I J, IsInvForm (RI I) (RI J) (fun y y' => hh Γ R (fun c => io I c y) (fun c => io J c y')) := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ε mu muI hR _ hF hT I J
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' y _
    simp only [hh, fun c => (hT.io_sm I c).add x hx x' hx', inner_add_right, mul_add, Finset.sum_add_distrib]
  · intro a x hx y _
    simp only [hh, fun c => (hT.io_sm I c).smul a x hx, inner_smul_right, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · intro x _ y hy y' hy'
    simp only [hh, fun c => (hT.io_sm J c).add y hy y' hy', inner_add_left, mul_add, Finset.sum_add_distrib]
  · intro a x _ y hy
    simp only [hh, fun c => (hT.io_sm J c).smul a y hy, inner_smul_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [RCLike.star_def]; ring
  · intro g hg x hx y hy
    show hh Γ R (fun c => io I c ((RI I).σ g x)) (fun c => io J c ((RI J).σ g y)) = _
    rw [hT.io_eq I g hg x hx, hT.io_eq J g hg y hy]
    exact hh_act ρ Γ R g (hF.2.2.2.2.1 g hg) ((Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.sigma_facts hR.2).2 g hg) _ _
  · obtain ⟨C, Ws, hW, hb⟩ := family_bound (RI I) R (io I) (hT.io_sm I)
    obtain ⟨C', Ws', hW', hb'⟩ := family_bound (RI J) R (io J) (hT.io_sm J)
    refine ⟨(∑ i, ∑ j, ‖Γ i j‖) * C * C', Ws, Ws', ?_, ?_⟩
    · intro W hWm
      rcases List.mem_append.1 hWm with h | h
      · exact hW W h
      · exact hW' W h
    · intro x hx y hy
      refine (norm_hh_le Γ R _ _ _ _ (fun c => hb c x hx) (fun c => hb' c y hy)).trans (le_of_eq ?_)
      ring

end GlobalTheory.TensForm
end Gp91
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorDecompositionParametersStatement
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.Gp91.GlobalTheory.T.tensor_decomposition_parameters : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDG ε mu → (∀ I, (RI I).IsDG ε (muI I)) → IsFRep ρ Γ d → TensRaw ρ R RI io pr → ∀ I J, IsInvForm (RI I) (RI J) (fun y y' => hh Γ R (fun c => io I c y) (fun c => io J c y')) := by
  first | exact @GlobalTheory.TensForm.pulledBack_isInvForm | exact GlobalTheory.TensForm.pulledBack_isInvForm | (intros; apply GlobalTheory.TensForm.pulledBack_isInvForm <;> assumption)
end Gp91
end
end

section -- merged from CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.CayleyExistsAndAny
namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CayleyChoice

open PI.UpqRep

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

lemma Kset_sub {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : g ∈ UJset ε := by
  have hg1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  show gᴴ * Jm ε * g = Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hg1, Matrix.one_mul]

lemma UJ_mul {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  calc (g * h)ᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Jm ε := by rw [hg', hh']

lemma symm_inter (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) :
    ∀ g ∈ UJset ε, ∀ v, T.symm (σ g v) = σ' g (T.symm v) := by
  intro g hg v
  apply T.injective
  rw [h g hg]; simp

lemma wt_transfer (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) {μ : Fin n → ℝ} {v : H}
    (hv : IsWtOn (Kset ε) σ' μ v) : IsWtOn (Kset ε) σ μ (T v) := by
  intro θ hθ
  rw [← h _ (Kset_sub hθ), hv θ hθ, map_smul]

lemma ktype_transfer (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (hS : IsKTypeOf ε σ' Λ S) :
    IsKTypeOf ε σ Λ (S.map (T.toLinearEquiv : H →ₗ[ℂ] H)) := by
  obtain ⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ⟨T v, ⟨v, hv, rfl⟩, by simpa using hv0, wt_transfer T h hvw⟩, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ' g x, h2 g hg x hx, h g (Kset_sub hg) x⟩
  · intro S' hle hst
    rcases h3 (S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H)) (by
        intro x hx
        obtain ⟨y, hy, e⟩ := hle hx
        have : y = x := T.injective e
        exact this ▸ hy) (by
        intro g hg x hx
        show T (σ' g x) ∈ S'
        rw [h g (Kset_sub hg)]
        exact hst g hg _ hx) with e | e
    · left
      rw [eq_bot_iff]
      intro x hx
      have : T.symm x ∈ S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H) := by
        show T (T.symm x) ∈ S'
        simpa using hx
      rw [e] at this
      simpa using this
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [← e] at hx
      exact hx
  · rintro μ _ ⟨x, hx, rfl⟩ h0 hw
    have := wt_transfer T.symm (symm_inter T h) hw
    refine h5 μ x hx (by rintro rfl; simp at h0) ?_
    simpa using this

theorem isDS_transfer (T : H ≃ₗᵢ[ℂ] H) (h : ∀ g ∈ UJset ε, ∀ v, T (σ' g v) = σ g (T v)) {lam : Fin n → ℝ}
    (hσ : IsDS ε lam σ) : IsDS ε lam σ' := by
  obtain ⟨c1, c2, ⟨⟨r1, r2⟩, r3, r4⟩, c4, c5, ⟨S, hS⟩, c7⟩ := hσ
  have h' := symm_inter T h
  have e : ∀ g ∈ UJset ε, ∀ v, σ' g v = T.symm (σ g (T v)) := by
    intro g hg v; rw [← h g hg]; simp
  have one : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
    show (1 : Matrix (Fin n) (Fin n) ℂ)ᴴ * Jm ε * 1 = Jm ε
    simp
  refine ⟨c1, c2, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ⟨_, ktype_transfer T.symm h' hS⟩,
    fun μ S' hS' => c7 μ _ (ktype_transfer T h hS')⟩
  · ext v; rw [e 1 one, r1]; simp
  · intro a ha b hb
    ext v
    rw [ContinuousLinearMap.comp_apply, e _ (UJ_mul ha hb), e a ha, e b hb, r2 a ha b hb]; simp
  · intro g hg v
    rw [e g hg]; simp [r3 g hg]
  · intro v
    exact (T.symm.continuous.comp_continuousOn (r4 (T v))).congr fun g hg => e g hg v
  · intro S' hcl hst
    rcases c4 (S'.comap (T.symm.toLinearEquiv : H →ₗ[ℂ] H)) (hcl.preimage T.symm.continuous) (by
        intro g hg x hx
        show T.symm (σ g x) ∈ S'
        rw [h' g hg]
        exact hst g hg _ hx) with e | e
    · left
      rw [eq_bot_iff]
      intro x hx
      have : T x ∈ S'.comap (T.symm.toLinearEquiv : H →ₗ[ℂ] H) := by
        show T.symm (T x) ∈ S'
        simpa using hx
      rw [e] at this
      simpa using this
    · right
      rw [eq_top_iff]
      intro x _
      have : T x ∈ S'.comap (T.symm.toLinearEquiv : H →ₗ[ℂ] H) := by rw [e]; trivial
      have h2 : T.symm (T x) ∈ S' := this
      simpa using h2
  · intro v w
    have : coefOn (ε := ε) σ' v w = coefOn (ε := ε) σ (T v) (T w) := by
      funext g
      show ⟪w, σ' (umat g) v⟫_ℂ = ⟪T w, σ (umat g) (T v)⟫_ℂ
      rw [← h _ g.2, T.inner_map_map]
    rw [this]; exact c5 _ _

theorem isDS_conj {lam : Fin n → ℝ} (hσ : IsDS ε lam σ) {u u' : Matrix (Fin n) (Fin n) ℂ}
    (hu : u ∈ UJset ε) (hu' : u' ∈ UJset ε) (h1 : u * u' = 1) :
    IsDS ε lam (fun g => σ (u' * g * u)) := by
  obtain ⟨⟨r1, r2⟩, r3, -⟩ := hσ.2.2.1
  have hs : ∀ v, σ u (σ u' v) = v := by
    intro v
    have := r2 u hu u' hu'
    rw [h1, r1] at this
    simpa using (congrArg (fun A : H →L[ℂ] H => A v) this).symm
  let T : H ≃ₗᵢ[ℂ] H := LinearIsometryEquiv.ofSurjective
    { toLinearMap := (σ u : H →ₗ[ℂ] H), norm_map' := r3 u hu } (fun v => ⟨σ u' v, hs v⟩)
  refine isDS_transfer T ?_ hσ
  intro g hg v
  show σ u (σ (u' * g * u) v) = σ g (σ u v)
  rw [r2 _ (UJ_mul hu' hg) u hu, r2 u' hu' g hg]
  simp [hs]

lemma card_even (r : ℕ) : ((range (2 * r + 2)).filter fun m => m % 2 = 0).card = r + 1 := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 2 * (r + 1) + 2 = 2 * r + 2 + 1 + 1 by ring, range_add_one, range_add_one, filter_insert,
      filter_insert, if_neg (by omega), if_pos (by omega), card_insert_of_notMem (by simp), ih]

lemma card_signs (k r : ℕ) (hk : 1 ≤ k) :
    (univ.filter fun i => PI.BesselPeriodGGP.eps48 k r i = true).card = k + r := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [card_filter]
  have h : ∀ i : Fin (2 * r + (j + 1) + 1), (if PI.BesselPeriodGGP.eps48 (j + 1) r i = true then 1 else 0) =
      (fun m : ℕ => if m < j ∨ (m - j) % 2 = 0 then 1 else 0) i.val := by
    intro i
    by_cases h1 : i.val < j <;> simp [PI.BesselPeriodGGP.eps48, h1]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun m : ℕ => if m < j ∨ (m - j) % 2 = 0 then 1 else 0),
    show 2 * r + (j + 1) + 1 = j + (2 * r + 2) by ring, sum_range_add]
  have a : ∑ m ∈ range j, (if m < j ∨ (m - j) % 2 = 0 then 1 else 0) = j := by
    rw [sum_congr rfl (g := fun _ => 1) (fun m hm => if_pos (Or.inl (mem_range.1 hm)))]; simp
  have b : ∑ m ∈ range (2 * r + 2), (if j + m < j ∨ (j + m - j) % 2 = 0 then 1 else 0) = r + 1 := by
    rw [← card_even r, card_filter]
    refine sum_congr rfl fun m _ => ?_
    simp
  rw [a, b]; ring

theorem cayley_exists_and_any : ∀ (k r : ℕ), (1 ≤ k → ∃ Q, PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q) ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ Q, PI.UpqRep.IsCayleyU k r ε Q → PI.UpqRep.IsDS ε mu (fun g => R.σ (Q⁻¹ * g * Q)) := by
  intro k r
  refine ⟨fun hk => (GlobalTheory.UnitaryCayley.exists_isCayleyU_iff k r _).2 (card_signs k r hk), ?_⟩
  rintro ε mu R ⟨-, ⟨P, ⟨⟨-, hP⟩, hPu⟩, hD⟩, -⟩ Q ⟨⟨-, hQ⟩, hQu⟩
  have p1 : Pᴴ * P = 1 := (Matrix.mem_unitaryGroup_iff').1 hPu
  have p2 : P * Pᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hPu
  have q1 : Qᴴ * Q = 1 := (Matrix.mem_unitaryGroup_iff').1 hQu
  have q2 : Q * Qᴴ = 1 := (Matrix.mem_unitaryGroup_iff).1 hQu
  have pi : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv p1
  have qi : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have gen : ∀ A B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, B * Bᴴ = 1 →
      Aᴴ * Jm ε * A = Bᴴ * Jm ε * B → A * Bᴴ ∈ UJset ε := by
    intro A B hB hAB
    show (A * Bᴴ)ᴴ * Jm ε * (A * Bᴴ) = Jm ε
    calc (A * Bᴴ)ᴴ * Jm ε * (A * Bᴴ) = B * (Aᴴ * Jm ε * A) * Bᴴ := by
          simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = (B * Bᴴ) * Jm ε * (B * Bᴴ) := by rw [hAB]; simp only [Matrix.mul_assoc]
      _ = Jm ε := by rw [hB]; simp
  have key := isDS_conj hD (gen Q P p2 (hQ.trans hP.symm)) (gen P Q q2 (hP.trans hQ.symm)) (by
    calc Q * Pᴴ * (P * Qᴴ) = Q * (Pᴴ * P) * Qᴴ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [p1, Matrix.mul_one, q2])
  have e : (fun g => R.σ (Q⁻¹ * g * Q)) = fun g => R.σ (P⁻¹ * (P * Qᴴ * g * (Q * Pᴴ)) * P) := by
    funext g
    congr 1
    rw [pi, qi]
    calc Qᴴ * g * Q = (Pᴴ * P) * Qᴴ * g * Q * (Pᴴ * P) := by rw [p1]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]
  exact key

end GlobalTheory.CayleyChoice
end
end Gp91
end
