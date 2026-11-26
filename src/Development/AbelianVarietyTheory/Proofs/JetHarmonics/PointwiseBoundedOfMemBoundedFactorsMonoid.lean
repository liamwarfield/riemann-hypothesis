module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFamilyFunctionals

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialRaisingOperatorsPointwiseAdjointPair
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.VanishAbstract
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.ZetaVanish

open MeasureTheory Topology Filter in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma isUnit_det_of_mem_Glev {k r : ℕ} {g : _root_.Formalism.FourierDecayAlt.Q.Mx k r}
    (hg : g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) : IsUnit (Matrix.det g) := by
  have h1 : Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r * g = _root_.Formalism.QuantumDeterminants.Hpk k r := hg.1
  have h2 : (_root_.Formalism.QuantumDeterminants.Hpk k r * Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r) * g = 1 := by
    calc (_root_.Formalism.QuantumDeterminants.Hpk k r * Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r) * g
        = _root_.Formalism.QuantumDeterminants.Hpk k r * (Matrix.conjTranspose g * _root_.Formalism.QuantumDeterminants.Hpk k r * g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h1, _root_.Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  exact Matrix.isUnit_det_of_left_inverse h2

open MeasureTheory Topology Filter in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma haar_isOpen_ne_zero_of_mem_Glev {k r : ℕ} {μ : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)}
    (hμ : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) μ) {V : Set (_root_.Formalism.QuantumDeterminants.Mt k r)} (hV : IsOpen V)
    {g₀ : _root_.Formalism.QuantumDeterminants.Mt k r} (hg₀ : Matrix.of g₀ ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) (hgV : g₀ ∈ V) :
    μ V ≠ 0 := by
  intro h0
  have hnull : ∀ a ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r), μ (_root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V) = 0 := by
    intro a ha
    rw [← Measure.map_apply (_root_.Formalism.FourierDecayAlt.P.B2x5.measurable_lmulM a) hV.measurableSet, hμ.left a ha, h0]
  obtain ⟨t, hts, htc, hteq⟩ := TopologicalSpace.isOpen_biUnion_countable
    (_root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) (fun a ↦ _root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V)
    (fun a _ ↦ hV.preimage (_root_.Formalism.QuantumDeterminants.BesselUnitaryEquiv.continuous_lmulM a))
  have hU : μ (⋃ a ∈ t, _root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V) = 0 :=
    (measure_biUnion_null_iff htc).2 fun a ha ↦ hnull a (hts ha)
  rw [hteq] at hU
  have hae : ∀ᵐ y ∂μ, y ∉ ⋃ a ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r), _root_.Formalism.QuantumDeterminants.lmulM a ⁻¹' V :=
    measure_eq_zero_iff_ae_notMem.1 hU
  have hfalse : ∀ᵐ _y ∂μ, False := by
    filter_upwards [hae, _root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy hyU
    apply hy
    refine Set.mem_iUnion₂.2 ⟨Matrix.of g₀ * (Matrix.of y)⁻¹,
      _root_.Formalism.FourierDecayAlt.P.Qx3.glev_mul hg₀ (_root_.Formalism.FourierDecayAlt.Q.TInvW.glev_inv hyU), ?_⟩
    show _root_.Formalism.QuantumDeterminants.lmulM _ y ∈ V
    unfold _root_.Formalism.QuantumDeterminants.lmulM
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_det_of_mem_Glev hyU), Matrix.mul_one]
    exact hgV
  exact hμ.ne_zero (ae_eq_bot.1 (Filter.eventually_false_iff_eq_bot.1 hfalse))

open MeasureTheory Topology Filter in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma zetaFunction_vanish_of_orthogonal_bumps_lemma {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
    (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) (hz' : _root_.Formalism.QuantumDeterminants.inWb k r z') (hT : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z) (hT' : 0 < _root_.Formalism.QuantumDeterminants.Tz k r z')
    (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt k r)) (c : Fin r → ℂ) (h : _root_.Formalism.FourierDecayAlt.Q.Mx k r → ℂ)
    (hμ : _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r)) μ)
    (hcont : ContinuousOn h {g | (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z'})
    (hfib : ∀ g g', (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z' → (c, g') ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z' →
      _root_.Formalism.FourierDecayAlt.P5.zeta k r z z' g = _root_.Formalism.FourierDecayAlt.P5.zeta k r z z' g' → h g = h g')
    (horth : ∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ {ζ | _root_.Formalism.QuantumDeterminants.Tz k r z * _root_.Formalism.QuantumDeterminants.Tz k r z' < Complex.normSq ζ} →
      ∫ y : _root_.Formalism.QuantumDeterminants.Mt k r, ((φ (_root_.Formalism.FourierDecayAlt.P5.zeta k r z z' (Matrix.of y)) : ℝ) : ℂ) * h (Matrix.of y) ∂μ = 0)
    (g₀ : _root_.Formalism.FourierDecayAlt.Q.Mx k r) (hg₀ : (c, g₀) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z') : h g₀ = 0 := by
  set TT := _root_.Formalism.QuantumDeterminants.Tz k r z * _root_.Formalism.QuantumDeterminants.Tz k r z' with hTT
  set ζf : _root_.Formalism.FourierDecayAlt.Q.Mx k r → ℂ := _root_.Formalism.FourierDecayAlt.Q.zetaL k r z z' (Fin.last r) with hζf
  have hζc : Continuous ζf := (_root_.Formalism.FourierDecayAlt.P.Qx5.zetaL_contDiff k r z z' (Fin.last r)).continuous
  have hzeta : ∀ g, _root_.Formalism.FourierDecayAlt.P5.zeta k r z z' g = ζf g := fun g ↦ rfl
  have hH : ∀ g, _root_.Formalism.FourierDecayAlt.Q.GGl k r z z' g = Complex.normSq (ζf g) - TT := fun g ↦ rfl
  have hD : ∀ g, (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z' ↔
      c ∈ _root_.Formalism.QuantumDeterminants.OmX r ∧ g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r) ∧ 0 < _root_.Formalism.FourierDecayAlt.Q.GGl k r z z' g := fun g ↦ Iff.rfl
  obtain ⟨hc, hg₀G, hg₀H⟩ := (hD g₀).1 hg₀
  by_contra hw
  set w := h g₀ with hwdef
  have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
  set ζ₀ := ζf g₀ with hζ₀
  set ε := (Complex.normSq ζ₀ - TT) / 2 with hε
  have hg₀H' : 0 < Complex.normSq ζ₀ - TT := by rw [hζ₀, ← hH]; exact hg₀H
  have hεpos : 0 < ε := by rw [hε]; linarith
  set R := ‖ζ₀‖ + 1 with hR
  set K := {g | g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r) ∧ ε ≤ _root_.Formalism.FourierDecayAlt.Q.GGl k r z z' g ∧ ‖ζf g‖ ≤ R} with hKdef
  have hK : IsCompact K := _root_.Formalism.FourierDecayAlt.P5.HerB.isCompact_zeta_le z z' hz hz' hT hT' ε R
  have hKD : K ⊆ {g | (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR k r z z'} := fun g hg ↦
    (hD g).2 ⟨hc, hg.1, lt_of_lt_of_le hεpos hg.2.1⟩
  set K' := K ∩ h ⁻¹' {x | ‖w‖ / 2 ≤ ‖x - w‖} with hK'def
  have hK'c : IsCompact K' := hK.of_isClosed_subset
    ((hcont.mono hKD).preimage_isClosed_of_isClosed hK.isClosed
      (isClosed_le continuous_const (continuous_norm.comp (continuous_sub_right w))))
    Set.inter_subset_left
  have hCc : IsCompact (ζf '' K') := hK'c.image hζc
  have hζ₀C : ζ₀ ∉ ζf '' K' := by
    rintro ⟨y, ⟨hyK, hyh⟩, hy⟩
    have hyw : h y = w := hfib y g₀ (hKD hyK) hg₀ (by rw [hzeta, hzeta, hy])
    have : ‖w‖ / 2 ≤ ‖h y - w‖ := hyh
    rw [hyw, sub_self, norm_zero] at this
    linarith
  obtain ⟨δ₁, hδ₁, hball₁⟩ := Metric.isOpen_iff.1 hCc.isClosed.isOpen_compl ζ₀ hζ₀C
  set O := {ζ : ℂ | TT + ε < Complex.normSq ζ} ∩ {ζ | ‖ζ‖ < R} with hOdef
  have hO : IsOpen O := (isOpen_lt continuous_const Complex.continuous_normSq).inter
    (isOpen_lt continuous_norm continuous_const)
  have hζ₀O : ζ₀ ∈ O := by
    refine ⟨?_, ?_⟩
    · show TT + ε < Complex.normSq ζ₀
      rw [hε]; linarith
    · show ‖ζ₀‖ < R
      rw [hR]; linarith
  obtain ⟨ρ, hρ, hballO⟩ := Metric.isOpen_iff.1 hO ζ₀ hζ₀O
  set δ := min δ₁ ρ with hδdef
  have hδ : 0 < δ := lt_min hδ₁ hρ
  let b : ContDiffBump ζ₀ := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
  have hball : ∀ ζ, ζ ∈ tsupport b → ζ ∈ Metric.ball ζ₀ δ := by
    intro ζ hζ
    rw [b.tsupport_eq] at hζ
    exact Metric.closedBall_subset_ball (show δ / 2 < δ by linarith) hζ
  have hballC : Metric.ball ζ₀ δ ⊆ (ζf '' K')ᶜ :=
    (Metric.ball_subset_ball (min_le_left _ _)).trans hball₁
  have hballO' : Metric.ball ζ₀ δ ⊆ O := (Metric.ball_subset_ball (min_le_right _ _)).trans hballO
  have hgood : ∀ g, g ∈ _root_.Formalism.FourierDecayAlt.Q.Glev k r (Fin.last r) → b (ζf g) ≠ 0 →
      g ∈ K ∧ ‖h g - w‖ < ‖w‖ / 2 := by
    intro g hg hb
    have hmem : ζf g ∈ Metric.ball ζ₀ δ := hball _ (subset_tsupport _ hb)
    have hO' := hballO' hmem
    have h1 : TT + ε < Complex.normSq (ζf g) := hO'.1
    have h2 : ‖ζf g‖ < R := hO'.2
    have hgK : g ∈ K := ⟨hg, by rw [hH]; linarith, le_of_lt h2⟩
    refine ⟨hgK, ?_⟩
    by_contra hlt
    exact hballC hmem ⟨g, ⟨hgK, le_of_not_gt hlt⟩, rfl⟩
  have hre : ∀ g, ‖h g - w‖ < ‖w‖ / 2 → 0 < (star w * h g).re := by
    intro g hg
    have hsplit : (star w * h g).re = (star w * w).re + (star w * (h g - w)).re := by
      rw [← Complex.add_re, ← mul_add, add_sub_cancel]
    have hww : (star w * w).re = ‖w‖ ^ 2 := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
        Complex.normSq_eq_norm_sq]
    have hlow : -(‖w‖ * ‖h g - w‖) ≤ (star w * (h g - w)).re := by
      have h3 := Complex.abs_re_le_norm (star w * (h g - w))
      rw [norm_mul, norm_star] at h3
      linarith [neg_abs_le (star w * (h g - w)).re]
    have h4 : ‖w‖ * ‖h g - w‖ ≤ ‖w‖ * (‖w‖ / 2) :=
      mul_le_mul_of_nonneg_left hg.le hwpos.le
    nlinarith
  have hof : Continuous (fun y : _root_.Formalism.QuantumDeterminants.Mt k r ↦ (Matrix.of y : _root_.Formalism.FourierDecayAlt.Q.Mx k r)) := continuous_id
  set F : _root_.Formalism.QuantumDeterminants.Mt k r → ℂ := fun y ↦ ((b (ζf (Matrix.of y)) : ℝ) : ℂ) * h (Matrix.of y) with hFdef
  have hint0 : ∫ y, F y ∂μ = 0 := horth b b.contDiff b.hasCompactSupport (fun ζ hζ ↦ by
    have h1 : TT + ε < Complex.normSq ζ := (hballO' (hball ζ hζ)).1
    show TT < Complex.normSq ζ
    linarith)
  set Kt : Set (_root_.Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ K} with hKtdef
  have hKt : IsCompact Kt := hK
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun S hS ↦ hμ.finite_compact S hS⟩
  have hFc : ContinuousOn F Kt :=
    (Complex.continuous_ofReal.comp (b.continuous.comp (hζc.comp hof))).continuousOn.mul
      ((hcont.mono hKD).comp hof.continuousOn fun y hy ↦ hy)
  have hIon : IntegrableOn F Kt μ := hFc.integrableOn_compact hKt
  have hae : F =ᵐ[μ] Kt.indicator F := by
    filter_upwards [_root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy
    by_cases hyK : y ∈ Kt
    · rw [Set.indicator_of_mem hyK]
    · rw [Set.indicator_of_notMem hyK]
      have hb0 : b (ζf (Matrix.of y)) = 0 := by
        by_contra hb
        exact hyK (hgood _ hy hb).1
      simp [hFdef, hb0]
  have hFint : Integrable F μ :=
    ((integrable_indicator_iff hKt.measurableSet).2 hIon).congr hae.symm
  set f : _root_.Formalism.QuantumDeterminants.Mt k r → ℝ := fun y ↦ (star w * F y).re with hfdef
  have hfint : Integrable f μ := (hFint.const_mul (star w)).re
  have hfint0 : ∫ y, f y ∂μ = 0 := by
    have e := ContinuousLinearMap.integral_comp_comm Complex.reCLM (hFint.const_mul (star w))
    simp only [Complex.reCLM_apply] at e
    rw [hfdef, e, integral_const_mul, hint0, mul_zero, Complex.zero_re]
  have hfval : ∀ y, f y = b (ζf (Matrix.of y)) * (star w * h (Matrix.of y)).re := by
    intro y
    simp only [hfdef, hFdef]
    rw [mul_left_comm, Complex.re_ofReal_mul]
  have hfnn : 0 ≤ᵐ[μ] f := by
    filter_upwards [_root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy
    rw [Pi.zero_apply, hfval]
    by_cases hb : b (ζf (Matrix.of y)) = 0
    · rw [hb, zero_mul]
    · exact mul_nonneg (b.nonneg) (hre _ (hgood _ hy hb).2).le
  have hf0 : f =ᵐ[μ] 0 := (integral_eq_zero_iff_of_nonneg_ae hfnn hfint).1 hfint0
  set V : Set (_root_.Formalism.QuantumDeterminants.Mt k r) := {y | ζf (Matrix.of y) ∈ Metric.ball ζ₀ (δ / 4)} with hVdef
  have hVo : IsOpen V := Metric.isOpen_ball.preimage (hζc.comp hof)
  have hg₀V : (g₀ : _root_.Formalism.QuantumDeterminants.Mt k r) ∈ V := Metric.mem_ball_self (by positivity)
  refine haar_isOpen_ne_zero_of_mem_Glev hμ hVo (g₀ := g₀) hg₀G hg₀V ?_
  refine measure_eq_zero_iff_ae_notMem.2 ?_
  filter_upwards [hf0, _root_.Formalism.FourierDecayAlt.P.B5.haar_ae hμ] with y hy0 hyG hyV
  have hb1 : b (ζf (Matrix.of y)) = 1 := b.one_of_mem_closedBall (Metric.ball_subset_closedBall hyV)
  have hpos := hre _ (hgood _ hyG (by rw [hb1]; exact one_ne_zero)).2
  have : f y = 0 := hy0
  rw [hfval, hb1, one_mul] at this
  linarith

theorem _root_.GlobalTheory.HatNF.ZetaVanish.zeta_vanish : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq) (μ : Measure (_root_.Formalism.QuantumDeterminants.Mt P.k P.r)) (c : Fin P.r → ℂ) (h : _root_.Formalism.FourierDecayAlt.Q.Mx P.k P.r → ℂ), _root_.Formalism.FourierDecayAlt.B.IsHaarOn (_root_.Formalism.FourierDecayAlt.Q.Glev P.k P.r (Fin.last P.r)) μ → ContinuousOn h {g | (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z'} → (∀ g g', (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z' → (c, g') ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z' → _root_.Formalism.FourierDecayAlt.P5.zeta P.k P.r Bs.z Bs.z' g = _root_.Formalism.FourierDecayAlt.P5.zeta P.k P.r Bs.z Bs.z' g' → h g = h g') → (∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ {ζ | _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z * _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z' < Complex.normSq ζ} → ∫ y : _root_.Formalism.QuantumDeterminants.Mt P.k P.r, ((φ (_root_.Formalism.FourierDecayAlt.P5.zeta P.k P.r Bs.z Bs.z' (Matrix.of y)) : ℝ) : ℂ) * h (Matrix.of y) ∂μ = 0) → ∀ g, (c, g) ∈ _root_.Formalism.FourierDecayAlt.Q.DomR P.k P.r Bs.z Bs.z' → h g = 0 := by
  intro Wp Wq _ _ _ _ _ _ P Bs μ c h hμ hcont hfib horth g hg
  have hT : 0 < _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z := by
    obtain ⟨⟩ := Bs
    assumption
  have hT' : 0 < _root_.Formalism.QuantumDeterminants.Tz P.k P.r Bs.z' := by
    obtain ⟨⟩ := Bs
    assumption
  exact zetaFunction_vanish_of_orthogonal_bumps_lemma Bs.z_mem Bs.z'_mem hT hT' μ c h hμ hcont hfib horth g hg

end GlobalTheory.HatNF.ZetaVanish
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjRaisingProjEqSmul
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.RaiseFormula

variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]

theorem up_unique {j : ℕ} {a b c : M.Ty P} (h : M.Up P j a b) (h' : M.Up P j a c) : b = c := by
  funext i
  exact Fin.ext ((h i).trans (h' i).symm)

theorem up_index {l j : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b)
    (h' : M.Up P j a b) : j = l := by
  rw [Finset.mem_Icc] at hl
  have h1 := h ⟨l - 1, by omega⟩
  have h2 := h' ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1 h2
  by_contra hne
  rw [if_neg (fun x => hne x.symm)] at h2
  omega

theorem up_ne {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) {a b : M.Ty P} (h : M.Up P l a b) : b ≠ a := by
  rw [Finset.mem_Icc] at hl
  rintro rfl
  have h1 := h ⟨l - 1, by omega⟩
  have e : l - 1 + 1 = l := by omega
  simp only [e, if_true] at h1
  omega

omit [StarRing A] in
theorem sum_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) : ∑ ρ, NF.proj κ ρ = 1 := by
  unfold NF.proj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_one κ]
  congr 1
  funext x
  simp [Finset.sum_apply]

omit [StarRing A] in
theorem kap_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (f : M.Ty P → ℂ) (ρ : M.Ty P) :
    κ f * NF.proj κ ρ = f ρ • NF.proj κ ρ := by
  unfold NF.proj
  rw [← map_mul, ← map_smul]
  congr 1
  funext x
  by_cases h : x = ρ <;> simp [h]

omit [StarRing A] in
theorem proj_mul_proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) {ρ ρ' : M.Ty P} (h : ρ' ≠ ρ) :
    NF.proj κ ρ' * NF.proj κ ρ = 0 := by
  have := kap_mul_proj κ (fun x => if x = ρ' then 1 else 0) ρ
  rw [if_neg (Ne.symm h), zero_smul] at this
  exact this

theorem proj_SS_proj (d : Q.NFData P A) (hd : d.Rel) {j : ℕ} {ρ ρ' : M.Ty P} (h : ¬ M.Up P j ρ ρ') :
    NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ = 0 := by
  have h1 := hd.2.2.2.1 j (fun a => if M.Up P j a ρ' then 1 else 0) (fun x => if x = ρ' then 1 else 0) (by
    intro a b hab
    by_cases hb : b = ρ'
    · subst hb; simp [hab]
    · have : ¬ M.Up P j a ρ' := fun h' => hb (up_unique hab h')
      simp [hb, this])
  have h2 : NF.proj d.κ ρ' * d.SS j = _ := h1
  rw [h2, mul_assoc, kap_mul_proj, if_neg h, zero_smul, mul_zero]

theorem proj_raising_proj_eq_smul (d : Q.NFData P A) (hd : d.Rel) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1)) (Y : ℂ)
    {ρ ρ' : M.Ty P} (h : M.Up P l ρ ρ') :
    NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ =
      M.xEx P {l} ρ Y • (NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ) := by
  have hq : d.QQ Y 1 0 = d.L.GG * d.x Y * d.L.l0 Y + d.weightedSumBis Y := rfl
  have hc : ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (NF.proj d.κ ρ') g := fun g hg => hd.2.1 _ g hg
  have c1 : Commute (NF.proj d.κ ρ') d.L.GG := hc _ (by simp [LevelData.fns])
  have c2 : Commute (NF.proj d.κ ρ') d.L.GGi := hc _ (by simp [LevelData.fns])
  have c3 : Commute (NF.proj d.κ ρ') d.L.ζb := hc _ (by simp [LevelData.fns])
  have c4 : Commute (NF.proj d.κ ρ') d.L.nab := hc _ (by simp)
  have c5 : Commute (NF.proj d.κ ρ') (d.x Y) := by
    unfold NF.proj Q.NFData.x
    exact (Commute.all _ _).map d.κ
  have c6 : Commute (NF.proj d.κ ρ') (d.L.l0 Y) := by
    unfold LevelData.l0
    exact c4.neg_right.sub_right ((Algebra.commute_algebraMap_right _ _).mul_right (c3.mul_right c2))
  have c7 := (c1.mul_right c5).mul_right c6
  rw [hq, mul_add, add_mul, c7.eq, mul_assoc _ (NF.proj d.κ ρ'), proj_mul_proj _ (up_ne hl h), mul_zero, zero_add]
  unfold Q.NFData.weightedSumBis
  have key : ∀ j, NF.proj d.κ ρ' * (d.SS j * d.κ fun ρ => M.xEx P {j} ρ Y) * NF.proj d.κ ρ =
      M.xEx P {j} ρ Y • (NF.proj d.κ ρ' * d.SS j * NF.proj d.κ ρ) := by
    intro j
    rw [← mul_assoc, mul_assoc _ (d.κ _), kap_mul_proj, mul_smul_comm]
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_eq_single l]
  · exact key l
  · intro j _ hj
    rw [key, proj_SS_proj d hd (fun h' => hj (up_index hl h h')), smul_zero]
  · intro h'; exact absurd hl h'

theorem xEx_ne_zero (ex : Finset ℕ) (ρ : M.Ty P) (Y : ℂ) (h : M.xC P ρ Y ≠ 0) : M.xEx P ex ρ Y ≠ 0 := by
  unfold M.xC at h
  unfold M.xEx
  rw [Finset.prod_ne_zero_iff] at h ⊢
  exact fun i hi => h i (Finset.mem_sdiff.1 hi).1

theorem ss_formula : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ Y : ℂ, (∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0) → ∃ co : M.Ty P → M.Ty P → ℂ, d.SS l = ∑ ρ, ∑ ρ', co ρ ρ' • (NF.proj d.κ ρ' * d.QQ Y 1 0 * NF.proj d.κ ρ) := by
  intro P A _ _ _ _ d hd l hl Y hY
  have hr : d.Rel := hd.2.2.1
  refine ⟨fun ρ ρ' => if M.Up P l ρ ρ' then (M.xEx P {l} ρ Y)⁻¹ else 0, ?_⟩
  have h0 : d.SS l = ∑ ρ, ∑ ρ', NF.proj d.κ ρ' * d.SS l * NF.proj d.κ ρ := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
    rw [sum_proj, one_mul, mul_one]
  refine h0.trans (Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun ρ' _ => ?_)
  by_cases h : M.Up P l ρ ρ'
  · simp only [if_pos h]
    rw [proj_raising_proj_eq_smul d hr hl Y h, smul_smul, inv_mul_cancel₀ (xEx_ne_zero _ _ _ (hY ρ)), one_smul]
  · simp only [if_neg h]
    rw [zero_smul, proj_SS_proj d hr h]

end GlobalTheory.HatNF.RaiseFormula
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DoubleCosetOfZetaEq
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF

theorem doubleCoset_of_zeta_eq :
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (c : Fin P.r → ℂ) (g g' : Q.Mx P.k P.r), (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' → (c, g') ∈ Q.DomR P.k P.r Bs.z Bs.z' → P5.zeta P.k P.r Bs.z Bs.z' g = P5.zeta P.k P.r Bs.z Bs.z' g' → ∃ h ∈ UWset P.k P.r Bs.z, ∃ h' ∈ UWset P.k P.r Bs.z', g' = h * g * h' := by
  intro Wp Wq _ _ _ _ _ _ P Bs c g g' hg hg' hζ
  obtain ⟨a, ha, b, hb, e⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec
    hg.2.1 hg.2.2
  obtain ⟨a', ha', b', hb', e'⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp Bs.k_pos Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos Bs.sec
    hg'.2.1 hg'.2.2
  unfold P5.zeta at hζ
  dsimp only at e e'
  rw [← hζ] at e'
  generalize NF.muZ P.k P.r Bs.μsec (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g) = m at e e'
  refine ⟨a' * a⁻¹, Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul ha' (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv ha), b⁻¹ * b',
    Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul (Formalism.FourierDecayAlt.P.BigCellInversePair.uw_inv hb) hb', ?_⟩
  have h1 := Formalism.FourierDecayAlt.P.NFRadRedS.uw_inv_mul ha
  have h2 := Formalism.FourierDecayAlt.P.NFRadRedS.uw_mul_inv hb
  rw [e', e]
  calc a' * m * b' = a' * (a⁻¹ * a) * m * (b * b⁻¹) * b' := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one]
    _ = a' * a⁻¹ * (a * m * b) * (b⁻¹ * b') := by simp only [Matrix.mul_assoc]

end GlobalTheory.HatNF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialRaisingOperatorsPointwiseAdjointPair
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ComplexConjugate InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.HatNF.RaiseAdj

open Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section gen

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)}

def Van (c : Fin r → ℂ) (K : Set (Q.Mx k r)) (Φ : Q.RadSp k r z z' π π') : Prop :=
  ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K → (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g = 0

theorem int_left {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hKc : IsCompact K) (hKG : K ⊆ {g | 0 < Q.GGl k r z z' g})
    (Φ Ψ : Q.RadSp k r z z' π π') (hΦ : Van c K Φ) :
    Integrable (fun x : Mt k r => B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ := by
  simp only [hsInner_eq_sum]
  exact integrable_finsetSum _ fun m _ => int_cpt_gen μ hμ Φ Ψ c _ K hKc hKG hc _ (Or.inr rfl) hΦ

theorem int_right {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hKc : IsCompact K) (hKG : K ⊆ {g | 0 < Q.GGl k r z z' g})
    (Φ Ψ : Q.RadSp k r z z' π π') (hΨ : Van c K Ψ) :
    Integrable (fun x : Mt k r => B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))
      ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of x))) μ := by
  simp only [hsInner_eq_sum]
  exact integrable_finsetSum _ fun m _ => int_cpt_gen μ hμ Ψ Φ c _ K hKc hKG hc _ (Or.inl rfl) hΨ

def adjSub {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Q.Glev k r (Fin.last r)) μ) {c : Fin r → ℂ}
    (hc : c ∈ OmX r) {K : Set (Q.Mx k r)} (hKc : IsCompact K) (hKG : K ⊆ {g | 0 < Q.GGl k r z z' g})
    (Φ Ψ : Q.RadSp k r z z' π π') (hΦ : Van c K Φ) (hΨ : Van c K Ψ) :
    Submodule ℂ (Q.Pr (Q.RadSp k r z z' π π')) where
  carrier := {b | pairAt μ (b.1 Φ) Ψ c = pairAt μ Φ ((star b).1 Ψ) c}
  zero_mem' := by
    show pairAt μ 0 Ψ c = pairAt μ Φ 0 c
    have h1 := pairAt_smul_left μ (0 : Q.RadSp k r z z' π π') Ψ c 0
    have h2 := pairAt_smul_right μ Φ (0 : Q.RadSp k r z z' π π') c 0
    simp only [zero_smul, zero_mul, map_zero] at h1 h2
    rw [h1, h2]
  add_mem' := by
    intro a b ha hb
    show pairAt μ (a.1 Φ + b.1 Φ) Ψ c = pairAt μ Φ ((star a).1 Ψ + (star b).1 Ψ) c
    have h1 := pairAt_add_smul_left μ (a.1 Φ) (b.1 Φ) Ψ c 1 (int_right hμ hc hKc hKG _ _ hΨ)
      (int_right hμ hc hKc hKG _ _ hΨ)
    have h2 := pairAt_add_smul_left μ ((star a).1 Ψ) ((star b).1 Ψ) Φ c 1 (int_right hμ hc hKc hKG _ _ hΦ)
      (int_right hμ hc hKc hKG _ _ hΦ)
    simp only [one_smul, one_mul] at h1 h2
    rw [h1, pairAt_swap μ _ Φ, h2, map_add (f := _), ← pairAt_swap, ← pairAt_swap]
    exact congrArg₂ _ ha hb
  smul_mem' := by
    intro s b hb
    show pairAt μ ((s • b).1 Φ) Ψ c = pairAt μ Φ ((star (s • b)).1 Ψ) c
    rw [star_smul, Formalism.FourierDecayAlt.P.NFx4.NO.fst_smul, Formalism.FourierDecayAlt.P.NFx4.NO.fst_smul, LinearMap.smul_apply, LinearMap.smul_apply,
      pairAt_smul_left, pairAt_smul_right]
    have hb' : pairAt μ (b.1 Φ) Ψ c = pairAt μ Φ ((star b).1 Ψ) c := hb
    rw [hb']
    simp

theorem exists_compact (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    {S : Set ℂ} (hS : IsCompact S) (hS' : S ⊆ {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ}) :
    ∃ K : Set (Q.Mx k r), IsCompact K ∧ K ⊆ {g | 0 < Q.GGl k r z z' g} ∧
      ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K → Q.zetaL k r z z' (Fin.last r) g ∉ S := by
  obtain ⟨ε, hε, h1⟩ := hS.exists_forall_le' (f := fun ζ => Complex.normSq ζ - Tz k r z * Tz k r z') (a := 0)
    (Complex.continuous_normSq.sub continuous_const).continuousOn (fun b hb => sub_pos.2 (hS' hb))
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  exact ⟨_, isCompact_zeta_le z z' hz hz' hT hT' ε R, fun g hg => lt_of_lt_of_le hε hg.2.1,
    fun g hg hgK h => hgK ⟨hg, h1 _ h, hR _ h⟩⟩

theorem van_mulZ {W : Module.End ℂ (Q.RadSp k r z z' π π')} {φ : ℂ → ℝ} (hW : NF.IsMulZ W fun ζ => (φ ζ : ℂ))
    {S : Set ℂ} (hS : tsupport φ ⊆ S) {K : Set (Q.Mx k r)}
    (hK : ∀ g ∈ Q.Glev k r (Fin.last r), g ∉ K → Q.zetaL k r z z' (Fin.last r) g ∉ S) (c : Fin r → ℂ)
    (Φ : Q.RadSp k r z z' π π') : Van c K (W Φ) := by
  intro g hg hgK
  rw [Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hW, image_eq_zero_of_notMem_tsupport (fun h => hK g hg hgK (hS h))]
  simp

theorem contOn_hs (Φ Ψ : Q.RadSp k r z z' π π') (c : Fin r → ℂ) :
    ContinuousOn (fun g : Q.Mx k r => B.hsInner ((Φ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)
      ((Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) c g)) {g | (c, g) ∈ Q.DomR k r z z'} := by
  have hA : ∀ (Ξ : Q.RadSp k r z z' π π') (v : Wq), ContinuousOn
      (fun g : Q.Mx k r => (Ξ : Q.Fn k r (Wq →L[ℂ] Wp)) c g v) {g | (c, g) ∈ Q.DomR k r z z'} := by
    intro Ξ v
    have h1 := (radSp_continuousOn Ξ).comp
      ((continuous_const.prodMk continuous_id : Continuous fun g : Q.Mx k r => (c, g)).continuousOn :
        ContinuousOn _ {g | (c, g) ∈ Q.DomR k r z z'}) (fun x hx => hx)
    exact h1.clm_apply continuousOn_const
  simp only [hsInner_eq_sum]
  exact continuousOn_finsetSum _ fun m _ => (hA Ψ _).inner (hA Φ _)

end gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
  {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem pairAt_of_ptAdj {b : RA P Bs} (hb : PtAdj P Bs b) (μ : Measure (Mt P.k P.r))
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) :
    pairAt μ (b.1 Φ) Ψ c = pairAt μ Φ ((star b).1 Ψ) c := by
  unfold pairAt
  congr 1
  funext x
  by_cases hx : (c, Matrix.of x) ∈ Q.DomR P.k P.r Bs.z Bs.z'
  · exact hb Φ Ψ _ hx
  · rw [radSp_zero_off (b.1 Φ) hx, radSp_zero_off Φ hx, hsInner_zero_left, hsInner_zero_left]

theorem hs_inv (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g g' : Q.Mx P.k P.r)
    (hg : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z') (hg' : (c, g') ∈ Q.DomR P.k P.r Bs.z Bs.z')
    (hζ : P5.zeta P.k P.r Bs.z Bs.z' g = P5.zeta P.k P.r Bs.z Bs.z' g') :
    B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) =
      B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g') ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g') := by
  obtain ⟨h, hh, h', hh', rfl⟩ := GlobalTheory.HatNF.doubleCoset_of_zeta_eq Wp Wq P Bs c g g' hg hg' hζ
  have e1 := Φ.2.2.2 (c, g) hg h hh h' hh'
  have e2 := Ψ.2.2.2 (c, g) hg h hh h' hh'
  simp only at e1 e2
  rw [e1, e2, Formalism.FourierDecayAlt.P.PBI.hsInner_comp_left _ (Bs.π_unitary _ hh),
    Formalism.FourierDecayAlt.P.PBI.hsInner_comp_right _ (Bs.π'_unitary _ hh')]

theorem triple (μ : Measure (Mt P.k P.r)) (c : Fin P.r → ℂ) (a t b : RA P Bs) (ha : PtAdj P Bs a)
    (hb : PtAdj P Bs b) (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (ht : pairAt μ (t.1 (b.1 Φ)) ((star a).1 Ψ) c = pairAt μ (b.1 Φ) ((star t).1 ((star a).1 Ψ)) c) :
    pairAt μ ((a * t * b).1 Φ) Ψ c = pairAt μ Φ ((star (a * t * b)).1 Ψ) c :=
  ((pairAt_of_ptAdj ha μ (t.1 (b.1 Φ)) Ψ c).trans ht).trans (pairAt_of_ptAdj hb μ Φ _ c)

theorem ptAdj_SS : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), PtAdj P Bs (d.SS l) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hNF l hl
  have hP := hD.1
  have hμ := hD.2.1
  have hH := (GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hNF).1
  have hκ := fun f => (GlobalTheory.HatNF.kappa_ptAdj_ptB Wp Wq P Bs X μ L st l0 d hD hNF f).1
  obtain ⟨co, hco⟩ := GlobalTheory.HatNF.RaiseFormula.ss_formula P _ d hH l hl Complex.I
    (fun ρ => Formalism.FourierDecayAlt.P.NFx4.SX.xC_ne ρ _ (by simp))

  have hmul : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → ∃ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'),
      NF.IsMulZ W (fun ζ => (φ ζ : ℂ)) ∧ (∀ g, Commute (d.κ g).1 W) ∧ Commute (d.SS l).1 W ∧
        Commute (star (d.SS l)).1 W := by
    intro φ hφ
    have hf : ContDiff ℝ ∞ (fun ζ => (φ ζ : ℂ)) := Complex.ofRealCLM.contDiff.comp hφ
    obtain ⟨W, hW⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P _ _ _ _ hP _ hf.contDiffOn
    obtain ⟨W1, hW1⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P _ _ _ _ hP _ (dZ_contDiff hf).contDiffOn
    obtain ⟨W2, hW2⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P _ _ _ _ hP _ (dZb_contDiff hf).contDiffOn
    have h := Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P _ _ _ _ hP X d hNF.1 hNF.2.1 hNF.2.2.1 hNF.2.2.2 _
      hf.contDiffOn W W1 W2 hW hW1 hW2
    exact ⟨W, hW, h.1, (h.2.1 l hl).1, (h.2.1 l hl).2⟩
  rintro Φ Ψ ⟨c, g0⟩ hx
  have hc : c ∈ OmX P.r := hx.1
  have hO : IsOpen {ζ : ℂ | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  obtain ⟨ψ, hψS, hψc, hψd, -, hψ1⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (x := P5.zeta P.k P.r Bs.z Bs.z' g0) (hO.mem_nhds (sub_pos.1 hx.2.2))
  obtain ⟨V, hV, hVκ, hVS, hVS'⟩ := hmul ψ hψd
  have key := GlobalTheory.HatNF.ZetaVanish.zeta_vanish Wp Wq P Bs μ c (fun g =>
    B.hsInner (((d.SS l).1 Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) ((V Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g) -
    B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g)
      (((star (d.SS l)).1 (V Ψ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g)) hμ
    ((contOn_hs _ _ c).sub (contOn_hs _ _ c))
    (fun g g' hg hg' hζ => by rw [hs_inv _ _ c g g' hg hg' hζ, hs_inv Φ _ c g g' hg hg' hζ]) ?_ g0 hx
  · have e : (star (d.SS l)).1 (V Ψ) = V ((star (d.SS l)).1 Ψ) := LinearMap.congr_fun hVS'.eq Ψ
    rw [e, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hV, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hV] at key
    unfold P5.zeta at hψ1
    rw [hψ1, Complex.ofReal_one, one_smul, one_smul] at key
    exact sub_eq_zero.1 key
  intro φ hφd hφc hφS
  obtain ⟨W, hW, hWκ, hWS, hWS'⟩ := hmul φ hφd
  obtain ⟨K, hKc, hKG, hK⟩ := exists_compact Bs.z_mem Bs.z'_mem Bs.T_pos Bs.T'_pos
    (hφc.isCompact.union hψc.isCompact) (Set.union_subset hφS hψS)
  have vW := van_mulZ hW Set.subset_union_left hK c
  have vV := van_mulZ hV Set.subset_union_right hK c
  have hmem : d.SS l ∈ adjSub hμ hc hKc hKG (W Φ) (V Ψ) (vW Φ) (vV Ψ) := by
    rw [hco]
    refine Submodule.sum_mem _ fun ρ _ => Submodule.sum_mem _ fun ρ' _ => Submodule.smul_mem _ _ ?_
    rw [← hNF.2.2.2]
    refine triple μ c _ _ _ (hκ _) (hκ _) _ _ ?_
    refine pairAt_t_adj_cpt' P _ _ _ _ hP X μ hμ _ _ c hc ⟨K, hKc, hKG, fun g hg hgK => ⟨?_, ?_⟩⟩ Complex.I 1 0
    · have e := LinearMap.congr_fun (hWκ fun ρ' => if ρ' = ρ then 1 else 0).eq Φ
      simp only [Module.End.mul_apply] at e
      rw [e]
      exact vW _ g hg hgK
    · rw [hNF.2.2.1.1]
      have e := LinearMap.congr_fun (hVκ fun ρ => star (if ρ = ρ' then (1 : ℂ) else 0)).eq Ψ
      simp only [Module.End.mul_apply] at e
      rw [e]
      exact vV _ g hg hgK
  have hm : pairAt μ ((d.SS l).1 (W Φ)) (V Ψ) c = pairAt μ (W Φ) ((star (d.SS l)).1 (V Ψ)) c := hmem
  have e : (d.SS l).1 (W Φ) = W ((d.SS l).1 Φ) := LinearMap.congr_fun hWS.eq Φ
  rw [e] at hm
  have hs := integral_sub (int_left hμ hc hKc hKG (W ((d.SS l).1 Φ)) (V Ψ) (vW _))
    (int_left hμ hc hKc hKG (W Φ) ((star (d.SS l)).1 (V Ψ)) (vW _))
  unfold pairAt at hm
  rw [hm, sub_self] at hs
  rw [← hs]
  congr 1
  funext y
  rw [Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hW, Formalism.FourierDecayAlt.P.NFx4.mulZ_apply hW, hsInner_smul_left', hsInner_smul_left', mul_sub]
  rfl

end GlobalTheory.HatNF.RaiseAdj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialRaisingOperatorsPointwiseAdjointPairStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radialRaisingOperators_pointwiseAdjointPair : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ l ∈ Finset.Icc 1 (P.k - 1), PtAdj P Bs (d.SS l) := by
  first | exact @GlobalTheory.HatNF.RaiseAdj.ptAdj_SS | exact GlobalTheory.HatNF.RaiseAdj.ptAdj_SS | (intros; apply GlobalTheory.HatNF.RaiseAdj.ptAdj_SS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedOfMemBoundedFactorsMonoid
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.BoundedFactors

theorem star_prod_ofFn {A : Type} [Ring A] [StarRing A] {r : ℕ} (f g : Fin r → A)
    (h : ∀ l, star (f l) = g l) (hc : ∀ l m, Commute (g l) (g m)) :
    star (List.ofFn f).prod = (List.ofFn g).prod := by
  induction r with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, star_mul, h,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun l => h _) (fun l m => hc _ _)]
    refine (Commute.list_prod_left _ _ ?_).eq
    intro x hx
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact hc _ _

theorem star_phase {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {r : ℕ} (L : LevelData A r)
    (hc : ∀ l, star (L.c l) = L.cb l) (hi : ∀ l, star (L.ci l) = L.cbi l) :
    star (L.Drb * L.Dri) = L.Dr * L.Drbi := by
  have h1 : star L.Drb = L.Dr :=
    star_prod_ofFn _ _ (fun l => by rw [← hc l, star_star])
      (fun l m => L.fns_comm _ (by simp) _ (by simp))
  have h2 : star L.Dri = L.Drbi :=
    star_prod_ofFn _ _ hi (fun l m => L.fns_comm _ (by simp) _ (by simp))
  rw [star_mul, h1, h2]
  refine (Commute.list_prod_left _ _ ?_).eq
  intro x hx
  obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
  refine Commute.list_prod_right _ _ ?_
  intro y hy
  obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hy
  exact L.fns_comm _ (by simp) _ (by simp)

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
  {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem hsInner_self_norm (A : Wq →L[ℂ] Wp) : ‖B.hsInner A A‖ = ‖B.hsVec A‖ ^ 2 := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K]
  simp

theorem hsInner_norm_le (A C : Wq →L[ℂ] Wp) : ‖B.hsInner A C‖ ≤ ‖B.hsVec A‖ * ‖B.hsVec C‖ := by
  unfold B.hsInner
  rw [mul_comm]
  exact norm_inner_le_norm _ _

theorem ptB_of_star_mul_self (b : RA P Bs) (ha : PtAdj P Bs b) (hb : PtB P Bs (star b * b)) : PtB P Bs b := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun Φ x hx => ?_⟩
  have h1 := ha Φ (b.1 Φ) x hx
  have h2 : nv ((star b).1 (b.1 Φ)) x ≤ C * nv Φ x := h Φ x hx
  have h3 : nv (b.1 Φ) x ^ 2 ≤ nv Φ x * nv ((star b).1 (b.1 Φ)) x := by
    unfold nv
    rw [← hsInner_self_norm, h1]
    exact hsInner_norm_le _ _
  have h0 : 0 ≤ nv Φ x := norm_nonneg _
  have h4 : nv (b.1 Φ) x ^ 2 ≤ (Real.sqrt C * nv Φ x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hC]
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) h0) two_ne_zero).1 h4

theorem ptB_star (b : RA P Bs) (ha : PtAdj P Bs b) (hb : PtB P Bs b) : PtB P Bs (star b) := by
  obtain ⟨C, hC, h⟩ := hb
  refine ⟨C, hC, fun Ψ x hx => ?_⟩
  have h1 := ha ((star b).1 Ψ) Ψ x hx
  have h2 := h ((star b).1 Ψ) x hx
  have h3 : nv ((star b).1 Ψ) x ^ 2 ≤ nv (b.1 ((star b).1 Ψ)) x * nv Ψ x := by
    unfold nv
    rw [← hsInner_self_norm, ← h1]
    exact hsInner_norm_le _ _
  have h0 : 0 ≤ nv Ψ x := norm_nonneg _
  have h0' : 0 ≤ nv ((star b).1 Ψ) x := norm_nonneg _
  rcases h0'.eq_or_lt with he | hp
  · rw [← he]; exact mul_nonneg hC h0
  · have h4 : nv ((star b).1 Ψ) x * nv ((star b).1 Ψ) x ≤ nv ((star b).1 Ψ) x * (C * nv Ψ x) := by
      nlinarith [mul_le_mul_of_nonneg_right h2 h0]
    exact le_of_mul_le_mul_left h4 hp

end

theorem ptB_of_mem_bmon : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ b ∈ bmon d, PtB P Bs b := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN
  obtain ⟨⟨-, -, hRel, -, hc, hi, -⟩, -⟩ := GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN
  have hκ := GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded Wp Wq P Bs X μ L st l0 d hD hN
  obtain ⟨⟨h1, hmul⟩, hζi, hζbi, hD1, hD2, hD3, hD4, -⟩ := GlobalTheory.T.pointwise_bounded_radial_ops_closure_and_functions Wp Wq P Bs X μ L st l0 d hD hN
  have hS := GlobalTheory.T.radialRaisingOperators_pointwiseAdjointPair Wp Wq P Bs X μ L st l0 d hD hN
  have hSb : ∀ l ∈ Finset.Icc 1 (P.k - 1), PtB P Bs (d.SS l) := fun l hl =>
    ptB_of_star_mul_self _ (hS l hl) (by rw [hRel.2.2.2.2.2 l hl]; exact (hκ _).2)
  have hSs : ∀ l ∈ Finset.Icc 1 (P.k - 1), PtB P Bs (star (d.SS l)) := fun l hl =>
    ptB_star _ (hS l hl) (hSb l hl)
  intro b hb
  induction hb using Submonoid.closure_induction with
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul _ _ hx hy
  | mem x hx =>
    rcases hx with ((hx | ⟨f, rfl⟩) | ⟨l, hl, rfl⟩) | ⟨l, hl, rfl⟩
    · rcases hx with rfl | rfl | rfl | rfl
      exacts [hζi, hζbi, hD1, hD2]
    · exact (hκ f).2
    · exact hmul _ _ hD3 (hSb l (by simpa using hl))
    · show PtB P Bs (star (d.L.Drb * d.L.Dri * d.SS l))
      rw [star_mul, star_phase d.L hc hi]
      exact hmul _ _ (hSs l (by simpa using hl)) hD4

end GlobalTheory.HatNF.BoundedFactors
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PointwiseBoundedOfMemBoundedFactorsMonoidStatement
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pointwiseBounded_of_mem_boundedFactors_monoid : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ b ∈ bmon d, PtB P Bs b := by
  first | exact @GlobalTheory.HatNF.BoundedFactors.ptB_of_mem_bmon | exact GlobalTheory.HatNF.BoundedFactors.ptB_of_mem_bmon | (intros; apply GlobalTheory.HatNF.BoundedFactors.ptB_of_mem_bmon <;> assumption)
end
