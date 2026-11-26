module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ThmFD
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsCompactUnitaryMat
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.PsiFor
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.ImportsAlt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.StdGapOfGapLap

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdConsA
noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_big {ε : Fin n → Bool} {h : ℝ} (hh : thrS ε + 1 < h) :
    2 * (n : ℝ) < h := by
  unfold thrS at hh
  have h1 := le_max_left (2 * (n : ℝ))
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))
  linarith

theorem one_le_q0_of_p_q_pos {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) : 1 ≤ S7.q0 ε := by
  show 1 ≤ min (pOf ε) (qOf ε)
  exact le_min hp hq

theorem fdc_eight {ε : Fin n → Bool} {h : ℝ} (hh : thrS ε + 1 < h) :
    8 * (n : ℝ) * (S7.q0 ε : ℝ) < h := by
  unfold thrS at hh
  have h1 := le_max_right (2 * (n : ℝ))
    (16 * (n : ℝ) * (S7.q0 ε : ℝ) + 8 * Real.sqrt (2 * (S7.q0 ε : ℝ)))
  have h2 : 0 ≤ (n : ℝ) * (S7.q0 ε : ℝ) := by positivity
  have h3 : 0 ≤ Real.sqrt (2 * (S7.q0 ε : ℝ)) := Real.sqrt_nonneg _
  nlinarith

theorem fdc_stdGap {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrS ε + 1 < h) : StdGap ε μ :=
  ⟨hμ.1, h, hg, fdc_big hh⟩

theorem fdc_hc_add {μ : Fin n → ℝ} {s : Fin n} (hμ : IsHCParam μ) (hs : StrictAnti (μ + Pi.single s 1)) :
    IsHCParam (μ + Pi.single s 1) := by
  refine ⟨hs, fun a => ?_⟩
  obtain ⟨m, hm⟩ := hμ.2 a
  by_cases has : a = s
  · subst has
    refine ⟨m + 1, ?_⟩
    rw [Pi.add_apply, Pi.single_eq_same]
    push_cast
    linarith
  · refine ⟨m, ?_⟩
    rw [Pi.add_apply, Pi.single_eq_of_ne has, add_zero]
    exact hm

theorem fdc_w_ne {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) : T.w ≠ 0 := by
  letI := T.instNACG
  intro h
  have h1 := T.w_norm
  rw [h, norm_zero] at h1
  exact zero_ne_one h1

theorem fdc_model {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ} {h : ℝ}
    (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (hh : thrS ε + 1 < h) (T : KType ε (lowK ε μ)) :
    ∃ m : Fin n → ℤ, IsMu μ m ∧ IsPsiFor ε μ T (PsiM T m) := by
  obtain ⟨m, hm⟩ := Lap.LemK.exists_isMu hμ
  exact ⟨m, hm, (Lap.Base.psiFor n ε μ h T m hμ hm hg (one_le_q0_of_p_q_pos hp hq) (fdc_eight hh)).1⟩

abbrev FdcGood (ε : Fin n → Bool) (μ : Fin n → ℝ) (d : ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε μ σ ∧ Formalism.MainNotions.S.IsFdeg (muCD ε) σ d

def fdcD (ε : Fin n → Bool) (μ : Fin n → ℝ) : ℝ := by
  classical
  exact if h : ∃ d, FdcGood ε μ d then h.choose else 0

theorem fdc_fdegOf_eq {ε : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (U : H ≃ₗᵢ[ℂ] H')
    (hU : ∀ g ∈ Formalism.MainNotions.S.UJset ε, ∀ x : H, U (σ g x) = σ' g (U x)) (ν : Measure (Formalism.REAL.UJ ε)) (v : H) :
    Formalism.MainNotions.S.fdegOf ν σ' (U v) = Formalism.MainNotions.S.fdegOf ν σ v := by
  have hfun : (fun g : Formalism.REAL.UJ ε => ‖⟪U v, σ' (Formalism.MainNotions.S.umat g) (U v)⟫_ℂ‖ ^ 2) =
      fun g => ‖⟪v, σ (Formalism.MainNotions.S.umat g) v⟫_ℂ‖ ^ 2 := by
    funext g
    rw [← hU (Formalism.MainNotions.S.umat g) g.2 v, LinearIsometryEquiv.inner_map_map]
  simp only [Formalism.MainNotions.S.fdegOf, Formalism.MainNotions.S.coefOn]
  rw [LinearIsometryEquiv.norm_map, hfun]

theorem fdcGood_unique {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrS ε + 1 < h) {d d' : ℝ} (h1 : FdcGood ε μ d) (h2 : FdcGood ε μ d') : d = d' := by
  obtain ⟨H, _, _, σ, hσ, hd⟩ := h1
  obtain ⟨H', _, _, σ', hσ', hd'⟩ := h2
  have := hσ.1
  have := hσ'.1
  have := hσ.2.1
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  obtain ⟨U, hU⟩ := (isDS_props_of_gap n ε μ hμ h hg (fdc_big hh) H σ hσ).2.2.2.2 H' σ' hσ'
  have hUv : U v ≠ 0 := by simpa using hv
  rw [← fdegOf_of_isFdeg' hd hv, ← fdegOf_of_isFdeg' hd' hUv, fdc_fdegOf_eq U hU]

theorem fdcD_eq {ε : Fin n → Bool} {μ : Fin n → ℝ} {h : ℝ} (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h)
    (hh : thrS ε + 1 < h) {d : ℝ} (hd : FdcGood ε μ d) : fdcD ε μ = d := by
  have hex : ∃ d, FdcGood ε μ d := ⟨d, hd⟩
  rw [fdcD, dite_eq_left hex]
  exact fdcGood_unique hμ hg hh hex.choose_spec hd

theorem fdcGood_of_isDS {ε : Fin n → Bool} {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDS ε μ σ) :
    ∃ d, Formalism.MainNotions.S.IsFdeg (muCD ε) σ d := by
  have := hσ.1
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS μ σ hσ
  exact isFdeg_muCD hd

theorem fdc_ds_exists {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {μ : Fin n → ℝ} {h : ℝ}
    (hμ : IsHCParam μ) (hg : GapAtLeast ε μ h) (hh : thrS ε + 1 < h) : ∃ d, FdcGood ε μ d := by
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ
  obtain ⟨m, -, hP⟩ := fdc_model hp hq hμ hg hh T
  have hDS := isDS_sigLam (fdc_stdGap hμ hg hh) hP (fdc_w_ne T)
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hDS
  exact ⟨d, _, inferInstance, inferInstance, _, hDS, hd⟩

theorem fdc_step {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {h : ℝ} (hh : thrS ε + 1 < h) :
    ∀ (μ : Fin n → ℝ) (s : Fin n), IsHCParam μ → GapAtLeast ε μ h →
      GapAtLeast ε (μ + Pi.single s 1) h → StrictAnti (μ + Pi.single s 1) →
        fdcD ε (μ + Pi.single s 1) = fdcD ε μ * ratioV μ s := by
  intro μ s hμ hg hg' hs
  have hμ' : IsHCParam (μ + Pi.single s 1) := fdc_hc_add hμ hs
  obtain ⟨d, H, _, _, σ, hσ, hd⟩ := fdc_ds_exists hp hq hμ hg hh
  obtain ⟨d', H', _, _, σ', hσ', -⟩ := fdc_ds_exists hp hq hμ' hg' hh
  have hr := fdeg_ratio_V hp hq hμ hg hh s hs hσ hσ' (muCD ε) (muCD_isHaar ε) hd
  rw [fdcD_eq hμ hg hh ⟨H, inferInstance, inferInstance, σ, hσ, hd⟩,
    fdcD_eq hμ' hg' hh ⟨H', inferInstance, inferInstance, σ', hσ', hr⟩]

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.ExistsHilbertRepOfPsi
noncomputable section

open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.Lap.Base

theorem exists_hilbert_rep_of_psi :
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), StdGap ε lam → IsPsiFor ε lam T Ψ →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
      IsHWSmooth ε σ lam w ∧ ∀ g ∈ UJset ε, ⟪w, σ g w⟫_ℂ = ⟪T.w, Ψ g T.w⟫_ℂ := by
  intro n ε lam T Ψ hgap hP
  have hv₀ : T.w ≠ 0 := by
    intro h
    have h1 := T.w_norm
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hN0 : ‖uniformisationL2 ε Ψ T.w T.w‖ ≠ 0 := norm_ne_zero_iff.mpr (datumEmbedding_highest_ne_zero hgap hP hv₀)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = ((‖uniformisationL2 ε Ψ T.w T.w‖⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  have h0 : uniformisationL2 ε Ψ T.w 0 = 0 := by simpa using datumEmbedding_smul hP T.w 0 T.w
  have hmem := datumEmbedding_mem_smooth hP T.w (c • T.w)
  refine ⟨L2 ε, inferInstance, inferInstance, rreg ε, uniformisationL2 ε Ψ T.w (c • T.w), ?_, ?_⟩
  · refine ⟨rreg_isURepOn ε, hmem, ?_, ?_, ?_⟩
    · rw [datumEmbedding_smul hP, norm_smul, hc, Complex.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
        inv_mul_cancel₀ hN0]
    · constructor
      · intro a
        apply Subtype.ext
        rw [rightDerivative_datum_embedding hP T.w (c • T.w) rfl, map_smul, T.w_wt a, Submodule.coe_smul, ← datumEmbedding_smul hP,
          smul_comm]
      · intro a b hab hε
        apply Subtype.ext
        rw [rightDerivative_datum_embedding hP T.w (c • T.w) hε, map_smul, T.w_hw a b hab hε, smul_zero, h0]
        rfl
    · exact datumV_casimir hP T.w _ ((mem_datumV_iff hP T.w _).2 ⟨c • T.w, rfl⟩)
  · intro g hg
    have key : ((‖uniformisationL2 ε Ψ T.w T.w‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ c * c) = 1 := by
      rw [hc, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_one]
      congr 1
      rw [pow_two, mul_mul_mul_comm, mul_inv_cancel₀ hN0, one_mul]
    rw [formulaF hgap hP hv₀ hg (c • T.w) (c • T.w), map_smul, inner_smul_left, inner_smul_right,
      ← mul_assoc (starRingEnd ℂ c), ← mul_assoc, key, one_mul]

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.G2

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem fdc_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrS ε + 1 < h) : fdcD ε lam = dimVlam lam := by
  have hgt : ∀ t : ℕ, GapAtLeast ε (lamT lam t) h := fun t a b hab =>
    le_trans (by linarith [(Nat.cast_nonneg t : (0:ℝ) ≤ t)]) (gap_lamT hlam.1 hgap t a b hab)
  have hct := isHCParam_lamT hlam
  have hT : ∀ t : ℕ, Nonempty (KType ε (lowK ε (lamT lam t))) := fun t => HW.kType_exists ε _ (hct t)
  let T : ∀ t : ℕ, KType ε (lowK ε (lamT lam t)) := fun t => Classical.choice (hT t)
  choose m hm hP using fun t => fdc_model hp hq (hct t) (hgt t) hh (T t)
  have hsg : ∀ t, StdGap ε (lamT lam t) := fun t => fdc_stdGap (hct t) (hgt t) hh
  have hDS : ∀ t, Formalism.MainNotions.S.IsDS ε (lamT lam t) (sigLam ε (PsiM (T t) (m t)) (T t).w) :=
    fun t => isDS_sigLam (hsg t) (hP t) (fdc_w_ne (T t))
  choose j hj1 hj2 hj3 hj4 using fun t => anyF (hDS t) (hsg t) (hP t)
  refine thmFD Lap.Base.b3 hp hq hlam hgap hh (fdcD ε) (fdc_step hp hq hh)
    (fun t => ↥(Hlam ε (PsiM (T t) (m t)) (T t).w)) (fun t => sigLam ε (PsiM (T t) (m t)) (T t).w) T j ?_ ?_ ?_
  · refine Filter.Eventually.of_forall fun t => ⟨(hDS t).2.2.1, hj1 t, hj2 t, fun z => ?_⟩
    rw [hj4 t _ (exp_pmat_inUJ z), psiM_exp_pmat, psM_exp_pmat (hm t)]
  · refine Filter.Eventually.of_forall fun t => ?_
    obtain ⟨H', i1, i2, σ', w', hsm, heq⟩ := exists_hilbert_rep_of_psi n ε (lamT lam t) (T t) _ (hsg t) (hP t)
    refine ⟨H', i1, i2, σ', w', hsm, fun z => ?_⟩
    rw [heq _ (exp_pmat_inUJ z), psiM_exp_pmat, psM_exp_pmat (hm t)]
  · refine Filter.Eventually.of_forall fun t => ?_
    obtain ⟨d, hd⟩ := fdcGood_of_isDS (hDS t)
    rw [fdcD_eq (hct t) (hgt t) hh ⟨_, inferInstance, inferInstance, _, hDS t, hd⟩]
    exact hd

theorem fdCons_cd {ε : Fin n → Bool} (hp : 1 ≤ pOf ε) (hq : 1 ≤ qOf ε) {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    {h : ℝ} (hgap : GapAtLeast ε lam h) (hh : thrS ε + 1 < h)
    (hΨ : ∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
      ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : Formalism.MainNotions.S.IsDS ε lam σ) {v : H} (hv : v ≠ 0) :
    Formalism.MainNotions.S.fdegOf (muCD ε) σ v = dimVlam lam := by
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hσ
  rw [fdegOf_of_isFdeg' hd hv, ← fdcD_eq hlam hgap hh ⟨H, inferInstance, inferInstance, σ, hσ, hd⟩]
  exact fdc_cd hp hq hlam hgap hh

theorem fdCons_muG (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      thrS ε + 1 < h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
        ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ) →
      v ≠ 0 → Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam := by
  have := muCD_isHaar ε
  have hs := Measure.haarScalarFactor_pos_of_isHaarMeasure (Formalism.REAL.muG ε) (muCD ε)
  have heq := Measure.isMulLeftInvariant_eq_smul (Formalism.REAL.muG ε) (muCD ε)
  have hc : (0 : ℝ) < (Measure.haarScalarFactor (Formalism.REAL.muG ε) (muCD ε) : ℝ) := by exact_mod_cast hs
  obtain ⟨s, hs0, hEq⟩ : ∃ s : ℝ, 0 < s ∧ Formalism.REAL.muG ε = ENNReal.ofReal s • muCD ε :=
    ⟨_, hc, by rw [ENNReal.ofReal_coe_nnreal]; exact heq⟩
  refine ⟨1 / s, by positivity, fun lam H _ _ _ σ v hlam hσ h hgap hh hp hq hΨ hv => ?_⟩
  obtain ⟨d, hd⟩ := fdcGood_of_isDS hσ
  have h1 := fdCons_cd hp hq hlam hgap hh hΨ hσ hv
  rw [fdegOf_of_isFdeg' hd hv] at h1
  rw [hEq, fdegOf_of_isFdeg' (isFdeg_smul hs0 hd) hv, h1]
  show dimVlam lam / s = 1 / s * dimVlam lam
  ring

end ReciprocityTheory.ChartRestriction.DS.G2
