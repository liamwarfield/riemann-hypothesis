module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.ExhaustionLabels
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.BackwardOfLineFormula

@[expose] public section

section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.ExhaustionStart
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniOfParabolicHaarMultipleStatement
theorem _root_.GlobalTheory.T.fubini_of_parabolic_haar_multiple :
    CompanionTheory.RgExh.Dec.N.S.Fub2 → CompanionTheory.RgExh.Dec.N.S.Fub :=
  GlobalTheory.CompanionTheory.RgFubOf.fubini_of_parabolic_multiple
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SlabStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SlabStatement
open MeasureTheory Set
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.SlabLemma

noncomputable def wt (c t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * c * t))

lemma wt_add (c s t : ℝ) : wt c (s + t) = wt c s * wt c t := by
  show ENNReal.ofReal (Real.exp (2 * c * (s + t))) =
    ENNReal.ofReal (Real.exp (2 * c * s)) * ENNReal.ofReal (Real.exp (2 * c * t))
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

lemma wt_ne_zero (c t : ℝ) : wt c t ≠ 0 := by
  show ENNReal.ofReal (Real.exp (2 * c * t)) ≠ 0
  exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

lemma measurable_wt (c : ℝ) : Measurable (wt c) := by
  show Measurable fun t => ENNReal.ofReal (Real.exp (2 * c * t))
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.ennreal_ofReal

noncomputable def unitInd : ℝ → ℝ≥0∞ := (Ico (0 : ℝ) 1).indicator 1

lemma measurable_unitInd : Measurable unitInd := by
  show Measurable ((Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞))
  exact measurable_const.indicator measurableSet_Ico

lemma lintegral_unitInd (x : ℝ) : ∫⁻ t, unitInd (x - t) = 1 := by
  show ∫⁻ t, (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) (x - t) = 1
  rw [lintegral_sub_left_eq_self (fun y => (Ico (0 : ℝ) 1).indicator (1 : ℝ → ℝ≥0∞) y) x,
    lintegral_indicator_one measurableSet_Ico, Real.volume_Ico, sub_zero, ENNReal.ofReal_one]

variable {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G]

noncomputable def line (F : G → ℝ≥0∞) (a : ℝ → G) (c : ℝ) (p : G × G) : ℝ≥0∞ :=
  ∫⁻ t, F (p.1 * p.2 * a t) * wt c t

lemma measurable_line {F : G → ℝ≥0∞} {a : ℝ → G} (c : ℝ) (hF : Measurable F) (ha : Measurable a) :
    Measurable (line F a c) := by
  have hm : Measurable fun q : (G × G) × ℝ => F (q.1.1 * q.1.2 * a q.2) * wt c q.2 :=
    (hF.comp ((measurable_fst.fst.mul measurable_fst.snd).mul (ha.comp measurable_snd))).mul
      ((measurable_wt c).comp measurable_snd)
  exact hm.lintegral_prod_right'

lemma line_shift {F : G → ℝ≥0∞} {a : ℝ → G} {c : ℝ} (hadd : ∀ s t, a (s + t) = a s * a t) (u m : G) (s : ℝ)
    (hF : Measurable F) (ha : Measurable a) :
    line F a c (u, m * a s) = wt c (-s) * line F a c (u, m) := by
  show ∫⁻ t, F (u * (m * a s) * a t) * wt c t = wt c (-s) * ∫⁻ t, F (u * m * a t) * wt c t
  rw [← lintegral_sub_right_eq_self (fun t => F (u * (m * a s) * a t) * wt c t) s,
    ← lintegral_const_mul _ (show Measurable fun t => F (u * m * a t) * wt c t from
      (hF.comp (measurable_const.mul ha)).mul (measurable_wt c))]
  refine lintegral_congr fun t => ?_
  have h1 : u * (m * a s) * a (t - s) = u * m * a t := by
    have h2 : s + (t - s) = t := by ring
    rw [mul_assoc u m, mul_assoc u, mul_assoc m, ← hadd, h2]
  rw [h1, sub_eq_add_neg, wt_add]
  ring

lemma slab_identity (μM : Measure G) [SFinite μM] {S : Set G} {a : ℝ → G} {δ : G → ℝ≥0∞} {τ : G → ℝ} {c : ℝ}
    (hSc : μM Sᶜ = 0) (ha : Measurable a) (hδ : Measurable δ) (hτ : Measurable τ)
    (hinv : ∀ t, μM.map (· * a t) = μM)
    (hδa : ∀ m ∈ S, ∀ t, δ (m * a t) = δ m * wt c t)
    (hτa : ∀ m ∈ S, ∀ t, τ (m * a t) = τ m + t)
    {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ m, unitInd (τ m) * δ m * ∫⁻ t, H (m * a t) * wt c t ∂volume ∂μM = ∫⁻ m, δ m * H m ∂μM := by
  have hSae : ∀ᵐ m ∂μM, m ∈ S := ae_iff.mpr hSc
  have hU : Measurable fun m => unitInd (τ m) := measurable_unitInd.comp hτ
  have e1 : ∀ m, unitInd (τ m) * δ m * ∫⁻ t, H (m * a t) * wt c t ∂volume =
      ∫⁻ t, unitInd (τ m) * δ m * (H (m * a t) * wt c t) := fun m =>
    (lintegral_const_mul _ ((hH.comp (measurable_const.mul ha)).mul (measurable_wt c))).symm
  have hmeas : Measurable (Function.uncurry fun (m : G) (t : ℝ) =>
      unitInd (τ m) * δ m * (H (m * a t) * wt c t)) :=
    ((hU.comp measurable_fst).mul (hδ.comp measurable_fst)).mul
      ((hH.comp (measurable_fst.mul (ha.comp measurable_snd))).mul ((measurable_wt c).comp measurable_snd))
  have hmeas2 : Measurable (Function.uncurry fun (t : ℝ) (m : G) => unitInd (τ m - t) * (δ m * H m)) :=
    (measurable_unitInd.comp ((hτ.comp measurable_snd).sub measurable_fst)).mul
      ((hδ.comp measurable_snd).mul (hH.comp measurable_snd))
  have e2 : ∀ t, ∫⁻ m, unitInd (τ m) * δ m * (H (m * a t) * wt c t) ∂μM =
      ∫⁻ m, unitInd (τ m - t) * (δ m * H m) ∂μM := by
    intro t
    have hg : Measurable fun m => unitInd (τ m - t) * (δ m * H m) :=
      (measurable_unitInd.comp (hτ.sub measurable_const)).mul (hδ.mul hH)
    have hf : Measurable fun m : G => m * a t := measurable_id.mul measurable_const
    conv_rhs => rw [← hinv t]
    rw [lintegral_map hg hf]
    refine lintegral_congr_ae (hSae.mono fun m hm => ?_)
    show unitInd (τ m) * δ m * (H (m * a t) * wt c t) =
      unitInd (τ (m * a t) - t) * (δ (m * a t) * H (m * a t))
    rw [hτa m hm t, hδa m hm t, add_sub_cancel_right]
    ring
  calc ∫⁻ m, unitInd (τ m) * δ m * ∫⁻ t, H (m * a t) * wt c t ∂volume ∂μM
      = ∫⁻ m, ∫⁻ t, unitInd (τ m) * δ m * (H (m * a t) * wt c t) ∂volume ∂μM := lintegral_congr e1
    _ = ∫⁻ t, ∫⁻ m, unitInd (τ m) * δ m * (H (m * a t) * wt c t) ∂μM ∂volume :=
      lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ t, ∫⁻ m, unitInd (τ m - t) * (δ m * H m) ∂μM ∂volume := lintegral_congr e2
    _ = ∫⁻ m, ∫⁻ t, unitInd (τ m - t) * (δ m * H m) ∂volume ∂μM :=
      lintegral_lintegral_swap hmeas2.aemeasurable
    _ = ∫⁻ m, δ m * H m ∂μM := by
      refine lintegral_congr fun m => ?_
      rw [lintegral_mul_const _ (show Measurable fun t => unitInd (τ m - t) from
          measurable_unitInd.comp (measurable_const.sub measurable_id)),
        lintegral_unitInd, one_mul]

end GlobalTheory.CompanionTheory.SlabLemma


open GlobalTheory.CompanionTheory.SlabLemma in
theorem GlobalTheory.CompanionTheory.SlabLemma.slab : CompanionTheory.RgExh.Dec.N.S.Slab := by
  intro G _ _ _ μN μM _ _ S a δ τ c hSm hSc ha hδ hτ hadd hS hinv hδa hτa hδ0 F hF hfin
  have hSae : ∀ᵐ m ∂μM, m ∈ S := ae_iff.mpr hSc
  have hline : Measurable (line F a c) := measurable_line c hF ha
  have hmeasF : Measurable fun q : G × G => δ q.2 * F (q.1 * q.2) :=
    (hδ.comp measurable_snd).mul (hF.comp (measurable_fst.mul measurable_snd))
  have hae1 : ∀ᵐ u ∂μN, ∫⁻ m, δ m * F (u * m) ∂μM < ⊤ :=
    ae_lt_top hmeasF.lintegral_prod_right' hfin.ne
  have key : ∀ᵐ u ∂μN, ∀ᵐ m ∂μM, line F a c (u, m) < ⊤ := by
    refine hae1.mono fun u hu => ?_
    have hid : ∫⁻ m, unitInd (τ m) * δ m * line F a c (u, m) ∂μM = ∫⁻ m, δ m * F (u * m) ∂μM := by
      have h := slab_identity μM hSc ha hδ hτ hinv hδa hτa (H := fun x => F (u * x))
        (hF.comp (measurable_const.mul measurable_id))
      refine Eq.trans (lintegral_congr fun m => ?_) h
      show unitInd (τ m) * δ m * ∫⁻ t, F (u * m * a t) * wt c t =
        unitInd (τ m) * δ m * ∫⁻ t, F (u * (m * a t)) * wt c t
      simp only [mul_assoc]
    have hfin2 : ∫⁻ m, unitInd (τ m) * δ m * line F a c (u, m) ∂μM < ⊤ := hid ▸ hu
    have hmeas3 : Measurable fun m => unitInd (τ m) * δ m * line F a c (u, m) :=
      ((measurable_unitInd.comp hτ).mul hδ).mul (hline.comp (measurable_const.prodMk measurable_id))
    have hae2 := ae_lt_top hmeas3 hfin2.ne
    have hshift : ∀ k : ℤ, ∀ᵐ m ∂μM,
        unitInd (τ (m * a k)) * δ (m * a k) * line F a c (u, m * a k) < ⊤ := by
      intro k
      have hf : AEMeasurable (fun m : G => m * a k) μM := (measurable_id.mul measurable_const).aemeasurable
      rw [← hinv k] at hae2
      exact ae_of_ae_map hf hae2
    have hall : ∀ᵐ m ∂μM, ∀ k : ℤ,
        unitInd (τ (m * a k)) * δ (m * a k) * line F a c (u, m * a k) < ⊤ := ae_all_iff.mpr hshift
    filter_upwards [hall, hSae] with m hm hmS
    have hmk : m * a ((-⌊τ m⌋ : ℤ) : ℝ) ∈ S := hS m hmS _
    have hmem : τ m + ((-⌊τ m⌋ : ℤ) : ℝ) ∈ Ico (0 : ℝ) 1 := by
      constructor <;> push_cast <;> linarith [Int.floor_le (τ m), Int.lt_floor_add_one (τ m)]
    have hU1 : unitInd (τ (m * a ((-⌊τ m⌋ : ℤ) : ℝ))) = 1 := by
      rw [hτa m hmS]
      exact (Set.indicator_of_mem hmem 1).trans rfl
    have h1 := hm (-⌊τ m⌋)
    rw [hU1, one_mul] at h1
    have hL : line F a c (u, m * a ((-⌊τ m⌋ : ℤ) : ℝ)) < ⊤ := by
      rcases ENNReal.mul_lt_top_iff.mp h1 with h | h | h
      · exact h.2
      · exact absurd h (hδ0 _ hmk)
      · rw [h]
        exact ENNReal.zero_lt_top
    rw [line_shift hadd u m _ hF ha] at hL
    rcases ENNReal.mul_lt_top_iff.mp hL with h | h | h
    · exact h.2
    · exact absurd h (wt_ne_zero _ _)
    · rw [h]
      exact ENNReal.zero_lt_top
  have hset : MeasurableSet {p : G × G | line F a c p < ⊤} := measurableSet_lt hline measurable_const
  have hprod : ∀ᵐ p ∂μN.prod μM, line F a c p < ⊤ := (Measure.ae_prod_iff_ae_ae hset).mpr key
  filter_upwards [hprod] with p hp
  exact lt_of_le_of_lt (setLIntegral_le_lintegral _ _) hp
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SlabStatementStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.SlabStatement : CompanionTheory.RgExh.Dec.N.S.Slab := by
  first | exact @GlobalTheory.CompanionTheory.SlabLemma.slab | exact GlobalTheory.CompanionTheory.SlabLemma.slab | (intros; apply GlobalTheory.CompanionTheory.SlabLemma.slab <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MaximalCompactStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MaximalCompactStatement
noncomputable section

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.RgKMaj

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_riesz (l : E →ₗ[ℂ] ℂ) : ∃ η : E, ∀ x, l x = ⟪η, x⟫_ℂ := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  refine ⟨(InnerProductSpace.toDual ℂ E).symm (LinearMap.toContinuousLinearMap l), fun x => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  rfl

theorem sum_sq_eq_of_basis {ι κ : Type*} [Fintype ι] [Fintype κ] (l : E →ₗ[ℂ] ℂ)
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) :
    ∑ i, ‖l (b i)‖ ^ 2 = ∑ j, ‖l (c j)‖ ^ 2 := by
  obtain ⟨η, hη⟩ := exists_riesz l
  simp only [hη]
  rw [b.sum_sq_norm_inner_left, c.sum_sq_norm_inner_left]

theorem sq_le_of_basis {ι : Type*} [Fintype ι] (l : E →ₗ[ℂ] ℂ)
    (b : OrthonormalBasis ι ℂ E) (x : E) :
    ‖l x‖ ^ 2 ≤ ‖x‖ ^ 2 * ∑ i, ‖l (b i)‖ ^ 2 := by
  obtain ⟨η, hη⟩ := exists_riesz l
  simp only [hη]
  rw [b.sum_sq_norm_inner_left, ← mul_pow, mul_comm ‖x‖]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm η x) 2

end Abstract

theorem sum_enorm_sq {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    ∑ i, ‖z i‖ₑ ^ 2 = ENNReal.ofReal (∑ i, ‖z i‖ ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem lintegral_enorm_sq_lt_top {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}
    (h : MemLp f 2 μ) : (∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ) < ⊤ := by
  have h1 := h.eLpNorm_lt_top
  have h2 := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero h.aestronglyMeasurable
  simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_ofNat] at h2
  rw [← h2]
  exact ENNReal.pow_lt_top h1

variable {n : ℕ} {ε : Fin n → Bool}

theorem continuous_uMat : Continuous (fun g : Formalism.REAL.UJ ε => Formalism.MainNotions.S.umat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_coef {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (ξ v : H) :
    Continuous (fun g : Formalism.REAL.UJ ε => ⟪ξ, σ (Formalism.MainNotions.S.umat g) v⟫_ℂ) := by
  have h : Continuous (fun g : Formalism.REAL.UJ ε => σ (Formalism.MainNotions.S.umat g) v) :=
    (hU.2.2 v).comp_continuous continuous_uMat (fun g => g.2)
  exact continuous_const.inner h

theorem sum_sq_translate {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hU : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ)
    {S : Submodule ℂ H} [FiniteDimensional ℂ S] (hst : Formalism.MainNotions.S.IsKStableOn ε σ S)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ S) (ξ : H) (g k : Formalism.REAL.UJ ε)
    (hk : k ∈ Formalism.REAL.KG ε) :
    ∑ i, ‖⟪ξ, σ (Formalism.MainNotions.S.umat (g * k)) (b i : H)⟫_ℂ‖ ^ 2 =
      ∑ i, ‖⟪ξ, σ (Formalism.MainNotions.S.umat g) (b i : H)⟫_ℂ‖ ^ 2 := by
  have hkK : Formalism.MainNotions.S.umat k ∈ Formalism.REAL.Kset ε := hk
  let T : S →ₗᵢ[ℂ] S :=
    { toLinearMap := ((σ (Formalism.MainNotions.S.umat k) : H →ₗ[ℂ] H).comp S.subtype).codRestrict S
        (fun x => hst _ hkK _ x.2)
      norm_map' := fun x => hU.2.1 _ k.2 _ }
  let Te : S ≃ₗᵢ[ℂ] S := T.toLinearIsometryEquiv rfl
  let l : S →ₗ[ℂ] ℂ :=
    { toFun := fun x => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (x : H)⟫_ℂ
      map_add' := fun x y => by simp [inner_add_right]
      map_smul' := fun c x => by simp [inner_smul_right] }
  have hmul : ∀ x : H, σ (Formalism.MainNotions.S.umat (g * k)) x = σ (Formalism.MainNotions.S.umat g) (σ (Formalism.MainNotions.S.umat k) x) := by
    intro x
    have : Formalism.MainNotions.S.umat (g * k) = Formalism.MainNotions.S.umat g * Formalism.MainNotions.S.umat k := rfl
    rw [this, hU.1.2 _ g.2 _ k.2]
    rfl
  have h := sum_sq_eq_of_basis l (b.map Te) b
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
  rw [hmul, OrthonormalBasis.map_apply]
  rfl

theorem kMaj : CompanionTheory.RgExh.Dec.N.S.KMaj := by
  intro n ε H _ _ _ σ D E hK hU hS u ξ
  obtain ⟨S, hfd, huS, hst⟩ := (hK.mem u).1 u.2
  haveI := hfd
  let b := stdOrthonormalBasis ℂ S
  let c : Formalism.REAL.UJ ε → Fin (Module.finrank ℂ S) → ℂ := fun g i => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (b i : H)⟫_ℂ
  have hcm : ∀ i, Measurable fun g => ‖c g i‖ₑ ^ 2 := fun i =>
    (continuous_coef hU ξ (b i : H)).measurable.enorm.pow_const 2
  refine ⟨fun g => ENNReal.ofReal (‖(u : H)‖ ^ 2) * ∑ i, ‖c g i‖ₑ ^ 2, ?_, ?_, ?_, ?_⟩
  · exact (Finset.measurable_sum _ fun i _ => hcm i).const_mul _
  · intro g k hk
    simp only [sum_enorm_sq]
    congr 2
    exact sum_sq_translate hU hst b ξ g k hk
  · rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hcm i),
      lintegral_finsetSum _ fun i _ => hcm i]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.2 fun i _ => ?_)
    exact lintegral_enorm_sq_lt_top (hS (b i : H) ξ)
  · intro g
    let l : S →ₗ[ℂ] ℂ :=
      { toFun := fun x => ⟪ξ, σ (Formalism.MainNotions.S.umat g) (x : H)⟫_ℂ
        map_add' := fun x y => by simp [inner_add_right]
        map_smul' := fun c x => by simp [inner_smul_right] }
    have h := sq_le_of_basis l b ⟨(u : H), huS⟩
    show ‖l ⟨(u : H), huS⟩‖ₑ ^ 2 ≤ ENNReal.ofReal (‖(u : H)‖ ^ 2) * ∑ i, ‖l (b i)‖ₑ ^ 2
    rw [sum_enorm_sq, ← ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h

end GlobalTheory.CompanionTheory.RgKMaj
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MaximalCompactStatementStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.MaximalCompactStatement : CompanionTheory.RgExh.Dec.N.S.KMaj := by
  first | exact @GlobalTheory.CompanionTheory.RgKMaj.kMaj | exact GlobalTheory.CompanionTheory.RgKMaj.kMaj | (intros; apply GlobalTheory.CompanionTheory.RgKMaj.kMaj <;> assumption)
end
end

namespace CompanionTheory.RgExh.Dec.N.S

theorem exhaustion_start : CompanionTheory.RgExh.Dec.Start :=
  GlobalTheory.T.InitialStatement GlobalTheory.T.rgExh_flagFacts GlobalTheory.T.ParabolicSubgroupEquality GlobalTheory.T.rgExh_lineFacts GlobalTheory.T.SlabStatement (GlobalTheory.T.fubini_of_parabolic_haar_multiple GlobalTheory.T.FubiniParabolicMultiple) GlobalTheory.T.MaximalCompactStatement

end CompanionTheory.RgExh.Dec.N.S
end

section -- merged from CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.DecayOf
namespace CompanionTheory.RgExh.Dec

open CompanionTheory.RgExh

theorem decay_of (hS : Start) (hJ : Labels) (hL : Back) : StepChar → Decay := by
  intro hSC n
  obtain ⟨B, hB⟩ := hJ hSC n
  exact ⟨B, fun ε H _ _ _ σ D E hK χ ss hU _ hL2 hC hG hF => hL hSC n ε H σ D E hK χ ss hU hL2 hC fun A μ hA hμ =>
    hB ε H σ D E hK χ ss hU hC hG hF A μ hA hμ (fun u ξ => hS n ε H σ D E hK hU hL2 A μ hA hμ u (ξ : H))⟩

end CompanionTheory.RgExh.Dec
end

namespace CompanionTheory.RgExh.Dec

theorem decay_estimate : CompanionTheory.RgExh.StepChar → CompanionTheory.RgExh.Decay :=
  decay_of N.S.exhaustion_start J.exhaustion_labels L.backward_of_line_formula

end CompanionTheory.RgExh.Dec
