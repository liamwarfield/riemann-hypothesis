module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Development

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.MeasurableTripleProduct
open MeasureTheory Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

variable {k r : ℕ}

theorem lim_sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  have : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

def invT (x : Mt k r) : Mt k r := ((Matrix.of x)⁻¹ : Mat k r)

def mul3 (p : Mt k r × Mt k r × Mt k r) : Mt k r := (Matrix.of p.1 * Matrix.of p.2.1 * Matrix.of p.2.2 : Mat k r)

def aDilT (t : ℝ) : Mt k r := aDil k r t

theorem lim_measurable_inv : Measurable (invT (k := k) (r := r)) := by
  have hid : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hd : Measurable (fun x : Mt k r => (Matrix.of x).det) := (Continuous.matrix_det hid).measurable
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  have e : ∀ x : Mt k r, invT x i j = ((Matrix.of x).det)⁻¹ * (Matrix.of x).adjugate i j := by
    intro x
    show ((Matrix.of x)⁻¹ : Mat k r) i j = _
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rfl
  simp_rw [e]
  have ha : Continuous (fun x : Mt k r => (Matrix.of x).adjugate i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (Continuous.matrix_adjugate hid))
  exact (measurable_inv.comp hd).mul ha.measurable

theorem measurable_triple_product : Measurable (mul3 (k := k) (r := r)) := by
  have h : Continuous (mul3 (k := k) (r := r)) := by
    unfold mul3
    exact (continuous_fst.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul
      (continuous_snd.comp continuous_snd)
  exact h.measurable

theorem lim_measurable_aDil : Measurable (aDilT (k := k) (r := r)) := by
  refine Measurable.of_eval fun i => Measurable.of_eval fun j => ?_
  by_cases hij : i = j
  · subst hij
    by_cases h1 : i.val < r
    · have e : (fun t : ℝ => aDilT (k := k) (r := r) t i i) = fun t => ((t ^ (r - i.val) : ℝ) : ℂ) := by
        funext t; simp [aDilT, aDil, h1]
      rw [e]; exact Complex.measurable_ofReal.comp (measurable_id.pow_const _)
    · by_cases h2 : i.val ≤ r + k
      · have e : (fun t : ℝ => aDilT (k := k) (r := r) t i i) = fun _ => (1 : ℂ) := by
          funext t; simp [aDilT, aDil, h1, h2]
        rw [e]; exact measurable_const
      · have e : (fun t : ℝ => aDilT (k := k) (r := r) t i i) =
            fun t => (((t ^ (i.val - (r + k)))⁻¹ : ℝ) : ℂ) := by
          funext t; simp [aDilT, aDil, h1, h2]
        rw [e]; exact Complex.measurable_ofReal.comp (measurable_id.pow_const _).inv
  · have e : (fun t : ℝ => aDilT (k := k) (r := r) t i j) = fun _ => (0 : ℂ) := by
      funext t; simp [aDilT, aDil, hij]
    rw [e]; exact measurable_const

def limDil (p : ℝ × (Mt k r × Mt k r)) : ℝ × (Mt k r × Mt k r) :=
  (p.1, (p.2.1, conjM (aDil k r p.1) p.2.2))

theorem lim_measurable_dil : Measurable (limDil (k := k) (r := r)) := by
  have e : (fun p : ℝ × (Mt k r × Mt k r) => conjM (aDil k r p.1) p.2.2) =
      mul3 ∘ (fun p : ℝ × (Mt k r × Mt k r) => (aDilT p.1, p.2.2, invT (aDilT (k := k) (r := r) p.1))) := by
    funext p
    simp only [Function.comp, mul3, invT, aDilT, conjM]
    rfl
  have hc : Measurable (fun p : ℝ × (Mt k r × Mt k r) => conjM (aDil k r p.1) p.2.2) := by
    rw [e]
    exact measurable_triple_product.comp ((lim_measurable_aDil.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_snd).prodMk ((lim_measurable_inv.comp lim_measurable_aDil).comp measurable_fst)))
  exact measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hc)

theorem lim_dil_mp (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN]
    (hJ : ∀ t : ℝ, 0 < t → μN.map (conjM (aDil k r t)) = ENNReal.ofReal ((t ^ kap k r)⁻¹) • μN) :
    MeasurePreserving (limDil (k := k) (r := r))
      (((volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod (μW.prod μN))
      ((volume.restrict (Ioi (0 : ℝ))).prod (μW.prod μN)) := by
  refine ⟨lim_measurable_dil, ?_⟩
  ext s hs
  have hw : Measurable (fun t : ℝ => ENNReal.ofReal (t ^ kap k r)) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  rw [Measure.map_apply lim_measurable_dil hs, Measure.prod_apply (lim_measurable_dil hs), Measure.prod_apply hs,
    lintegral_withDensity_eq_lintegral_mul _ hw (measurable_measure_prodMk_left (lim_measurable_dil hs))]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  have hcm : Measurable (conjM (k := k) (r := r) (aDil k r t)) := (BesselUnitaryEquiv.continuous_conjM _).measurable
  have hm : Measurable (Prod.map (id : Mt k r → Mt k r) (conjM (aDil k r t))) := measurable_id.prodMap hcm
  have hpre : Prod.mk t ⁻¹' (limDil (k := k) (r := r) ⁻¹' s) =
      Prod.map id (conjM (aDil k r t)) ⁻¹' (Prod.mk t ⁻¹' s) := rfl
  simp only [Pi.mul_apply]
  rw [hpre, ← Measure.map_apply hm (measurable_prodMk_left hs), ← Measure.map_prod_map _ _ measurable_id hcm,
    Measure.map_id, hJ t ht', Measure.prod_smul_right, Measure.smul_apply, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]

theorem lim_dil_fubini (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN]
    (hJ : ∀ t : ℝ, 0 < t → μN.map (conjM (aDil k r t)) = ENNReal.ofReal ((t ^ kap k r)⁻¹) • μN)
    (χ : ℝ → ℝ) (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ0 : ∀ t : ℝ, t ≤ 0 → χ t = 0)
    (hχ1 : ∫ t, χ t = 1) (Nn : Set (Mt k r)) (hN : ∀ᵐ n ∂μN, n ∈ Nn)
    (Λ : Mt k r → ℝ) (hΛ : ∀ t : ℝ, 0 < t → ∀ n ∈ Nn, Λ (conjM (aDil k r t) n) = t * Λ n)
    (B : Mt k r × Mt k r → ℂ)
    (hB : Integrable (fun x => B x * Complex.exp (Complex.I * (Λ x.2 : ℂ))) (μW.prod μN)) :
    ∫ x, (∫ t : ℝ, ((χ t * t ^ kap k r : ℝ) : ℂ) * B (x.1, conjM (aDil k r t) x.2) *
        Complex.exp (Complex.I * ((Λ x.2 * t : ℝ) : ℂ))) ∂(μW.prod μN) =
      ∫ x, B x * Complex.exp (Complex.I * (Λ x.2 : ℂ)) ∂(μW.prod μN) := by
  set μ := μW.prod μN with hμ
  set ρ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hρ
  set E : Mt k r × Mt k r → ℂ := fun x => B x * Complex.exp (Complex.I * (Λ x.2 : ℂ)) with hE
  set K : ℝ × (Mt k r × Mt k r) → ℂ := fun p => ((χ p.1 : ℝ) : ℂ) * E p.2 with hK
  set G : ℝ × (Mt k r × Mt k r) → ℂ := fun p => ((χ p.1 * p.1 ^ kap k r : ℝ) : ℂ) *
    B (p.2.1, conjM (aDil k r p.1) p.2.2) * Complex.exp (Complex.I * ((Λ p.2.2 * p.1 : ℝ) : ℂ)) with hG
  set w : ℝ → NNReal := fun t => (t ^ kap k r).toNNReal with hw
  have hwm : Measurable w := measurable_real_toNNReal.comp (measurable_id.pow_const _)
  have hχi : Integrable (fun t => ((χ t : ℝ) : ℂ)) ρ :=
    ((hχc.integrable_of_hasCompactSupport hχs).ofReal).integrableOn
  have hKi : Integrable K (ρ.prod μ) := hχi.mul_prod hB
  have hMP := lim_dil_mp μW μN hJ
  have hKD : Integrable (K ∘ limDil) ((ρ.withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod μ) :=
    (hMP.integrable_comp hKi.aestronglyMeasurable).2 hKi
  have hKDint : ∫ p, (K ∘ limDil) p ∂((ρ.withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod μ) =
      ∫ p, K p ∂(ρ.prod μ) := by
    have := integral_map hMP.measurable.aemeasurable (hMP.map_eq.symm ▸ hKi.aestronglyMeasurable)
    rw [hMP.map_eq] at this
    exact this.symm
  have hdens : (ρ.withDensity (fun t => ENNReal.ofReal (t ^ kap k r))).prod μ =
      (ρ.prod μ).withDensity (fun p => ((w p.1 : NNReal) : ℝ≥0∞)) :=
    prod_withDensity_left (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _))
  have hwm' : Measurable (fun p : ℝ × (Mt k r × Mt k r) => w p.1) := hwm.comp measurable_fst
  rw [hdens] at hKD hKDint
  rw [integrable_withDensity_iff_integrable_smul hwm'] at hKD
  rw [integral_withDensity_eq_integral_smul hwm'] at hKDint

  have hae : ∀ᵐ p ∂(ρ.prod μ), w p.1 • (K ∘ limDil) p = G p := by
    have a1 : ∀ᵐ p ∂(ρ.prod μ), p.1 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    have a2 : ∀ᵐ p ∂(ρ.prod μ), p.2.2 ∈ Nn :=
      (Measure.quasiMeasurePreserving_snd.comp Measure.quasiMeasurePreserving_snd).ae hN
    filter_upwards [a1, a2] with p hp1 hp2
    have hp1' : (0 : ℝ) < p.1 := hp1
    have hl := hΛ p.1 hp1' p.2.2 hp2
    have hw1 : ((w p.1 : NNReal) : ℝ) = p.1 ^ kap k r := Real.coe_toNNReal _ (by positivity)
    simp only [hG, hK, hE, Function.comp, limDil, hl]
    rw [NNReal.smul_def, hw1, Complex.real_smul]
    push_cast
    ring_nf
  have hGi : Integrable G (ρ.prod μ) := hKD.congr hae
  have hGint : ∫ p, G p ∂(ρ.prod μ) = ∫ x, E x ∂μ := by
    rw [← integral_congr_ae hae, hKDint, hK, integral_prod_mul (fun t => ((χ t : ℝ) : ℂ)) E, integral_complex_ofReal]
    have : ∫ t in Ioi (0 : ℝ), χ t = 1 := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ)) (fun t ht => hχ0 t (not_lt.mp ht))]
      exact hχ1
    rw [this]; simp

  have hR : ρ.prod μ = (volume.prod μ).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hz : ∀ p : ℝ × (Mt k r × Mt k r), p ∉ Ioi (0 : ℝ) ×ˢ (univ : Set (Mt k r × Mt k r)) → G p = 0 := by
    intro p hp
    have : p.1 ≤ 0 := by
      by_contra hc
      exact hp ⟨not_le.mp hc, mem_univ _⟩
    simp [hG, hχ0 p.1 this]
  have hGv : Integrable G (volume.prod μ) := by
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 (hR ▸ hGi)
    intro p hp
    by_contra hc
    exact hp (hz p hc)
  have hGvint : ∫ p, G p ∂(volume.prod μ) = ∫ p, G p ∂(ρ.prod μ) := by
    rw [hR, setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  have hF : Integrable (fun z : (Mt k r × Mt k r) × ℝ => G z.swap) (μ.prod volume) := hGv.swap
  calc ∫ x, (∫ t : ℝ, ((χ t * t ^ kap k r : ℝ) : ℂ) * B (x.1, conjM (aDil k r t) x.2) *
        Complex.exp (Complex.I * ((Λ x.2 * t : ℝ) : ℂ))) ∂μ
      = ∫ z, G z.swap ∂(μ.prod volume) := (integral_prod (fun z => G z.swap) hF).symm
    _ = ∫ p, G p ∂(volume.prod μ) := integral_prod_swap G
    _ = ∫ x, E x ∂μ := by rw [hGvint, hGint]

theorem lim_conj_transfer (μW μN : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN] (U : Set (Mat k r))
    (hW : ∀ᵐ h ∂μW, Matrix.of h ∈ U) (hC : ∀ h : Mt k r, Matrix.of h ∈ U → μN.map (conjM (Matrix.of h)⁻¹) = μN)
    (f g : Mt k r × Mt k r → ℂ) (hf : Integrable f (μW.prod μN))
    (hfg : ∀ᵐ x ∂(μW.prod μN), f (x.1, conjM (Matrix.of x.1)⁻¹ x.2) = g x) :
    Integrable g (μW.prod μN) ∧ ∫ x, g x ∂(μW.prod μN) = ∫ x, f x ∂(μW.prod μN) := by
  have e : (Function.uncurry fun (h n : Mt k r) => conjM (Matrix.of h)⁻¹ n) =
      mul3 ∘ (fun p : Mt k r × Mt k r => (invT p.1, p.2, invT (invT p.1))) := by
    funext p
    simp only [Function.comp, Function.uncurry, mul3, invT, conjM]
    rfl
  have hmeas : Measurable (Function.uncurry fun (h n : Mt k r) => conjM (Matrix.of h)⁻¹ n) := by
    rw [e]
    exact measurable_triple_product.comp ((lim_measurable_inv.comp measurable_fst).prodMk
      (measurable_snd.prodMk (lim_measurable_inv.comp (lim_measurable_inv.comp measurable_fst))))
  have hmp : MeasurePreserving (fun x : Mt k r × Mt k r => (id x.1, conjM (Matrix.of x.1)⁻¹ x.2))
      (μW.prod μN) (μW.prod μN) :=
    MeasurePreserving.skew_product (MeasurePreserving.id μW) hmeas (hW.mono fun h hh => hC h hh)
  have hi : Integrable (f ∘ fun x : Mt k r × Mt k r => (id x.1, conjM (Matrix.of x.1)⁻¹ x.2)) (μW.prod μN) :=
    (hmp.integrable_comp hf.aestronglyMeasurable).2 hf
  refine ⟨hi.congr hfg, ?_⟩
  rw [← integral_congr_ae hfg]
  have := integral_map hmp.measurable.aemeasurable (hmp.map_eq.symm ▸ hf.aestronglyMeasurable)
  rw [hmp.map_eq] at this
  exact this.symm

end PI.BICNZ
end
end

open MeasureTheory Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

variable {k r : ℕ}

theorem lim_chi_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) {t : ℝ} (ht : t ≤ 0) : D.χ t = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hm
  have := D.χ_supp hm
  simp only [Set.mem_Ioo] at this
  linarith [this.1]

theorem lim_chi_hcs {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) : HasCompactSupport D.χ :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
    (D.χ_supp.trans Set.Ioo_subset_Icc_self)

theorem lim_pi_inner {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {U : Set (Mat k r)}
    {π : Mat k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn U π) (hu : ∀ h ∈ U, ∀ v, ‖π h v‖ = ‖v‖)
    {H : Mat k r} (hH : H ∈ U) (hHi : H⁻¹ ∈ U) (hHu : IsUnit H.det) (ξ : Wp) :
    ⟪π H⁻¹ ξ, ξ⟫_ℂ = ⟪ξ, π H ξ⟫_ℂ := by
  let I : Wp →ₗᵢ[ℂ] Wp := ⟨(π H).toLinearMap, hu H hH⟩
  have h1 : π H (π H⁻¹ ξ) = ξ := BesselUnitaryEquiv.rep_inv hπ hH hHi (Matrix.mul_nonsing_inv _ hHu) ξ
  have h2 := I.inner_map_map (π H⁻¹ ξ) ξ
  change ⟪π H (π H⁻¹ ξ), π H ξ⟫_ℂ = _ at h2
  rw [h1] at h2
  exact h2.symm

theorem lim_conj_mul {H M : Mat k r} (hu : IsUnit H.det) : H * (H⁻¹ * M * H⁻¹⁻¹) = M * H := by
  rw [Matrix.nonsing_inv_nonsing_inv _ hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
    Matrix.one_mul]

theorem lim_psi_conj {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {H M : Mat k r} (hH : H ∈ UWset k r z)
    (hM : M ∈ Nset k r) :
    psi k r z cStd (H⁻¹ * M * H⁻¹⁻¹) = Complex.exp (Complex.I * ((lam k r z M : ℝ) : ℂ)) := by
  unfold psi
  rw [(Formalism.QuantumDeterminants.unitary_weyl_normal_holds k r z hz _ (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hH) M hM).2]
  rfl

theorem lim_left_pt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (v : H) (ξ : Wp)
    (x : Mt k r × Mt k r) (hh : Matrix.of x.1 ∈ UWset k r D.z) (hm : Matrix.of x.2 ∈ Nset k r) :
    star ⟪ξ, Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v (x.1, conjM (Matrix.of x.1)⁻¹ x.2) ξ⟫_ℂ =
      Lf D σ v ξ x * Complex.exp (Complex.I * ((lam k r D.z (Matrix.of x.2) : ℝ) : ℂ)) := by
  obtain ⟨h, m⟩ := x
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have hi := Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh
  have eM : Matrix.of h * Matrix.of (conjM (Matrix.of h)⁻¹ m) = Matrix.of m * Matrix.of h :=
    lim_conj_mul (M := Matrix.of m) hu
  have eψ : psi k r D.z cStd (Matrix.of (conjM (Matrix.of h)⁻¹ m)) =
      Complex.exp (Complex.I * ((lam k r D.z (Matrix.of m) : ℝ) : ℂ)) :=
    lim_psi_conj D.z_mem hh hm
  have eπ := lim_pi_inner D.π_rep D.π_unitary hh hi hu ξ
  dsimp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, Lf]
  rw [eM, eψ, ContinuousLinearMap.smul_apply, inner_smul_right, star_mul', star_mul', star_star,
    Complex.star_def, inner_conj_symm, inner_conj_symm, eπ]
  ring

theorem lim_right_pt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H)) (v' : H) (ξ' : Wq)
    (x : Mt k r × Mt k r) (hh : Matrix.of x.1 ∈ UWset k r D.z') (hm : Matrix.of x.2 ∈ Nset k r) :
    ⟪ξ', Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' cStd D.π' σ v' v' (x.1, conjM (Matrix.of x.1)⁻¹ x.2) ξ'⟫_ℂ =
      Rf D σ v' ξ' x * Complex.exp (Complex.I * ((-lam k r D.z' (Matrix.of x.2) : ℝ) : ℂ)) := by
  obtain ⟨h, m⟩ := x
  have hu := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  have eM : Matrix.of h * Matrix.of (conjM (Matrix.of h)⁻¹ m) = Matrix.of m * Matrix.of h :=
    lim_conj_mul (M := Matrix.of m) hu
  have eψ : psi k r D.z' cStd (Matrix.of (conjM (Matrix.of h)⁻¹ m)) =
      Complex.exp (Complex.I * ((lam k r D.z' (Matrix.of m) : ℝ) : ℂ)) :=
    lim_psi_conj D.z'_mem hh hm
  have es : ∀ a : ℝ, star (Complex.exp (Complex.I * (a : ℂ))) = Complex.exp (Complex.I * ((-a : ℝ) : ℂ)) := by
    intro a
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring_nf
  dsimp only [Formalism.FourierDecayAlt.ThreeDimData.beInt, Rf]
  rw [eM, eψ, es, ContinuousLinearMap.smul_apply, inner_smul_right]
  ring

theorem lim_leftLimit : LeftLimit := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS v ξ hv hI
  haveI := lim_sf D.haarW
  haveI := lim_sf D.haarN
  set f : Mt k r × Mt k r → ℂ := fun p => star ⟪ξ, Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v p ξ⟫_ℂ with hf
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hLi : Integrable (fun p => L (Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v p)) (D.μW.prod D.μN) :=
    L.integrable_comp hI
  have hfi : Integrable f (D.μW.prod D.μN) :=
    (Complex.conjCLE.toContinuousLinearMap).integrable_comp hLi
  have hfint : ∫ p, f p ∂(D.μW.prod D.μN) =
      star ⟪ξ, Formalism.FourierDecayAlt.ThreeDimData.be D.z cStd D.π σ D.μW D.μN v v ξ⟫_ℂ := by
    have h1 : ∫ p, f p ∂(D.μW.prod D.μN) =
        (starRingEnd ℂ) (∫ p, L (Formalism.FourierDecayAlt.ThreeDimData.beInt D.z cStd D.π σ v v p) ∂(D.μW.prod D.μN)) :=
      integral_conj
    rw [h1, L.integral_comp_comm hI]
    rfl
  have hCI := Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D
  have hC : ∀ h : Mt k r, Matrix.of h ∈ UWset k r D.z → D.μN.map (conjM (Matrix.of h)⁻¹) = D.μN :=
    fun h hh => hCI _ (Or.inl (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh))
  have q1 : ∀ᵐ x ∂(D.μW.prod D.μN), Matrix.of x.1 ∈ UWset k r D.z :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 D.haarW.conc)
  have q2 : ∀ᵐ x ∂(D.μW.prod D.μN), Matrix.of x.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 D.haarN.conc)
  have hfg : ∀ᵐ x ∂(D.μW.prod D.μN), f (x.1, conjM (Matrix.of x.1)⁻¹ x.2) =
      Lf D σ v ξ x * Complex.exp (Complex.I * ((lam k r D.z (Matrix.of x.2) : ℝ) : ℂ)) := by
    filter_upwards [q1, q2] with x hh hm
    exact lim_left_pt D σ v ξ x hh hm
  obtain ⟨hLi2, hLint⟩ := lim_conj_transfer D.μW D.μN (UWset k r D.z) (ae_iff.2 D.haarW.conc) hC f _ hfi hfg
  have hJ := Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting k r Wp Wq D
  have hΛ : ∀ t : ℝ, 0 < t → ∀ n ∈ {n : Mt k r | Matrix.of n ∈ Nset k r},
      (fun n : Mt k r => lam k r D.z (Matrix.of n)) (conjM (aDil k r t) n) =
        t * (fun n : Mt k r => lam k r D.z (Matrix.of n)) n :=
    fun t ht n hn => (Formalism.FourierDecayAlt.P.dilation_unipotent_measure k r D.z t ht.ne' D.z_mem (Matrix.of n) hn).2.2
  have key := lim_dil_fubini D.μW D.μN hJ D.χ D.χ_smooth.continuous (lim_chi_hcs D) (fun t ht => lim_chi_zero D ht)
    D.χ_int {n : Mt k r | Matrix.of n ∈ Nset k r} (ae_iff.2 D.haarN.conc)
    (fun n : Mt k r => lam k r D.z (Matrix.of n)) hΛ (Lf D σ v ξ) hLi2
  rw [← hfint, ← hLint]
  exact key

theorem lim_rightLimit : RightLimit := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS v' ξ' hv' hI
  haveI := lim_sf D.haarW'
  haveI := lim_sf D.haarN
  set f : Mt k r × Mt k r → ℂ := fun p => ⟪ξ', Formalism.FourierDecayAlt.ThreeDimData.beInt D.z' cStd D.π' σ v' v' p ξ'⟫_ℂ with hf
  let L : (Wq →L[ℂ] Wq) →L[ℂ] ℂ := (innerSL ℂ ξ').comp (ContinuousLinearMap.apply ℂ Wq ξ')
  have hfi : Integrable f (D.μW'.prod D.μN) := L.integrable_comp hI
  have hfint : ∫ p, f p ∂(D.μW'.prod D.μN) =
      ⟪ξ', Formalism.FourierDecayAlt.ThreeDimData.be D.z' cStd D.π' σ D.μW' D.μN v' v' ξ'⟫_ℂ :=
    L.integral_comp_comm hI
  have hCI := Formalism.FourierDecayAlt.P.conjugation_invariance_every_setting k r Wp Wq D
  have hC : ∀ h : Mt k r, Matrix.of h ∈ UWset k r D.z' → D.μN.map (conjM (Matrix.of h)⁻¹) = D.μN :=
    fun h hh => hCI _ (Or.inr (Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hh))
  have q1 : ∀ᵐ x ∂(D.μW'.prod D.μN), Matrix.of x.1 ∈ UWset k r D.z' :=
    Measure.quasiMeasurePreserving_fst.ae (ae_iff.2 D.haarW'.conc)
  have q2 : ∀ᵐ x ∂(D.μW'.prod D.μN), Matrix.of x.2 ∈ Nset k r :=
    Measure.quasiMeasurePreserving_snd.ae (ae_iff.2 D.haarN.conc)
  have hfg : ∀ᵐ x ∂(D.μW'.prod D.μN), f (x.1, conjM (Matrix.of x.1)⁻¹ x.2) =
      Rf D σ v' ξ' x * Complex.exp (Complex.I * ((-lam k r D.z' (Matrix.of x.2) : ℝ) : ℂ)) := by
    filter_upwards [q1, q2] with x hh hm
    exact lim_right_pt D σ v' ξ' x hh hm
  obtain ⟨hLi2, hLint⟩ := lim_conj_transfer D.μW' D.μN (UWset k r D.z') (ae_iff.2 D.haarW'.conc) hC f _ hfi hfg
  have hJ := Formalism.FourierDecayAlt.P.dilation_jacobian_every_setting k r Wp Wq D
  have hΛ : ∀ t : ℝ, 0 < t → ∀ n ∈ {n : Mt k r | Matrix.of n ∈ Nset k r},
      (fun n : Mt k r => -lam k r D.z' (Matrix.of n)) (conjM (aDil k r t) n) =
        t * (fun n : Mt k r => -lam k r D.z' (Matrix.of n)) n := by
    intro t ht n hn
    have := (Formalism.FourierDecayAlt.P.dilation_unipotent_measure k r D.z' t ht.ne' D.z'_mem (Matrix.of n) hn).2.2
    show -lam k r D.z' (aDil k r t * Matrix.of n * (aDil k r t)⁻¹) = t * -lam k r D.z' (Matrix.of n)
    rw [this]; ring
  have key := lim_dil_fubini D.μW' D.μN hJ D.χ D.χ_smooth.continuous (lim_chi_hcs D) (fun t ht => lim_chi_zero D ht)
    D.χ_int {n : Mt k r | Matrix.of n ∈ Nset k r} (ae_iff.2 D.haarN.conc)
    (fun n : Mt k r => -lam k r D.z' (Matrix.of n)) hΛ (Rf D σ v' ξ') hLi2
  rw [← hfint, ← hLint]
  exact key

end PI.BICNZ
