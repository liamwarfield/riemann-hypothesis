module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGHead

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.NormOfMemRootSetOne
namespace Formalism.FourierDecayAlt.P.PBK

open MeasureTheory Filter Topology Set Polynomial

noncomputable section

open Classical

theorem mem_rootSet' {s : ℕ} (hs : s ≠ 0) {a z : ℂ} : z ∈ G.rootSet s a ↔ z ^ s = a := by
  rw [G.rootSet, Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hs)]

theorem one_mem_rootSet_one {s : ℕ} (hs : s ≠ 0) : (1 : ℂ) ∈ G.rootSet s 1 := by
  exact (Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs).mpr (one_pow s)

theorem norm_of_mem_rootSet_one {s : ℕ} (hs : s ≠ 0) {ζ : ℂ} (hζ : ζ ∈ G.rootSet s 1) : ‖ζ‖ = 1 := by
  exact Complex.norm_eq_one_of_pow_eq_one ((Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs).mp hζ) hs

theorem rootSet_mul_eq {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0) (hz : z ^ s = w) (hρ : ρ ^ s = l)
    (hl : l ≠ 0) : G.rootSet s (l * w) = (G.rootSet s 1).image (fun ζ => ζ * ρ * z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hw (by rw [← hz, zero_pow hs])
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact hl (by rw [← hρ, zero_pow hs])
  ext y
  rw [Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs, Finset.mem_image]
  constructor
  · intro hy
    refine ⟨y / (ρ * z), (Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs).mpr ?_, ?_⟩
    · rw [div_pow, mul_pow, hρ, hz, hy, div_self (mul_ne_zero hl hw)]
    · field_simp
  · rintro ⟨ζ, hζ, rfl⟩
    rw [Formalism.FourierDecayAlt.P.PBK.mem_rootSet' hs] at hζ
    rw [mul_pow, mul_pow, hζ, hρ, hz, one_mul]

theorem injOn_rootSet_mul {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0) (hz : z ^ s = w) (hρ : ρ ^ s = l)
    (hl : l ≠ 0) : Set.InjOn (fun ζ => ζ * ρ * z) (G.rootSet s 1 : Set ℂ) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hw (by rw [← hz, zero_pow hs])
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    exact hl (by rw [← hρ, zero_pow hs])
  intro ζ _ ζ' _ h
  exact mul_right_cancel₀ hρ0 (mul_right_cancel₀ hz0 h)

theorem sum_rootSet_mul {E : Type} [AddCommMonoid E] {s : ℕ} (hs : s ≠ 0) {w z ρ l : ℂ} (hw : w ≠ 0)
    (hz : z ^ s = w) (hρ : ρ ^ s = l) (hl : l ≠ 0) (Gf : ℂ → E) :
    ∑ y ∈ G.rootSet s (l * w), Gf y = ∑ ζ ∈ G.rootSet s 1, Gf (ζ * ρ * z) := by
  rw [Formalism.FourierDecayAlt.P.PBK.rootSet_mul_eq hs hw hz hρ hl,
    Finset.sum_image fun x hx y hy h => Formalism.FourierDecayAlt.P.PBK.injOn_rootSet_mul hs hw hz hρ hl hx hy h]

theorem sum_rootSet_eq_range {E : Type} [AddCommMonoid E] {s : ℕ} (hs : s ≠ 0) {w : ℂ} (hw : w ≠ 0)
    (F : ℂ → E) : ∑ z ∈ G.rootSet s w, F z = ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k w) := by
  have hnd := (Complex.isPrimitiveRoot_exp s hs).nthRoots_nodup hw
  rw [G.rootSet, ← Multiset.toFinset_eq hnd]
  show (Multiset.map F (nthRoots s w)).sum = _
  rw [Formalism.FourierDecayAlt.P.NthRootMeasurability.nthRoots_eq_R s hs w, Multiset.map_map]
  rfl

section change

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rootBranch (s k : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (F : ℂ → E)
    (hF : Integrable (fun z => ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z)) :
    Integrable (fun c => F (NthRootMeasurability.R s k (u * c))) ∧
      ∫ c, F (NthRootMeasurability.R s k (u * c)) = ∫ z in NthRootMeasurability.A s k, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
  have hA : MeasurableSet (NthRootMeasurability.A s k) := Formalism.FourierDecayAlt.P.NthRootMeasurability.measurableSet_A s k

  have hderiv : ∀ z ∈ NthRootMeasurability.A s k, HasFDerivWithinAt (fun z => u⁻¹ * z ^ s)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (u⁻¹ * (s * z ^ (s - 1)))).restrictScalars ℝ)
      (NthRootMeasurability.A s k) z := fun z _ =>
    (((hasDerivAt_pow s z).const_mul u⁻¹).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj := Formalism.FourierDecayAlt.P.NthRootMeasurability.injOn_A s k u hu
  have himg := Formalism.FourierDecayAlt.P.NthRootMeasurability.image_A s k hs u hu
  have hdet : ∀ z : ℂ, |((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ)
      (u⁻¹ * (s * z ^ (s - 1)))).restrictScalars ℝ).det| = ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 := fun z => by
    rw [Formalism.FourierDecayAlt.P.NthRootMeasurability.detC, abs_of_nonneg (by positivity)]
  have hback : ∀ z ∈ NthRootMeasurability.A s k, F (NthRootMeasurability.R s k (u * (u⁻¹ * z ^ s))) = F z := fun z hz => by
    rw [← mul_assoc, mul_inv_cancel₀ hu, one_mul, hz.2]
  have hnull : (volume : Measure ℂ).restrict ({0}ᶜ : Set ℂ) = volume := MeasureTheory.restrict_compl_singleton 0
  constructor
  · have h1 : IntegrableOn (fun c => F (NthRootMeasurability.R s k (u * c))) ((fun z => u⁻¹ * z ^ s) '' NthRootMeasurability.A s k) := by
      rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hA hderiv hinj]
      refine (hF.integrableOn (s := NthRootMeasurability.A s k)).congr_fun (fun z hz => ?_) hA
      simp only [hdet, hback z hz]
    rw [himg, IntegrableOn, hnull] at h1
    exact h1
  · have h2 := integral_image_eq_integral_abs_det_fderiv_smul volume hA hderiv hinj
      (fun c => F (NthRootMeasurability.R s k (u * c)))
    rw [himg, hnull] at h2
    rw [h2]
    refine setIntegral_congr_fun hA (fun z hz => ?_)
    simp only [hdet, hback z hz]

theorem integral_sum_rootSet (s : ℕ) (hs : s ≠ 0) (u : ℂ) (hu : u ≠ 0) (F : ℂ → E)
    (hF : Integrable (fun z => ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z)) :
    Integrable (fun c => ∑ z ∈ G.rootSet s (u * c), F z) ∧
      ∫ c, ∑ z ∈ G.rootSet s (u * c), F z = ∫ z, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
  have hae : ∀ᵐ c : ℂ, c ≠ 0 := compl_mem_ae_iff.mpr (measure_singleton 0)

  have hsum : (fun c => ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k (u * c))) =ᵐ[volume]
      fun c => ∑ z ∈ G.rootSet s (u * c), F z := by
    filter_upwards [hae] with c hc
    rw [Formalism.FourierDecayAlt.P.PBK.sum_rootSet_eq_range hs (mul_ne_zero hu hc)]
  have hbr := fun k => Formalism.FourierDecayAlt.P.PBK.rootBranch s k hs u hu F hF
  refine ⟨(integrable_finsetSum _ fun k _ => (hbr k).1).congr hsum, ?_⟩
  calc ∫ c, ∑ z ∈ G.rootSet s (u * c), F z
      = ∫ c, ∑ k ∈ Finset.range s, F (NthRootMeasurability.R s k (u * c)) := integral_congr_ae hsum.symm
    _ = ∑ k ∈ Finset.range s, ∫ c, F (NthRootMeasurability.R s k (u * c)) :=
        integral_finsetSum _ fun k _ => (hbr k).1
    _ = ∑ k ∈ Finset.range s, ∫ z in NthRootMeasurability.A s k, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z :=
        Finset.sum_congr rfl fun k _ => (hbr k).2
    _ = ∫ z in ⋃ k ∈ Finset.range s, NthRootMeasurability.A s k, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z :=
        (integral_biUnion_finset _ (fun k _ => Formalism.FourierDecayAlt.P.NthRootMeasurability.measurableSet_A s k)
          (Formalism.FourierDecayAlt.P.NthRootMeasurability.A_disjoint s hs) (fun k _ => hF.integrableOn)).symm
    _ = ∫ z in ({0}ᶜ : Set ℂ), ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
        rw [Formalism.FourierDecayAlt.P.NthRootMeasurability.A_union s hs]
    _ = ∫ z, ‖u⁻¹ * (s * z ^ (s - 1))‖ ^ 2 • F z := by
        rw [MeasureTheory.restrict_compl_singleton]

end change

section asym

def lamR (s : ℕ) (σ x : ℂ) : ℂ := (x / (x + σ)) ^ (s - 1)

def rhoR (s : ℕ) (σ x : ℂ) : ℂ := lamR s σ x ^ ((s : ℂ)⁻¹)

theorem eventually_ne_zero_add (σ : ℂ) : ∀ᶠ x in cocompact ℂ, x ≠ 0 ∧ x + σ ≠ 0 := by
  have h1 : ∀ᶠ x in cocompact ℂ, x ≠ 0 := (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have h2 : ∀ᶠ x in cocompact ℂ, x ≠ -σ := (isCompact_singleton (x := -σ)).compl_mem_cocompact
  filter_upwards [h1, h2] with x hx1 hx2
  exact ⟨hx1, fun h => hx2 (eq_neg_of_add_eq_zero_left h)⟩

theorem tendsto_eps (σ : ℂ) : Tendsto (fun x : ℂ => σ / (x + σ)) (cocompact ℂ) (𝓝 0) := by
  have h : Tendsto (fun x : ℂ => x + σ) (cocompact ℂ) (cocompact ℂ) :=
    (Homeomorph.addRight σ).map_cocompact.le
  have hinv : Tendsto Inv.inv (cocompact ℂ) (𝓝 (0 : ℂ)) :=
    Metric.cobounded_eq_cocompact (α := ℂ) ▸ tendsto_inv₀_cobounded
  have h2 := (hinv.comp h).const_mul σ
  simpa [div_eq_mul_inv] using h2

theorem rhoR_eq_eventually (s : ℕ) (σ : ℂ) :
    ∀ᶠ x in cocompact ℂ, rhoR s σ x = (1 - σ / (x + σ)) ^ (((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹) := by
  have h1 : Tendsto (fun x : ℂ => 1 - σ / (x + σ)) (cocompact ℂ) (𝓝 1) := by
    simpa using (Formalism.FourierDecayAlt.P.PBK.tendsto_eps σ).const_sub 1
  have hlog : Tendsto (fun x : ℂ => Complex.log (1 - σ / (x + σ))) (cocompact ℂ) (𝓝 0) := by
    have h2 := (continuousAt_clog (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
    simpa [Function.comp_def] using h2
  have hpos : 0 < Real.pi / ((s : ℝ) + 1) := by positivity
  have hsmall : ∀ᶠ x in cocompact ℂ, Complex.log (1 - σ / (x + σ)) ∈ Metric.ball (0 : ℂ) (Real.pi / ((s : ℝ) + 1)) :=
    hlog (Metric.ball_mem_nhds 0 hpos)
  filter_upwards [Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add σ, hsmall] with x hx hlx
  rw [Metric.mem_ball, dist_zero_right] at hlx

  have hb : ‖Complex.log (1 - σ / (x + σ)) * ((s - 1 : ℕ) : ℂ)‖ < Real.pi := by
    rw [norm_mul, Complex.norm_natCast]
    have hs1 : ((s - 1 : ℕ) : ℝ) ≤ (s : ℝ) + 1 := by
      have : ((s - 1 : ℕ) : ℝ) ≤ s := by exact_mod_cast Nat.sub_le s 1
      linarith
    calc ‖Complex.log (1 - σ / (x + σ))‖ * ((s - 1 : ℕ) : ℝ)
        ≤ ‖Complex.log (1 - σ / (x + σ))‖ * ((s : ℝ) + 1) := mul_le_mul_of_nonneg_left hs1 (norm_nonneg _)
      _ < Real.pi / ((s : ℝ) + 1) * ((s : ℝ) + 1) := mul_lt_mul_of_pos_right hlx (by positivity)
      _ = Real.pi := by field_simp
  have him := Complex.abs_im_le_norm (Complex.log (1 - σ / (x + σ)) * ((s - 1 : ℕ) : ℂ))
  have hw : x / (x + σ) = 1 - σ / (x + σ) := by
    field_simp [hx.2]
    ring
  unfold Formalism.FourierDecayAlt.P.PBK.rhoR Formalism.FourierDecayAlt.P.PBK.lamR
  have hlt := abs_lt.mp (lt_of_le_of_lt him hb)
  rw [hw, ← Complex.cpow_natCast, ← Complex.cpow_mul _ hlt.1 hlt.2.le]

theorem tendsto_rhoR (s : ℕ) (σ : ℂ) : Tendsto (rhoR s σ) (cocompact ℂ) (𝓝 1) := by
  have h1 : Tendsto (fun x : ℂ => 1 - σ / (x + σ)) (cocompact ℂ) (𝓝 1) := by
    simpa using (Formalism.FourierDecayAlt.P.PBK.tendsto_eps σ).const_sub 1
  have h2 : Tendsto (fun x : ℂ => (1 - σ / (x + σ)) ^ (((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹)) (cocompact ℂ) (𝓝 1) := by
    have h3 := (continuousAt_cpow_const (b := ((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹)
      (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp h1
    simpa [Function.comp_def] using h3
  exact h2.congr' ((Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually s σ).mono fun x hx => hx.symm)

theorem tendsto_shift (s : ℕ) (hs : 1 ≤ s) (σ : ℂ) :
    Tendsto (fun x => (s : ℂ) * (rhoR s σ x * (x + σ) - x)) (cocompact ℂ) (𝓝 σ) := by
  set a : ℂ := ((s - 1 : ℕ) : ℂ) * (s : ℂ)⁻¹ with ha
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hsa : (s : ℂ) * (1 - a) = 1 := by
    rw [ha, Nat.cast_sub hs]
    field_simp
    ring
  rcases eq_or_ne σ 0 with rfl | hσ
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually s 0] with x hx
    rw [hx]
    simp
  ·
    have hφ : HasDerivAt (fun e : ℂ => (1 - e) ^ a) (-a) 0 := by
      have h1 : HasDerivAt (fun e : ℂ => 1 - e) (-1) 0 := by
        simpa using (hasDerivAt_id (0 : ℂ)).const_sub 1
      have h2 := h1.cpow_const (c := a) (by simp)
      simpa using h2
    have hslope := hasDerivAt_iff_tendsto_slope.mp hφ
    have hε : Tendsto (fun x : ℂ => σ / (x + σ)) (cocompact ℂ) (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨Formalism.FourierDecayAlt.P.PBK.tendsto_eps σ, ?_⟩
      filter_upwards [Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add σ] with x hx
      exact div_ne_zero hσ hx.2
    have hlim := (((hslope.comp hε).const_mul σ).add_const σ).const_mul (s : ℂ)
    have hval : (s : ℂ) * (σ * -a + σ) = σ := by linear_combination σ * hsa
    rw [hval] at hlim
    refine hlim.congr' ?_
    filter_upwards [Formalism.FourierDecayAlt.P.PBK.rhoR_eq_eventually s σ, Formalism.FourierDecayAlt.P.PBK.eventually_ne_zero_add σ] with x hx hx2
    rw [hx, ← ha]
    simp only [Function.comp_apply, slope_def_field, sub_zero, Complex.one_cpow]
    generalize (1 - σ / (x + σ)) ^ a = φv
    field_simp [hx2.2]
    ring

theorem tendsto_shift_ne (s : ℕ) (hs : 1 ≤ s) (σ ζ : ℂ) (hζ : ζ ≠ 1) :
    Tendsto (fun x => ζ * rhoR s σ x * (x + σ) - x) (cocompact ℂ) (cocompact ℂ) := by
  have hρ := Formalism.FourierDecayAlt.P.PBK.tendsto_rhoR s σ
  have hζ1 : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ)
  have hA : ∀ᶠ x in cocompact ℂ, ‖ζ - 1‖ / 2 < ‖ζ * rhoR s σ x - 1‖ := by
    have h2 : Tendsto (fun x => ‖ζ * rhoR s σ x - 1‖) (cocompact ℂ) (𝓝 ‖ζ * 1 - 1‖) :=
      ((hρ.const_mul ζ).sub_const 1).norm
    rw [mul_one] at h2
    exact h2.eventually (lt_mem_nhds (by linarith))
  have hB : ∀ᶠ x in cocompact ℂ, ‖ζ * rhoR s σ x * σ‖ < ‖ζ * σ‖ + 1 := by
    have h2 : Tendsto (fun x => ‖ζ * rhoR s σ x * σ‖) (cocompact ℂ) (𝓝 ‖ζ * 1 * σ‖) :=
      ((hρ.const_mul ζ).mul_const σ).norm
    rw [mul_one] at h2
    exact h2.eventually (gt_mem_nhds (by linarith))
  have hc : comap norm atTop = cocompact ℂ := by rw [comap_norm_atTop, Metric.cobounded_eq_cocompact]
  refine (tendsto_comap_iff.mpr ?_).mono_right hc.le
  have hlow : Tendsto (fun x : ℂ => ‖ζ - 1‖ / 2 * ‖x‖ + -(‖ζ * σ‖ + 1)) (cocompact ℂ) atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_norm_cocompact_atTop.const_mul_atTop (by linarith))
  refine tendsto_atTop_mono' _ ?_ hlow
  filter_upwards [hA, hB] with x hxA hxB

  have heq : ζ * rhoR s σ x * (x + σ) - x = (ζ * rhoR s σ x - 1) * x + ζ * rhoR s σ x * σ := by ring
  have htri := norm_add_le ((ζ * rhoR s σ x - 1) * x + ζ * rhoR s σ x * σ) (-(ζ * rhoR s σ x * σ))
  rw [add_neg_cancel_right, norm_neg, norm_mul] at htri
  have hmul : ‖ζ - 1‖ / 2 * ‖x‖ ≤ ‖ζ * rhoR s σ x - 1‖ * ‖x‖ :=
    mul_le_mul_of_nonneg_right hxA.le (norm_nonneg _)
  simp only [Function.comp_apply, heq]
  linarith

end asym

end

end Formalism.FourierDecayAlt.P.PBK
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntegralPsiMoving
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem norm_psi (β w : ℂ) : ‖G.psi β w‖ = 1 := by
  unfold G.psi
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_psi (β : ℂ) : Continuous (G.psi β) := by
  unfold G.psi
  fun_prop

def freq (β w : ℂ) : ℂ := ((2 * Real.pi)⁻¹ : ℝ) • (-(conj (β * w)))

theorem psi_eq_fourierChar (β w z : ℂ) :
    G.psi β (w * z) = ((Real.fourierChar (-⟪z, freq β w⟫_ℝ) : Circle) : ℂ) := by
  rw [Real.fourierChar_apply, G.psi, freq, real_inner_smul_right, Complex.inner]
  congr 1
  have hre : (-conj (β * w) * conj z).re = -(β * (w * z)).re := by
    simp only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
    ring
  rw [hre]
  push_cast
  field_simp

theorem tendsto_freq (β : ℂ) (hβ : β ≠ 0) : Tendsto (freq β) (cocompact ℂ) (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded, Metric.cobounded_eq_cocompact]
  have hn : ∀ w, ‖freq β w‖ = ((2 * Real.pi)⁻¹ * ‖β‖) * ‖w‖ := by
    intro w
    rw [freq, norm_smul, norm_neg, Complex.norm_conj, norm_mul, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    ring
  simp_rw [hn]
  exact (tendsto_norm_cocompact_atTop).const_mul_atTop (by positivity)

theorem tendsto_integral_psi (β : ℂ) (hβ : β ≠ 0) (f : ℂ → E) :
    Tendsto (fun w => ∫ z, G.psi β (w * z) • f z) (cocompact ℂ) (𝓝 0) := by
  have RL := (tendsto_integral_exp_inner_smul_cocompact f).comp (tendsto_freq β hβ)
  refine RL.congr fun w => ?_
  simp only [Function.comp_apply]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [psi_eq_fourierChar, Circle.smul_def]

theorem norm_integral_psi_sub_le (β w : ℂ) (f g : ℂ → E) (hf : Integrable f) (hg : Integrable g) :
    ‖(∫ z, G.psi β (w * z) • f z) - ∫ z, G.psi β (w * z) • g z‖ ≤ ∫ z, ‖f z - g z‖ := by
  have hfi : Integrable (fun z => G.psi β (w * z) • f z) :=
    hf.bdd_smul 1 ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => (norm_psi β _).le)
  have hgi : Integrable (fun z => G.psi β (w * z) • g z) :=
    hg.bdd_smul 1 ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun z => (norm_psi β _).le)
  rw [← integral_sub hfi hgi]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun _ => norm_nonneg _) (hf.sub hg).norm (Eventually.of_forall fun z => ?_))
  simp only [← smul_sub, norm_smul, norm_psi, one_mul, le_refl]

theorem tendsto_integral_psi_moving {α : Type} {l : Filter α} (β : ℂ) (hβ : β ≠ 0) (f : α → ℂ → E)
    (f0 : ℂ → E) (hf0 : Integrable f0) (hfi : ∀ᶠ x in l, Integrable (f x))
    (hf : Tendsto (fun x => ∫ z, ‖f x z - f0 z‖) l (𝓝 0)) (w : α → ℂ) (hw : Tendsto w l (cocompact ℂ)) :
    Tendsto (fun x => ∫ z, G.psi β (w x * z) • f x z) l (𝓝 0) := by
  have h0 := (tendsto_integral_psi β hβ f0).comp hw
  rw [← add_zero (0 : E)]
  have hsplit : ∀ᶠ x in l, ∫ z, G.psi β (w x * z) • f x z =
      ((∫ z, G.psi β (w x * z) • f x z) - ∫ z, G.psi β (w x * z) • f0 z) +
        ∫ z, G.psi β (w x * z) • f0 z := by
    filter_upwards with x
    abel
  refine Tendsto.congr' (EventuallyEq.symm hsplit) (Tendsto.add ?_ h0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hf
  filter_upwards [hfi] with x hx
  exact norm_integral_psi_sub_le β (w x) (f x) f0 hx hf0

theorem continuous_integral_psi (β : ℂ) (f : ℂ → E) (hf : Integrable f) :
    Continuous (fun w => ∫ z, G.psi β (w * z) • f z) := by
  refine continuous_of_dominated (bound := fun z => ‖f z‖) (fun w => ?_) (fun w => ?_) hf.norm ?_
  · exact (((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable).smul hf.1
  · exact Eventually.of_forall fun z => by rw [norm_smul, norm_psi, one_mul]
  · exact Eventually.of_forall fun z =>
      ((continuous_psi β).comp (continuous_id.mul continuous_const)).smul continuous_const

theorem tendsto_integral_psi_conv {α : Type} {l : Filter α} (β : ℂ) (f : α → ℂ → E)
    (f0 : ℂ → E) (hf0 : Integrable f0) (hfi : ∀ᶠ x in l, Integrable (f x))
    (hf : Tendsto (fun x => ∫ z, ‖f x z - f0 z‖) l (𝓝 0)) (w : α → ℂ) (σ : ℂ) (hw : Tendsto w l (𝓝 σ)) :
    Tendsto (fun x => ∫ z, G.psi β (w x * z) • f x z) l (𝓝 (∫ z, G.psi β (σ * z) • f0 z)) := by
  have h0 := ((continuous_integral_psi β f0 hf0).tendsto σ).comp hw
  rw [← zero_add (∫ z, G.psi β (σ * z) • f0 z)]
  have hsplit : ∀ᶠ x in l, ∫ z, G.psi β (w x * z) • f x z =
      ((∫ z, G.psi β (w x * z) • f x z) - ∫ z, G.psi β (w x * z) • f0 z) +
        ∫ z, G.psi β (w x * z) • f0 z := by
    filter_upwards with x
    abel
  refine Tendsto.congr' (EventuallyEq.symm hsplit) (Tendsto.add ?_ h0)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hf
  filter_upwards [hfi] with x hx
  exact norm_integral_psi_sub_le β (w x) (f x) f0 hx hf0

end

end Formalism.FourierDecayAlt.P.PBK
end

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section main

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def mainD (s : ℕ) (β ε : ℂ) (bt : ℂ → H) (x D : ℂ) : H :=
  ∑ z ∈ G.rootSet s (ε * D), G.psi β ((s : ℂ) * z * x) • bt z

def bz (s : ℕ) (bt : ℂ → H) (z : ℂ) : H := (((s : ℝ) * ‖z‖ ^ (s - 1) : ℝ) : ℂ) • bt z

def pairD (s : ℕ) (β ε : ℂ) (bt bt' : ℂ → H) (x x' ρ : ℂ) : ℂ :=
  ∫ D, ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ

theorem psi_conj_mul (β a b : ℂ) : conj (G.psi β a) * G.psi β b = G.psi β (b - a) := by
  unfold G.psi
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, mul_sub, Complex.sub_re]
  push_cast
  ring

def termZ (s : ℕ) (β : ℂ) (bt bt' : ℂ → H) (x x' ρ ζ z : ℂ) : ℂ :=
  G.psi β ((s : ℂ) * (ζ * ρ * x' - x) * z) • ⟪bz s bt z, ((‖ρ‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ * z)⟫_ℂ

theorem integrable_termZ {s : ℕ} (_hs : s ≠ 0) (β : ℂ) {bt bt' : ℂ → H} (hb : MemLp (bz s bt) 2 volume)
    (hb' : MemLp (bz s bt') 2 volume) (x x' ρ ζ : ℂ) (hρ : ρ ≠ 0) (hζ : ζ ≠ 0) :
    Integrable (termZ s β bt bt' x x' ρ ζ) := by
  have hd : MemLp (fun z => ((‖ρ‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ * z)) 2 volume :=
    (memLp_comp_mul hb' (ζ * ρ) (mul_ne_zero hζ hρ)).const_smul _
  have hi := integrable_inner_of_memLp hb hd
  refine hi.bdd_smul 1 ?_ (Eventually.of_forall fun z => (norm_psi β _).le)
  exact ((continuous_psi β).comp (continuous_const.mul continuous_id)).aestronglyMeasurable

theorem pairD_eq {s : ℕ} (hs : s ≠ 0) (β : ℂ) {ε : ℂ} (hε : ‖ε‖ = 1) {bt bt' : ℂ → H}
    (hb : MemLp (bz s bt) 2 volume) (hb' : MemLp (bz s bt') 2 volume) (x x' ρ : ℂ) (hρ : ρ ≠ 0) :
    pairD s β ε bt bt' x x' ρ = ∑ ζ ∈ G.rootSet s 1, ∫ z, termZ s β bt bt' x x' ρ ζ z := by
  have hε0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hζ0 : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 0 := fun ζ hζ h0 => by
    have := norm_of_mem_rootSet_one hs hζ; rw [h0, norm_zero] at this; exact zero_ne_one this

  set Φ : ℂ → ℂ := fun z => ∑ ζ ∈ G.rootSet s 1,
    (conj (G.psi β ((s : ℂ) * z * x)) * G.psi β ((s : ℂ) * (ζ * ρ * z) * x')) *
      (((‖ρ‖ ^ s : ℝ) : ℂ) * ⟪bt z, bt' (ζ * ρ * z)⟫_ℂ) with hΦ
  have hjac : ∀ z : ℂ, ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • Φ z =
      ∑ ζ ∈ G.rootSet s 1, termZ s β bt bt' x x' ρ ζ z := by
    intro z
    rw [hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ζ hζ => ?_
    have hζn := norm_of_mem_rootSet_one hs hζ
    have hn : ‖ζ * ρ * z‖ = ‖ρ‖ * ‖z‖ := by rw [norm_mul, norm_mul, hζn, one_mul]
    have hj : ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 = ((s : ℝ) * ‖z‖ ^ (s - 1)) ^ 2 := by
      rw [norm_mul, norm_inv, hε, inv_one, one_mul, norm_mul, norm_pow, Complex.norm_natCast]
    have hps : conj (G.psi β ((s : ℂ) * z * x)) * G.psi β ((s : ℂ) * (ζ * ρ * z) * x') =
        G.psi β ((s : ℂ) * (ζ * ρ * x' - x) * z) := by
      rw [psi_conj_mul]; congr 1; ring
    have hρs : ‖ρ‖ ^ s = ‖ρ‖ * ‖ρ‖ ^ (s - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [hj, hps]
    simp only [termZ, bz, inner_smul_left, inner_smul_right, Complex.conj_ofReal, smul_eq_mul, hn, hρs, mul_pow,
      Complex.real_smul]
    push_cast
    ring
  have hint : Integrable (fun z => ‖ε⁻¹ * ((s : ℂ) * z ^ (s - 1))‖ ^ 2 • Φ z) := by
    simp_rw [hjac]
    exact integrable_finsetSum _ fun ζ hζ => integrable_termZ hs β hb hb' x x' ρ ζ hρ (hζ0 ζ hζ)
  obtain ⟨-, hch⟩ := integral_sum_rootSet s hs ε hε0 Φ hint

  have hD : ∀ D : ℂ, D ≠ 0 → ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ =
      ∑ z ∈ G.rootSet s (ε * D), Φ z := by
    intro D hD0
    rw [inner_smul_right, mainD, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun z hz => ?_
    have hzs : z ^ s = ε * D := (mem_rootSet' hs).1 hz
    have hw : ε * D ≠ 0 := mul_ne_zero hε0 hD0
    have hrD : ε * (ρ ^ s * D) = ρ ^ s * (ε * D) := by ring
    rw [mainD, hrD, sum_rootSet_mul hs hw hzs rfl (pow_ne_zero _ hρ), inner_sum, Finset.mul_sum, hΦ]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [inner_smul_left, inner_smul_right]
    ring
  have hDae : (fun D => ⟪mainD s β ε bt x D, ((‖ρ‖ ^ s : ℝ) : ℂ) • mainD s β ε bt' x' (ρ ^ s * D)⟫_ℂ) =ᵐ[volume]
      fun D => ∑ z ∈ G.rootSet s (ε * D), Φ z := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with D hD0
    exact hD D hD0
  rw [pairD, integral_congr_ae hDae, hch]
  simp_rw [hjac]
  exact integral_finsetSum _ fun ζ hζ => integrable_termZ hs β hb hb' x x' ρ ζ hρ (hζ0 ζ hζ)

theorem tendsto_smul_cocompact {α : Type} {l : Filter α} (c : ℂ) (hc : c ≠ 0) (y : α → ℂ)
    (hy : Tendsto y l (cocompact ℂ)) : Tendsto (fun a => c * y a) l (cocompact ℂ) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded] at hy ⊢
  simp only [norm_mul]
  exact hy.const_mul_atTop (norm_pos_iff.mpr hc)

theorem tendsto_pairD {s : ℕ} (hs : s ≠ 0) {β : ℂ} (hβ : β ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {bt bt' : ℂ → H}
    (hb : MemLp (bz s bt) 2 volume) (hb' : MemLp (bz s bt') 2 volume) {α : Type} {l : Filter α}
    (x x' ρ : α → ℂ) (σ : ℂ) (hρ0 : ∀ᶠ a in l, ρ a ≠ 0) (hρ : Tendsto ρ l (𝓝 1))
    (hsh : Tendsto (fun a => (s : ℂ) * (ρ a * x' a - x a)) l (𝓝 σ))
    (hne : ∀ ζ ∈ G.rootSet s 1, ζ ≠ 1 → Tendsto (fun a => ζ * ρ a * x' a - x a) l (cocompact ℂ)) :
    Tendsto (fun a => pairD s β ε bt bt' (x a) (x' a) (ρ a)) l
      (𝓝 (∫ z, G.psi β (σ * z) • ⟪bz s bt z, bz s bt' z⟫_ℂ)) := by
  set L : ℂ := ∫ z, G.psi β (σ * z) • ⟪bz s bt z, bz s bt' z⟫_ℂ with hL
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  have hlim : ∀ ζ ∈ G.rootSet s 1, Tendsto (fun a => ∫ z, termZ s β bt bt' (x a) (x' a) (ρ a) ζ z) l
      (𝓝 (if ζ = 1 then L else 0)) := by
    intro ζ hζ
    have hζn := norm_of_mem_rootSet_one hs hζ
    have hζ0 : ζ ≠ 0 := fun h0 => by rw [h0, norm_zero] at hζn; exact zero_ne_one hζn
    have hf0 : Integrable (fun z => ⟪bz s bt z, bz s bt' (ζ * z)⟫_ℂ) :=
      integrable_inner_of_memLp hb (memLp_comp_mul hb' ζ hζ0)
    have hfi : ∀ᶠ a in l, Integrable (fun z => ⟪bz s bt z, ((‖ρ a‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ a * z)⟫_ℂ) := by
      filter_upwards [hρ0] with a ha
      exact integrable_inner_of_memLp hb ((memLp_comp_mul hb' (ζ * ρ a) (mul_ne_zero hζ0 ha)).const_smul _)
    have hL1 : Tendsto (fun a => ∫ z, ‖⟪bz s bt z, ((‖ρ a‖ : ℝ) : ℂ) • bz s bt' (ζ * ρ a * z)⟫_ℂ -
        ⟪bz s bt z, bz s bt' (ζ * z)⟫_ℂ‖) l (𝓝 0) := by
      have hζρ : Tendsto (fun a => ζ * ρ a) l (𝓝 ζ) := by
        simpa using (tendsto_const_nhds (x := ζ)).mul hρ
      have h1 := (tendsto_inner_dil (bz s bt) (bz s bt') hb hb' ζ hζ0).comp hζρ
      refine h1.congr fun a => ?_
      simp only [Function.comp_apply, norm_mul, hζn, one_mul, Complex.ofReal_one, one_smul]
    by_cases h1 : ζ = 1
    · subst h1
      rw [if_pos rfl]
      have hw : Tendsto (fun a => (s : ℂ) * (1 * ρ a * x' a - x a)) l (𝓝 σ) := by simpa using hsh
      have := tendsto_integral_psi_conv β _ _ hf0 hfi hL1 _ σ hw
      simpa [termZ, hL] using this
    · rw [if_neg h1]
      have hw := tendsto_smul_cocompact (s : ℂ) hs0 _ (hne ζ hζ h1)
      have := tendsto_integral_psi_moving β hβ _ _ hf0 hfi hL1 _ hw
      simpa [termZ, mul_assoc] using this
  have hsum := tendsto_finsetSum (G.rootSet s 1) hlim
  rw [Finset.sum_ite_eq' (G.rootSet s 1) 1 (fun _ => L), if_pos (one_mem_rootSet_one hs)] at hsum
  refine hsum.congr' ?_
  filter_upwards [hρ0] with a ha
  exact (pairD_eq hs β hε hb hb' (x a) (x' a) (ρ a) ha).symm

end main

end

end Formalism.FourierDecayAlt.P.PBK
