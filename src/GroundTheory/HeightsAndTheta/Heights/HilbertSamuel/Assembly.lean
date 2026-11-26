module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageChi
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiBounds
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegralInt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRealGramComparison
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace RealGramComparison

open MvPolynomial MeasureTheory Filter Asymptotics Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder ComplexConjugate Matrix

noncomputable section

set_option linter.unusedSectionVars false

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def dVGram (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  bGram d.dV (fun k y => secFun (b k) (resPt d y)) fun y => wgt d.m n (resPt d y)

theorem pairVal_eq (m : ConeMetric ℂ (Ix κ)) (n : ℕ) (b b' : MvPolynomial (Ix κ) ℚ) (z : Ix κ → ℂ) :
    pairVal m n b b' z = starRingEnd ℂ (secFun b' z) * secFun b z * (wgt m n z : ℂ) := by
  simp only [pairVal, secFun, wgt, div_eq_mul_inv]
  push_cast
  ring

theorem resCGram_eq (d : HSMDatum D Ω κ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    resCGram d n b = (dVGram d n b).transpose := by
  ext k l
  simp only [resCGram, dVGram, bGram, Matrix.transpose_apply, Matrix.of_apply, pairVal_eq]

theorem integrable_dV (d : HSMDatum D Ω κ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (i j : Fin r) :
    Integrable (fun y => starRingEnd ℂ (secFun (b i) (resPt d y)) * secFun (b j) (resPt d y) *
      (wgt d.m n (resPt d y) : ℂ)) d.dV := by
  have := d.vol.1
  have hc := ResSym.continuous_degZero_resPt d (ResSym.continuousOn_gramFun d.smooth n (b i) (b j))
    fun c z hc => ResSym.gramFun_smul (hb i) (hb j) c z hc
  exact integrableOn_univ.1 (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem quad_bGram {X : Type*} [MeasurableSpace X] (μ : Measure X) {r : ℕ} (s : Fin r → X → ℂ) (w : X → ℝ)
    (hint : ∀ i j, Integrable (fun x => starRingEnd ℂ (s i x) * s j x * (w x : ℂ)) μ) (c : Fin r → ℂ) :
    (star c ⬝ᵥ (bGram μ s w *ᵥ c)).re = bNormSq μ s w c := by
  rw [dot_bGram μ s w hint c, Complex.ofReal_re]

theorem isHermitian_ofReal_smul {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ} (hA : A.IsHermitian) (t : ℝ) :
    ((t : ℂ) • A).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_smul, hA.eq, Complex.star_def, Complex.conj_ofReal]

theorem re_det_ofReal_smul {r : ℕ} (t : ℝ) (A : Matrix (Fin r) (Fin r) ℂ) :
    ((t : ℂ) • A).det.re = t ^ r * A.det.re := by
  rw [Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem re_det_le_of_quad {r : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ} (hA : A.PosSemidef) (hB : B.IsHermitian)
    (t : ℝ) (h : ∀ c : Fin r → ℂ, (star c ⬝ᵥ (A *ᵥ c)).re ≤ t * (star c ⬝ᵥ (B *ᵥ c)).re) :
    A.det.re ≤ t ^ r * B.det.re := by
  have hsub := psd_sub_of_quad_le (isHermitian_ofReal_smul hB t) hA.isHermitian fun c => by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact h c
  have := GroundTheory.Heights₂.Heights.MCDet.re_det_mono hA hsub
  simp only [RCLike.re_to_complex] at this
  rwa [re_det_ofReal_smul] at this

theorem abs_sub_le (hR : ResolutionSupBound.Statement) (d : HSMDatum D Ω κ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n : ℕ, 1 ≤ n →
      |resChi d n - resCChi d n| ≤
        (finrank ℤ (sec ℤ d.x n) : ℝ) * (Real.log 2 + Real.log K + D * Real.log n) := by
  classical
  obtain ⟨C, hC⟩ := hR D Ω κ d
  refine ⟨max (C ^ 2) 1, le_max_right _ _, fun n hn => ?_⟩
  set K := max (C ^ 2) 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogK := Real.log_nonneg hK1
  have hlogn := Real.log_nonneg hn1
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hL : 0 ≤ Real.log 2 + Real.log K + D * Real.log n := by positivity
  by_cases h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2
  swap
  · simp only [resChi, resCChi, dif_neg h, sub_zero, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hL
  rw [ResSym.resChi_eq d n h]
  simp only [resCChi, dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r, b⟩ := p
  have hb : IsSecBasis d.x n b := hp
  have hrk : (r : ℝ) = finrank ℤ (sec ℤ d.x n) := by exact_mod_cast hb.card_eq
  rw [resCGram_eq, Matrix.det_transpose, ← hrk]
  have hintG := integrable_dV d hb.1
  have hintH := ResSym.integrable_gram d hb.1
  have key : ∀ c : Fin r → ℂ,
      bNormSq d.dV (fun k y => secFun (b k) (resPt d y)) (fun y => wgt d.m n (resPt d y)) c ≤
        2 * bNormSq (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c ∧
      bNormSq (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c ≤
        K * (n : ℝ) ^ D *
          bNormSq d.dV (fun k y => secFun (b k) (resPt d y)) (fun y => wgt d.m n (resPt d y)) c := by
    intro c
    have := d.vol.1
    set g : (Ix κ → ℂ) → ℝ := fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt d.m n z with hg
    have hnn : ∀ z, 0 ≤ g z := fun z =>
      mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg z) _))
    have hcont : ContinuousOn g {0}ᶜ := continuousOn_normSq d.smooth b c
    have hdeg : ∀ (a : ℂ) z, a ≠ 0 → g (a • z) = g z := fun a z ha => isDegZero_normSq hb.1 c a z ha
    have eG : bNormSq d.dV (fun k y => secFun (b k) (resPt d y)) (fun y => wgt d.m n (resPt d y)) c =
        ∫ y, g (resPt d y) ∂d.dV := rfl
    have eH : bNormSq (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) c =
        2⁻¹ * ((∫ y, g (resPt d y) ∂d.dV) + ∫ y, g (conjPt (resPt d y)) ∂d.dV) := by
      rw [← smul_eq_mul, ← ResSym.integral_symMeasure d hcont hdeg]
      rfl
    have hA : 0 ≤ ∫ y, g (resPt d y) ∂d.dV := integral_nonneg fun y => hnn _
    have hB : 0 ≤ ∫ y, g (conjPt (resPt d y)) ∂d.dV := integral_nonneg fun y => hnn _
    refine ⟨by rw [eG, eH]; linarith, ?_⟩

    set f : MvPolynomial (Ix κ) ℂ := ∑ k, MvPolynomial.C (c k) * map (algebraMap ℚ ℂ) (b k) with hf
    have hfh : f.IsHomogeneous n := by
      refine MvPolynomial.IsHomogeneous.sum _ _ _ fun k _ => ?_
      obtain ⟨g', hg', hgb⟩ := hb.1 k
      rw [hgb, MvPolynomial.map_map]
      exact (hg'.map _).C_mul _
    have hevf : ∀ w, eval w f = ∑ i, c i * secFun (b i) w := by
      intro w
      set_option synthInstance.maxHeartbeats 100000 in
        simp [hf, secFun, map_sum]
    have hpt : ∀ w : Ix κ → ℂ, w ≠ 0 → ptNorm d.m (RingHom.id ℂ) n f w ^ 2 = g w := by
      intro w hw
      rw [ptNorm, MvPolynomial.map_id, hevf]
      simp only [hg, wgt]
      rw [div_pow, ← pow_mul, mul_comm n 2, div_eq_mul_inv]
    have hL2 : resolutionVolumeL2Complex d n f ^ 2 = ∫ y, g (resPt d y) ∂d.dV := by
      rw [resolutionVolumeL2Complex, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]
      exact integral_congr_ae (Eventually.of_forall fun y => hpt _ (ResSym.resPt_mem_pts d y).1)
    have hpow : ((n : ℝ) ^ ((D : ℝ) / 2)) ^ 2 = (n : ℝ) ^ D := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n),
        show (D : ℝ) / 2 * ((2 : ℕ) : ℝ) = (D : ℝ) by push_cast; ring, Real.rpow_natCast]
    set S := K * (n : ℝ) ^ D * ∫ y, g (resPt d y) ∂d.dV with hS
    have hsup : ∀ z ∈ pts (coordIdeal ℤ d.x), g z ≤ S := by
      intro z hz
      have h1 := hC n hn f hfh z hz
      have h0 : 0 ≤ ptNorm d.m (RingHom.id ℂ) n f z :=
        div_nonneg (norm_nonneg _) (pow_nonneg (d.m.nonneg z) _)
      have h2 := pow_le_pow_left₀ h0 h1 2
      rw [hpt z hz.1] at h2
      calc g z ≤ (C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2Complex d n f) ^ 2 := h2
        _ = C ^ 2 * (n : ℝ) ^ D * ∫ y, g (resPt d y) ∂d.dV := by rw [mul_pow, mul_pow, hpow, hL2]
        _ ≤ S := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hA
    have hi1 : Integrable (fun y => g (resPt d y)) d.dV :=
      integrableOn_univ.1 ((ResSym.continuous_degZero_resPt d hcont hdeg).continuousOn.integrableOn_compact
        isCompact_univ)
    have hi2 : Integrable (fun y => g (conjPt (resPt d y))) d.dV :=
      integrableOn_univ.1 ((ResSym.continuous_degZero_conj_resPt d hcont hdeg).continuousOn.integrableOn_compact
        isCompact_univ)
    have hS1 : ∫ y, g (resPt d y) ∂d.dV ≤ S := by
      have := integral_mono hi1 (integrable_const S) fun y => hsup _ (ResSym.resPt_mem_pts d y)
      simpa using this
    have hS2 : ∫ y, g (conjPt (resPt d y)) ∂d.dV ≤ S := by
      have := integral_mono hi2 (integrable_const S) fun y =>
        hsup _ (ResSym.conjPt_mem_pts (ResSym.resPt_mem_pts d y))
      simpa using this
    rw [eH, eG]
    rw [hS] at hS1 hS2
    linarith
  have hGpsd : (dVGram d n b).PosSemidef :=
    Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (bGram_isHermitian _ _ _) fun c => by
      rw [dVGram, dot_bGram _ _ _ hintG c]
      exact Complex.zero_le_real.mpr (integral_nonneg fun y =>
        mul_nonneg (by positivity) (inv_nonneg.mpr (pow_nonneg (d.m.nonneg _) _)))
  have hHpd := ResSym.posDef_gram d hb
  have d1 := re_det_le_of_quad hGpsd (bGram_isHermitian (ResSym.symMeasure d) (fun k => secFun (b k))
    (wgt d.m n)) 2 fun c => by
      rw [dVGram, quad_bGram _ _ _ hintG, quad_bGram _ _ _ hintH]
      exact (key c).1
  have d2 := re_det_le_of_quad hHpd.posSemidef (bGram_isHermitian d.dV
    (fun k y => secFun (b k) (resPt d y)) fun y => wgt d.m n (resPt d y)) (K * (n : ℝ) ^ D) fun c => by
      rw [quad_bGram _ _ _ hintG, quad_bGram _ _ _ hintH]
      exact (key c).2
  rw [← dVGram] at d2
  set G := dVGram d n b with hG
  set H := bGram (ResSym.symMeasure d) (fun k => secFun (b k)) (wgt d.m n) with hH
  have hHpos : 0 < H.det.re := by
    have := GroundTheory.Heights₂.Heights.MCDet.re_det_pos hHpd
    simpa using this
  have hKn : 0 < K * (n : ℝ) ^ D := by positivity
  have hGpos : 0 < G.det.re := by
    by_contra hle
    push Not at hle
    have : (K * (n : ℝ) ^ D) ^ r * G.det.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    linarith
  have l1 : Real.log G.det.re ≤ r * Real.log 2 + Real.log H.det.re := by
    have := Real.log_le_log hGpos d1
    rwa [Real.log_mul (by positivity) hHpos.ne', Real.log_pow] at this
  have l2 : Real.log H.det.re ≤ r * (Real.log K + D * Real.log n) + Real.log G.det.re := by
    have := Real.log_le_log hHpos d2
    rwa [Real.log_mul (by positivity) hGpos.ne', Real.log_pow, Real.log_mul (by positivity) (by positivity),
      Real.log_pow] at this
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have a1 := mul_nonneg hr0 hlog2
  have a2 := mul_nonneg hr0 (add_nonneg hlogK (mul_nonneg (Nat.cast_nonneg D) hlogn))
  rw [abs_le]
  constructor <;> nlinarith

theorem rank_le (hP : ProjectionBounds.Statement) (hF : PullFSExtension.Statement) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame d.x e) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, (finrank ℤ (sec ℤ d.x n) : ℝ) ≤ A * ((n : ℝ) + 1) ^ D := by
  obtain ⟨m₀, hs, hc, hp, hpull⟩ := hF D Ω κ d.x e hfr
  obtain ⟨k, E, C, -, -, -, -, hrank, -⟩ := hP D Ω κ (d.withMetric m₀ ⊥ hs hc bot_le hp) e hfr hpull
  refine ⟨(projDeg d.x e : ℝ) / D.factorial + |C|, by positivity, fun n => ?_⟩
  have h1 : (finrank ℤ (sec ℤ d.x n) : ℝ) - (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤
      C * ((n : ℝ) + 1) ^ (D - 1) := (abs_le.mp (hrank n)).2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ n + 1 := by linarith
  have h2 : (n : ℝ) ^ D ≤ ((n : ℝ) + 1) ^ D := pow_le_pow_left₀ hn0 (by linarith) D
  have h3 : ((n : ℝ) + 1) ^ (D - 1) ≤ ((n : ℝ) + 1) ^ D := pow_le_pow_right₀ hn1 (Nat.sub_le D 1)
  have h4 : C * ((n : ℝ) + 1) ^ (D - 1) ≤ |C| * ((n : ℝ) + 1) ^ D :=
    (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h3 (abs_nonneg C))
  have h5 : (projDeg d.x e : ℝ) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤
      (projDeg d.x e : ℝ) / D.factorial * ((n : ℝ) + 1) ^ D := by
    rw [div_mul_eq_mul_div]
    gcongr
  rw [add_mul]
  linarith

theorem proof (hR : ResolutionSupBound.Statement) (hP : ProjectionBounds.Statement)
    (hF : PullFSExtension.Statement) : RealGramComparison.Statement := by
  intro D Ω _ _ κ _ d e hfr
  obtain ⟨K, hK1, hK⟩ := abs_sub_le hR d
  obtain ⟨A, hA0, hA⟩ := rank_le hP hF d e hfr
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK := Real.log_nonneg hK1
  set B := (Real.log 2 + Real.log K) / Real.log 2 + D with hB
  have hB0 : 0 ≤ B := by positivity
  refine IsBigO.of_bound (A * 2 ^ D * B) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn0 := Real.log_nonneg hn1
  have hlog21 : Real.log 2 ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by norm_num) (by linarith)
  have hlogn : Real.log n ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log (by linarith) (by linarith)
  have hlog1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hL : Real.log 2 + Real.log K + D * Real.log n ≤ B * Real.log ((n : ℝ) + 1) := by
    have h1 : Real.log 2 + Real.log K ≤ (Real.log 2 + Real.log K) / Real.log 2 * Real.log ((n : ℝ) + 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
      nlinarith
    have h2 : (D : ℝ) * Real.log n ≤ D * Real.log ((n : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlogn (Nat.cast_nonneg _)
    rw [hB, add_mul]
    linarith
  have hL0 : 0 ≤ Real.log 2 + Real.log K + D * Real.log n := by positivity
  have hpow : ((n : ℝ) + 1) ^ D ≤ 2 ^ D * (n : ℝ) ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) D
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1))]
  calc |resChi d n - resCChi d n|
      ≤ (finrank ℤ (sec ℤ d.x n) : ℝ) * (Real.log 2 + Real.log K + D * Real.log n) := hK n hn
    _ ≤ (A * ((n : ℝ) + 1) ^ D) * (B * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul (hA n) hL hL0 (by positivity)
    _ ≤ (A * (2 ^ D * (n : ℝ) ^ D)) * (B * Real.log ((n : ℝ) + 1)) := by
        gcongr
    _ = A * 2 ^ D * B * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by ring

end

end RealGramComparison

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFSExtension
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4 ProjLine
open scoped Topology

noncomputable section

namespace PullFSExtension

theorem leviForm_comp_clm {E F : Type} [Fintype E] [Fintype F] (L : (E → ℂ) →L[ℂ] (F → ℂ))
    (φ : (F → ℂ) → ℝ) (z w : E → ℂ) (hφ : ContDiffAt ℝ 2 φ (L z)) :
    leviForm (fun y => φ (L y)) z w = leviForm φ (L z) (L w) := by
  set Lr : (E → ℂ) →L[ℝ] (F → ℂ) := L.restrictScalars ℝ with hLr
  have hLr' : ∀ y, Lr y = L y := fun _ => rfl
  have hev : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ 2 φ (L y) :=
    (L.continuous.tendsto z).eventually (hφ.eventually (by simp))
  have hfd : fderiv ℝ (fun y => φ (L y)) =ᶠ[𝓝 z]
      fun y => (ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr (fderiv ℝ φ (Lr y)) := by
    filter_upwards [hev] with y hy
    have h := (hy.differentiableAt (by norm_num)).hasFDerivAt.comp y Lr.hasFDerivAt
    exact h.fderiv
  have hd2 : DifferentiableAt ℝ (fderiv ℝ φ) (Lr z) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hD : HasFDerivAt
      (fun y => (ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr (fderiv ℝ φ (Lr y)))
      (((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).comp
        ((fderiv ℝ (fderiv ℝ φ) (Lr z)).comp Lr)) z :=
    ((ContinuousLinearMap.compL ℝ (E → ℂ) (F → ℂ) ℝ).flip Lr).hasFDerivAt.comp z
      (hd2.hasFDerivAt.comp z Lr.hasFDerivAt)
  unfold leviForm
  rw [hfd.fderiv_eq, hD.fderiv]
  have hI : Lr (Complex.I • w) = Complex.I • L w := by rw [hLr']; exact L.map_smul _ _
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.compL_apply, hI]
  rfl

theorem leviForm_congr {E : Type} [Fintype E] {φ ψ : (E → ℂ) → ℝ} {z : E → ℂ} (h : φ =ᶠ[𝓝 z] ψ)
    (w : E → ℂ) : leviForm φ z w = leviForm ψ z w := by
  have h1 : fderiv ℝ φ =ᶠ[𝓝 z] fderiv ℝ ψ := by
    filter_upwards [h.eventuallyEq_nhds] with y hy
    exact hy.fderiv_eq
  unfold leviForm
  rw [h1.fderiv_eq]

theorem normSqE_eq {J : Type} [Fintype J] (z : J → ℂ) : normSqE z = ∑ i, ‖z i‖ ^ 2 := by
  unfold normSqE
  rw [eL_apply, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

theorem normSqE_smul {J : Type} [Fintype J] (c : ℂ) (z : J → ℂ) :
    normSqE (c • z) = ‖c‖ ^ 2 * normSqE z := by
  simp only [normSqE_eq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

theorem normSqE_conj {J : Type} [Fintype J] (z : J → ℂ) :
    normSqE (fun i => (starRingEnd ℂ) (z i)) = normSqE z := by
  simp only [normSqE_eq, Complex.norm_conj]

theorem normSqE_zero {J : Type} [Fintype J] : normSqE (0 : J → ℂ) = 0 := by
  simp [normSqE_eq]

theorem contDiff_normSqE {J : Type} [Fintype J] {n : WithTop ℕ∞} : ContDiff ℝ n (normSqE (J := J)) := by
  have : normSqE (J := J) = fun z => ‖eL z‖ ^ 2 := rfl
  rw [this]
  exact (contDiff_norm_sq ℝ).comp (eL (J := J)).contDiff

variable {κ : Type} [Fintype κ] {D : ℕ}

def pr (e : Fin (D + 1) → Ix κ) : (Ix κ → ℂ) →L[ℂ] (Fin (D + 1) → ℂ) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.proj (e k)

def ratio (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) : ℝ := normSqE (pr e z) / normSqE z

theorem ratio_smul (e : Fin (D + 1) → Ix κ) {c : ℂ} (hc : c ≠ 0) (z : Ix κ → ℂ) :
    ratio e (c • z) = ratio e z := by
  unfold ratio
  rw [map_smul, normSqE_smul, normSqE_smul]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))

theorem ratio_conj (e : Fin (D + 1) → Ix κ) (z : Ix κ → ℂ) :
    ratio e (fun i => (starRingEnd ℂ) (z i)) = ratio e z := by
  unfold ratio
  have : pr e (fun i => (starRingEnd ℂ) (z i)) = fun k => (starRingEnd ℂ) (pr e z k) := rfl
  rw [this, normSqE_conj, normSqE_conj]

theorem contDiffAt_ratio (e : Fin (D + 1) → Ix κ) {z : Ix κ → ℂ} (hz : z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (ratio e) z :=
  (contDiff_normSqE.comp ((pr e).restrictScalars ℝ).contDiff).contDiffAt.div contDiff_normSqE.contDiffAt
    (normSqE_pos hz).ne'

def cut (δ t : ℝ) : ℝ := Real.smoothTransition ((t - δ / 4) / (δ / 4))

theorem cut_of_le {δ t : ℝ} (hδ : 0 < δ) (ht : t ≤ δ / 4) : cut δ t = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

theorem cut_of_ge {δ t : ℝ} (hδ : 0 < δ) (ht : δ / 2 ≤ t) : cut δ t = 1 :=
  Real.smoothTransition.one_of_one_le ((one_le_div (by linarith)).mpr (by linarith))

def gfac (δ t : ℝ) : ℝ := Real.exp (cut δ t * Real.log t / 2)

theorem contDiff_gfac {δ : ℝ} (hδ : 0 < δ) {n : ℕ∞} : ContDiff ℝ n (gfac δ) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  by_cases ht : t < δ / 4
  · have : gfac δ =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [gfac, cut_of_le hδ (le_of_lt hs)]
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have ht0 : t ≠ 0 := by intro h; subst h; linarith
    have hcut : ContDiff ℝ n (cut δ) := by
      have : cut δ = Real.smoothTransition ∘ fun t => (t - δ / 4) / (δ / 4) := rfl
      rw [this]
      exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
    exact Real.contDiff_exp.contDiffAt.comp t
      (((hcut.contDiffAt.mul (Real.contDiffAt_log.mpr ht0))).div_const _)

theorem gfac_of_ge {δ t : ℝ} (hδ : 0 < δ) (ht : δ / 2 ≤ t) : gfac δ t = Real.sqrt t := by
  have ht0 : 0 < t := by linarith
  rw [gfac, cut_of_ge hδ ht, one_mul, ← Real.log_sqrt ht0.le, Real.exp_log (Real.sqrt_pos.mpr ht0)]

def metric (e : Fin (D + 1) → Ix κ) (δ : ℝ) : ConeMetric ℂ (Ix κ) where
  ρ z := Real.sqrt (normSqE z) * gfac δ (ratio e z)
  pos z hz := mul_pos (Real.sqrt_pos.mpr (normSqE_pos hz)) (Real.exp_pos _)
  smul c z := by
    by_cases hc : c = 0
    · subst hc
      simp [normSqE_zero]
    rw [ratio_smul e hc, normSqE_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_assoc]

theorem metric_rho (e : Fin (D + 1) → Ix κ) (δ : ℝ) (z : Ix κ → ℂ) :
    (metric e δ).ρ z = Real.sqrt (normSqE z) * gfac δ (ratio e z) := rfl

theorem metric_of_ge (e : Fin (D + 1) → Ix κ) {δ : ℝ} (hδ : 0 < δ) {z : Ix κ → ℂ} (hz : z ≠ 0)
    (hr : δ / 2 ≤ ratio e z) : (metric e δ).ρ z = Real.sqrt (normSqE (pr e z)) := by
  rw [metric_rho, gfac_of_ge hδ hr, ← Real.sqrt_mul (normSqE_pos hz).le, ratio,
    mul_div_cancel₀ _ (normSqE_pos hz).ne']

theorem isSmoothMetric_metric (e : Fin (D + 1) → Ix κ) {δ : ℝ} (hδ : 0 < δ) :
    IsSmoothMetric (metric e δ) := by
  intro z hz
  have hz' : z ≠ 0 := hz
  refine ContDiffAt.contDiffWithinAt ?_
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Real.sqrt (normSqE y)) z :=
    contDiff_normSqE.contDiffAt.sqrt (normSqE_pos hz').ne'
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => gfac δ (ratio e y)) z :=
    (contDiff_gfac hδ).contDiffAt.comp z (contDiffAt_ratio e hz')
  exact h1.mul h2

theorem isConjInvariant_metric (e : Fin (D + 1) → Ix κ) (δ : ℝ) : IsConjInvariant (metric e δ) := by
  intro z
  rw [metric_rho, metric_rho, normSqE_conj, ratio_conj]

variable {Ω : Type} [Field Ω] [CharZero Ω] {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ}

theorem pr_ne_zero (hBP : ProjFrameBasePtFree.Statement) (hfr : IsProjFrame x e) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) : pr e z ≠ 0 := by
  intro h0
  apply hz.1
  funext i
  obtain ⟨u, j⟩ := i
  cases u
  obtain ⟨N, hN⟩ := hBP D Ω κ x e hfr () (fun _ => j)
  set ψ : MvPolynomial (Ix κ) ℤ →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ)) with hψ
  have hle : coordIdeal ℤ x ⊔ Ideal.span (Set.range fun k : Fin (D + 1) =>
      ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩) ≤ RingHom.ker ψ := by
    refine sup_le (fun f hf => RingHom.mem_ker.mpr (hz.2 f hf)) (Ideal.span_le.mpr ?_)
    rintro _ ⟨k, rfl⟩
    have hk : z (e k) = 0 := congrFun h0 k
    have he : (⟨(), (e k).2⟩ : Ix κ) = e k := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [SetLike.mem_coe, RingHom.mem_ker, hψ, RingHom.comp_apply, ReciprocityTheory.ChartRestriction.G.AI.I4.linForm, map_sum, map_mul,
      map_C, map_X, eval_C, eval_X, projMat]
    simp only [eq_intCast, Int.cast_ite, Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single (e k).2 (fun i _ hi => if_neg (Ne.symm hi))
      (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, he]
    exact hk
  have h1 := hle hN
  rw [RingHom.mem_ker] at h1
  simp only [hψ, RingHom.comp_apply, map_pow, map_X, eval_X, Finset.univ_unique,
    Finset.prod_singleton] at h1
  exact eq_zero_of_pow_eq_zero h1

theorem ratio_pos (hBP : ProjFrameBasePtFree.Statement) (hfr : IsProjFrame x e) {z : Ix κ → ℂ}
    (hz : z ∈ pts (coordIdeal ℤ x)) : 0 < ratio e z :=
  div_pos (normSqE_pos (pr_ne_zero hBP hfr hz)) (normSqE_pos hz.1)

theorem exists_ratio_lb (hBP : ProjFrameBasePtFree.Statement) (hfr : IsProjFrame x e) :
    ∃ δ > 0, ∀ z ∈ pts (coordIdeal ℤ x), δ ≤ ratio e z := by
  set S : Set (Ix κ → ℂ) :=
    {z | (∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0) ∧ normSqE z = 1} with hSdef
  have hSpts : ∀ z ∈ S, z ∈ pts (coordIdeal ℤ x) := fun z hz =>
    ⟨fun h0 => by
      have h1 := hz.2
      rw [h0, normSqE_zero] at h1
      exact zero_ne_one h1, hz.1⟩
  have hnorm : ∀ z ∈ pts (coordIdeal ℤ x), ∃ z' ∈ S, ratio e z' = ratio e z := by
    intro z hz
    have hq := normSqE_pos hz.1
    have hs := Real.sqrt_pos.mpr hq
    set c : ℂ := (((Real.sqrt (normSqE z))⁻¹ : ℝ) : ℂ) with hcdef
    have hcn : ‖c‖ = (Real.sqrt (normSqE z))⁻¹ := by
      rw [hcdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    have hc : c ≠ 0 := by
      intro h
      rw [h, norm_zero] at hcn
      exact (inv_pos.mpr hs).ne' hcn.symm
    refine ⟨c • z, ⟨(smul_mem_pts_coord x hz hc).2, ?_⟩, ratio_smul e hc z⟩
    rw [normSqE_smul, hcn, inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']
  have hSc : IsCompact S := by
    apply Metric.isCompact_of_isClosed_isBounded
    · have hA : IsClosed
          {z : Ix κ → ℂ | ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0} := by
        have h : {z : Ix κ → ℂ | ∀ f ∈ coordIdeal ℤ x, eval z (map (Int.castRingHom ℂ) f) = 0} =
            ⋂ f ∈ coordIdeal ℤ x, {z | eval z (map (Int.castRingHom ℂ) f) = 0} := by
          ext z
          simp
        rw [h]
        exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
      exact hA.inter (isClosed_eq (contDiff_normSqE (n := 0)).continuous continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : Ix κ → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
      have h1 : ‖z i‖ ^ 2 ≤ 1 := by
        rw [← hz.2, normSqE_eq]
        exact Finset.single_le_sum (f := fun i => ‖z i‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [norm_nonneg (z i)]
  have hcont : ContinuousOn (ratio e) S := fun z hz =>
    (contDiffAt_ratio e (hSpts z hz).1 (n := 0)).continuousAt.continuousWithinAt
  rcases S.eq_empty_or_nonempty with hS | hS
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    obtain ⟨z', hz', -⟩ := hnorm z hz
    rw [hS] at hz'
    simp at hz'
  · obtain ⟨z0, hz0, hmin⟩ := hSc.exists_isMinOn hS hcont
    refine ⟨ratio e z0, ratio_pos hBP hfr (hSpts z0 hz0), fun z hz => ?_⟩
    obtain ⟨z', hz', hr⟩ := hnorm z hz
    rw [← hr]
    exact hmin hz'

end PullFSExtension


open PullFSExtension in
theorem PullFSExtension.proof (hBP : ProjFrameBasePtFree.Statement) : PullFSExtension.Statement := by
  intro D Ω _ _ κ _ x e hfr
  obtain ⟨δ, hδ, hlb⟩ := exists_ratio_lb hBP hfr
  have hsm := isSmoothMetric_metric e hδ
  refine ⟨metric e δ, hsm, isConjInvariant_metric e δ, ⟨?_, ?_⟩, ?_⟩
  · refine hsm.mono fun z hz => ?_
    obtain ⟨i, hi⟩ := hz ()
    exact fun h0 => hi (congrFun h0 _)
  · intro z hz w _
    have hzp : z ∈ pts (coordIdeal ℤ x) :=
      ⟨fun h0 => by obtain ⟨i, hi⟩ := hz.1 (); exact hi (congrFun h0 _), hz.2⟩
    have hpz := pr_ne_zero hBP hfr hzp
    have hev : (fun y => Real.log ((HermLine.ofCone (metric e δ)).h y)) =ᶠ[𝓝 z]
        fun y => Real.log ((fsMetric (ι := Fin (D + 1))).ρ (pr e y)) := by
      have hr : ∀ᶠ y in 𝓝 z, δ / 2 < ratio e y :=
        (contDiffAt_ratio e hzp.1 (n := 0)).continuousAt.eventually
          (lt_mem_nhds (by linarith [hlb z hzp]))
      filter_upwards [hr, isOpen_ne.mem_nhds hzp.1] with y hy hy0
      change Real.log ((metric e δ).ρ y) = _
      rw [metric_of_ge e hδ hy0 hy.le, congrFun log_fs_eq (pr e y),
        Real.log_sqrt (by rw [normSqE_eq]; positivity)]
      ring
    have hφ : ContDiffAt ℝ 2 (fun u => Real.log ((fsMetric (ι := Fin (D + 1))).ρ u)) (pr e z) := by
      rw [log_fs_eq]
      exact contDiffAt_const.mul (contDiff_normSqE.contDiffAt.log (normSqE_pos hpz).ne')
    have key := leviForm_comp_clm (pr e) (fun u => Real.log ((fsMetric (ι := Fin (D + 1))).ρ u)) z w hφ
    beta_reduce at key
    rw [leviForm_congr hev w, key]
    exact leviForm_log_fs_nonneg hpz (pr e w)
  · intro z hz
    rw [metric_of_ge e hδ hz.1 (by linarith [hlb z hz]), normSqE_eq]
    rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem BlockImageChi.full : GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.BlockImageChi.proof

theorem ResChiBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiBounds.proof ResolutionSupBound.full

theorem ProjectionBounds.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ProjectionBounds.proof ResChiBounds.full

theorem PullFSExtension.full : GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullFSExtension.proof ProjFrameBasePtFree.full

theorem RealGramComparison.full : GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.RealGramComparison.proof ResolutionSupBound.full ProjectionBounds.full PullFSExtension.full

theorem ResChiIndex.full : GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.ResChiIndex.proof

theorem VeroneseMonoBasis.full : GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.VeroneseMonoBasis.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
