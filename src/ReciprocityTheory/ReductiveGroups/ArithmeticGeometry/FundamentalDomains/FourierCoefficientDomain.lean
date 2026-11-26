module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SpanColsMul
public import Lemmata.GeneralBFactBisForm.Imports
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD MeasureTheory Metric Set Filter
open scoped ComplexConjugate Topology

noncomputable section

section Cauchy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

lemma norm_fderiv_le {U : Set F} (hU : IsOpen U) {G : F → ℂ} (hG : DifferentiableOn ℂ G U)
    {y : F} {R C : ℝ} (hR : 0 < R) (hball : closedBall y R ⊆ U)
    (hC : ∀ z ∈ closedBall y R, ‖G z‖ ≤ C) : ‖fderiv ℂ G y‖ ≤ C / R := by
  first | exact Bl.general_b_fact_bis_form.goal1 .. | (apply Bl.general_b_fact_bis_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis_form.goal1 <;> assumption)

end Cauchy

section Param

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ}

theorem diffOn_param {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKm : MeasurableSet K)
    (A : (Fin n → ℝ) → F →L[ℂ] F) (hA : Continuous A) {U : Set F} (hU : IsOpen U)
    (hAU : ∀ t ∈ K, ∀ x ∈ U, A t x ∈ U) (G : F → ℂ) (hG : DifferentiableOn ℂ G U)
    (e : (Fin n → ℝ) → ℂ) (he : Continuous e) :
    DifferentiableOn ℂ (fun x => ∫ t in K, G (A t x) * e t) U := by
  intro x0 hx0
  have hcA : ∀ x, Continuous fun t => A t x := fun x => hA.clm_apply continuous_const
  set K0 := (fun t => A t x0) '' K with hK0def
  have hK0 : IsCompact K0 := hK.image (hcA x0)
  have hK0U : K0 ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact hAU t ht x0 hx0
  obtain ⟨δ, hδ, hδU⟩ := hK0.exists_cthickening_subset_open hU hK0U
  have hK1 : IsCompact (cthickening δ K0) := hK0.cthickening
  obtain ⟨C, hC⟩ := hK1.exists_bound_of_continuousOn (hG.continuousOn.mono hδU)
  obtain ⟨Am, hAm⟩ := hK.exists_bound_of_continuousOn hA.continuousOn
  obtain ⟨Me, hMe⟩ := hK.exists_bound_of_continuousOn he.continuousOn
  set A1 := max Am 1 with hA1def
  have hA1 : 0 < A1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  set ε := δ / 2 / A1 with hεdef
  have hε : 0 < ε := by positivity
  have hnear : ∀ t ∈ K, ∀ x ∈ ball x0 ε, closedBall (A t x) (δ / 2) ⊆ cthickening δ K0 := by
    intro t ht x hx z hz
    have hx' : ‖x - x0‖ < ε := by rw [← dist_eq_norm]; exact hx
    have h1 : dist (A t x) (A t x0) ≤ δ / 2 := by
      rw [dist_eq_norm, ← map_sub]
      calc ‖A t (x - x0)‖ ≤ ‖A t‖ * ‖x - x0‖ := (A t).le_opNorm _
        _ ≤ A1 * ε := mul_le_mul (le_trans (hAm t ht) (le_max_left _ _)) hx'.le (norm_nonneg _) hA1.le
        _ = δ / 2 := by rw [hεdef]; field_simp
    have h2 : dist z (A t x0) ≤ δ := by
      linarith [dist_triangle z (A t x) (A t x0), mem_closedBall.1 hz]
    exact mem_cthickening_of_dist_le z (A t x0) δ K0 ⟨t, ht, rfl⟩ h2
  have hin : ∀ t ∈ K, ∀ x ∈ ball x0 ε, A t x ∈ U := fun t ht x hx =>
    hδU (hnear t ht x hx (mem_closedBall_self (by positivity)))
  have hfd : ∀ t ∈ K, ∀ x ∈ ball x0 ε, ‖fderiv ℂ G (A t x)‖ ≤ C / (δ / 2) := fun t ht x hx =>
    norm_fderiv_le hU hG (by positivity) ((hnear t ht x hx).trans hδU)
      (fun z hz => hC z (hnear t ht x hx hz))
  have hball : ball x0 ε ∈ 𝓝 x0 := ball_mem_nhds x0 hε
  have hcont : ∀ x ∈ ball x0 ε, ContinuousOn (fun t => G (A t x) * e t) K := fun x hx =>
    (hG.continuousOn.comp (hcA x).continuousOn (fun t ht => hin t ht x hx)).mul he.continuousOn
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have m1 : Measurable fun t => fderiv ℂ G (A t x0) := (measurable_fderiv ℂ G).comp (hcA x0).measurable
  have m2 : Measurable fun t => (fderiv ℂ G (A t x0)).comp (A t) :=
    (isBoundedBilinearMap_comp.continuous.measurable).comp (m1.prodMk hA.measurable)
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume.restrict K)
    (F := fun x t => G (A t x) * e t)
    (F' := fun x t => e t • (fderiv ℂ G (A t x)).comp (A t))
    (bound := fun _ => Me * (C / (δ / 2) * A1)) hball
    (by filter_upwards [hball] with x hx; exact (hcont x hx).aestronglyMeasurable hKm)
    ((hcont x0 (mem_ball_self hε)).integrableOn_compact hK)
    ((he.measurable.smul m2).aestronglyMeasurable)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      calc ‖e t • (fderiv ℂ G (A t x)).comp (A t)‖
          = ‖e t‖ * ‖(fderiv ℂ G (A t x)).comp (A t)‖ := norm_smul _ _
        _ ≤ Me * (C / (δ / 2) * A1) := by
          refine mul_le_mul (hMe t ht) ?_ (norm_nonneg _) (le_trans (norm_nonneg _) (hMe t ht))
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hfd t ht x hx)
            (le_trans (hAm t ht) (le_max_left _ _)) (norm_nonneg _)
            (le_trans (norm_nonneg _) (hfd t ht x hx)))))
    (integrable_const _)
    ((ae_restrict_iff' hKm).2 (Eventually.of_forall fun t ht x hx => by
      have h1 : HasFDerivAt G (fderiv ℂ G (A t x)) (A t x) :=
        (hG.differentiableAt (hU.mem_nhds (hin t ht x hx))).hasFDerivAt
      exact (h1.comp x (A t).hasFDerivAt).mul_const (e t)))
  exact key.differentiableAt.differentiableWithinAt

end Param

section Dom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
  (u : Fin 2 → Fin r → E)

lemma cont_gram (τ : X.Ψ) : Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

lemma isOpen_dom : IsOpen X.dom := by
  have h : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
      ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
    ext x; simp [Data.dom, GG]
  rw [h]
  refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
  · exact isOpen_ne_fun (show Continuous fun x : Frame X.Ψ r => mat x τ from continuous_apply τ).matrix_det
      continuous_const
  · exact isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp
      ((cont_gram X τ).matrix_submatrix _ _).matrix_det))

def ZbL (b : X.Ψ → Fin 2 → Fin 2 → ℂ) : Frame X.Ψ r →L[ℂ] Frame X.Ψ r :=
  LinearMap.toContinuousLinearMap
    { toFun := X.Zb u b
      map_add' x y := by
        funext τ
        show X.zmat u b τ * (mat x τ + mat y τ) = _
        rw [Matrix.mul_add]; rfl
      map_smul' c x := by
        funext τ
        show X.zmat u b τ * (c • mat x τ) = _
        rw [Matrix.mul_smul]; rfl }

lemma cont_Zb {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) (y : Frame X.Ψ r) : Continuous fun t => X.Zb u (B t) y := by
  have hB' : ∀ τ i k, Continuous fun t => B t τ i k := fun τ i k => by fun_prop
  refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun c => ?_
  simp only [Data.Zb, Data.zmat, Matrix.mul_apply, Matrix.of_apply, mat]
  fun_prop

lemma cont_ZbL {n : ℕ} {B : (Fin n → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ}
    (hB : Continuous B) : Continuous fun t => ZbL X u (B t) :=
  continuous_clm_apply.2 fun y => cont_Zb X u hB y

end Dom

end

end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientDomain
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

section Mat

variable {n : ℕ}

lemma uGu_lower (G : Matrix (Fin n) (Fin n) ℂ) (hdet : ∀ c : Fin n, (blk G c).det ≠ 0) {a c : Fin n}
    (hac : a < c) : ((uMat G)ᵀ * G * (uMat G).map (starRingEnd ℂ)) c a = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge a k with h | h
  · rw [Matrix.map_apply, upper_lt (uMat_upper G) h, map_zero, mul_zero]
  · rw [uT_G_zero G c (hdet c) k (lt_of_le_of_lt h hac), zero_mul]

lemma prod_castLE_succ {k : ℕ} (h : k + 1 ≤ n) (f : Fin n → ℂ) :
    ∏ j : Fin (k + 1), f (Fin.castLE h j) = (∏ j : Fin k, f (Fin.castLE (Nat.le_of_succ_le h) j)) * f ⟨k, h⟩ := by
  rw [Fin.prod_univ_castSucc]
  rfl

lemma lminor_diagonal (D : Fin n → ℂ) (i : Fin (n + 1)) :
    lminor (Matrix.diagonal D) i = ∏ j : Fin i, D (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  rw [lminor, det_sub_upper _ (Matrix.blockTriangular_diagonal D)]
  simp

end Mat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def uOf (x : Frame X.Ψ r) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ := uMat (gram τ.1 X.Gm (mat x τ))

def dOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := gram τ.1 X.Gm (mat x τ * uOf X x τ) k k

lemma blk_det {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (c : Fin r) :
    (blk (gram τ.1 X.Gm (mat x τ)) c).det ≠ 0 := by
  intro h0
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 c.castSucc
  have h2 : dmin X.Gm x τ c.castSucc = 0 := h0
  rw [h2, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1

lemma gram_u_eq {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat x τ * uOf X x τ) = Matrix.diagonal (dOf X x τ) := by
  ext c a
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · rcases lt_or_gt_of_ne h with h' | h'
    · have hH := gram_isHermitian τ.1 X.Gm_herm (mat x τ * uOf X x τ)
      rw [← hH.apply c a, uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h', star_zero]
    · rw [uOf, gram_mul, uGu_lower _ (blk_det X hx τ) h']

lemma dOf_real {x : Frame X.Ψ r} (_hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : (dOf X x τ k).im = 0 := by
  have hH := gram_isHermitian τ.1 X.Gm_herm (mat x τ * uOf X x τ)
  exact Complex.conj_eq_iff_im.mp (hH.apply k k)

lemma dmin_prod {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ∏ j : Fin i, dOf X x τ (Fin.castLE (Nat.le_of_lt_succ i.isLt) j) := by
  have h1 := lminor_conj (N := uOf X x τ) (A := gram τ.1 X.Gm (mat x τ)) (uMat_upper _) i
  rw [← gram_mul, gram_u_eq X hx τ, lminor_diagonal] at h1
  simp only [uOf, uMat_diag, Finset.prod_const_one, map_one, one_mul, mul_one] at h1
  exact h1.symm

lemma dmin_succ {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    dmin X.Gm x τ k.succ = dmin X.Gm x τ k.castSucc * dOf X x τ k := by
  rw [dmin_prod X hx τ, dmin_prod X hx τ]
  exact prod_castLE_succ k.isLt (dOf X x τ)

lemma psgn_succ (p0 k : ℕ) : psgn p0 (k + 1) = psgn p0 k * sgn p0 k := by
  rw [psgn, psgn, Finset.prod_range_succ]

lemma sgn_dOf_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    0 < sgn X.p0 k * (dOf X x τ k).re := by
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 k.castSucc
  have h2 := ((X.mem_dom_iff x).1 hx τ).2 k.succ
  rw [dmin_succ X hx τ k, Complex.mul_re, dOf_real X hx τ k, mul_zero, sub_zero] at h2
  rw [Fin.val_succ, psgn_succ] at h2
  rw [Fin.coe_castSucc] at h1
  by_contra hneg
  push_neg at hneg
  nlinarith

def sOf (x : Frame X.Ψ r) (τ : X.Ψ) (k : Fin r) : ℂ := ((Real.sqrt |(dOf X x τ k).re|)⁻¹ : ℝ)

def bOf (x : Frame X.Ψ r) : Frame X.Ψ r := fun τ => (uOf X x τ * Matrix.diagonal (sOf X x τ) : Matrix _ _ ℂ)

lemma sgn_sq (p0 k : ℕ) : sgn p0 k = 1 ∨ sgn p0 k = -1 := by
  unfold sgn
  split_ifs <;> simp

lemma abs_re_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : 0 < |(dOf X x τ k).re| := by
  have h := sgn_dOf_pos X hx τ k
  refine abs_pos.mpr fun h0 => ?_
  rw [h0, mul_zero] at h
  exact lt_irrefl _ h

lemma sOf_ne {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : sOf X x τ k ≠ 0 := by
  unfold sOf
  rw [Ne, Complex.ofReal_eq_zero, inv_eq_zero, Real.sqrt_eq_zero']
  exact not_le.mpr (abs_re_pos X hx τ k)

lemma bOf_mem {x : Frame X.Ψ r} (hx : x ∈ X.dom) : bOf X x ∈ Bor X.Ψ r := by
  intro τ
  refine ⟨?_, fun a c hca => ?_⟩
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)).det ≠ 0
    unfold uOf
    rw [Matrix.det_mul, Matrix.det_diagonal, Matrix.det_of_upperTriangular (uMat_upper _)]
    simp only [uMat_diag, Finset.prod_const_one, one_mul]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => sOf_ne X hx τ k
  · change (uOf X x τ * Matrix.diagonal (sOf X x τ)) a c = 0
    unfold uOf
    rw [Matrix.mul_diagonal, upper_lt (uMat_upper _) hca, zero_mul]

lemma ortho_bOf {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.IsOrtho (rmul x (bOf X x)) := by
  intro τ
  change gram τ.1 X.Gm (mat x τ * (uOf X x τ * Matrix.diagonal (sOf X x τ))) = _
  rw [← Matrix.mul_assoc, gram_mul, gram_u_eq X hx τ, Matrix.diagonal_transpose,
    Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  have hd : dOf X x τ a = ((dOf X x τ a).re : ℂ) :=
    Complex.ext (by simp) (by simp [dOf_real X hx τ a])
  have hpos := sgn_dOf_pos X hx τ a
  have habs := abs_re_pos X hx τ a
  rw [hd]
  simp only [sOf, Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  set d := (dOf X x τ a).re
  have hs : (Real.sqrt |d|)⁻¹ * d * (Real.sqrt |d|)⁻¹ = d / |d| := by
    rw [mul_comm _ d, mul_assoc, ← mul_inv, Real.mul_self_sqrt (abs_nonneg _), div_eq_mul_inv]
  rw [hs]
  rcases sgn_sq X.p0 a with h1 | h1 <;> rw [h1] at hpos ⊢
  · rw [abs_of_pos (by linarith), div_self (by linarith)]
  · have hn : d < 0 := by linarith
    rw [abs_of_neg hn, div_neg, div_self hn.ne]

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainTranslate
namespace ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate

open MeasureTheory Complex
open scoped Pointwise

variable {ι : Type} [Fintype ι]

theorem fd_translate (L : AddSubgroup (ι → ℝ)) [Countable L] (D : Set (ι → ℝ))
    (hD : IsAddFundamentalDomain L D volume) (f : (ι → ℝ) → ℂ) (hf : ∀ p ∈ L, ∀ s, f (p + s) = f s)
    (v : ι → ℝ) : ∫ s in D, f (v + s) = ∫ s in D, f s := by
  have hv : IsAddFundamentalDomain L (v +ᵥ D) volume := hD.vadd_of_comm v
  have h1 : ∫ s in D, f (v + s) = ∫ s in v +ᵥ D, f s := by
    have := (measurePreserving_add_left (volume : Measure (ι → ℝ)) v).setIntegral_image_emb
      (measurableEmbedding_addLeft v) f D
    rw [← this]
    rfl
  rw [h1]
  exact hv.setIntegral_eq hD (fun p s => hf p.1 p.2 s)

theorem orth (L : AddSubgroup (ι → ℝ)) [Countable L] (D : Set (ι → ℝ))
    (hD : IsAddFundamentalDomain L D volume) (μ : ι → ℝ) (hμ : ∀ p ∈ L, ∃ k : ℤ, 2 * ∑ i, μ i * p i = k) :
    ∫ s in D, cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * s i) =
      if μ = 0 then ((volume D).toReal : ℂ) else 0 := by
  split_ifs with h0
  · subst h0
    simp [Measure.real]
  · obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
      by_contra h
      push_neg at h
      exact h0 (funext h)
    classical
    set e : (ι → ℝ) → ℂ := fun s => cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * s i) with he
    have hadd : ∀ v s : ι → ℝ,
        e (v + s) = cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * (v i : ℂ)) * e s := by
      intro v s
      simp only [he, Pi.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib,
        Complex.exp_add]
    have hinv : ∀ p ∈ L, ∀ s, e (p + s) = e s := by
      intro p hp s
      obtain ⟨k, hk⟩ := hμ p hp
      rw [hadd]
      have hk' : (2 : ℂ) * ∑ i, (μ i : ℂ) * (p i : ℂ) = k := by exact_mod_cast hk
      have h2 : 4 * (Real.pi : ℂ) * I * ∑ i, (μ i : ℂ) * (p i : ℂ) = k * (2 * Real.pi * I) := by
        linear_combination (2 * (Real.pi : ℂ) * I) * hk'
      rw [h2, Complex.exp_int_mul_two_pi_mul_I, one_mul]

    let v : ι → ℝ := Pi.single j (1 / (4 * μ j))
    have hsumR : ∑ i, μ i * v i = 1 / 4 := by
      rw [Finset.sum_eq_single j (fun i _ hi => by simp [v, Pi.single_apply, hi]) (by simp)]
      simp only [v, Pi.single_eq_same]
      field_simp
    have hsum : ∑ i, (μ i : ℂ) * (v i : ℂ) = 1 / 4 := by
      have h := congrArg Complex.ofReal hsumR
      push_cast at h
      exact h
    have hexp : cexp (4 * Real.pi * I * ∑ i, (μ i : ℂ) * (v i : ℂ)) = -1 := by
      rw [hsum]
      have h3 : 4 * (Real.pi : ℂ) * I * (1 / 4) = Real.pi * I := by ring
      rw [h3, Complex.exp_pi_mul_I]
    have htr := fd_translate L D hD e hinv v
    simp only [hadd, hexp, neg_one_mul, integral_neg] at htr
    linear_combination (-1 / 2 : ℂ) * htr

end ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate
end

namespace ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

section Lattice

variable (X : Data E r) (la : Wt X.Ψ r)

noncomputable def perB : Module.Basis (Module.Free.ChooseBasisIndex ℤ (perL X la)) ℝ (X.Ψ → ℝ) :=
  (Module.Free.chooseBasis ℤ (perL X la)).ofZLatticeBasis ℝ (perL X la)

theorem perB_span : (Submodule.span ℤ (Set.range (perB X la))).toAddSubgroup = X.periods la := by
  rw [perB, Module.Basis.ofZLatticeBasis_span]
  rfl

instance periods_countable : Countable (X.periods la) := inferInstanceAs (Countable (perL X la))

theorem fd_exists : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧
    IsAddFundamentalDomain (X.periods la) D volume ∧ 0 < volume D ∧ volume D < ⊤ := by
  refine ⟨ZSpan.fundamentalDomain (perB X la), ZSpan.fundamentalDomain_measurableSet _, ?_, ?_, ?_⟩
  · have h := ZSpan.isAddFundamentalDomain (perB X la) volume
    rw [← perB_span X la]
    exact h
  · exact pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero _)
  · exact (ZSpan.fundamentalDomain_isBounded _).measure_lt_top

theorem compact_reps : ∃ K : Set (X.Ψ → ℝ), IsCompact K ∧ ∀ s, ∃ p ∈ X.periods la, s - p ∈ K := by
  refine ⟨closure (ZSpan.fundamentalDomain (perB X la)),
    (ZSpan.fundamentalDomain_isBounded _).isCompact_closure, fun s => ?_⟩
  refine ⟨(ZSpan.floor (perB X la) s : X.Ψ → ℝ), ?_, subset_closure ?_⟩
  · rw [← perB_span X la]
    exact (ZSpan.floor (perB X la) s).prop
  · rw [← ZSpan.fract_apply]
    exact ZSpan.fract_mem_fundamentalDomain _ _

end Lattice

section Glue

variable (X : Data E r) (u : Fin 2 → Fin r → E)

def e00 (s : X.Ψ → ℝ) : X.Ψ → Fin 2 → Fin 2 → ℂ := fun τ i k => if i = 0 ∧ k = 0 then (s τ : ℂ) else 0

theorem diag_unit_family_hermitian (s : X.Ψ → ℝ) : IsHermFam (e00 X s) := by
  intro τ i k
  unfold e00
  by_cases h : i = 0 ∧ k = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · have h' : ¬ (k = 0 ∧ i = 0) := fun h2 => h ⟨h2.2, h2.1⟩
    simp [h, h']

theorem flow_eq_Zb (s : X.Ψ → ℝ) (y : Frame X.Ψ r) :
    X.flow (u 0) (cR X s) y = X.Zb u (e00 X s) y := by
  funext τ
  simp only [Data.flow, Data.Zb]
  congr 1
  ext a j
  simp [Data.flowMat, Data.zmat, e00, Fin.sum_univ_two, Data.emb, cR]
  ring

theorem real_pairing_diag_unit (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (s : X.Ψ → ℝ) :
    X.pairR χ (e00 X s) = ∑ τ, (χ τ 0 0).re * s τ := by
  simp [Data.pairR, e00, Fin.sum_univ_two, Complex.re_sum]

theorem flow_Zb_comm (hu : ∀ i k, herm X.Gm (u i) (u k) = 0) (s : X.Ψ → ℝ)
    (b : X.Ψ → Fin 2 → Fin 2 → ℂ) (y : Frame X.Ψ r) :
    X.flow (u 0) (cR X s) (X.Zb u b y) = X.Zb u b (X.flow (u 0) (cR X s) y) := by
  funext τ
  obtain ⟨W, hW⟩ : ∃ W : Fin 2 → Fin r → ℂ,
      W = fun k j => ∑ l, τ.1 (X.Gm j l) * conj (τ.1 (u k l)) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Fin 2 → Fin r → ℂ, V = fun i a => τ.1 (u i a) := ⟨_, rfl⟩

  have hk : ∀ i k : Fin 2, ∑ j, W k j * V i j = 0 := by
    intro i k
    have h := congrArg τ.1 (hu i k)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, map_sum, map_mul, emb_cc, map_zero] at h
    rw [← h, hW, hV]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  set α : ℂ := I * X.c τ * cR X s τ
  set γ : ℂ := I * X.c τ
  let A : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a j => α * V 0 a * W 0 j
  let B : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a j => γ * ∑ i, ∑ k, b τ i k * V i a * W k j
  have hF : X.flowMat (u 0) τ (cR X s τ) = 1 - A := by
    ext a j
    simp only [Data.flowMat, A, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, hW, hV, α]
  have hZ : X.zmat u b τ = 1 - B := by
    ext a j
    simp only [Data.zmat, B, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply, hW, hV, γ,
      Data.emb]
  have hAB : A * B = 0 := by
    ext a j
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ m, α * V 0 a * W 0 m * (γ * ∑ i, ∑ k, b τ i k * V i m * W k j)
        = ∑ i, ∑ k, (α * V 0 a * γ * b τ i k * W k j) * ∑ m, W 0 m * V i m := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := by simp [hk]
  have hBA : B * A = 0 := by
    ext a j
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ m, γ * (∑ i, ∑ k, b τ i k * V i a * W k m) * (α * V 0 m * W 0 j)
        = ∑ i, ∑ k, (γ * b τ i k * V i a * α * W 0 j) * ∑ m, W k m * V 0 m := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := by simp [hk]
  have key : X.flowMat (u 0) τ (cR X s τ) * X.zmat u b τ =
      X.zmat u b τ * X.flowMat (u 0) τ (cR X s τ) := by
    rw [hF, hZ]
    simp only [sub_mul, mul_sub, one_mul, mul_one, hAB, hBA]
    abel
  show X.flowMat (u 0) τ (cR X s τ) * (X.zmat u b τ * mat y τ) =
    X.zmat u b τ * (X.flowMat (u 0) τ (cR X s τ) * mat y τ)
  rw [← Matrix.mul_assoc, key, Matrix.mul_assoc]

theorem Zb_cont (y : Frame X.Ψ r) : Continuous fun b : X.Ψ → Fin 2 → Fin 2 → ℂ => X.Zb u b y := by
  refine continuous_pi fun τ => ?_
  simp only [Data.Zb, Data.zmat]
  refine continuous_pi fun a => continuous_pi fun j => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply]
  fun_prop

end Glue

end ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CompactEntryBounds
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace CompactEntryBounds

open Matrix NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem hermC_expand (τ : E →+* ℂ) (P : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((P.map τ) *ᵥ u) ((P.map τ) *ᵥ w) =
      ∑ k, ∑ l, u k * conj (w l) * τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) := by
  have hcc : ∀ x : E, τ (cc x) = conj (τ x) := fun x =>
    NumberField.IsCMField.complexEmbedding_complexConj E τ x
  have hL : ∀ a b, ((P.map τ) *ᵥ u) a * τ (X.Gm a b) * conj (((P.map τ) *ᵥ w) b) =
      ∑ k, ∑ l, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := by
    intro a b
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul]
    ring
  have hR : ∀ k l, u k * conj (w l) *
      τ (herm X.Gm (P *ᵥ Pi.single k 1) (P *ᵥ Pi.single l 1)) = ∑ a, ∑ b, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := by
    intro k l
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [herm, Matrix.mulVec_single_one, Matrix.transpose_apply, map_sum, map_mul, hcc,
      Finset.mul_sum]
    rfl
  simp only [hermC, hL, hR]
  calc _ = ∑ a, ∑ k, ∑ b, ∑ l, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ b, ∑ l, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := Finset.sum_comm
    _ = ∑ k, ∑ a, ∑ l, ∑ b, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ a, ∑ b, u k * conj (w l) * (τ (P a k) * τ (X.Gm a b) * conj (τ (P b l))) := Finset.sum_congr rfl fun k _ => Finset.sum_comm

theorem hermC_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ) (u w : Fin r → ℂ) :
    hermC τ X.Gm ((γ.map τ) *ᵥ u) ((γ.map τ) *ᵥ w) = hermC τ X.Gm u w := by
  rw [hermC_expand X τ γ u w]
  have h1 := hermC_expand X τ 1 u w
  rw [Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.one_mulVec, Matrix.one_mulVec] at h1
  rw [h1]
  simp only [hγ, Matrix.one_mulVec]

theorem gram_stab {γ : Matrix (Fin r) (Fin r) E}
    (hγ : ∀ x y, herm X.Gm (γ *ᵥ x) (γ *ᵥ y) = herm X.Gm x y) (τ : E →+* ℂ)
    (Y : Matrix (Fin r) (Fin r) ℂ) : gram τ X.Gm (γ.map τ * Y) = gram τ X.Gm Y := by
  have hc : ∀ a, col (γ.map τ * Y) a = (γ.map τ) *ᵥ col Y a := fun a => by
    funext k
    simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  ext a b
  simp only [gram, Matrix.of_apply, hc, hermC_stab X hγ τ]

theorem inv_lact (γ : GL (Fin r) E) (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → E) :
    ((γ : Matrix (Fin r) (Fin r) E).map τ * Y)⁻¹ *ᵥ Data.emb τ v =
      Y⁻¹ *ᵥ Data.emb τ (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ v) := by
  have hinv : ((γ : Matrix (Fin r) (Fin r) E).map τ)⁻¹ =
      ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ := by
    apply Matrix.inv_eq_right_inv
    rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero τ) (map_one τ)]
  rw [Matrix.mul_inv_rev, hinv, ← Matrix.mulVec_mulVec]
  congr 1
  funext a
  exact (RingHom.map_mulVec τ _ v a).symm

private theorem gram_eq_transpose_mul_map_mul_fundamental_domains (τ : E →+* ℂ) (Y : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm Y = Yᵀ * X.Gm.map τ * (Yᴴ)ᵀ := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Finset.sum_mul, Complex.star_def]
  exact Finset.sum_comm

theorem entry_bound {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} (hY : Y.det ≠ 0)
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (l b : Fin r) :
    ‖Y l b‖ ≤ ∑ k, ‖(X.Gm.map τ)⁻¹ k l‖ * ‖Y⁻¹ b k‖ := by
  set d : Fin r → ℂ := fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hd_def
  have hA : (X.Gm.map τ).det ≠ 0 := by
    have h := RingHom.map_det τ X.Gm
    rw [RingHom.mapMatrix_apply] at h
    rw [← h]
    exact (map_ne_zero τ).2 X.Gm_det
  have e1 : Yᵀ * X.Gm.map τ * (Yᴴ)ᵀ = diagonal d := by
    rw [← gram_eq_transpose_mul_map_mul_fundamental_domains, hg]
  have e2 := congrArg Matrix.transpose e1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    ← Matrix.mul_assoc] at e2
  have hYH : IsUnit (Yᴴ).det := by
    rw [Matrix.det_conjTranspose]
    exact isUnit_iff_ne_zero.2 (star_ne_zero.2 hY)
  have hAT : IsUnit (X.Gm.map τ)ᵀ.det := by
    rw [Matrix.det_transpose]
    exact isUnit_iff_ne_zero.2 hA
  have e3 : Y = ((X.Gm.map τ)ᵀ)⁻¹ * (Yᴴ)⁻¹ * diagonal d := by
    rw [← e2]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc ((X.Gm.map τ)ᵀ)⁻¹ (Yᴴ)⁻¹ Yᴴ, Matrix.nonsing_inv_mul _ hYH, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ hAT, Matrix.one_mul]
  have e4 : Y l b = (∑ k, (X.Gm.map τ)⁻¹ k l * star (Y⁻¹ b k)) * d b := by
    conv_lhs => rw [e3]
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.transpose_nonsing_inv, Matrix.transpose_apply, ← Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_apply]
  have hdb : ‖d b‖ = 1 := by
    rw [hd_def, Complex.norm_real]
    unfold sgn
    split_ifs <;> norm_num
  rw [e4, norm_mul, hdb, mul_one]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_mul, norm_star]

theorem comp_le_Qy (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) (p : Fin r → E) (b : Fin r) :
    X.c τ * ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) b‖ ^ 2 ≤ QuadraticLatticeForms.Qy X y p := by
  unfold QuadraticLatticeForms.Qy
  have hc : ∀ τ' : X.Ψ, 0 ≤ X.c τ' := fun τ' => by unfold Data.c; positivity
  calc X.c τ * ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) b‖ ^ 2
      ≤ X.c τ * ∑ a, ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.single_le_sum
          (f := fun a => ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 p) a‖ ^ 2) (fun a _ => by positivity)
          (Finset.mem_univ b)) (hc τ)
    _ ≤ _ := Finset.single_le_sum
          (f := fun τ' => X.c τ' * ∑ a, ‖((y τ')⁻¹ *ᵥ Data.emb τ'.1 p) a‖ ^ 2)
          (fun τ' _ => mul_nonneg (hc τ') (by positivity)) (Finset.mem_univ τ)

theorem comb_bound (y : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (τ : X.Ψ) {ι : Type} [Fintype ι]
    (q : ι → ℚ) (f : ι → Fin r → E) (b : Fin r) :
    ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (∑ i, q i • f i)) b‖ ≤
      ∑ i, ‖(q i : ℂ)‖ * (1 + QuadraticLatticeForms.Qy X y (f i) / X.c τ) := by
  have hcpos : 0 < X.c τ := by
    unfold Data.c
    have := (map_ne_zero τ.1).2 X.ξ0_ne
    positivity
  have hemb : Data.emb τ.1 (∑ i, q i • f i) = ∑ i, (q i : ℂ) • Data.emb τ.1 (f i) := by
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Data.emb, map_sum, Finset.sum_apply, Rat.smul_def, map_mul, map_ratCast]
  have hlin : ((y τ)⁻¹ *ᵥ Data.emb τ.1 (∑ i, q i • f i)) b =
      ∑ i, (q i : ℂ) * ((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b := by
    rw [hemb, Matrix.mulVec_sum, Finset.sum_apply]
    simp [Matrix.mulVec_smul]
  rw [hlin]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have h1 := comp_le_Qy X y τ (f i) b
  have h2 : ‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b‖ ^ 2 ≤ QuadraticLatticeForms.Qy X y (f i) / X.c τ := by
    rw [le_div_iff₀ hcpos]
    linarith
  nlinarith [sq_nonneg (‖((y τ)⁻¹ *ᵥ Data.emb τ.1 (f i)) b‖ - 1)]

def Kset (R : ℝ) : Set (Frame X.Ψ r) :=
  {w | ∀ τ : X.Ψ, gram τ.1 X.Gm (mat w τ) = diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ∧
    ∀ a c, ‖w τ a c‖ ≤ R}

theorem cont_gram' (τ : X.Ψ) : Continuous fun w : Frame X.Ψ r => gram τ.1 X.Gm (mat w τ) := by
  apply continuous_matrix
  intro a b
  simp only [gram, hermC, col, mat, Matrix.of_apply]
  fun_prop

theorem Kset_compact (R : ℝ) : IsCompact (Kset X R) := by
  have hcl : IsClosed (Kset X R) := by
    have : Kset X R = ⋂ τ : X.Ψ, ({w : Frame X.Ψ r | gram τ.1 X.Gm (mat w τ) =
        diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))} ∩
        ⋂ a, ⋂ c, {w : Frame X.Ψ r | ‖w τ a c‖ ≤ R}) := by
      ext w
      simp only [Kset, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [this]
    refine isClosed_iInter fun τ => (isClosed_eq (cont_gram' X τ) continuous_const).inter
      (isClosed_iInter fun a => isClosed_iInter fun c => isClosed_le (by fun_prop) continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := max R 0)).subset ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a =>
      (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun c =>
        ((hw τ).2 a c).trans (le_max_left _ _)

theorem det_ne_of_gram {τ : E →+* ℂ} {Y : Matrix (Fin r) (Fin r) ℂ} {p0 : ℕ}
    (hg : gram τ X.Gm Y = diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : Y.det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det hg
  rw [gram_eq_transpose_mul_map_mul_fundamental_domains, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul,
    zero_mul, Matrix.det_diagonal] at h
  refine absurd h.symm (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
  rw [ne_eq, Complex.ofReal_eq_zero]
  unfold sgn
  split_ifs <;> norm_num

theorem Kset_sub (R : ℝ) : Kset X R ⊆ X.dom := by
  intro w hw
  refine (X.mem_dom_iff w).2 fun τ => ?_
  have hg := (hw τ).1
  refine ⟨det_ne_of_gram X hg, fun i => ?_⟩
  have hd : dmin X.Gm w τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    rw [dmin, hg, lminor, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
      Matrix.det_diagonal, psgn, Complex.ofReal_prod]
    exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i
  rw [hd, Complex.ofReal_re]
  have hne : psgn X.p0 i ≠ 0 := by
    unfold psgn
    exact Finset.prod_ne_zero_iff.2 fun a _ => by unfold sgn; split_ifs <;> norm_num
  exact mul_self_pos.2 hne

end CompactEntryBounds

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticOffDiagonalBounds
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace QuadraticOffDiagonalBounds

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem quad_nonneg {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (v : Fin 2 → ℂ) :
    0 ≤ (∑ i, ∑ k, M i k * v i * conj (v k)).re := by
  have h := hM.dotProduct_mulVec_nonneg (star v)
  have e : dotProduct (star (star v)) ((Matrix.of M).mulVec (star v)) = ∑ i, ∑ k, M i k * v i * conj (v k) := by
    simp only [star_star, dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Pi.star_apply, ← starRingEnd_apply]
    ring
  rw [e] at h
  simpa using (Complex.le_def.mp h).1

theorem quad_comb {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef) (α β : ℂ)
    (v w : Fin 2 → ℂ) :
    (∑ i, ∑ k, M i k * (α • v + β • w) i * conj ((α • v + β • w) k)).re ≤
      (‖α‖ ^ 2 + ‖β‖ ^ 2) * ((∑ i, ∑ k, M i k * v i * conj (v k)).re +
        (∑ i, ∑ k, M i k * w i * conj (w k)).re) := by
  have hid : (∑ i, ∑ k, M i k * (α • v + β • w) i * conj ((α • v + β • w) k)) +
      (∑ i, ∑ k, M i k * (conj β • v - conj α • w) i * conj ((conj β • v - conj α • w) k)) =
      (α * conj α + β * conj β) * ((∑ i, ∑ k, M i k * v i * conj (v k)) +
        (∑ i, ∑ k, M i k * w i * conj (w k))) := by
    simp only [Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _),
      map_sub, map_mul, Complex.conj_conj]
    ring
  have h0 := quad_nonneg hM (conj β • v - conj α • w)
  have hαβ : α * conj α + β * conj β = ((‖α‖ ^ 2 + ‖β‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hre := congrArg Complex.re hid
  rw [Complex.add_re, hαβ, Complex.re_ofReal_mul, Complex.add_re] at hre
  linarith

theorem offdiag_le {M : Fin 2 → Fin 2 → ℂ} (hM : (Matrix.of M).PosSemidef)
    (h10 : M 1 0 = conj (M 0 1)) : 2 * ‖M 0 1‖ ≤ (M 0 0).re + (M 1 1).re := by
  have d0 := quad_nonneg hM ![1, 0]
  have d1 := quad_nonneg hM ![0, 1]
  simp [Fin.sum_univ_two] at d0 d1
  rcases eq_or_ne (M 0 1) 0 with h0 | h0
  · rw [h0, norm_zero, mul_zero]
    linarith
  · have hn : 0 < ‖M 0 1‖ := norm_pos_iff.mpr h0
    have hs : M 0 1 * conj (M 0 1) = ((‖M 0 1‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    have h := quad_nonneg hM ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)]
    have e : (∑ i, ∑ k, M i k * ![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] i *
        conj (![conj (M 0 1), -((‖M 0 1‖ : ℝ) : ℂ)] k)) =
        ((‖M 0 1‖ ^ 2 : ℝ) : ℂ) * (M 0 0 + M 1 1) - ((2 * ‖M 0 1‖ ^ 3 : ℝ) : ℂ) := by
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        map_neg, Complex.conj_conj, Complex.conj_ofReal, h10]
      push_cast
      linear_combination (M 0 0 - 2 * ((‖M 0 1‖ : ℝ) : ℂ)) * hs
    rw [e] at h
    have h' := h
    simp only [Complex.zero_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.add_re,
      Complex.ofReal_re] at h'
    by_contra hlt
    push_neg at hlt
    have hm := mul_lt_mul_of_pos_left hlt (pow_pos hn 2)
    nlinarith

variable {r : ℕ} {X : Data E r}

private theorem Hf_smul_add_smul_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) (a b : ℂ) :
    X.Hf z τ u (a • v + b • w) = conj a * X.Hf z τ u v + conj b * X.Hf z τ u w := by
  simp only [Data.Hf, hermC, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add (f := _), map_mul]
  ring

theorem coord {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (f1 f2 e : Fin r → ℂ) (a0 a1 : ℂ)
    (c : ℝ) (he : e = a0 • f1 + a1 • f2) (h1 : c * (X.Hf z τ f1 f1).re = 1)
    (h2 : X.Hf z τ e f1 = 0) (h3 : c * (X.Hf z τ e e).re = 1) :
    ∃ p q : ℂ, q * a0 + p = 0 ∧ q * a1 = 1 ∧ ‖p‖ ^ 2 + ‖q‖ ^ 2 = c * (X.Hf z τ f2 f2).re := by
  have hc : ∀ u w, conj (X.Hf z τ u w) = X.Hf z τ w u := fun u w => UnipotentCoefficientShift.Hf_conj hz τ u w
  have hL : ∀ w, X.Hf z τ e w = a0 * X.Hf z τ f1 w + a1 * X.Hf z τ f2 w := by
    intro w
    rw [← hc w e, he, Hf_smul_add_smul_right, map_add (f := _), map_mul, map_mul, Complex.conj_conj, Complex.conj_conj,
      hc, hc]
  have h2' : a0 * X.Hf z τ f1 f1 + a1 * X.Hf z τ f2 f1 = 0 := by rw [← hL, h2]
  have hee : X.Hf z τ e e = conj a0 * X.Hf z τ e f1 + conj a1 * X.Hf z τ e f2 := by
    have := Hf_smul_add_smul_right z τ e f1 f2 a0 a1
    rwa [← he] at this
  rw [h2, mul_zero, zero_add, hL f2, ← hc f2 f1] at hee
  have hA : conj (X.Hf z τ f1 f1) = X.Hf z τ f1 f1 := hc f1 f1
  have hD : conj (X.Hf z τ f2 f2) = X.Hf z τ f2 f2 := hc f2 f2
  have hB : conj a1 * conj (X.Hf z τ f2 f1) = -(conj a0 * X.Hf z τ f1 f1) := by
    rw [← map_mul, show a1 * X.Hf z τ f2 f1 = -(a0 * X.Hf z τ f1 f1) by linear_combination h2',
      map_neg, map_mul, hA]
  have hee2 : X.Hf z τ e e = -(a0 * conj a0) * X.Hf z τ f1 f1 + (a1 * conj a1) * X.Hf z τ f2 f2 := by
    rw [hee]
    linear_combination a0 * hB
  have hAr : ((X.Hf z τ f1 f1).re : ℂ) = X.Hf z τ f1 f1 := Complex.conj_eq_iff_re.mp hA
  have hDr : ((X.Hf z τ f2 f2).re : ℂ) = X.Hf z τ f2 f2 := Complex.conj_eq_iff_re.mp hD
  have hre : (X.Hf z τ e e).re =
      -(‖a0‖ ^ 2) * (X.Hf z τ f1 f1).re + ‖a1‖ ^ 2 * (X.Hf z τ f2 f2).re := by
    rw [hee2, ← hAr, ← hDr, Complex.mul_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  rw [hre] at h3
  have key : ‖a1‖ ^ 2 * (c * (X.Hf z τ f2 f2).re) = 1 + ‖a0‖ ^ 2 := by
    linear_combination h3 + ‖a0‖ ^ 2 * h1
  have ha1 : a1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at key
    nlinarith [sq_nonneg ‖a0‖]
  have hn : 0 < ‖a1‖ := norm_pos_iff.mpr ha1
  have hcd : c * (X.Hf z τ f2 f2).re = (1 + ‖a0‖ ^ 2) / ‖a1‖ ^ 2 := by
    rw [eq_div_iff (by positivity)]
    linear_combination key
  refine ⟨-a0 * a1⁻¹, a1⁻¹, by ring, inv_mul_cancel₀ ha1, ?_⟩
  rw [hcd, norm_mul, norm_neg, norm_inv]
  field_simp
  ring

end QuadraticOffDiagonalBounds

end ReciprocityTheory.ChartRestriction.G.FD
end
