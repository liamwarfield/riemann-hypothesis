module

public import ReciprocityTheory.SemistableReduction.RestBlockSubstIsMultiHomogeneous
public import ReciprocityTheory.SemistableReduction.SJCoreD
public import ReciprocityTheory.SemistableReduction.SemiDegSt
public import ReciprocityTheory.SemistableReduction.SemiDegCE

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.LogNormCoeffSubLeBlockSphereLogMean
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory MvPolynomial NumberField

theorem harmonic_pred_le_one_add_log {n : ℕ} (hn : 0 < n) : (harmonic (n - 1) : ℝ) ≤ 1 + Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := harmonic_le_one_add_log (m + 1)
  have h2 : harmonic (m + 1 - 1) ≤ harmonic (m + 1) := by
    have e : m + 1 - 1 = m := by omega
    rw [e, harmonic_succ]
    have : (0 : ℚ) ≤ (((m + 1 : ℕ) : ℚ))⁻¹ := by positivity
    linarith
  have h3 : (harmonic (m + 1 - 1) : ℝ) ≤ harmonic (m + 1) := by exact_mod_cast h2
  linarith

theorem log_norm_coeff_sub_le_blockSphereLogMean (hSJ : SJStatement) (hInt : SphereLogIntegrableStatement) {B n : ℕ}
    (hn : 0 < n) {a : Fin B → ℕ} {g : MvPolynomial (Fin B × Fin n) ℂ}
    (hg : IsMultiHomogeneous a g) (s : Fin B × Fin n →₀ ℕ) (hs : g.coeff s ≠ 0) :
    Real.log ‖g.coeff s‖ - ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) ≤ blockSphereMean B n g := by
  obtain ⟨z, hz1, hzc⟩ := exists_torus_coeff_le g s
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set r : ℝ := Real.sqrt n with hrdef
  have hr : 0 < r := Real.sqrt_pos.mpr hnpos
  have hr2 : r ^ 2 = n := Real.sq_sqrt hnpos.le

  have hmem : ∀ b : Fin B, (WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)) : EuclideanSpace ℂ (Fin n)) ∈
      Metric.sphere (0 : EuclideanSpace ℂ (Fin n)) 1 := by
    intro b
    have hj : ∀ j, ‖z (b, j) / (r : ℂ)‖ = 1 / r := by
      intro j
      rw [norm_div, hz1, Complex.norm_of_nonneg hr.le]
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    simp only [PiLp.toLp_apply, hj, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [div_pow, one_pow, hr2, mul_one_div_cancel hnpos.ne', Real.sqrt_one]
  let u : BlockSphere B n := fun b => ⟨WithLp.toLp 2 (fun j => z (b, j) / (r : ℂ)), hmem b⟩
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hz' : (fun p => (r : ℂ) * blockPoint u p) = z := by
    funext p
    simp only [blockPoint, spherePoint, u, PiLp.toLp_apply]
    field_simp
  have hev := eval_mul_of_isMultiHomogeneous hg (r : ℂ) (blockPoint u)
  rw [hz'] at hev
  have hcpos : 0 < ‖g.coeff s‖ := norm_pos_iff.mpr hs
  have hgz : 0 < ‖eval z g‖ := lt_of_lt_of_le hcpos hzc
  have hnorm : ‖eval z g‖ = r ^ (∑ b, a b) * ‖eval (blockPoint u) g‖ := by
    rw [hev, norm_mul, norm_pow, Complex.norm_of_nonneg hr.le]
  have hgu : eval (blockPoint u) g ≠ 0 := by
    intro h0
    rw [hnorm, h0, norm_zero, mul_zero] at hgz
    exact lt_irrefl _ hgz
  have hbb := blockSphere_logMean_bound hSJ hInt hn B a g u hg hgu
  have hH := harmonic_pred_le_one_add_log hn
  have hlogr : Real.log r = Real.log n / 2 := Real.log_sqrt hnpos.le
  have hlz : Real.log ‖eval z g‖ =
      ((∑ b, a b : ℕ) : ℝ) * Real.log r + Real.log ‖eval (blockPoint u) g‖ := by
    rw [hnorm, Real.log_mul (by positivity) (norm_ne_zero_iff.mpr hgu), Real.log_pow]
  have hlc : Real.log ‖g.coeff s‖ ≤ Real.log ‖eval z g‖ := Real.log_le_log hcpos hzc
  set A : ℝ := ∑ b, (a b : ℝ) with hAdef
  have hsum : ((∑ b, a b : ℕ) : ℝ) = A := by rw [hAdef]; push_cast; rfl
  have hA0 : 0 ≤ A := Finset.sum_nonneg (fun b _ => Nat.cast_nonneg _)
  have hmul : A / 2 * (harmonic (n - 1) : ℝ) ≤ A / 2 * (1 + Real.log n) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hgoal : ∑ b, (a b : ℝ) * (Real.log n + 1 / 2) = A * (Real.log n + 1 / 2) := by
    rw [hAdef, Finset.sum_mul]
  rw [hgoal]
  rw [hsum, hlogr] at hlz
  nlinarith

theorem neg_log_norm_coeff_le_finitePlaces {K : Type*} [Field K] [NumberField K] {ι : Type*} (f : MvPolynomial ι K)
    (s : ι →₀ ℕ) (hs : s ∈ f.support) :
    -Real.log |((Algebra.norm ℚ (f.coeff s) : ℚ) : ℝ)| ≤
      ∑ᶠ w : FinitePlace K, Real.log (gaussAbs w f) := by
  classical
  have hc : f.coeff s ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have hA : ∀ w : FinitePlace K, w (f.coeff s) ≤ gaussAbs w f := by
    intro w
    unfold gaussAbs
    have h1 := Finset.le_sup (f := fun t => (w (f.coeff t)).toNNReal) hs
    calc w (f.coeff s) ≤ ((w (f.coeff s)).toNNReal : ℝ) := Real.le_coe_toNNReal _
      _ ≤ _ := by exact_mod_cast h1
  have hpos : ∀ w : FinitePlace K, 0 < w (f.coeff s) := fun w => NumberField.FinitePlace.pos_iff.mpr hc
  have hU : (⋃ t ∈ f.support, Function.mulSupport (fun w : FinitePlace K => w (f.coeff t))).Finite :=
    Set.Finite.biUnion f.support.finite_toSet
      (fun t ht => NumberField.FinitePlace.hasFiniteMulSupport (MvPolynomial.mem_support_iff.mp ht))
  set T := hU.toFinset with hT
  have hsubG : Function.support (fun w : FinitePlace K => Real.log (gaussAbs w f)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    by_contra hnot
    apply hw
    simp only [Set.mem_iUnion, Function.mem_mulSupport, not_exists, not_not] at hnot
    have h1 : gaussAbs w f = 1 := by
      unfold gaussAbs
      have hne : f.support.Nonempty := ⟨s, hs⟩
      rw [Finset.sup_congr rfl (g := fun _ => (1 : NNReal)) (fun t ht => by simp [hnot t ht]),
        Finset.sup_const hne]
      simp
    simp [h1]
  have hsubW : Function.mulSupport (fun w : FinitePlace K => w (f.coeff s)) ⊆ (T : Set _) := by
    intro w hw
    rw [hT, Set.Finite.coe_toFinset]
    exact Set.mem_biUnion hs hw
  have hprod := NumberField.FinitePlace.prod_eq_inv_abs_norm hc
  rw [finprod_eq_prod_of_mulSupport_subset _ hsubW] at hprod
  rw [finsum_eq_sum_of_support_subset _ hsubG]
  have hlog : Real.log (∏ w ∈ T, w (f.coeff s)) = ∑ w ∈ T, Real.log (w (f.coeff s)) :=
    Real.log_prod (fun w _ => (hpos w).ne')
  rw [hprod] at hlog
  have hle : ∑ w ∈ T, Real.log (w (f.coeff s)) ≤ ∑ w ∈ T, Real.log (gaussAbs w f) :=
    Finset.sum_le_sum (fun w _ => Real.log_le_log (hpos w) (hA w))
  push_cast at hlog
  rw [Real.log_inv] at hlog
  linarith

theorem sum_log_norm_embedding_eq {K : Type*} [Field K] [NumberField K] (c : K) (hc : c ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ c‖ = Real.log |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
  classical
  have hne : ∀ σ : K →+* ℂ, ‖σ c‖ ≠ 0 := fun σ => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hc)
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ c
  have h2 : ∏ σ : K →+* ℂ, σ c = ∏ σ : K →ₐ[ℚ] ℂ, σ c :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) _ _ (fun σ => rfl)
  have hprod : ∏ σ : K →+* ℂ, ‖σ c‖ = |((Algebra.norm ℚ c : ℚ) : ℝ)| := by
    rw [← norm_prod, h2, ← h]
    simp [Complex.norm_ratCast]
  rw [← hprod, Real.log_prod (fun σ _ => hne σ)]

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.SJCore
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Set Real

theorem gaussLogC_div {a : ℝ} (ha : 0 < a) :
    gaussLogC a / gaussOneC = log a + radK 1 / radJ 1 := by
  have hdim : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  have h1 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => exp (-r ^ 2))
  have h2 := integral_fun_norm_addHaar (volume : Measure ℂ) (fun r : ℝ => log (a * r) * exp (-r ^ 2))
  rw [hdim] at h1 h2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl, pow_one] at h1 h2
  set C : ℝ := (volume : Measure ℂ).real (Metric.ball 0 1) with hCdef
  have hC : 0 < C :=
    ENNReal.toReal_pos (Metric.measure_ball_pos volume (0 : ℂ) one_pos).ne' measure_ball_lt_top.ne
  have hG : gaussOneC = 2 * C * radJ 1 := by
    unfold gaussOneC radJ
    rw [h1]
    simp only [pow_one]
    ring
  have hsplit : ∫ y in Ioi (0 : ℝ), y * (log (a * y) * exp (-y ^ 2)) =
      log a * radJ 1 + radK 1 := by
    have heq : EqOn (fun y : ℝ => y * (log (a * y) * exp (-y ^ 2)))
        (fun y : ℝ => log a * (y ^ 1 * exp (-y ^ 2)) + y ^ 1 * log y * exp (-y ^ 2)) (Ioi 0) := by
      intro y hy
      simp only
      rw [log_mul ha.ne' (ne_of_gt hy)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq,
      integral_add ((integrableOn_radJ 1).const_mul (log a)) (integrableOn_radK le_rfl),
      integral_const_mul]
    rfl
  have hL : gaussLogC a = 2 * C * (log a * radJ 1 + radK 1) := by
    unfold gaussLogC
    rw [h2, hsplit]
    ring
  have hM := radJ_pos 1
  rw [hL, hG]
  field_simp

theorem sjCore_holds : SphereLinLogStatement := by
  intro n c hc
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd (Subsingleton.elim c 0) hc
    · exact h
  obtain ⟨hi, he⟩ := polar_mean hn c hc
  refine ⟨hi, ?_⟩
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have h2 : 2 * n - 1 = 2 * (n - 1) + 1 := by omega
  rw [he, gaussLogC_div hcn, h2, radRatio_odd]
  ring

end ReciprocityTheory.MultiplicativeHeights
end
end

section -- merged from ReciprocityTheory.SemistableReduction.DegAddHolds
section -- merged from ReciprocityTheory.SemistableReduction.EmbMatMulVecInjective
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

namespace DegAdd

open Matrix NumberField
open scoped ComplexOrder

def embMat {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    (v : Fin k → Fin r → K) : Matrix (Fin r) (Fin k) ℂ :=
  Matrix.of fun a j => σ (v j a)

theorem gramC_eq_mul {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (v : Fin k → Fin r → K) :
    gramC H σ v = (embMat σ v)ᴴ * H * embMat σ v := by
  ext i j
  simp only [gramC, embMat, embVec, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring

theorem embMat_mulVec_injective {K : Type} [Field K] [NumberField K] {r k : ℕ} (σ : K →+* ℂ)
    {v : Fin k → Fin r → K} (hv : LinearIndependent K v) :
    Function.Injective (embMat σ v).mulVec := by
  set B : Matrix (Fin r) (Fin k) K := Matrix.of fun a j => v j a
  have hcol : B.col = v := by
    funext j a
    rfl
  have hB : Function.Injective B.mulVec := by
    rw [Matrix.mulVec_injective_iff, hcol]
    exact hv
  have hker : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    exact hB (by simpa [Matrix.toLin'_apply] using h)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) hker
  have hNB : LinearMap.toMatrix' g * B = 1 := by
    rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  have hE : embMat σ v = B.map σ := rfl
  have h1 : (LinearMap.toMatrix' g).map σ * embMat σ v = 1 := by
    rw [hE, ← Matrix.map_mul, hNB, Matrix.map_one _ σ.map_zero σ.map_one]
  intro x y hxy
  have h := congrArg ((LinearMap.toMatrix' g).map σ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, h1] using h

theorem gramC_posDef {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) {v : Fin k → Fin r → K} (hH : H.PosDef)
    (hv : LinearIndependent K v) : (gramC H σ v).PosDef := by
  rw [gramC_eq_mul]
  exact hH.conjTranspose_mul_mul_same (embMat_mulVec_injective σ hv)

theorem gramC_append_blocks {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) :
    (gramC H σ (Fin.append b c)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (gramC H σ b) (gramX H σ b c) (gramX H σ c b) (gramC H σ c) := by
  ext (i | i) (j | j) <;> simp [gramC, gramX]

theorem log_det_gram_append {K : Type} [Field K] [NumberField K] {r k m : ℕ}
    (H : Matrix (Fin r) (Fin r) ℂ) (σ : K →+* ℂ) (b : Fin k → Fin r → K)
    (c : Fin m → Fin r → K) (hH : H.PosDef) (hb : LinearIndependent K b)
    (h : LinearIndependent K (Fin.append b c)) :
    Real.log (gramC H σ (Fin.append b c)).det.re =
      Real.log (gramC H σ b).det.re + Real.log (quotGramC H σ b c).det.re := by
  have hG := (gramC_posDef H σ hH h).det_pos
  have hGb := (gramC_posDef H σ hH hb).det_pos
  have : Invertible (gramC H σ b) := (gramC_posDef H σ hH hb).isUnit.invertible
  have hdet : (gramC H σ (Fin.append b c)).det =
      (gramC H σ b).det * (quotGramC H σ b c).det := by
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv (gramC H σ (Fin.append b c)),
      gramC_append_blocks, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv]
    rfl
  rw [hdet] at hG ⊢
  rw [Complex.pos_iff] at hG hGb
  have hre : ((gramC H σ b).det * (quotGramC H σ b c).det).re =
      (gramC H σ b).det.re * (quotGramC H σ b c).det.re := by
    simp [Complex.mul_re, ← hGb.2]
  have hy : 0 < (quotGramC H σ b c).det.re := by
    rw [hre] at hG
    exact (pos_iff_pos_of_mul_pos hG.1).mp hGb.1
  rw [hre, Real.log_mul hGb.1.ne' hy.ne']

end DegAdd

end ReciprocityTheory.MultiplicativeHeights
end
end

namespace ReciprocityTheory.MultiplicativeHeights

open NumberField

theorem degAdd_holds : DegAddStatement := by
  intro K _ _ r k m H L b c hH hL hb hc hlin hspan
  obtain ⟨hbi, -, hdis⟩ := DegAdd.indep_parts hlin
  have hidx := DegAdd.index_split L b c hb hc hdis
  have hne := DegAdd.relIndex_ne_zero_of_fg L hL (Fin.append b c) hspan
  rw [hidx] at hne
  have h1 := left_ne_zero_of_mul hne
  have h2 := right_ne_zero_of_mul hne
  have hs : ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ (Fin.append b c)).det.re =
      ∑ σ : K →+* ℂ, Real.log (gramC (H σ) σ b).det.re +
        ∑ σ : K →+* ℂ, Real.log (quotGramC (H σ) σ b c).det.re := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun σ _ => DegAdd.log_det_gram_append (H σ) σ b c (hH σ) hbi hlin
  unfold latDeg quotDeg
  rw [hidx, Nat.cast_mul, Real.log_mul (Nat.cast_ne_zero.mpr h1) (Nat.cast_ne_zero.mpr h2), hs]
  ring

end ReciprocityTheory.MultiplicativeHeights
end

section -- merged from ReciprocityTheory.SemistableReduction.SemiDegC
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField Matrix
open scoped nonZeroDivisors

theorem hermForm_sum_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {ι : Type} (s : Finset ι) (u : Fin r → K) (w : ι → Fin r → K) :
    S.h u (∑ i ∈ s, w i) = ∑ i ∈ s, S.h u (w i) := by
  classical
  refine Finset.induction_on s (by simp [HermForm.h]) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
  simp only [HermForm.h, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermForm_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (a : K) (u w : Fin r → K) : S.h u (a • w) = a * S.h u w := by
  simp only [HermForm.h, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def coordForm {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) : HermForm K k where
  c := S.c
  c_invol := S.c_invol
  c_emb := S.c_emb
  G := hGram S b
  G_herm i j := hermForm_conj S (b i) (b j)

def combMap {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) :
    (Fin k → K) →ₗ[K] (Fin r → K) where
  toFun t := ∑ i, t i • b i
  map_add' s t := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a t := by simp [Finset.smul_sum, smul_smul]

theorem combMap_apply {K : Type} [Field K] {r k : ℕ} (b : Fin k → Fin r → K) (t : Fin k → K) :
    combMap b t = ∑ i, t i • b i := rfl

theorem coordForm_h {K : Type} [Field K] [NumberField K] {r k : ℕ} (S : HermForm K r)
    (b : Fin k → Fin r → K) (s t : Fin k → K) :
    S.h (combMap b s) (combMap b t) = (coordForm S b).h s t := by
  have key : ∀ j, S.h (combMap b s) (b j) = ∑ i, S.c (s i) * S.h (b i) (b j) := by
    intro j
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hermForm_conj S (b j), combMap_apply, hermForm_sum_right, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hermForm_smul_right, map_mul, hermForm_conj]
  show _ = ∑ i, ∑ j, S.c (s i) * S.h (b i) (b j) * t j
  rw [combMap_apply b t, hermForm_sum_right]
  simp only [hermForm_smul_right, key, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem combMap_injective {K : Type} [Field K] {r k : ℕ} {b : Fin k → Fin r → K}
    (hb : LinearIndependent K b) : Function.Injective (combMap b) := by
  rw [Fintype.linearIndependent_iff] at hb
  refine (injective_iff_map_eq_zero (combMap b)).2 fun t ht => funext fun i => ?_
  exact hb t (by simpa only [combMap_apply] using ht) i

def coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) : Submodule (𝓞 K) (Fin k → K) := B.comap ((combMap b).restrictScalars (𝓞 K))

theorem mem_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {t : Fin k → K} : t ∈ coordLat B b ↔ combMap b t ∈ B := Iff.rfl

theorem exists_coord {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) {y : Fin r → K} (hy : y ∈ B) :
    ∃ t ∈ coordLat B b, combMap b t = y := by
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hb.2.2 y hy)
  exact ⟨t, mem_coordLat.2 (by rw [combMap_apply, ht]; exact hy), by rw [combMap_apply, ht]⟩

theorem map_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) :
    (coordLat B b).map ((combMap b).restrictScalars (𝓞 K)) = B := by
  ext y
  refine ⟨fun h => ?_, fun hy => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.1 h
    exact mem_coordLat.1 ht
  · obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
    exact Submodule.mem_map.2 ⟨t, ht, rfl⟩

theorem coordLat_fg {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hB : B.FG) (hb : IsKBasisIn B b) : (coordLat B b).FG := Submodule.fg_of_fg_map_injective ((combMap b).restrictScalars (𝓞 K)) (combMap_injective hb.2.1) (by rw [map_coordLat hb]; exact hB)

theorem combMap_intVec {K : Type} [Field K] [NumberField K] {r k : ℕ}
    {b : Fin k → Fin r → K} {t : Fin k → K} (ht : t ∈ intVec K k)
    (P : Submodule (𝓞 K) (Fin r → K)) (hP : ∀ i, b i ∈ P) : combMap b t ∈ P := by
  rw [combMap_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨x, hx⟩ := Submodule.mem_one.1 ((Submodule.mem_pi).1 ht i (Set.mem_univ i))
  rw [← hx, algebraMap_smul]
  exact P.smul_mem x (hP i)

theorem intVec_le_coordLat {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) : intVec K k ≤ coordLat B b := fun t ht => mem_coordLat.2 (combMap_intVec ht B hb.1)

theorem spanIdx_eq_vecIdx {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} (hb : IsKBasisIn B b) : spanIdx B b = vecIdx (coordLat B b) := by
  have hinj := combMap_injective hb.2.1
  have hspan : (intVec K k).map ((combMap b).restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (Set.range b) := by
    refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · rintro _ ⟨t, ht, rfl⟩
      exact combMap_intVec ht _ fun i => Submodule.subset_span ⟨i, rfl⟩
    · rintro _ ⟨i, rfl⟩
      refine ⟨Pi.single i 1, (Submodule.mem_pi).2 fun j _ => ?_, ?_⟩
      · rcases eq_or_ne j i with rfl | hj
        · rw [Pi.single_apply, if_pos rfl]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
        · rw [Pi.single_apply, if_neg hj]; exact zero_mem _
      · show combMap b (Pi.single i 1) = b i
        simp [combMap_apply, Pi.single_apply, ite_smul]
  have e1 : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup =
      (intVec K k).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    rw [← hspan]; exact AddSubgroup.ext fun _ => Iff.rfl
  have e2 : B.toAddSubgroup =
      (coordLat B b).toAddSubgroup.map ((combMap b).restrictScalars (𝓞 K)).toAddMonoidHom := by
    conv_lhs => rw [← map_coordLat hb]
    exact AddSubgroup.ext fun _ => Iff.rfl
  unfold spanIdx vecIdx
  rw [e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

theorem coordLat_integral {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {S : HermForm K r} (hint : IsIntegralOn S B) :
    IsIntegralOn (coordForm S b) (coordLat B b) := by
  intro s hs t ht
  rw [← coordForm_h]
  exact hint _ (mem_coordLat.1 hs) _ (mem_coordLat.1 ht)

theorem coordLat_selfDual {K : Type} [Field K] [NumberField K] {r k : ℕ} {B : Submodule (𝓞 K) (Fin r → K)}
    {b : Fin k → Fin r → K} {S : HermForm K r} (hb : IsKBasisIn B b)
    (hsd : IsSelfDual S B) : IsSelfDual (coordForm S b) (coordLat B b) := by
  refine ⟨coordLat_integral hsd.1, fun s hs => mem_coordLat.2 (hsd.2 _ fun y hy => ?_)⟩
  obtain ⟨t, ht, rfl⟩ := exists_coord hb hy
  rw [coordForm_h]
  exact hs t ht

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

namespace ReciprocityTheory.MultiplicativeHeights

open SemiDegIdx

theorem integralIndex_holds : IntegralIndexStatement := by
  intro K _ _ r k S B b hB hb hint hdet
  have key : ((vecIdx (coordLat B b) : ℕ) : ℚ) ^ 2 ≤ |Algebra.norm ℚ (hGram S b).det| :=
    vec_integral_bound (coordForm S b) _ (coordLat_fg hB hb) (intVec_le_coordLat hb)
      (coordLat_integral hint) hdet
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key

theorem selfDualIndex_holds : SelfDualIndexStatement := by
  intro K _ _ r S L b hL hsd hb
  have key : |Algebra.norm ℚ (hGram S b).det| ≤ ((vecIdx (coordLat L b) : ℕ) : ℚ) ^ 2 :=
    vec_selfDual_bound (coordForm S b) _ (coordLat_fg hL.1 hb) (intVec_le_coordLat hb)
      (coordLat_selfDual hb hsd)
  rw [spanIdx_eq_vecIdx hb]
  exact_mod_cast key

end ReciprocityTheory.MultiplicativeHeights
end
end
