module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TLeftH

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiRNonneg
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.XiIntH
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.GaNonneg
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.GramReDetLe
noncomputable section

open Matrix InnerProductSpace
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

variable {n m : ℕ}

theorem gram_det_zero (w : Fin m → EuclideanSpace ℂ (Fin n)) (hw : ¬ LinearIndependent ℂ w) :
    (GS.gram w).det = 0 := by
  rw [Fintype.not_linearIndependent_iff] at hw
  obtain ⟨g, hg, i, hi⟩ := hw
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨g, fun h => hi (congrFun h i), ?_⟩
  funext a
  simp only [mulVec, dotProduct, GS.gram, Matrix.of_apply, Pi.zero_apply]
  have hs : ∑ b, inner ℂ (w a) (w b) * g b = inner ℂ (w a) (∑ b, g b • w b) := by
    rw [inner_sum]
    congr 1
    funext b
    rw [inner_smul_right]
    ring
  rw [hs, hg, inner_zero_right]

theorem gram_re_det_le (v : Fin m → EuclideanSpace ℂ (Fin n)) (M : ℝ) (hM : ∀ j, ‖v j‖ ≤ M) :
    (GS.gram v).det.re ≤ (M ^ 2) ^ m := by
  by_cases hv : LinearIndependent ℂ v
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac v hv
    rw [det_gram_of v u τ hu hτ hwe, Complex.ofReal_re]
    have hτj : ∀ j, ‖τ j j‖ ≤ M := by
      intro j
      have h1 : inner ℂ (u j) (v j) = τ j j := by
        rw [hwe j]; exact hu.inner_right_fintype (fun b => τ b j) j
      rw [← h1]
      calc ‖inner ℂ (u j) (v j)‖ ≤ ‖u j‖ * ‖v j‖ := norm_inner_le_norm _ _
        _ = ‖v j‖ := by rw [hu.1 j, one_mul]
        _ ≤ M := hM j
    calc ∏ j, ‖τ j j‖ ^ 2 ≤ ∏ _j : Fin m, M ^ 2 :=
          Finset.prod_le_prod₀ (fun j _ => by positivity) fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hτj j) 2
      _ = (M ^ 2) ^ m := by simp
  · rw [gram_det_zero v hv, Complex.zero_re]
    by_cases hm : m = 0
    · subst hm; simp
    · exact pow_nonneg (sq_nonneg M) m

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB

namespace ReciprocityTheory.ChartRestriction.DS.Xi.GSB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B ReciprocityTheory.ChartRestriction.DS.Xi.GS

def linA {k r : ℕ} (A : Mat k r) :
    EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
  (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).symm.toLinearMap ∘ₗ Matrix.toLin' A ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Fin (2 * r + k + 1) → ℂ)).toLinearMap

theorem linA_apply {k r : ℕ} (A : Mat k r) (x : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    linA A x = WithLp.toLp 2 (A *ᵥ WithLp.ofLp x) := rfl

theorem gram_one {m n : ℕ} (u : Fin m → EuclideanSpace ℂ (Fin n)) (hu : Orthonormal ℂ u) : GS.gram u = 1 := by
  ext a b
  simp only [GS.gram, Matrix.of_apply, Matrix.one_apply]
  exact orthonormal_iff_ite.mp hu a b

theorem ga_mul_le (k r : ℕ) (A : Mat k r) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (gN A ^ 2) ^ (l.val + 1) * Ga k r l Y := by
  rw [ga_eq, ga_eq]
  set w : Fin (l.val + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    fun a => WithLp.toLp 2 (Y (Fin.castLE (by omega) a)) with hwdef
  have hAw : (fun a : Fin (l.val + 1) =>
      (WithLp.toLp 2 (A *ᵥ Y (Fin.castLE (by omega) a)) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) =
      fun a => linA A (w a) := by
    funext a; rw [linA_apply]
  rw [hAw]
  by_cases hw : LinearIndependent ℂ w
  · obtain ⟨u, τ, hu, hτ, -, hwe, -⟩ := gs_fac w hw
    have h1 : (fun a => linA A (w a)) = fun a => ∑ b, τ b a • linA A (u b) := by
      funext a; rw [hwe a, map_sum]; simp only [map_smul]
    have hgw : (GS.gram w).det = (τᴴ).det * τ.det := by
      rw [show w = (fun a => ∑ b, τ b a • u b) from funext hwe, gram_comb, gram_one u hu, Matrix.mul_one, det_mul]
    have hv : ∀ b, ‖linA A (u b)‖ ≤ gN A := by
      intro b
      have := norm_mulVec_le A (WithLp.ofLp (u b))
      rw [WithLp.toLp_ofLp, hu.1 b, mul_one] at this
      rw [linA_apply]; exact this
    have hle := gram_re_det_le (fun b => linA A (u b)) (gN A) hv
    have hX := det_gram_of w u τ hu hτ hwe
    rw [h1, gram_comb, det_mul, det_mul]
    have e1 : (τᴴ).det * (GS.gram fun b => linA A (u b)).det * τ.det =
        (GS.gram w).det * (GS.gram fun b => linA A (u b)).det := by rw [hgw]; ring
    rw [e1, hX, Complex.re_ofReal_mul]
    have hnn : (0 : ℝ) ≤ ∏ j, ‖τ j j‖ ^ 2 := Finset.prod_nonneg fun j _ => by positivity
    rw [Complex.ofReal_re, mul_comm]
    exact mul_le_mul_of_nonneg_right hle hnn
  · have hw' : ¬ LinearIndependent ℂ (fun a => linA A (w a)) := fun h => hw (h.of_comp (linA A))
    rw [gram_det_zero _ hw', gram_det_zero _ hw, Complex.zero_re, mul_zero]

end ReciprocityTheory.ChartRestriction.DS.Xi.GSB
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem H_es (k r : ℕ) (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  have ha := a.isLt
  funext i
  have hi := i.isLt
  simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega) | omega

theorem row_fix {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (a : Fin r)
    (j : Fin (2 * r + k + 1)) : h (eI k r a) j = if j = eI k r a then 1 else 0 := by
  obtain ⟨hU, hfix, -⟩ := hm
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have h1 : hᴴ *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
    have := congrArg (fun M => M *ᵥ bvec (esI k r a)) hU'
    simp only [← Matrix.mulVec_mulVec, (hfix a).2, H_es] at this
    exact this
  have h2 := congrFun h1 j
  simp only [bvec, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Pi.single_apply, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  have h3 := congrArg star h2
  rw [star_star] at h3
  rw [h3]
  split_ifs <;> simp

theorem row_apply {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (a : Fin r)
    (v : Fin (2 * r + k + 1) → ℂ) : (h *ᵥ v) (eI k r a) = v (eI k r a) := by
  simp only [Matrix.mulVec, dotProduct, row_fix hm a, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem inv_fix {k r : ℕ} {h : Mat k r} (hu : IsUnit h.det) {v : Fin (2 * r + k + 1) → ℂ} (hv : h *ᵥ v = v) :
    h⁻¹ *ᵥ v = v := by
  calc h⁻¹ *ᵥ v = h⁻¹ *ᵥ (h *ᵥ v) := by rw [hv]
    _ = v := by rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]

theorem conj_apply {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z) (n : Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : h⁻¹ *ᵥ v = v) (a : Fin r) :
    ((h * n * h⁻¹) *ᵥ v) (eI k r a) = (n *ᵥ v) (eI k r a) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv, row_apply hm a]

theorem lam_conj {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hm : h ∈ UWset k r z)
    (hu : IsUnit h.det) (n : Mat k r) : lam k r z (h * n * h⁻¹) = lam k r z n := by
  have hent : ∀ (g : Mat k r) (i j : Fin (2 * r + k + 1)), g i j = (g *ᵥ bvec j) i := by
    intro g i j
    simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hz : h⁻¹ *ᵥ z = z := inv_fix hu hm.2.2
  have hell : ell k r z (h * n * h⁻¹) = ell k r z n := by
    unfold ell
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs with hlt
    · rw [hent (h * n * h⁻¹), hent n]
      exact conj_apply hm n _ (inv_fix hu (hm.2.1 _).1) a
    · exact conj_apply hm n z hz a
  simp only [lam, hell]

end ReciprocityTheory.ChartRestriction.DS.Xi.XI

namespace ReciprocityTheory.ChartRestriction.DS.Xi.XI

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS ReciprocityTheory.ChartRestriction.DS.Xi.GSB

theorem ga_nonneg (k r : ℕ) (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) : 0 ≤ Ga k r l Y := by
  unfold Ga
  let M : Matrix (Fin (2 * r + k + 1)) (Fin (l.val + 1)) ℂ := fun i b => Y (Fin.castLE (by omega) b) i
  have key : 0 ≤ ((Mᴴ * M).det).re := by
    open scoped ComplexOrder in
    have h0 := Complex.le_def.mp (Matrix.posSemidef_conjTranspose_mul_self M).det_nonneg
    rw [Complex.zero_re] at h0
    exact h0.1
  convert key using 3
  ext a b
  first
    | rfl
    | (simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct, Pi.star_apply, M]; rfl)

theorem rpow_bd (a b K s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hK : 1 ≤ K) (hs : 0 ≤ s) (h1 : b ≤ K * a)
    (h2 : a ≤ K * b) : a ^ (-s) ≤ K ^ s * b ^ (-s) := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have hb0 : b = 0 := le_antisymm (by simpa using h1) hb
    subst hb0
    have h3 : 1 ≤ K ^ s := Real.one_le_rpow hK hs
    have h4 : 0 ≤ (0:ℝ) ^ (-s) := Real.rpow_nonneg le_rfl _
    nlinarith
  · have hbpos : 0 < b := by
      by_contra hc
      push_neg at hc
      nlinarith
    rw [Real.rpow_neg ha, Real.rpow_neg hb]
    have hbs : b ^ s ≤ K ^ s * a ^ s := by
      rw [← Real.mul_rpow (by linarith) ha]
      exact Real.rpow_le_rpow hb h1 hs
    have hapos : 0 < a ^ s := Real.rpow_pos_of_pos hpos s
    have hbpos' : 0 < b ^ s := Real.rpow_pos_of_pos hbpos s
    rw [← div_eq_mul_inv, inv_eq_one_div]
    first
      | (rw [div_le_div_iff_of_pos hapos hbpos']; linarith)
      | (rw [div_le_div_iff₀ hapos hbpos']; linarith)

theorem gN_nonneg {k r : ℕ} (g : Mat k r) : 0 ≤ gN g := Real.sqrt_nonneg _

theorem ga_two {k r : ℕ} (A : Mat k r) (K : ℝ) (hA : gN A ≤ K) (l : Fin (r + 1))
    (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => A *ᵥ Y a) ≤ (K ^ (l.val + 1)) ^ 2 * Ga k r l Y := by
  refine (ga_mul_le k r A l Y).trans (mul_le_mul_of_nonneg_right ?_ (ga_nonneg k r l Y))
  rw [← pow_mul, ← pow_mul, mul_comm]
  exact pow_le_pow_left₀ (gN_nonneg A) hA _

theorem xi_bd {k r : ℕ} (s : Fin (r + 1) → ℝ) (hs : ∀ l, 0 ≤ s l) (h : Mat k r) (hu : IsUnit h.det) (K : ℝ)
    (hK : 1 ≤ K) (h1 : gN h ≤ K) (h2 : gN h⁻¹ ≤ K) (m : Mat k r) :
    xiR k r s (h * m) ≤ (∏ l, (K ^ (l.val + 1)) ^ s l) * xiR k r s m := by
  unfold xiR
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro l _
    exact Real.rpow_nonneg (Real.sqrt_nonneg _) _
  · intro l _
    have hK0 : 0 ≤ K ^ (l.val + 1) := pow_nonneg (by linarith) _
    have hK' : 1 ≤ K ^ (l.val + 1) := one_le_pow₀ hK
    have e1 : Ga k r l (fun a => (h * m) *ᵥ phiV k r a) ≤
        (K ^ (l.val + 1)) ^ 2 * Ga k r l (fun a => m *ᵥ phiV k r a) := by
      have := ga_two h K h1 l (fun a => m *ᵥ phiV k r a)
      simp only [Matrix.mulVec_mulVec] at this
      exact this
    have e2 : Ga k r l (fun a => m *ᵥ phiV k r a) ≤
        (K ^ (l.val + 1)) ^ 2 * Ga k r l (fun a => (h * m) *ᵥ phiV k r a) := by
      have := ga_two h⁻¹ K h2 l (fun a => (h * m) *ᵥ phiV k r a)
      simp only [Matrix.mulVec_mulVec, ← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul] at this
      exact this
    have d1 : Del k r l (h * m) ≤ K ^ (l.val + 1) * Del k r l m := by
      have := Real.sqrt_le_sqrt e1
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0] at this
      exact this
    have d2 : Del k r l m ≤ K ^ (l.val + 1) * Del k r l (h * m) := by
      have := Real.sqrt_le_sqrt e2
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hK0] at this
      exact this
    exact rpow_bd _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hK' (hs l) d2 d1

theorem cont_gN {k r : ℕ} : Continuous (gN : Mat k r → ℝ) := by
  unfold gN
  refine Continuous.sqrt ?_
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact Complex.continuous_normSq.comp (continuous_id.matrix_elem i j)

theorem cont_ga {k r : ℕ} (l : Fin (r + 1)) :
    Continuous fun x : Mt k r => Ga k r l (fun a => Matrix.of x *ᵥ phiV k r a) := by
  unfold Ga
  refine Complex.continuous_re.comp ?_
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun a b => ?_
  simp only [Matrix.of_apply]
  have hx : Continuous fun x : Mt k r => Matrix.of x := continuous_id
  first
    | exact ((hx.matrix_mulVec continuous_const).star).dotProduct (hx.matrix_mulVec continuous_const)
    | (simp only [dotProduct]; exact continuous_finset_sum _ fun i _ => ((continuous_apply i).comp (hx.matrix_mulVec continuous_const).star).mul ((continuous_apply i).comp (hx.matrix_mulVec continuous_const)))
    | (simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply]; fun_prop)

theorem meas_xi (k r : ℕ) (s : Fin (r + 1) → ℝ) : Measurable fun x : Mt k r => xiN k r s (Matrix.of x) := by
  unfold xiN xiR
  refine Measurable.real_toNNReal ?_
  refine Finset.measurable_prod _ fun l _ => ?_
  refine Measurable.pow_const ?_ _
  exact ((cont_ga l).sqrt).measurable

end ReciprocityTheory.ChartRestriction.DS.Xi.XI
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.XI

namespace XI

private theorem lintegral_prod_le_lintegral_lintegral {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α × β → ℝ≥0∞) :
    ∫⁻ p, f p ∂(μ.prod ν) ≤ ∫⁻ x, ∫⁻ y, f (x, y) ∂ν ∂μ := by
  exact lintegral_prod_le f

private theorem side {k r : ℕ} (s : Fin (r + 1) → ℝ) (hs : ∀ l, 0 ≤ s l) (z : Fin (2 * r + k + 1) → ℂ)
    (μW μN : Measure (Mt k r)) (hW : IsHaarOn (UWset k r z) μW)
    (hconj : ∀ h₀ ∈ UWset k r z, μN.map (conjM h₀) = μN) (hcomp : IsCompact (UWset k r z))
    (hcl : IsClosedSubgroup (UWset k r z)) (hI : IInt μN z s (1 / 2) < ∞) :
    (∫⁻ p : Mt k r × Mt k r, (xiN k r s (Matrix.of p.2 * Matrix.of p.1) : ℝ≥0∞) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂(μW.prod μN)) < ∞ := by
  obtain ⟨K₀, hK₀⟩ := hcomp.exists_bound_of_continuousOn (cont_gN (k := k) (r := r)).continuousOn
  obtain ⟨K, hK1, hKb⟩ : ∃ K : ℝ, 1 ≤ K ∧ ∀ g ∈ UWset k r z, gN g ≤ K := by
    refine ⟨max K₀ 1, le_max_right _ _, fun g hg => ?_⟩
    have h1 := hK₀ g hg
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  obtain ⟨C, hC0, hCeq⟩ : ∃ C : ℝ, 0 ≤ C ∧ C = ∏ l : Fin (r + 1), (K ^ (l.val + 1)) ^ s l :=
    ⟨_, Finset.prod_nonneg fun l _ => Real.rpow_nonneg (pow_nonneg (by linarith) _) _, rfl⟩
  have hlam : Continuous (fun m : Mt k r => lam k r z (Matrix.of m)) := by
    unfold lam ell
    refine Complex.continuous_re.comp (continuous_const.mul (continuous_finsetSum _ fun a _ => ?_))
    split_ifs with ha
    · first
        | (simp only [Matrix.of_apply]; fun_prop)
        | fun_prop
        | exact (continuous_apply _).comp (continuous_apply _)
    · first
        | (simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]; fun_prop)
        | (simp only [Matrix.mulVec, Matrix.dotProduct, Matrix.of_apply]; fun_prop)
        | exact (continuous_apply _).comp (Continuous.matrix_mulVec continuous_id continuous_const)
  have hWfin : μW Set.univ < ∞ := by
    have h2 : μW Set.univ ≤ μW (UWset k r z) + μW (UWset k r z)ᶜ := by
      first
        | exact measure_univ_le_add_compl _
        | (rw [← Set.union_compl_self (UWset k r z)]; exact measure_union_le _ _)
    rw [hW.conc, add_zero] at h2
    exact lt_of_le_of_lt h2 (hW.finite_compact _ hcomp)
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := by
    rw [ae_iff]
    first
      | exact hW.conc
      | exact measure_mono_null (fun a ha => ha) hW.conc
  have hinner : ∀ h ∈ UWset k r z, (∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
      ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN) ≤
      ENNReal.ofReal C * IInt μN z s (1 / 2) := by
    intro h hh
    have hu : IsUnit h.det := hcl.unit h hh
    have hinv : h⁻¹ ∈ UWset k r z := hcl.inv_mem h hh
    have hu' : IsUnit h⁻¹.det := hcl.unit _ hinv
    have hii : h⁻¹⁻¹ = h := Matrix.nonsing_inv_nonsing_inv h hu
    have hcm : Measurable (conjM (k := k) (r := r) h⁻¹) := by
      apply Continuous.measurable
      first
        | exact continuous_pi fun i => continuous_pi fun j => by
            simp only [conjM, Matrix.mul_apply, Matrix.of_apply]; fun_prop
        | (unfold conjM; fun_prop)
        | (unfold conjM; exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    have hG : Measurable (fun m : Mt k r => ENNReal.ofReal (xiR k r s (Matrix.of m)) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) := by
      have hm1 : Measurable (fun m : Mt k r => ENNReal.ofReal (xiR k r s (Matrix.of m))) :=
        (meas_xi k r s).coe_nnreal_ennreal
      have hm2 : Measurable (fun m : Mt k r =>
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) :=
        ENNReal.measurable_ofReal.comp ((continuous_const.add hlam.abs).measurable.pow_const _)
      exact hm1.mul hm2
    have hpt : ∀ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ≤
        ENNReal.ofReal C * (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) := by
      intro n
      have e : Matrix.of (conjM h⁻¹ n) = h⁻¹ * Matrix.of n * h := by
        show h⁻¹ * Matrix.of n * h⁻¹⁻¹ = _
        rw [hii]
      have hl : lam k r z (h⁻¹ * Matrix.of n * h) = lam k r z (Matrix.of n) := by
        have := lam_conj hinv hu' (Matrix.of n)
        rwa [hii] at this
      have hxi : xiR k r s (Matrix.of n * h) ≤ C * xiR k r s (h⁻¹ * Matrix.of n * h) := by
        have := xi_bd s hs h hu K hK1 (hKb h hh) (hKb h⁻¹ hinv) (h⁻¹ * Matrix.of n * h)
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
          Matrix.one_mul] at this
        rw [hCeq]
        exact this
      have hw : (1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ)) ≤
          (1 + |lam k r z (Matrix.of n)|) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg (lam k r z (Matrix.of n))])
          (by norm_num)
      rw [e, hl, ← mul_assoc, ← ENNReal.ofReal_mul hC0]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hxi) (ENNReal.ofReal_le_ofReal hw)
    calc (∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * h) : ℝ≥0∞) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN)
        ≤ ∫⁻ n : Mt k r, ENNReal.ofReal C * (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) ∂μN :=
          lintegral_mono hpt
      _ = ENNReal.ofReal C * ∫⁻ n : Mt k r, (ENNReal.ofReal (xiR k r s (Matrix.of (conjM h⁻¹ n))) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of (conjM h⁻¹ n))|) ^ (-(1 / 2 : ℝ)))) ∂μN :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal C * ∫⁻ m : Mt k r, (ENNReal.ofReal (xiR k r s (Matrix.of m)) *
          ENNReal.ofReal ((1 + |lam k r z (Matrix.of m)|) ^ (-(1 / 2 : ℝ)))) ∂(μN.map (conjM h⁻¹)) := by
          rw [lintegral_map hG hcm]
      _ = ENNReal.ofReal C * IInt μN z s (1 / 2) := by
          rw [hconj h⁻¹ hinv]
          try rfl
  calc (∫⁻ p : Mt k r × Mt k r, (xiN k r s (Matrix.of p.2 * Matrix.of p.1) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of p.2)|) ^ (-(2 : ℝ))) ∂(μW.prod μN))
      ≤ ∫⁻ x : Mt k r, ∫⁻ n : Mt k r, (xiN k r s (Matrix.of n * Matrix.of x) : ℝ≥0∞) *
        ENNReal.ofReal ((1 + |lam k r z (Matrix.of n)|) ^ (-(2 : ℝ))) ∂μN ∂μW :=
        lintegral_prod_le_lintegral_lintegral μW μN _
    _ ≤ ∫⁻ _x : Mt k r, ENNReal.ofReal C * IInt μN z s (1 / 2) ∂μW :=
        lintegral_mono_ae (hae.mono fun x hx => hinner (Matrix.of x) hx)
    _ = ENNReal.ofReal C * IInt μN z s (1 / 2) * μW Set.univ := lintegral_const _
    _ < ∞ := by
        first
          | exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hI) hWfin
          | exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_ne_top hI.ne) hWfin.ne

end XI

theorem xiIntH (hB2 : InductiveHeisenbergInputs) : XiIntStep := by
  unfold InductiveHeisenbergInputs at hB2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hCI, hCW, -, -, -, -, -, -, -, hClW, -, -, -, -, -⟩ := hB2
  intro k r Wp Wq _ _ _ _ _ _ D s hs hI hI'
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hs0 : ∀ l, 0 ≤ s l := by
    intro l
    have h1 := (hs l).2
    have h2 : (1 : ℝ) ≤ s0 k r l := by
      unfold s0
      split_ifs <;> linarith
    linarith
  unfold XiInt
  refine ⟨XI.meas_xi k r s, ?_, ?_⟩
  · exact XI.side s hs0 D.z D.μW D.μN D.haarW
      (fun h₀ hh => hCI k r Wp Wq D h₀ (Set.mem_union_left _ hh))
      (hCW k r D.z D.z_mem D.T_pos) (hClW k r D.z) hI
  · exact XI.side s hs0 D.z' D.μW' D.μN D.haarW'
      (fun h₀ hh => hCI k r Wp Wq D h₀ (Set.mem_union_right _ hh))
      (hCW k r D.z' D.z'_mem D.T'_pos) (hClW k r D.z') hI'

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

noncomputable section

open Matrix MeasureTheory
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.CB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Xi.GS

variable {k r : ℕ}

theorem hpk_conjT : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  simp only [conjTranspose_apply, hpk_apply]
  by_cases h : j = sigI k r i
  · subst h; rw [if_pos (sig_sig i).symm, if_pos rfl, sgn_sig, star_sgn]
  · have h' : ¬ i = sigI k r j := fun h2 => h (by rw [h2, sig_sig])
    rw [if_neg h', if_neg h, star_zero]

theorem hpk_K : Hpk k r ∈ Kset k r := by
  have h2 := HermitianLiftIdentities.hpk_sq (k := k) (r := r)
  refine ⟨?_, ?_⟩
  · show (Hpk k r)ᴴ * Hpk k r * Hpk k r = Hpk k r
    rw [hpk_conjT, Matrix.mul_assoc, h2, Matrix.mul_one]
  · rw [hpk_conjT, h2]

theorem gN_sq (g : Mat k r) : (∑ i, ∑ j, Complex.normSq (g i j)) = (trace (gᴴ * g)).re := by
  simp only [trace, diag, Matrix.mul_apply, conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply, Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

theorem gN_left {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (κ * g) = gN g := by
  unfold gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]

theorem gN_right {κ : Mat k r} (g : Mat k r) (hκ : κᴴ * κ = 1) : gN (g * κ) = gN g := by
  have hκ' : κ * κᴴ = 1 := mul_eq_one_comm.mp hκ
  unfold gN
  rw [gN_sq, gN_sq, conjTranspose_mul, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc,
    Matrix.mul_assoc, hκ', Matrix.mul_one]

theorem conjH_mul (a b : Mat k r) :
    Hpk k r * a * Hpk k r * (Hpk k r * b * Hpk k r) = Hpk k r * (a * b) * Hpk k r := by
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Hpk k r) (Hpk k r), HermitianLiftIdentities.hpk_sq, Matrix.one_mul]

theorem dot_H (v w : Fin (2 * r + k + 1) → ℂ) :
    star (Hpk k r *ᵥ v) ⬝ᵥ (Hpk k r *ᵥ w) = star v ⬝ᵥ w := by
  have h := HE_adj (HE k r (WithLp.toLp 2 v)) (WithLp.toLp 2 w)
  rw [HE_HE] at h
  simp only [HE_apply, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp] at h
  rw [dotProduct_comm (star (Hpk k r *ᵥ v)), ← h, dotProduct_comm]

theorem ga_H (l : Fin (r + 1)) (Y : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) :
    Ga k r l (fun a => Hpk k r *ᵥ Y a) = Ga k r l Y := by
  unfold Ga; simp only [dot_H]

theorem fsR_conj (s : Fin (r + 1) → ℝ) (x : Mat k r) :
    fsR k r s (Hpk k r * x * Hpk k r) = xiR k r s x := by
  unfold fsR xiR Del
  refine Finset.prod_congr rfl fun l _ => ?_
  have e : (fun a => (Hpk k r * x * Hpk k r) *ᵥ phiV' k r a) = fun a => Hpk k r *ᵥ (x *ᵥ phiV k r a) := by
    funext a
    rw [phiV', mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Hpk k r * x), HermitianLiftIdentities.hpk_sq, Matrix.mul_one]
  rw [e, ga_H, Real.sqrt_eq_rpow, ← Real.rpow_mul (XI.ga_nonneg _ _ _ _)]
  congr 1; ring

theorem xiR_nonneg (s : Fin (r + 1) → ℝ) (x : Mat k r) : 0 ≤ xiR k r s x :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _

theorem norm_bd {E : Type*} [NormedAddCommGroup E] (hGN : GNLower) (F : Mat k r → E) (c A : ℝ)
    (hF : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) (h : Mat k r) (hh : h ∈ GV k r) :
    ‖F h‖ₑ ≤ ENNReal.ofReal c * ENNReal.ofReal (gN h ^ (-A)) := by
  have h1 : 1 ≤ gN h := hGN k r h hh
  have hp : 0 < gN h ^ A := Real.rpow_pos_of_pos (by linarith) A
  have hc0 : 0 ≤ c := le_trans (mul_nonneg hp.le (norm_nonneg _)) (hF h hh)
  have h2 : ‖F h‖ ≤ c * gN h ^ (-A) := by
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]; exact hF h hh
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc0]
  exact ENNReal.ofReal_le_ofReal h2

theorem c_nonneg {E : Type*} [NormedAddCommGroup E] (hGN : GNLower) (F : Mat k r → E) (c A : ℝ)
    (hF : ∀ g ∈ GV k r, gN g ^ A * ‖F g‖ ≤ c) (h1 : (1 : Mat k r) ∈ GV k r) : 0 ≤ c := by
  have : 0 < gN (1 : Mat k r) ^ A := Real.rpow_pos_of_pos (by linarith [hGN k r 1 h1]) A
  exact le_trans (mul_nonneg this.le (norm_nonneg _)) (hF 1 h1)

theorem sum_le (hk : 1 ≤ k) (s : Fin (r + 1) → ℝ) (hs : SAdm k r s) (A : ℝ) (hA : AB k r ≤ A) :
    ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ A := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l ≤ ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l :=
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (by linarith [(hs l).1]) (by positivity)
  have h2 : ∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s0 k r l ≤ 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k := by
    rw [Fin.sum_univ_castSucc]
    simp only [s0, Fin.coe_castSucc, Fin.is_lt, ite_true, Fin.val_last, lt_self_iff_false, ite_false]
    have h3 : ∑ i : Fin r, ((i.val : ℝ) + 1) * 2 ≤ ∑ i : Fin r, (r : ℝ) * 2 := Finset.sum_le_sum fun i _ => by
      have h := Nat.succ_le_of_lt i.isLt
      have : (i.val : ℝ) + 1 ≤ r := by exact_mod_cast h
      linarith
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
    linarith
  have hr : (0 : ℝ) ≤ r := by positivity
  have h4 : 2 * (r : ℝ) * r + ((r : ℝ) + 1) * k ≤ AB k r := by unfold AB; nlinarith
  linarith

theorem s_nonneg (hk : 1 ≤ k) (s : Fin (r + 1) → ℝ) (hs : SAdm k r s) (l : Fin (r + 1)) : 0 ≤ s l := by
  have h1 := (hs l).2
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold s0 at h1; split_ifs at h1 <;> linarith

theorem coefStepC (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := by
  intro k r Wp Wq _ _ _ _ _ _ D A s hs hA hJ
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -, -, -, hCG', -⟩ := hB2
  have hCG := hCG' k r
  have hk := D.k_pos
  have hμ := D.haarG
  have hHK : Hpk k r ∈ Kset k r := hpk_K
  have hHG : Hpk k r ∈ GV k r := hHK.1
  have hH2 : Hpk k r * Hpk k r = 1 := HermitianLiftIdentities.hpk_sq k r
  obtain ⟨CD, hCD⟩ := hD k r s A hk (s_nonneg hk s hs) (sum_le hk s hs A hA)
  have hgc : Continuous fun g : Mt k r => gN (Matrix.of g) := by
    unfold gN
    simp only [Matrix.of_apply]
    exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))
  have hΦm : Measurable fun g : Mt k r => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    (hgc.measurable.pow_const (-A)).ennreal_ofReal
  have hΦinv : ∀ κ ∈ Kset k r, ∀ g : Mt k r,
      ENNReal.ofReal (gN (Matrix.of (lmulM κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) ∧
      ENNReal.ofReal (gN (Matrix.of (rmulF κ g)) ^ (-A)) = ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) :=
    fun κ hκ g => ⟨by rw [show Matrix.of (lmulM κ g) = κ * Matrix.of g from rfl, gN_left _ hκ.2],
      by rw [show Matrix.of (rmulF κ g) = Matrix.of g * κ from rfl, gN_right _ hκ.2]⟩
  refine ⟨CD * (JInt D.μG A s).toReal, fun F F' c c' _ _ hF hF' x hx y hy => ?_⟩
  have hc0 : 0 ≤ c := c_nonneg hGN F c A hF hCG.one_mem
  have hc0' : 0 ≤ c' := c_nonneg hGN F' c' A hF' hCG.one_mem
  have hx' : Hpk k r * x * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hx) _ hHG
  have hy' : Hpk k r * y * Hpk k r ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ hHG _ hy) _ hHG
  have hxinv : (Hpk k r * x * Hpk k r)⁻¹ = Hpk k r * x⁻¹ * Hpk k r :=
    Matrix.inv_eq_left_inv (by rw [conjH_mul, HermitianLiftIdentities.uh_inv_mul hx, Matrix.mul_one, hH2])
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ GV k r := by rw [ae_iff]; exact hμ.conc
  set K : ℝ≥0∞ := ENNReal.ofReal c * ENNReal.ofReal c' * (CD : ℝ≥0∞) with hK
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    ENNReal.coe_ne_top
  have hpt : ∀ᵐ g ∂D.μG, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ≤
      K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) := by
    filter_upwards [hae] with g hg
    have hh : x⁻¹ * Matrix.of g * y ∈ GV k r := hCG.mul_mem _ (hCG.mul_mem _ (hCG.inv_mem _ hx) _ hg) _ hy
    have e1 : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r = (Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r) := by
      rw [hxinv, conjH_mul, conjH_mul]
    have hhH : Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r ∈ GV k r :=
      hCG.mul_mem _ (hCG.mul_mem _ hHG _ hh) _ hHG
    have gNe : gN (x⁻¹ * Matrix.of g * y) = gN (Hpk k r * (x⁻¹ * Matrix.of g * y) * Hpk k r) := by
      rw [gN_right _ hHK.2, gN_left _ hHK.2]
    have b1 := norm_bd hGN F c A hF _ hh
    have b2 : ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A)) ≤ (CD : ℝ≥0∞) * FsE k r s
        ((Hpk k r * x * Hpk k r)⁻¹ * (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) := by
      rw [gNe, ← e1]; exact hCD _ hhH
    have b3 := norm_bd hGN F' c' A hF' _ hg
    calc ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ
        ≤ (ENNReal.ofReal c * ENNReal.ofReal (gN (x⁻¹ * Matrix.of g * y) ^ (-A))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) := mul_le_mul' b1 b3
      _ ≤ (ENNReal.ofReal c * ((CD : ℝ≥0∞) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
            (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)))) *
          (ENNReal.ofReal c' * ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) :=
        mul_le_mul' (mul_le_mul' le_rfl b2) le_rfl
      _ = _ := by rw [hK]; ring
  have hsub : (∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG) =
      ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        Matrix.of g * (Hpk k r * y * Hpk k r)) ∂D.μG := by
    rw [← HermitianLiftIdentities.rmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of g * (Hpk k r * y * Hpk k r))),
      ← HermitianLiftIdentities.lmul_int hHG hμ (fun g => ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) g)) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) g) * (Hpk k r * y * Hpk k r)))]
    refine lintegral_congr fun g => ?_
    show _ = ENNReal.ofReal (gN (Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g))) ^ (-A)) *
        FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ * Matrix.of (rmulF (Hpk k r) (lmulM (Hpk k r) g)) *
          (Hpk k r * y * Hpk k r))
    rw [(hΦinv _ hHK _).2, (hΦinv _ hHK _).1]
    rfl
  have hTb := hT k r s D.μG (fun g => ENNReal.ofReal (gN (Matrix.of g) ^ (-A))) hk hμ hΦm hΦinv _ hx' _ hy'
  calc (∫⁻ g, ‖F (x⁻¹ * Matrix.of g * y)‖ₑ * ‖F' (Matrix.of g)‖ₑ ∂D.μG)
      ≤ ∫⁻ g, K * (ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r))) ∂D.μG := lintegral_mono_ae hpt
    _ = K * ∫⁻ g, ENNReal.ofReal (gN (Matrix.of g) ^ (-A)) * FsE k r s ((Hpk k r * x * Hpk k r)⁻¹ *
        (Hpk k r * Matrix.of g * Hpk k r) * (Hpk k r * y * Hpk k r)) ∂D.μG := lintegral_const_mul' _ _ hKt
    _ = K * (ENNReal.ofReal (fsR k r s (Hpk k r * x * Hpk k r) * fsR k r s (Hpk k r * y * Hpk k r)) *
        JInt D.μG A s) := by rw [hsub, hTb]; rfl
    _ = ENNReal.ofReal (CD * (JInt D.μG A s).toReal * c * c') * (xiN k r s x : ℝ≥0∞) *
        (xiN k r s y : ℝ≥0∞) := by
      rw [fsR_conj, fsR_conj, ENNReal.ofReal_mul (xiR_nonneg s x)]
      rw [show (xiN k r s x : ℝ≥0∞) = ENNReal.ofReal (xiR k r s x) from rfl,
        show (xiN k r s y : ℝ≥0∞) = ENNReal.ofReal (xiR k r s y) from rfl]
      rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg) hc0),
        ENNReal.ofReal_mul (mul_nonneg (NNReal.coe_nonneg CD) ENNReal.toReal_nonneg), ENNReal.ofReal_mul (NNReal.coe_nonneg CD),
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hJ.ne, hK]
      ring

end ReciprocityTheory.ChartRestriction.DS.Xi.CB
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.HermitianLiftIdentities
noncomputable section

open Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.DetB

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem entry_le_gN {k r : ℕ} (h : Mat k r) (m j : Fin (2 * r + k + 1)) : ‖h m j‖ ≤ gN h := by
  unfold gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (h m j) ≤ ∑ j', Complex.normSq (h m j') :=
        Finset.single_le_sum (f := fun j' => Complex.normSq (h m j')) (fun _ _ => Complex.normSq_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j', Complex.normSq (h i j') :=
        Finset.single_le_sum (f := fun i => ∑ j', Complex.normSq (h i j'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ m)

def cst {k r : ℕ} (H : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  ∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖

theorem cst_nonneg {k r : ℕ} (H : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) : 0 ≤ cst H v w :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem herm_le {k r : ℕ} (H h : Mat k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    ‖herm H (h *ᵥ v) w‖ ≤ cst H v w * gN h := by
  have hb := entry_le_gN h
  unfold herm cst
  calc ‖star w ⬝ᵥ (H *ᵥ (h *ᵥ v))‖ = ‖∑ i, ∑ m, ∑ j, star (w i) * (H i m * (h m j * v j))‖ := by
        simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum]
    _ ≤ ∑ i, ∑ m, ∑ j, ‖star (w i) * (H i m * (h m j * v j))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun m _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖ * gN h := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul, norm_mul, norm_mul, norm_star]
        calc ‖w i‖ * (‖H i m‖ * (‖h m j‖ * ‖v j‖)) = (‖w i‖ * ‖H i m‖ * ‖v j‖) * ‖h m j‖ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hb m j) (by positivity)
    _ = (∑ i, ∑ m, ∑ j, ‖w i‖ * ‖H i m‖ * ‖v j‖) * gN h := by simp only [Finset.sum_mul]

def K0 (k r : ℕ) : ℝ := ∑ a : Fin (r + 1), ∑ b : Fin (r + 1), cst (Hpk k r) (phiV' k r b) (phiV' k r a)

theorem lipschitzConst_nonneg (k r : ℕ) : 0 ≤ K0 k r :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => cst_nonneg _ _ _

theorem hermForm_phi_le_bound (k r : ℕ) (a b : Fin (r + 1)) :
    cst (Hpk k r) (phiV' k r b) (phiV' k r a) ≤ K0 k r := by
  unfold K0
  calc cst (Hpk k r) (phiV' k r b) (phiV' k r a) ≤ ∑ b', cst (Hpk k r) (phiV' k r b') (phiV' k r a) :=
        Finset.single_le_sum (f := fun b' => cst (Hpk k r) (phiV' k r b') (phiV' k r a))
          (fun _ _ => cst_nonneg _ _ _) (Finset.mem_univ b)
    _ ≤ _ := Finset.single_le_sum (f := fun a' => ∑ b', cst (Hpk k r) (phiV' k r b') (phiV' k r a'))
          (fun _ _ => Finset.sum_nonneg fun _ _ => cst_nonneg _ _ _) (Finset.mem_univ a)

theorem Dl_le (k r : ℕ) (l : Fin (r + 1)) (h : Mat k r) :
    ‖Dl k r l h‖ ≤ (l.val + 1).factorial * (K0 k r * gN h) ^ (l.val + 1) := by
  have hx : ∀ i j, NormedField.toAbsoluteValue ℂ ((Matrix.of fun a b : Fin (l.val + 1) =>
      herm (Hpk k r) (h *ᵥ phiV' k r (Fin.castLE (by omega) b)) (phiV' k r (Fin.castLE (by omega) a))) i j)
        ≤ K0 k r * gN h := by
    intro i j
    show ‖herm (Hpk k r) (h *ᵥ phiV' k r _) (phiV' k r _)‖ ≤ _
    exact (herm_le _ _ _ _).trans (mul_le_mul_of_nonneg_right (hermForm_phi_le_bound _ _ _ _)
      (le_trans (norm_nonneg _) (entry_le_gN h 0 0)))
  have := Matrix.det_le hx
  simp only [Fintype.card_fin, nsmul_eq_mul] at this
  exact this

def cl (k r : ℕ) (l : Fin (r + 1)) : ℝ := (l.val + 1).factorial * K0 k r ^ (l.val + 1) + 1

theorem cl_pos (k r : ℕ) (l : Fin (r + 1)) : 0 < cl k r l := by
  have := lipschitzConst_nonneg k r
  unfold cl; positivity

theorem fac_le (k r : ℕ) (l : Fin (r + 1)) (s : ℝ) (hs : 0 ≤ s) (h : Mat k r) (hM : 1 ≤ gN h) :
    ENNReal.ofReal (gN h ^ (-(((l.val : ℝ) + 1) * s))) ≤
      ENNReal.ofReal (cl k r l ^ s) * (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s) := by
  have hM0 : 0 < gN h := by linarith
  have hc := cl_pos k r l
  have hK := lipschitzConst_nonneg k r
  have hD : ‖Dl k r l h‖ ≤ cl k r l * gN h ^ (l.val + 1) := by
    have := Dl_le k r l h
    rw [mul_pow, ← mul_assoc] at this
    refine this.trans ?_
    unfold cl
    have : 0 ≤ gN h ^ (l.val + 1) := by positivity
    nlinarith
  have hb : 0 < cl k r l * gN h ^ (l.val + 1) := mul_pos hc (pow_pos hM0 _)
  have h1 : (‖Dl k r l h‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (cl k r l * gN h ^ (l.val + 1)) := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm]; exact ENNReal.ofReal_le_ofReal hD
  have h2 : ENNReal.ofReal (cl k r l * gN h ^ (l.val + 1)) ^ (-s) ≤ (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow h1 hs)
  refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl h2)
  rw [ENNReal.ofReal_rpow_of_pos hb, ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
  congr 1
  rw [Real.mul_rpow hc.le (pow_nonneg hM0.le _), Real.rpow_neg hc.le, ← Real.rpow_natCast,
    ← Real.rpow_mul hM0.le, ← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hc s).ne', one_mul]
  congr 1
  push_cast; ring

end ReciprocityTheory.ChartRestriction.DS.Xi.DetB

namespace ReciprocityTheory.ChartRestriction.DS.Xi

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 DetB

theorem detH (hB2 : InductiveHeisenbergInputs) : DET := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hGN, -⟩ := hB2
  intro k r s A _ hs hA
  refine ⟨∏ l, Real.toNNReal (cl k r l ^ s l), fun h hh => ?_⟩
  have hM : 1 ≤ gN h := hGN k r h hh
  have hM0 : 0 < gN h := by linarith
  calc ENNReal.ofReal (gN h ^ (-A))
        ≤ ENNReal.ofReal (gN h ^ (-∑ l : Fin (r + 1), ((l.val : ℝ) + 1) * s l)) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le hM (neg_le_neg hA))
    _ = ∏ l : Fin (r + 1), ENNReal.ofReal (gN h ^ (-(((l.val : ℝ) + 1) * s l))) := by
        rw [← Finset.sum_neg_distrib, Real.rpow_sum_of_pos hM0,
          ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.rpow_nonneg hM0.le _)]
    _ ≤ ∏ l : Fin (r + 1), (ENNReal.ofReal (cl k r l ^ s l) * (‖Dl k r l h‖₊ : ℝ≥0∞) ^ (-s l)) :=
        Finset.prod_le_prod' fun l _ => fac_le k r l (s l) (hs l) h hM
    _ = _ := by
        rw [Finset.prod_mul_distrib, FsE, ENNReal.ofNNReal_finsetProd]; rfl

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

namespace ReciprocityTheory.ChartRestriction.DS.Xi

theorem det_of (hB2 : InductiveHeisenbergInputs) : DET := detH hB2

theorem coefStep_of (hB2 : InductiveHeisenbergInputs) (hT : TBoth) (hD : DET) : CoefStep := CB.coefStepC hB2 hT hD

end ReciprocityTheory.ChartRestriction.DS.Xi
