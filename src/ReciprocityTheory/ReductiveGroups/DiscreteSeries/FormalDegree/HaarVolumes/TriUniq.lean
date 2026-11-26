module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriDens

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriHaar
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.TriHaarA
noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

def IsUpT (M : Matrix (Fin N) (Fin N) ℂ) : Prop := ∀ a b, b < a → M a b = 0

theorem upMat_isUpT (t : TriCo N) : IsUpT (upMat t) := by
  intro a b h
  simp [upMat, ne_of_gt h, not_lt.mpr h.le]

theorem upMat_diag (t : TriCo N) (a : Fin N) : upMat t a a = ((t.1 a : ℝ) : ℂ) := by
  simp [upMat]

theorem upMat_lt (t : TriCo N) {a b : Fin N} (h : a < b) : upMat t a b = t.2 ⟨(a, b), h⟩ := by
  simp [upMat, h.ne, h]

theorem isUpT_mul {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsUpT A) (hB : IsUpT B) : IsUpT (A * B) := by
  intro a b h
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases lt_or_ge k a with hk | hk
  · rw [hA a k hk, zero_mul]
  · rw [hB k b (lt_of_lt_of_le h hk), mul_zero]

theorem isUpT_mul_diag {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsUpT A) (hB : IsUpT B) (a : Fin N) :
    (A * B) a a = A a a * B a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hA a k hk, zero_mul]
    · rw [hB k a hk, mul_zero]
  · simp

theorem upMat_triCoOf_of {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsUpT M) (hd : ∀ a, (M a a).im = 0) :
    upMat (triCoOf M) = M := by
  ext a b
  rcases lt_trichotomy a b with h | h | h
  · rw [upMat_lt _ h]; rfl
  · subst h; rw [upMat_diag]; simp only [triCoOf]
    exact Complex.ext (by simp) (by simp [hd])
  · rw [upMat_isUpT _ a b h, hM a b h]

theorem triCoOf_upMat (t : TriCo N) : triCoOf (upMat t) = t := by
  ext j
  · simp [triCoOf, upMat]
  · simp only [triCoOf]; rw [upMat_lt _ j.2]

theorem upMat_add (s t : TriCo N) : upMat (s + t) = upMat s + upMat t := by
  ext a b; simp only [upMat, Matrix.add_apply, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> simp

theorem upMat_smul (c : ℝ) (t : TriCo N) : upMat (c • t) = c • upMat t := by
  ext a b; simp only [upMat, Matrix.smul_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
  split_ifs <;> simp [Complex.real_smul]

theorem triCoOf_add (A B : Matrix (Fin N) (Fin N) ℂ) : triCoOf (A + B) = triCoOf A + triCoOf B := by
  ext j <;> simp [triCoOf]

theorem triCoOf_smul (c : ℝ) (A : Matrix (Fin N) (Fin N) ℂ) : triCoOf (c • A) = c • triCoOf A := by
  ext j <;> simp [triCoOf]

theorem upMat_injective : Function.Injective (upMat (N := N)) := by
  intro s t h
  rw [← triCoOf_upMat s, ← triCoOf_upMat t, h]

def rmulL (B : Matrix (Fin N) (Fin N) ℂ) : TriCo N →ₗ[ℝ] TriCo N where
  toFun t := triCoOf (upMat t * B)
  map_add' s t := by rw [upMat_add, Matrix.add_mul, triCoOf_add]
  map_smul' c t := by rw [upMat_smul, Matrix.smul_mul, triCoOf_smul]; rfl

theorem rmulL_apply (B : Matrix (Fin N) (Fin N) ℂ) (t : TriCo N) :
    rmulL B t = triCoOf (upMat t * B) := rfl

theorem triCoOf_sub (A B : Matrix (Fin N) (Fin N) ℂ) : triCoOf (A - B) = triCoOf A - triCoOf B := by
  ext j <;> simp [triCoOf]

theorem upMat_zero : upMat (0 : TriCo N) = 0 := by
  ext a b; simp only [upMat, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]; split_ifs <;> simp

theorem upMat_triCoOf_eq_zero {X : Matrix (Fin N) (Fin N) ℂ} {a b : Fin N} (h : X a b = 0) :
    upMat (triCoOf X) a b = 0 := by
  rcases lt_trichotomy a b with hab | hab | hab
  · rw [upMat_lt _ hab]; exact h
  · subst hab; rw [upMat_diag]; simp [triCoOf, h]
  · exact upMat_isUpT _ a b hab

theorem det_rmulL_unip (U : Matrix (Fin N) (Fin N) ℂ) (hU : ∀ c b, b ≤ c → (1 - U) c b = 0) :
    LinearMap.det (rmulL U) = 1 := by
  set Nl : Module.End ℝ (TriCo N) := 1 - rmulL U with hNl
  have hN : ∀ s, Nl s = triCoOf (upMat s * (1 - U)) := by
    intro s
    rw [Matrix.mul_sub, Matrix.mul_one, triCoOf_sub, triCoOf_upMat, hNl]
    rfl
  have hpow : ∀ k s, ∀ a b : Fin N, (b : ℕ) < a + k → upMat ((Nl ^ k) s) a b = 0 := by
    intro k
    induction k with
    | zero => intro s a b h; exact upMat_isUpT _ a b (by simpa using h)
    | succ k ih =>
      intro s a b h
      rw [pow_succ', Module.End.mul_apply, hN]
      apply upMat_triCoOf_eq_zero
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      by_cases hc : (c : ℕ) < a + k
      · rw [ih s a c hc, zero_mul]
      · rw [hU c b (by rw [Fin.le_def]; omega), mul_zero]
  have hnil : IsNilpotent Nl := by
    refine ⟨N, LinearMap.ext fun s => ?_⟩
    apply upMat_injective
    rw [LinearMap.zero_apply, upMat_zero]
    ext a b
    exact hpow N s a b (by omega)
  have h1 := LinearMap.eval_charpoly Nl 1
  rw [hnil.charpoly_eq_X_pow_finrank] at h1
  simp only [Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h1
  rw [h1, hNl, sub_sub_cancel]

def scaleL (d : Fin N → ℝ) : TriCo N →ₗ[ℝ] TriCo N :=
  LinearMap.prodMap (LinearMap.pi fun j => (d j • LinearMap.id).comp (LinearMap.proj j))
    (LinearMap.pi fun ab : {ab : Fin N × Fin N // ab.1 < ab.2} =>
      ((d ab.1.2 • LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj ab))

theorem scaleL_triCoOf (d : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℂ) :
    scaleL d (triCoOf X) = triCoOf (X * Matrix.diagonal fun j => ((d j : ℝ) : ℂ)) := by
  ext j
  · simp [scaleL, triCoOf, Matrix.mul_diagonal, mul_comm]
  · simp [scaleL, triCoOf, Matrix.mul_diagonal, Complex.real_smul, mul_comm]

theorem prod_subtype_snd (f : Fin N → ℝ) :
    ∏ ab : {ab : Fin N × Fin N // ab.1 < ab.2}, f ab.1.2 = ∏ j : Fin N, f j ^ (j : ℕ) := by
  rw [← Finset.prod_subtype (univ.filter fun ab : Fin N × Fin N => ab.1 < ab.2) (by simp)
    (fun ab => f ab.2), Finset.prod_filter, Fintype.prod_prod_type, Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_filter]
  show ∏ a ∈ univ.filter (fun a : Fin N => a < j), f j = _
  rw [Finset.prod_const]
  have : (univ.filter fun a : Fin N => a < j) = Iio j := by ext; simp
  rw [this, Fin.card_Iio]

theorem det_scaleL (d : Fin N → ℝ) :
    LinearMap.det (scaleL d) = ∏ j : Fin N, d j ^ (2 * (j : ℕ) + 1) := by
  rw [scaleL, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  simp only [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_self, pow_one,
    Complex.finrank_real_complex]
  rw [prod_subtype_snd (fun j => d j ^ 2), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

def unipOf (t0 : TriCo N) : TriCo N := (fun _ => 1, fun ab => t0.2 ab / ((t0.1 ab.1.2 : ℝ) : ℂ))

theorem upMat_eq_unip_mul (t0 : TriCo N) (h0 : ∀ j, t0.1 j ≠ 0) :
    upMat t0 = upMat (unipOf t0) * Matrix.diagonal fun j => ((t0.1 j : ℝ) : ℂ) := by
  ext a b
  rw [Matrix.mul_diagonal]
  rcases lt_trichotomy a b with h | h | h
  · rw [upMat_lt _ h, upMat_lt _ h]
    have : ((t0.1 b : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h0 b
    simp only [unipOf]
    field_simp
  · subst h; rw [upMat_diag, upMat_diag]; simp [unipOf]
  · rw [upMat_isUpT _ a b h, upMat_isUpT _ a b h, zero_mul]

theorem det_rmulL_upMat (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    LinearMap.det (rmulL (upMat t0)) = ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) := by
  have hne : ∀ j, t0.1 j ≠ 0 := fun j => (h0 j).ne'
  have hc : rmulL (upMat t0) = scaleL t0.1 ∘ₗ rmulL (upMat (unipOf t0)) := by
    refine LinearMap.ext fun t => ?_
    rw [LinearMap.comp_apply, rmulL_apply, rmulL_apply, scaleL_triCoOf, upMat_eq_unip_mul t0 hne,
      Matrix.mul_assoc]
  rw [hc, LinearMap.det_comp, det_scaleL, det_rmulL_unip, mul_one]
  intro c b hbc
  rcases lt_or_eq_of_le hbc with h | h
  · rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_gt h), upMat_isUpT _ c b h, sub_zero]
  · subst h; rw [Matrix.sub_apply, Matrix.one_apply_eq, upMat_diag]; simp [unipOf]

theorem upMat_triCoOf_mul' (t t0 : TriCo N) :
    upMat (triCoOf (upMat t * upMat t0)) = upMat t * upMat t0 ∧
      ∀ j, (triCoOf (upMat t * upMat t0)).1 j = t.1 j * t0.1 j := by
  have hU := isUpT_mul (upMat_isUpT t) (upMat_isUpT t0)
  have hd : ∀ a, (upMat t * upMat t0) a a = ((t.1 a * t0.1 a : ℝ) : ℂ) := fun a => by
    rw [isUpT_mul_diag (upMat_isUpT t) (upMat_isUpT t0), upMat_diag, upMat_diag]; push_cast; ring
  refine ⟨upMat_triCoOf_of hU fun a => by rw [hd]; simp, fun j => ?_⟩
  simp only [triCoOf]; rw [hd]; simp

theorem triDens_measurable : Measurable (triDens (N := N)) := by unfold triDens; fun_prop

theorem triDens_rmulL (t0 t : TriCo N) (h0 : t0 ∈ triPos N) :
    triDens t = ENNReal.ofReal (∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1)) *
      triDens (rmulL (upMat t0) t) := by
  have h2 := (upMat_triCoOf_mul' t t0).2
  unfold triDens
  rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun j _ => pow_nonneg (h0 j).le _)]
  congr 1
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [rmulL_apply, h2 j, mul_zpow]
  have hne : t0.1 j ≠ 0 := (h0 j).ne'
  have : t0.1 j ^ (2 * (j : ℕ) + 1) * t0.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1)) = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hne]; push_cast; simp
  rw [mul_left_comm, this, mul_one]

theorem rmulL_mem_triPos (t0 t : TriCo N) (h0 : t0 ∈ triPos N) :
    rmulL (upMat t0) t ∈ triPos N ↔ t ∈ triPos N := by
  simp only [triPos, Set.mem_ofPred_eq, rmulL_apply, (upMat_triCoOf_mul' t t0).2]
  exact forall_congr' fun j => mul_pos_iff_of_pos_right (h0 j)

end ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.UpperTriangularMatrices

variable {N : ℕ}

theorem upMat_triCoOf_mul (t t0 : TriCo N) :
    upMat (triCoOf (upMat t * upMat t0)) = upMat t * upMat t0 ∧
      ∀ j, (triCoOf (upMat t * upMat t0)).1 j = t.1 j * t0.1 j := by
  have hU : ∀ (s : TriCo N) (a b : Fin N), upMat s a b =
      if a = b then ((s.1 a : ℝ) : ℂ) else if h : a < b then s.2 ⟨(a, b), h⟩ else 0 :=
    fun s a b => rfl
  have hz : ∀ (s : TriCo N) (a b : Fin N), b < a → upMat s a b = 0 := by
    intro s a b h
    rw [hU s a b, if_neg (ne_of_gt h), dite_eq_right (not_lt.mpr h.le)]
  have hlow : ∀ a b : Fin N, b < a → (upMat t * upMat t0) a b = 0 := by
    intro a b hba
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero (fun k _ => ?_)
    by_cases hka : k < a
    · rw [hz t a k hka, zero_mul]
    · rw [hz t0 k b (lt_of_lt_of_le hba (not_lt.mp hka)), mul_zero]
  have hdiag : ∀ a, (upMat t * upMat t0) a a = ((t.1 a * t0.1 a : ℝ) : ℂ) := by
    intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU t a a, hU t0 a a, if_pos rfl, if_pos rfl, Complex.ofReal_mul]
    · intro k _ hka
      rcases lt_or_gt_of_ne hka with h | h
      · rw [hz t a k h, zero_mul]
      · rw [hz t0 k a h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  refine ⟨?_, fun j => ?_⟩
  · ext a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hU _ a b, if_neg (ne_of_lt h), dite_eq_left h]
      rfl
    · subst h
      rw [hU _ a a, if_pos rfl]
      show (((upMat t * upMat t0) a a).re : ℂ) = (upMat t * upMat t0) a a
      rw [hdiag, Complex.ofReal_re]
    · rw [hU _ a b, if_neg (ne_of_gt h), dite_eq_right (not_lt.mpr h.le), hlow a b h]
  · show ((upMat t * upMat t0) j j).re = t.1 j * t0.1 j
    rw [hdiag, Complex.ofReal_re]

theorem triMeas_map_mul_right (t0 : TriCo N) (h0 : t0 ∈ triPos N) :
    Measure.map (fun t : TriCo N => triCoOf (upMat t * upMat t0)) (triMeas N) = triMeas N := by
  classical
  have hfun : (fun t : TriCo N => triCoOf (upMat t * upMat t0)) = ⇑(rmulL (upMat t0)) := by
    funext t
    rw [rmulL_apply]
  set L : TriCo N →ₗ[ℝ] TriCo N := rmulL (upMat t0) with hL
  have hdet : LinearMap.det L = ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) := det_rmulL_upMat t0 h0
  set D : ℝ := ∏ j : Fin N, t0.1 j ^ (2 * (j : ℕ) + 1) with hD
  have hDpos : 0 < D := Finset.prod_pos fun j _ => pow_pos (h0 j) _
  have hLm : Measurable L := L.continuous_of_finiteDimensional.measurable
  haveI hC : (volume : Measure ({ab : Fin N × Fin N // ab.1 < ab.2} → ℂ)).IsAddHaarMeasure := by
    first
      | infer_instance
      | exact Measure.pi.isAddHaarMeasure _
  haveI hR : (volume : Measure (Fin N → ℝ)).IsAddHaarMeasure := by
    first
      | infer_instance
      | exact Measure.pi.isAddHaarMeasure _
  haveI hT : (volume : Measure (TriCo N)).IsAddHaarMeasure := by
    first
      | exact Measure.prod.instIsAddHaarMeasure volume volume
      | infer_instance
  have hvol : Measure.map L (volume : Measure (TriCo N)) = ENNReal.ofReal |D⁻¹| • volume := by
    rw [← hdet]
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar _ (by rw [hdet]; exact hDpos.ne')
  have hP : MeasurableSet (triPos N) := by
    have : triPos N = ⋂ j : Fin N, {t : TriCo N | 0 < t.1 j} := by
      ext t
      simp [triPos]
    rw [this]
    exact MeasurableSet.iInter fun j =>
      measurableSet_lt measurable_const ((measurable_pi_apply j).comp measurable_fst)
  have hpre : ∀ S : Set (TriCo N), L ⁻¹' S ∩ triPos N = L ⁻¹' (S ∩ triPos N) := by
    intro S
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [hL, rmulL_mem_triPos t0 x h0]
  rw [hfun]
  ext s hs
  have hS : MeasurableSet (s ∩ triPos N) := hs.inter hP
  rw [Measure.map_apply hLm hs, triMeas, withDensity_apply _ (hLm hs), withDensity_apply _ hs,
    Measure.restrict_restrict (hLm hs), Measure.restrict_restrict hs, hpre s]
  have h1 : ∫⁻ x in L ⁻¹' (s ∩ triPos N), triDens x =
      ∫⁻ x in L ⁻¹' (s ∩ triPos N), ENNReal.ofReal D * triDens (L x) := by
    refine lintegral_congr fun x => ?_
    rw [hL, hD, ← triDens_rmulL t0 x h0]
  have h2 : ∫⁻ x in L ⁻¹' (s ∩ triPos N), ENNReal.ofReal D * triDens (L x) =
      ENNReal.ofReal D * ∫⁻ x, (s ∩ triPos N).indicator triDens (L x) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator (hLm hS)]
    congr 1
  have h3 : ∫⁻ x, (s ∩ triPos N).indicator triDens (L x) =
      ENNReal.ofReal |D⁻¹| * ∫⁻ y in s ∩ triPos N, triDens y := by
    rw [← lintegral_map ((triDens_measurable).indicator hS) hLm, hvol, lintegral_smul_measure,
      lintegral_indicator hS]
    rfl
  rw [h1, h2, h3, ← mul_assoc, ← ENNReal.ofReal_mul hDpos.le, abs_of_pos (inv_pos.mpr hDpos),
    mul_inv_cancel₀ hDpos.ne', ENNReal.ofReal_one, one_mul]

theorem triMeas_compact_lt_top (K : Set (TriCo N)) (hK : IsCompact K) (hK0 : K ⊆ triPos N) :
    triMeas N K < ⊤ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  unfold triMeas
  rw [withDensity_apply _ hKm, Measure.restrict_restrict hKm, Set.inter_eq_left.mpr hK0]
  have hgc : ContinuousOn (fun t : TriCo N => ∏ j : Fin N, t.1 j ^ (-(2 * ((j : ℕ) : ℤ) + 1))) K := by
    refine continuousOn_finsetProd _ (fun j _ => ?_)
    exact ContinuousOn.zpow₀ (by fun_prop : Continuous fun t : TriCo N => t.1 j).continuousOn _
      (fun x hx => Or.inl (hK0 hx j).ne')
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hgc
  calc ∫⁻ a in K, triDens a ≤ ∫⁻ _ in K, ENNReal.ofReal C := by
        refine setLIntegral_mono' hKm (fun x hx => ?_)
        exact ENNReal.ofReal_le_ofReal ((Real.le_norm_self _).trans (hC x hx))
    _ = ENNReal.ofReal C * volume K := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top

end ReciprocityTheory.ChartRestriction.DS
end
end

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {N : ℕ}

namespace PositiveTriangularSet

theorem triCoOf_upMat (t : TriCo N) : triCoOf (upMat t) = t := by
  rcases t with ⟨d, u⟩
  refine Prod.ext ?_ ?_
  · funext j; simp [triCoOf, upMat]
  · funext ab; simp [triCoOf, upMat, ab.2.ne, ab.2]

theorem upMat_up (t : TriCo N) : (upMat t).BlockTriangular id := by
  intro i j h
  have h' : j < i := h
  simp [upMat, h'.ne', not_lt.mpr h'.le]

theorem upMat_diag (t : TriCo N) (j : Fin N) : upMat t j j = ((t.1 j : ℝ) : ℂ) := by
  simp [upMat]

theorem upMat_triCoOf_of_up (A : Matrix (Fin N) (Fin N) ℂ) (hA : A.BlockTriangular id)
    (hd : ∀ j, (A j j).im = 0) : upMat (triCoOf A) = A := by
  ext i j
  simp only [upMat, triCoOf]
  split_ifs with h1 h2
  · subst h1; exact Complex.ext (by simp) (by simp [hd])
  · rfl
  · have : j < i := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
    exact (@hA i j this).symm

theorem diag_mul_of_up {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (j : Fin N) : (A * B) j j = A j j * B j j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single j (fun k _ hk => ?_) (by simp)
  rcases lt_or_gt_of_ne hk with h | h
  · rw [@hA j k h, zero_mul]
  · rw [@hB k j h, mul_zero]

theorem isOpen_triPos : IsOpen (triPos N) := by
  have : triPos N = ⋂ j : Fin N, {t : TriCo N | 0 < t.1 j} := by ext; simp [triPos]
  rw [this]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt continuous_const ((continuous_apply j).comp continuous_fst)

theorem ms_triPos : MeasurableSet (triPos N) := isOpen_triPos.measurableSet

theorem continuous_upMat : Continuous (upMat : TriCo N → Matrix (Fin N) (Fin N) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  simp only [upMat]
  split_ifs
  · exact Complex.continuous_ofReal.comp ((continuous_apply a).comp continuous_fst)
  · exact (continuous_apply _).comp continuous_snd
  · exact continuous_const

theorem continuous_triCoOf : Continuous (triCoOf : Matrix (Fin N) (Fin N) ℂ → TriCo N) := by
  refine Continuous.prodMk (continuous_pi fun j => ?_) (continuous_pi fun ab => ?_)
  · exact Complex.continuous_re.comp ((continuous_apply j).comp (continuous_apply j))
  · exact (continuous_apply _).comp (continuous_apply _)

theorem det_upMat (t : TriCo N) : (upMat t).det = ∏ j, ((t.1 j : ℝ) : ℂ) := by
  rw [det_of_isUpperTriangular (upMat_up t)]
  simp [upMat_diag]

theorem det_upMat_ne (t : TriCo N) (ht : t ∈ triPos N) : IsUnit (upMat t).det := by
  rw [det_upMat, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro j _
  exact Complex.ofReal_ne_zero.mpr (ht j).ne'

theorem inv_up (t : TriCo N) (ht : t ∈ triPos N) : (upMat t)⁻¹.BlockTriangular id := by
  let _ := (upMat t).invertibleOfIsUnitDet (det_upMat_ne t ht)
  exact blockTriangular_inv_of_blockTriangular (upMat_up t)

theorem inv_diag (t : TriCo N) (ht : t ∈ triPos N) (j : Fin N) :
    (upMat t)⁻¹ j j = (((t.1 j)⁻¹ : ℝ) : ℂ) := by
  have h1 := congrFun (congrFun (nonsing_inv_mul _ (det_upMat_ne t ht)) j) j
  rw [diag_mul_of_up (inv_up t ht) (upMat_up t), upMat_diag, Matrix.one_apply_eq] at h1
  have h2 : ((t.1 j : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ht j).ne'
  rw [Complex.ofReal_inv]
  exact eq_inv_of_mul_eq_one_left h1

theorem upMat_mul_mem (a b : TriCo N) (ha : a ∈ triPos N) (hb : b ∈ triPos N) :
    upMat (triCoOf (upMat a * upMat b)) = upMat a * upMat b ∧
      triCoOf (upMat a * upMat b) ∈ triPos N := by
  have hu := (upMat_up a).mul (upMat_up b)
  have hd : ∀ j, (upMat a * upMat b) j j = (((a.1 j * b.1 j : ℝ)) : ℂ) := fun j => by
    rw [diag_mul_of_up (upMat_up a) (upMat_up b), upMat_diag, upMat_diag, Complex.ofReal_mul]
  refine ⟨upMat_triCoOf_of_up _ hu (fun j => by rw [hd]; simp), fun j => ?_⟩
  show 0 < ((upMat a * upMat b) j j).re
  rw [hd, Complex.ofReal_re]
  exact mul_pos (ha j) (hb j)

theorem upMat_inv_mem (a : TriCo N) (ha : a ∈ triPos N) :
    upMat (triCoOf (upMat a)⁻¹) = (upMat a)⁻¹ ∧ triCoOf (upMat a)⁻¹ ∈ triPos N := by
  refine ⟨upMat_triCoOf_of_up _ (inv_up a ha) (fun j => by rw [inv_diag a ha]; simp), fun j => ?_⟩
  show 0 < ((upMat a)⁻¹ j j).re
  rw [inv_diag a ha, Complex.ofReal_re]
  exact inv_pos.mpr (ha j)

theorem one_mem : upMat (triCoOf (1 : Matrix (Fin N) (Fin N) ℂ)) = 1 ∧
    triCoOf (1 : Matrix (Fin N) (Fin N) ℂ) ∈ triPos N := by
  refine ⟨upMat_triCoOf_of_up _ Matrix.blockTriangular_one (fun j => by simp), fun j => ?_⟩
  show 0 < ((1 : Matrix (Fin N) (Fin N) ℂ) j j).re
  simp

abbrev TG (N : ℕ) : Type := ↥(triPos N)

scoped instance : Mul (TG N) := ⟨fun a b => ⟨triCoOf (upMat b.1 * upMat a.1), (upMat_mul_mem b.1 a.1 b.2 a.2).2⟩⟩
scoped instance : One (TG N) := ⟨⟨triCoOf 1, one_mem.2⟩⟩
scoped instance : Inv (TG N) := ⟨fun a => ⟨triCoOf (upMat a.1)⁻¹, (upMat_inv_mem a.1 a.2).2⟩⟩

theorem upMat_tg_mul (a b : TG N) : upMat (a * b).1 = upMat b.1 * upMat a.1 :=
  (upMat_mul_mem b.1 a.1 b.2 a.2).1

theorem upMat_tg_one : upMat (1 : TG N).1 = 1 := one_mem.1

theorem upMat_tg_inv (a : TG N) : upMat a⁻¹.1 = (upMat a.1)⁻¹ := (upMat_inv_mem a.1 a.2).1

theorem tg_ext {a b : TG N} (h : upMat a.1 = upMat b.1) : a = b := by
  apply Subtype.ext
  rw [← triCoOf_upMat a.1, ← triCoOf_upMat b.1, h]

scoped instance : Group (TG N) where
  mul_assoc a b c := tg_ext (by simp only [upMat_tg_mul, Matrix.mul_assoc])
  one_mul a := tg_ext (by rw [upMat_tg_mul, upMat_tg_one, Matrix.mul_one])
  mul_one a := tg_ext (by rw [upMat_tg_mul, upMat_tg_one, Matrix.one_mul])
  inv_mul_cancel a := tg_ext (by
    rw [upMat_tg_mul, upMat_tg_inv, upMat_tg_one, mul_nonsing_inv _ (det_upMat_ne a.1 a.2)])

theorem continuous_tg_mul : Continuous fun p : TG N × TG N => p.1 * p.2 :=
  Continuous.subtype_mk (continuous_triCoOf.comp
    ((continuous_upMat.comp (continuous_subtype_val.comp continuous_snd)).matrix_mul
      (continuous_upMat.comp (continuous_subtype_val.comp continuous_fst)))) _

theorem continuous_tg_inv : Continuous fun a : TG N => a⁻¹ := by
  refine Continuous.subtype_mk (continuous_triCoOf.comp ?_) _
  rw [continuous_iff_continuousAt]
  intro a
  have hd : (upMat a.1).det ≠ 0 := (det_upMat_ne a.1 a.2).ne_zero
  have hinv : ContinuousAt Ring.inverse (upMat a.1).det := by
    rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hd
  exact (continuousAt_matrix_inv (upMat a.1) hinv).comp (f := fun x : TG N => upMat x.1)
    (continuous_upMat.comp continuous_subtype_val).continuousAt

scoped instance : IsTopologicalGroup (TG N) where
  continuous_mul := continuous_tg_mul
  continuous_inv := continuous_tg_inv

scoped instance : LocallyCompactSpace (TG N) := isOpen_triPos.locallyCompactSpace

theorem continuous_rmul (g : TriCo N) : Continuous fun t : TriCo N => triCoOf (upMat t * upMat g) :=
  continuous_triCoOf.comp (continuous_upMat.matrix_mul continuous_const)

theorem lift_inv (κ : Measure (TriCo N)) (hκ0 : κ (triPos N)ᶜ = 0)
    (hinv : ∀ t0 ∈ triPos N, Measure.map (fun t : TriCo N => triCoOf (upMat t * upMat t0)) κ = κ) :
    (κ.comap Subtype.val : Measure (TG N)).IsMulLeftInvariant := by
  constructor
  intro g
  ext A hA
  rw [Measure.map_apply (measurable_const_mul g) hA, comap_subtype_coe_apply ms_triPos,
    comap_subtype_coe_apply ms_triPos]
  have key : Subtype.val '' ((fun x : TG N => g * x) ⁻¹' A) =
      (fun t : TriCo N => triCoOf (upMat t * upMat g.1)) ⁻¹' (Subtype.val '' A) ∩ triPos N := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨g * x, hx, rfl⟩, x.2⟩
    · rintro ⟨⟨y, hy, hyt⟩, ht⟩
      refine ⟨⟨t, ht⟩, ?_, rfl⟩
      have : g * ⟨t, ht⟩ = y := Subtype.ext (by rw [hyt]; rfl)
      show g * ⟨t, ht⟩ ∈ A
      rw [this]; exact hy
  rw [key, measure_inter_conull hκ0, ← Measure.map_apply (continuous_rmul g.1).measurable
    (MeasurableSet.subtype_image ms_triPos hA), hinv g.1 g.2]

theorem lift_fin (κ : Measure (TriCo N))
    (hfin : ∀ K : Set (TriCo N), IsCompact K → K ⊆ triPos N → κ K < ⊤) :
    IsFiniteMeasureOnCompacts (κ.comap Subtype.val : Measure (TG N)) :=
  ⟨fun K hK => by
    rw [comap_subtype_coe_apply ms_triPos]
    exact hfin _ (hK.image continuous_subtype_val) (by rintro _ ⟨x, -, rfl⟩; exact x.2)⟩

theorem restore (κ : Measure (TriCo N)) (hκ0 : κ (triPos N)ᶜ = 0) :
    (κ.comap Subtype.val : Measure (TG N)).map Subtype.val = κ := by
  rw [map_comap_subtype_coe ms_triPos]
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hκ0)

theorem triMeas_compl : triMeas N (triPos N)ᶜ = 0 := by
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply ms_triPos.compl]
  simp

theorem triDens_pos (t : TriCo N) (ht : t ∈ triPos N) : triDens t ≠ 0 := by
  unfold triDens
  rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact Finset.prod_pos fun j _ => zpow_pos (ht j) _

theorem triMeas_ne_zero : triMeas N ≠ 0 := by
  intro h0
  have h1 : triMeas N (triPos N) = 0 := by rw [h0]; rfl
  unfold triMeas at h1
  have haem : AEMeasurable triDens (volume.restrict (triPos N)) := by
    refine ContinuousOn.aemeasurable ?_ ms_triPos
    refine ENNReal.continuous_ofReal.comp_continuousOn (continuousOn_finsetProd _ fun j _ => ?_)
    exact ContinuousOn.zpow₀ ((continuous_apply j).comp continuous_fst).continuousOn _
      (fun t ht => Or.inl (ht j).ne')
  rw [withDensity_apply _ ms_triPos, Measure.restrict_restrict ms_triPos, Set.inter_self,
    setLIntegral_eq_zero_iff' ms_triPos haem] at h1
  have h2 := ae_iff.mp h1
  have h3 : {x | ¬(x ∈ triPos N → triDens x = 0)} = triPos N := by
    ext x
    constructor
    · intro h
      by_contra hx
      exact h (fun h' => absurd h' hx)
    · intro h h'
      exact triDens_pos x h (h' h)
  rw [h3] at h2
  exact isOpen_triPos.measure_ne_zero volume ⟨(fun _ => 1, 0), fun j => one_pos⟩ h2

end PositiveTriangularSet

open PositiveTriangularSet in
theorem triMeas_unique (κ : Measure (TriCo N)) (hκ0 : κ (triPos N)ᶜ = 0)
    (hfin : ∀ K : Set (TriCo N), IsCompact K → K ⊆ triPos N → κ K < ⊤)
    (hinv : ∀ t0 ∈ triPos N, Measure.map (fun t : TriCo N => triCoOf (upMat t * upMat t0)) κ = κ) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ κ = c • triMeas N := by
  have := lift_inv κ hκ0 hinv
  have := lift_fin κ hfin
  have := lift_inv (triMeas N) triMeas_compl (fun t0 h => triMeas_map_mul_right t0 h)
  have := lift_fin (triMeas N) (fun K hK h => triMeas_compact_lt_top K hK h)
  obtain ⟨a, h1⟩ : ∃ a : NNReal, (κ.comap Subtype.val : Measure (TG N)) = a • Measure.haar :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  obtain ⟨b, h2⟩ : ∃ b : NNReal, ((triMeas N).comap Subtype.val : Measure (TG N)) = b • Measure.haar :=
    ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩
  set η : Measure (TriCo N) := (Measure.haar : Measure (TG N)).map Subtype.val
  have hval : AEMeasurable (Subtype.val : TG N → TriCo N) Measure.haar :=
    measurable_subtype_coe.aemeasurable
  have hk : κ = (a : ENNReal) • η := by
    rw [← restore κ hκ0, h1, ENNReal.smul_def, Measure.map_smul _ hval]
  have ht : triMeas N = (b : ENNReal) • η := by
    rw [← restore (triMeas N) triMeas_compl, h2, ENNReal.smul_def, Measure.map_smul _ hval]
  have hb : b ≠ 0 := by
    rintro hb0
    apply triMeas_ne_zero (N := N)
    rw [ht, hb0]; simp
  refine ⟨((a / b : NNReal) : ENNReal), ENNReal.coe_ne_top, ?_⟩
  rw [ht, smul_smul, ← ENNReal.coe_mul, div_mul_cancel₀ a hb, hk]

end ReciprocityTheory.ChartRestriction.DS
