module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelHeightBoundSection
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagUnipotentEqStabilizerTimesSection
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableFlagGramNumberNormalizedIndicator
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentLebesgueMeasureIsHaarOn

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentGramNullAndFibreVolumeNormalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramEqGramDetProjectionNormalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramEqGramDetProjectionNormalForm
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NormalGram

variable {k r : ℕ}

def mid (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

theorem idx_cases (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ j, i = wI k r j) ∨ ∃ a, i = esI k r a := by
  have hi := i.2
  by_cases h1 : i.val < r
  · exact Or.inl ⟨⟨i.val, h1⟩, rfl⟩
  by_cases h2 : i.val ≤ r + k
  · exact Or.inr (Or.inl ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩)
  · exact Or.inr (Or.inr ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp only [esI]; omega)⟩)

theorem wI_inj : Function.Injective (wI k r) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [wI] at this
  exact Fin.ext (by omega)

theorem sum_mid (f : Fin (2 * r + k + 1) → ℂ) (hf : inWb k r f) : ∑ i, f i = ∑ j, f (wI k r j) := by
  symm
  refine Finset.sum_of_injOn (wI k r) wI_inj.injOn (by simp) ?_ (by simp)
  intro i _ hi
  apply hf
  by_contra hc
  apply hi
  refine ⟨⟨i.val - r, by omega⟩, by simp, Fin.ext ?_⟩
  simp only [wI]; omega

theorem mulVec_of_row {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (i i' : Fin n) (c : ℂ)
    (h : ∀ j, A i j = if j = i' then c else 0) : (A *ᵥ v) i = c * v i' := by
  simp [Matrix.mulVec, dotProduct, h]

theorem H_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  rw [mulVec_of_row _ _ _ (esI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem H_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  rw [mulVec_of_row _ _ _ (eI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  simp only [Hpk, eI, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem H_wI (v : Fin (2 * r + k + 1) → ℂ) (b : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r b) = (if b = Fin.last k then -1 else 1) * v (wI k r b) := by
  rw [mulVec_of_row _ _ _ (wI k r b) _]
  intro j
  have := b.2; have := j.2
  have e : (wI k r b).val = r + b.val := rfl
  simp only [Hpk, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | omega

theorem herm_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  rw [← H_eI v a]
  simp [herm, bvec, dotProduct, Pi.single_apply]

theorem herm_mid (v z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) v z = herm (Hb k) (mid k r v) (mid k r z) := by
  unfold herm dotProduct
  rw [sum_mid]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [H_wI]
    simp [Hb, mid, Matrix.mulVec_diagonal]
  · intro i hi
    simp [hz i hi]

theorem mid_uEmb (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    mid k r (uEmb k r u *ᵥ v) = mid k r v := by
  funext b
  simp only [mid]
  rw [mulVec_of_row _ _ _ (wI k r b) 1, one_mul]
  intro j
  have := b.2; have := j.2
  simp only [uEmb, wI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem mid_mEmb (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    mid k r (mEmb k r m *ᵥ v) = m *ᵥ mid k r v := by
  funext b
  simp only [mid, Matrix.mulVec, dotProduct]
  have := b.2
  rw [sum_mid]
  · refine Finset.sum_congr rfl fun j _ => ?_
    have := j.2
    congr 1
    have e : (wI k r b).val = r + b.val := rfl
    have e' : (wI k r j).val = r + j.val := rfl
    unfold mEmb
    rw [dite_eq_left (by omega)]
    congr 1 <;> exact Fin.ext (by simp only []; omega)
  · intro i hi
    simp only [mEmb, wI, Fin.ext_iff]
    split_ifs <;> first | omega | simp

theorem top_mEmb (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (mEmb k r m *ᵥ v) (esI k r a) = v (esI k r a) := by
  rw [mulVec_of_row _ _ _ (esI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  simp only [mEmb, esI, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem top_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    (pEl k r B S *ᵥ v) (esI k r a) = v (esI k r a) := by
  rw [mulVec_of_row _ _ _ (esI k r a) 1, one_mul]
  intro j
  have := a.2; have := j.2
  have e : (esI k r a).val = 2 * r + k - a.val := rfl
  simp only [pEl, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem top_uEmb (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) (hv : ∀ a, v (esI k r a) = 0) (a : Fin r) :
    (uEmb k r u *ᵥ v) (esI k r a) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := a.2
  rcases idx_cases i with ⟨b, rfl⟩ | ⟨b, rfl⟩ | ⟨b, rfl⟩
  · have := b.2
    simp only [uEmb, esI, eI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · have := b.2
    simp only [uEmb, esI, wI, Fin.ext_iff]
    split_ifs <;> first | omega | simp
  · simp [hv]

theorem top_uEmb_iff (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (v : Fin (2 * r + k + 1) → ℂ) :
    (∀ a, (uEmb k r u *ᵥ v) (esI k r a) = 0) ↔ ∀ a, v (esI k r a) = 0 := by
  refine ⟨fun h a => ?_, top_uEmb u v⟩
  have h1 := top_uEmb u⁻¹ _ h a
  obtain ⟨hm, h0, -⟩ := GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties k r
  rwa [Matrix.mulVec_mulVec, ← hm _ _ (Matrix.isUnit_nonsing_inv_det u hu) hu, Matrix.nonsing_inv_mul u hu, h0,
    Matrix.one_mulVec] at h1

theorem mid_pEl (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ)
    (hv : ∀ a, v (esI k r a) = 0) : mid k r (pEl k r B S *ᵥ v) = mid k r v := by
  funext b
  simp only [mid, Matrix.mulVec, dotProduct]
  have := b.2
  rw [Finset.sum_eq_single (wI k r b)]
  · simp [pEl]
  · intro i _ hi
    rcases idx_cases i with ⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩
    · have := c.2
      have e : (wI k r b).val = r + b.val := rfl
      have e' : (eI k r c).val = c.val := rfl
      simp only [pEl, Fin.ext_iff]
      split_ifs <;> first | omega | simp
    · have := c.2
      have e : (wI k r b).val = r + b.val := rfl
      have e' : (wI k r c).val = r + c.val := rfl
      simp only [pEl, Fin.ext_iff, ne_eq] at hi ⊢
      split_ifs <;> first | omega | simp
    · simp [hv]
  · simp

theorem mid_pEl_esI (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (a : Fin r) :
    mid k r (pEl k r B S *ᵥ bvec (esI k r a)) = B a := by
  funext b
  have := a.2; have := b.2
  simp only [mid, bvec, Matrix.mulVec_single_one, Matrix.col_apply, pEl, wI, esI, Fin.ext_iff]
  rw [if_neg (by omega), dif_neg (by omega), dite_eq_left (by omega)]
  congr 1 <;> exact Fin.ext (by simp only []; omega)

theorem gramProj_mul {n j : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (C : Matrix (Fin j) (Fin j) ℂ)
    (w : Fin j → Fin n → ℂ) : gramProj P (fun a => ∑ b, C b a • w b) = ‖C.det‖ * gramProj P w := by
  unfold gramProj
  have h : (Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (∑ b, C b a • w b))) =
      Cᴴ * (Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (w a))) * C := by
    ext a a'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.gram_apply, WithLp.toLp_sum, WithLp.toLp_smul, map_sum, map_smul, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Complex.star_def]
    ring
  rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_mul, norm_star,
    show ∀ x y : ℝ, x * y * x = x ^ 2 * y from fun x y => by ring, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

theorem inner_mid (v u : EuclideanSpace ℂ (Fin (2 * r + k + 1))) (hu : inWb k r u.ofLp) :
    ⟪v, u⟫_ℂ = ⟪(WithLp.toLp 2 (mid k r v.ofLp) : EuclideanSpace ℂ (Fin (k + 1))), WithLp.toLp 2 (mid k r u.ofLp)⟫_ℂ := by
  simp only [PiLp.inner_apply]
  rw [sum_mid]
  · rfl
  · intro i hi
    simp [hu i hi]

theorem exists_mid (p : Fin (k + 1) → ℂ) : ∃ u, inWb k r u ∧ mid k r u = p := by
  refine ⟨fun i => if h : r ≤ i.val ∧ i.val ≤ r + k then p ⟨i.val - r, by omega⟩ else 0, ?_, ?_⟩
  · intro i hi
    exact dif_neg (by omega)
  · funext b
    have := b.2
    have e : (wI k r b).val = r + b.val := rfl
    unfold mid
    simp only []
    rw [dite_eq_left (by omega)]
    congr 1
    exact Fin.ext (by simp only []; omega)

theorem gramProj_mid {j : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1))))
    (P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))))
    (hP : ∀ v, v ∈ P ↔ inWb k r v.ofLp ∧ WithLp.toLp 2 (mid k r v.ofLp) ∈ P₀) (v : Fin j → Fin (2 * r + k + 1) → ℂ) :
    gramProj P v = gramProj P₀ fun a => mid k r (v a) := by
  have key : ∀ y : EuclideanSpace ℂ (Fin (2 * r + k + 1)),
      P₀.starProjection (WithLp.toLp 2 (mid k r y.ofLp)) = WithLp.toLp 2 (mid k r (P.starProjection y).ofLp) := by
    intro y
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ((hP _).1 (P.starProjection_apply_mem y)).2 ?_
    intro w hw
    obtain ⟨u, hu, hu'⟩ := exists_mid (r := r) w.ofLp
    have hmem : WithLp.toLp 2 u ∈ P := (hP _).2 ⟨hu, by simpa [hu'] using hw⟩
    have h1 := P.starProjection_inner_eq_zero y _ hmem
    rw [inner_mid _ _ hu] at h1
    simp only [hu'] at h1
    exact h1
  unfold gramProj
  congr 3
  ext a b
  simp only [Matrix.gram_apply]
  rw [inner_mid _ _ ((hP _).1 (P.starProjection_apply_mem _)).1, ← key, ← key]

def P0 (k : ℕ) (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : Fin (k + 1) → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))) :=
  (Submodule.span ℂ {WithLp.toLp 2 (Pi.single (Fin.last k) 1), WithLp.toLp 2 (mᴴ *ᵥ ((Hb k)ᴴ *ᵥ ζ))})ᗮ

theorem mem_lastZeroOrthImageSubspace_iff (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : Fin (k + 1) → ℂ) (p : Fin (k + 1) → ℂ) :
    WithLp.toLp 2 p ∈ P0 k m ζ ↔ p (Fin.last k) = 0 ∧ herm (Hb k) (m *ᵥ p) ζ = 0 := by
  have e1 : ⟪(WithLp.toLp 2 (Pi.single (Fin.last k) 1) : EuclideanSpace ℂ (Fin (k + 1))), WithLp.toLp 2 p⟫_ℂ =
      p (Fin.last k) := by
    simp [PiLp.inner_apply]
  have e2 : ⟪(WithLp.toLp 2 (mᴴ *ᵥ ((Hb k)ᴴ *ᵥ ζ)) : EuclideanSpace ℂ (Fin (k + 1))), WithLp.toLp 2 p⟫_ℂ =
      herm (Hb k) (m *ᵥ p) ζ := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, herm, Matrix.star_mulVec, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.dotProduct_mulVec,
      Matrix.dotProduct_mulVec]
  unfold P0
  rw [Submodule.span_insert, ← Submodule.inf_orthogonal, Submodule.mem_inf,
    Submodule.mem_orthogonal_singleton_iff_inner_right, Submodule.mem_orthogonal_singleton_iff_inner_right, e1, e2]

theorem finrank_lastZeroOrthImageSubspace_ge (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : Fin (k + 1) → ℂ) :
    k - 1 ≤ Module.finrank ℂ (P0 k m ζ) := by
  classical
  unfold P0
  set a : EuclideanSpace ℂ (Fin (k + 1)) := WithLp.toLp 2 (Pi.single (Fin.last k) 1)
  set b : EuclideanSpace ℂ (Fin (k + 1)) := WithLp.toLp 2 (mᴴ *ᵥ ((Hb k)ᴴ *ᵥ ζ))
  have h1 := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℂ ({a, b} : Set _))
  have h2 : Module.finrank ℂ (Submodule.span ℂ ({a, b} : Set _)) ≤ 2 := by
    have := finrank_span_finset_le_card (R := ℂ) ({a, b} : Finset _)
    have e : ((({a, b} : Finset _)) : Set (EuclideanSpace ℂ (Fin (k + 1)))) = {a, b} := by simp
    rw [← e]
    exact this.trans Finset.card_le_two
  simp only [finrank_euclideanSpace, Fintype.card_fin] at h1
  omega

theorem mem_Ppos_iff (z z' : Fin (2 * r + k + 1) → ℂ) (hz' : inWb k r z') (g : Mat k r)
    (hH : ∀ w, w ∈ Hcom k r z z' g ⊔ Xsp k r ↔ ∀ a : Fin (r + 1), herm (Hpk k r) w (fvec k r z' a) = 0)
    (B : Fin r → Fin (k + 1) → ℂ) (S u t : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) (ht : IsUnit t.det)
    (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : EuclideanSpace ℂ (Fin (2 * r + k + 1))) :
    v ∈ Ppos k r z z' g (pEl k r B S * uEmb k r u * (uEmb k r t * mEmb k r m)) ↔
      inWb k r v.ofLp ∧ WithLp.toLp 2 (mid k r v.ofLp) ∈ P0 k m (mid k r z') := by
  set x := pEl k r B S * uEmb k r u * (uEmb k r t * mEmb k r m) with hx
  have hxv : x *ᵥ v.ofLp = pEl k r B S *ᵥ (uEmb k r u *ᵥ (uEmb k r t *ᵥ (mEmb k r m *ᵥ v.ofLp))) := by
    simp only [hx, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have htop : (∀ a, (x *ᵥ v.ofLp) (esI k r a) = 0) ↔ ∀ a, v.ofLp (esI k r a) = 0 := by
    simp only [hxv, top_pEl]
    rw [top_uEmb_iff u hu, top_uEmb_iff t ht]
    simp only [top_mEmb]
  have hmid : (∀ a, v.ofLp (esI k r a) = 0) → mid k r (x *ᵥ v.ofLp) = m *ᵥ mid k r v.ofLp := by
    intro h
    rw [hxv, mid_pEl, mid_uEmb, mid_uEmb, mid_mEmb]
    exact top_uEmb _ _ (top_uEmb _ _ (by simpa only [top_mEmb] using h))
  have hf : (∀ a : Fin (r + 1), herm (Hpk k r) (x *ᵥ v.ofLp) (fvec k r z' a) = 0) ↔
      (∀ a, (x *ᵥ v.ofLp) (esI k r a) = 0) ∧ herm (Hpk k r) (x *ᵥ v.ofLp) z' = 0 := by
    constructor
    · intro h
      refine ⟨fun a => ?_, ?_⟩
      · have := h a.castSucc
        rw [← herm_eI (x *ᵥ v.ofLp) a]
        simpa [fvec] using this
      · simpa [fvec] using h (Fin.last r)
    · rintro ⟨h1, h2⟩ a
      unfold fvec
      split_ifs
      · rw [herm_eI]; exact h1 _
      · exact h2
  have hm : v ∈ Ppos k r z z' g x ↔ Hpk k r *ᵥ v.ofLp = v.ofLp ∧ x *ᵥ v.ofLp ∈ Hcom k r z z' g ⊔ Xsp k r := by
    simp only [Ppos, Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
    rfl
  rw [hm, hH, hf, htop, mem_lastZeroOrthImageSubspace_iff, herm_mid _ _ hz']
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hmid h2] at h3
    refine ⟨?_, ?_, h3⟩
    · intro i hi
      rcases idx_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, rfl⟩
      · rw [← h1, H_eI]; exact h2 a
      · have := b.2
        have e : (wI k r b).val = r + b.val := rfl
        omega
      · exact h2 a
    · have := congrFun h1 (wI k r (Fin.last k))
      rw [H_wI, if_pos rfl] at this
      show v.ofLp (wI k r (Fin.last k)) = 0
      linear_combination (-1 / 2 : ℂ) * this
  · rintro ⟨h1, h2, h3⟩
    have he : ∀ a, v.ofLp (eI k r a) = 0 := fun a => h1 _ (Or.inl a.2)
    have hs : ∀ a, v.ofLp (esI k r a) = 0 := fun a => h1 _ (Or.inr (by have := a.2; simp only [esI]; omega))
    refine ⟨?_, hs, by rw [hmid hs]; exact h3⟩
    funext i
    rcases idx_cases i with ⟨a, rfl⟩ | ⟨b, rfl⟩ | ⟨a, rfl⟩
    · rw [H_eI, he, hs]
    · rw [H_wI]
      split_ifs with hb
      · have : v.ofLp (wI k r b) = 0 := by rw [hb]; exact h2
        rw [this, mul_zero]
      · rw [one_mul]
    · rw [H_esI, he, hs]

theorem eq_sum_of_mem_XstJ {j : ℕ} (hj : j ≤ r) (y : Fin (2 * r + k + 1) → ℂ) (hy : y ∈ XstJ k r j) :
    y = ∑ b : Fin j, y (esI k r (Fin.castLE hj b)) • bvec (esI k r (Fin.castLE hj b)) := by
  unfold XstJ at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨a, ha⟩, rfl⟩ := hy
    rw [Finset.sum_eq_single (⟨a.val, ha⟩ : Fin j)]
    · have : Fin.castLE hj ⟨a.val, ha⟩ = a := rfl
      simp [this, bvec]
    · intro b _ hb
      have : esI k r (Fin.castLE hj b) ≠ esI k r a := by
        intro h
        have h1 := congrArg Fin.val h
        have := b.2
        simp only [esI, Fin.val_castLE] at h1
        exact hb (Fin.ext (by simp only []; omega))
      simp [bvec, Pi.single_eq_of_ne this]
    · simp
  | zero => simp
  | add y y' _ _ h h' =>
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    rw [← h, ← h']
  | smul c y _ h =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum]
    rw [← h]

theorem mid_sum {j : ℕ} (c : Fin j → ℂ) (v : Fin j → Fin (2 * r + k + 1) → ℂ) :
    mid k r (∑ b, c b • v b) = ∑ b, c b • mid k r (v b) := by
  funext i
  simp [mid, Finset.sum_apply]

theorem Dj_eq {j : ℕ} (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) :
    Dj k r hj z z' g = ‖(Matrix.of fun b a : Fin j =>
      (g *ᵥ bvec (eI k r (Fin.castLE hj a))) (esI k r (Fin.castLE hj b))).det‖ := by
  unfold Dj Dmin
  congr 2
  ext b a
  have ha : a.val < r := lt_of_lt_of_le a.2 hj
  have hb : b.val < r := lt_of_lt_of_le b.2 hj
  simp only [Matrix.submatrix_apply, Formalism.QuantumDeterminants.Zhat, fvec, Fin.val_castLE, Matrix.of_apply]
  rw [dite_eq_left ha, dite_eq_left hb, herm_eI]
  rfl

theorem Yj_eq_gramProj : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), k - 1 ≤ Module.finrank ℂ P₀ ∧ ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yj k r hj z z' g₀ (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := by
  intro k r j hj z z' g β c hz hz' hT hN m hm
  obtain ⟨-, -, -, hD, hD', -, hH⟩ := GlobalTheory.T.normalFormFlagZero_middle_inverse_minor_orthogonal k r j hj z z' g β c hz hz' hT hN
  obtain ⟨-, -, hU, hup⟩ := GlobalTheory.T.isotropicLeviEmbedding_homomorphism_properties k r
  obtain ⟨hp, hsk, -, -, hM⟩ := GlobalTheory.T.isotropicStabilizerRadical_structure k r
  refine ⟨P0 k m (mid k r z'), finrank_lastZeroOrthImageSubspace_ge _ _, fun q a ha => ?_⟩
  have hu : IsUnit (upperOff β q.2).det := by
    unfold upperOff
    rw [(hup _).1]; exact isUnit_one
  have ht : IsUnit (Matrix.diagonal fun b => (a b : ℂ)).det := by
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => by exact_mod_cast (ha b).ne'
  unfold Yj sEl pSec pOf
  rw [gramProj_mid _ _ (mem_Ppos_iff z z' hz' g hH _ _ _ _ hu ht m), div_eq_iff hD.ne', ← hD', Dj_eq, mul_comm (gramProj _ _)]
  set C : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun b a : Fin j =>
      (g⁻¹ *ᵥ bvec (eI k r (Fin.castLE hj a))) (esI k r (Fin.castLE hj b)) with hC
  have hn : ‖C.det‖ = ‖(-C).det‖ := by
    rw [Matrix.det_neg, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [hn, ← gramProj_mul]
  congr 1
  funext b
  rw [eq_sum_of_mem_XstJ hj _ (hN.2.2.2.2.2.1 (Fin.castLE hj b) b.2).1, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]
  rw [mid_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev, (hM m hm).2, (hU _ hu).2.1, (hU _ ht).2.1,
    ((hp _ _).2.2.2 (hsk _ _)).2]
  simp only [← Matrix.mulVec_mulVec]
  rw [mid_mEmb, mid_uEmb, mid_uEmb, mid_pEl_esI]
  simp only [Pi.neg_apply, Matrix.neg_apply, hC, Matrix.of_apply, Matrix.mulVec_neg, smul_neg, neg_smul]
  rw [dite_eq_left (show (Fin.castLE hj d).val < j from d.2)]

end GlobalTheory.Amp.NormalGram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGramEqGramDetProjectionNormalFormStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagGram_eq_gramDetProjection_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), k - 1 ≤ Module.finrank ℂ P₀ ∧ ∀ (q : PSec k r j × (UToff β → ℂ)) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yj k r hj z z' g₀ (sEl k r j β q * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := by
  first | exact @GlobalTheory.Amp.NormalGram.Yj_eq_gramProj | exact GlobalTheory.Amp.NormalGram.Yj_eq_gramProj | (intros; apply GlobalTheory.Amp.NormalGram.Yj_eq_gramProj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoMulPiPowLeFourPow
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem two_mul_pi_pow_le_four_pow (k : ℕ) (hk : 3 ≤ k) : 2 * Real.pi ^ k ≤ (4 : ℝ) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h0 := Real.pi_pos.le
  have h1 : Real.pi ^ 3 ≤ (3.15 : ℝ) ^ 3 := pow_le_pow_left₀ h0 Real.pi_lt_d2.le 3
  have h2 : Real.pi ^ m ≤ (4 : ℝ) ^ m := pow_le_pow_left₀ h0 Real.pi_le_four m
  have h3 : 2 * Real.pi ^ 3 ≤ (4 : ℝ) ^ 3 := by norm_num at h1 ⊢; linarith
  rw [pow_add, pow_add, ← mul_assoc]
  exact mul_le_mul h3 h2 (by positivity) (by positivity)

theorem box_volume_arith : ∀ (r j n₁ n₂ n₃ : ℕ) (M : ℝ), 1 ≤ j → j ≤ r → 2 * n₁ ≤ r * (r - 1) → 2 * n₂ ≤ r * (r - 1) → n₃ ≤ r → 1 ≤ M → (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2)) ≤ (4 * r : ℝ) ^ (4 * r ^ 2) * M ^ (8 * r ^ 2) := by
  intro r j n₁ n₂ n₃ M hj hjr h1 h2 h3 hM
  have hr : 1 ≤ r := hj.trans hjr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpi := Real.pi_pos.le
  have hpi4 := Real.pi_le_four
  have hM0 : 0 ≤ M := by linarith
  have hA : (1 : ℝ) ≤ 4 * r := by linarith
  have hrr : r * (r - 1) + r = r ^ 2 := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
    simp only [Nat.add_sub_cancel_left]; ring
  have hjj : j ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left hjr 2
  have hr2 : r ≤ r ^ 2 := by nlinarith
  have hj2 : 1 ≤ j ^ 2 := by nlinarith
  have e : (Real.pi * M ^ 2) ^ n₁ * (Real.pi * (2 * r * M ^ 2) ^ 2) ^ n₂ * (2 * (2 * r * M ^ 2)) ^ n₃ * (2 * (Real.pi * M ^ 2) ^ (2 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2))
      = (Real.pi ^ n₁ * (Real.pi * (2 * r) ^ 2) ^ n₂ * (4 * r) ^ n₃ * (2 * Real.pi ^ (2 * j + j ^ 2))) *
        M ^ (2 * n₁ + 4 * n₂ + 2 * n₃ + 4 * j + 2 * j ^ 2) := by
    have a1 : Real.pi * (2 * r * M ^ 2) ^ 2 = (Real.pi * (2 * r) ^ 2) * M ^ 4 := by ring
    have a2 : 2 * (2 * r * M ^ 2) = (4 * (r : ℝ)) * M ^ 2 := by ring
    rw [a1, a2, mul_pow Real.pi, mul_pow _ (M ^ 4), mul_pow _ (M ^ 2), mul_pow Real.pi (M ^ 2)]
    generalize Real.pi * (2 * (r : ℝ)) ^ 2 = B
    generalize 4 * (r : ℝ) = C
    ring
  rw [e]
  have b1 : Real.pi ^ n₁ ≤ (4 * r : ℝ) ^ n₁ := pow_le_pow_left₀ hpi (by linarith) _
  have b2 : (Real.pi * (2 * r) ^ 2) ^ n₂ ≤ (4 * r : ℝ) ^ (2 * n₂) := by
    rw [pow_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : (0 : ℝ) ≤ (2 * r) ^ 2 := by positivity
    nlinarith
  have b4 : 2 * Real.pi ^ (2 * j + j ^ 2) ≤ (4 * r : ℝ) ^ (2 * j + j ^ 2) :=
    (two_mul_pi_pow_le_four_pow _ (by omega)).trans
      (pow_le_pow_left₀ (by norm_num) (by linarith) _)
  refine mul_le_mul ?_ (pow_le_pow_right₀ hM (by omega)) (by positivity) (by positivity)
  calc _ ≤ (4 * r : ℝ) ^ n₁ * (4 * r : ℝ) ^ (2 * n₂) * (4 * r) ^ n₃ * (4 * r : ℝ) ^ (2 * j + j ^ 2) := by
        gcongr
    _ = (4 * r : ℝ) ^ (n₁ + 2 * n₂ + n₃ + (2 * j + j ^ 2)) := by
        rw [← pow_add, ← pow_add, ← pow_add]
    _ ≤ _ := pow_le_pow_right₀ hA (by omega)

end GlobalTheory.Amp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentGramNullAndFibreVolumeNormalForm
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreNormal

theorem vol_discs (ι : Type) [Fintype ι] {M : ℝ} (hM : 0 ≤ M) :
    volume {x : ι → ℂ | ∀ p, ‖x p‖ ≤ M} = ENNReal.ofReal ((Real.pi * M ^ 2) ^ Fintype.card ι) := by
  have h : {x : ι → ℂ | ∀ p, ‖x p‖ ≤ M} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) M := by
    ext x; simp
  rw [h, volume_pi_pi, Finset.prod_const, Finset.card_univ, Complex.volume_closedBall,
    ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hM, mul_comm]
  congr 2
  exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm

theorem vol_ints (ι : Type) [Fintype ι] {M : ℝ} (hM : 0 ≤ M) :
    volume {x : ι → ℝ | ∀ p, |x p| ≤ M} = ENNReal.ofReal ((2 * M) ^ Fintype.card ι) := by
  have h : {x : ι → ℝ | ∀ p, |x p| ≤ M} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℝ) M := by
    ext x; simp
  rw [h, volume_pi_pi, Finset.prod_const, Finset.card_univ, Real.volume_closedBall,
    ENNReal.ofReal_pow (by positivity)]

def lowEquiv {r j : ℕ} (hj : j ≤ r) : Fin j ≃ {a : Fin r // a.val < j} where
  toFun b := ⟨Fin.castLE hj b, b.2⟩
  invFun a := ⟨a.1.val, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem vol_reindex {k r j : ℕ} (hj : j ≤ r) (T : Set (Fin j → Fin (k + 1) → ℂ)) :
    volume {B : {a : Fin r // a.val < j} → Fin (k + 1) → ℂ | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈ T} =
      volume T := by
  have h := (volume_measurePreserving_piCongrLeft (fun _ : {a : Fin r // a.val < j} => Fin (k + 1) → ℂ)
    (lowEquiv hj)).symm
  rw [← h.measure_preimage_equiv T]
  rfl

theorem card_UT (r : ℕ) : 2 * Fintype.card (UT r) ≤ r * (r - 1) := by
  have h : Fintype.card (UT r) = r.choose 2 := by
    rw [Fintype.card_subtype, ← Finset.univ_product_univ, Finset.card_product_filter_lt]
    simp
  rw [h, Nat.choose_two_right]
  exact Nat.mul_div_le _ _

theorem vol_box {k r j : ℕ} (β : Fin r → ℕ) (A : Set ({a : Fin r // a.val < j} → Fin (k + 1) → ℂ))
    (B : Set ({p : UT r // p.1.1.val < j} → ℂ)) (C : Set ({a : Fin r // a.val < j} → ℝ)) (D : Set (UToff β → ℂ)) :
    (volume : Measure (PSec k r j × (UToff β → ℂ))) ((A ×ˢ B ×ˢ C) ×ˢ D) =
      volume A * (volume B * volume C) * volume D := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod,
    Measure.volume_eq_prod, Measure.prod_prod]

theorem sEl_mem {k r j : ℕ} (β : Fin r → ℕ) (q : PSec k r j × (UToff β → ℂ)) : sEl k r j β q ∈ Nset k r :=
  isClosedSub_Nset.2.2.2.1 _ ((((Rad.radical k r).1 _ _).2.2.2 (Rad.skewM_skew _ _)).1) _ (UEmb.upper_mem _)

theorem ae_mem_range {k r j : ℕ} (β : Fin r → ℕ) {S : Set (Mat k r)} (hS : IsClosed S)
    (h : Set.range (rEl k r j β) ⊆ S) : ∀ᵐ ρ ∂(lebR0 k r j β), Matrix.of ρ ∈ S := by
  unfold lebR0
  have hS' : IsClosed {x : Mt k r | Matrix.of x ∈ S} := hS
  have hu : Measurable fun x : UTin β → ℂ =>
      (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
    have hU : Continuous (upperIn β) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      simp only [upperIn, upper]
      split_ifs <;> first | exact continuous_apply _ | exact continuous_const
    have heq : ∀ x, (upperIn β x)⁻¹ = (upperIn β x).adjugate := fun x => by
      rw [Matrix.inv_def, upperIn, UEmb.det_upper]; simp
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => Continuous.measurable ?_
    simp only [Matrix.of_symm_apply, uEmb, heq]
    split_ifs
    · exact hU.matrix_elem _ _
    · exact (hU.matrix_adjugate.matrix_elem _ _).star
    · exact continuous_const
    · exact continuous_const
  have hp : Measurable fun q : PTop k r j => (Matrix.of.symm (pTop k r j q) : Mt k r) := by
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => Continuous.measurable ?_
    simp only [Matrix.of_symm_apply, pTop, pOf, pEl, skewM, herm, bvec, dotProduct, Matrix.mulVec]
    split_ifs <;> fun_prop
  have hm : AEMeasurable (fun q => (Matrix.of.symm (rEl k r j β q) : Mt k r))
      (volume : Measure ((UTin β → ℂ) × PTop k r j)) := by
    unfold rEl
    apply Measurable.aemeasurable
    refine measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => ?_
    simp only [Matrix.of_symm_apply, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_iff.1 (measurable_pi_iff.1 hu a)) i).comp measurable_fst).mul
        (((measurable_pi_iff.1 (measurable_pi_iff.1 hp i)) b).comp measurable_snd)
  rw [ae_map_iff hm hS'.measurableSet]
  exact Filter.Eventually.of_forall fun q => h ⟨q, rfl⟩

theorem N_sub_S {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, (isClosedSub_UWset z).2.2.1, n, hn, (Matrix.one_mul n).symm⟩

theorem Sg2_N {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) {n x : Mat k r}
    (hn : n ∈ Nset k r) (hx : x ∈ GG k r) : Sg2 k r z (n * x) = Sg2 k r z x := by
  have := (TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.1 x hx n (N_sub_S z hn) 1
    ⟨isClosedSub_GG.2.2.1, (Matrix.unitaryGroup _ ℂ).one_mem⟩
  rwa [Matrix.mul_one] at this

theorem fibre_volume : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → 1 ≤ j → j + 2 ≤ k → ∀ De : ℝ, DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yj k r hj z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR0 k r j β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
  intro k r j hj z z' g₀ β c hz hz' hT hN h1j hjk De hDe m hm a ha
  have hT' : 0 < Tz k r z' := by rw [(GlobalTheory.Amp.NfMid.normal0_middle k r j hj z z' g₀ β c hz hz' hT hN).1]; exact hT
  obtain ⟨hR, hRc⟩ := GlobalTheory.T.commonStabilizerSet_eq_range_normalForm k r j hj z z' g₀ β c hz hz' hT hN
  obtain ⟨P₀, hP₀, hY⟩ := GlobalTheory.T.flagGram_eq_gramDetProjection_normalForm k r j hj z z' g₀ β c hz hz' hT hN m hm
  obtain ⟨hnull, hvol⟩ := GlobalTheory.Amp.GramVol.vol_gram k j h1j hjk m hm P₀ hP₀
  obtain ⟨hYm, hEm⟩ := GlobalTheory.T.measurable_flagGramNumberNormalized_indicator k r j hj z z' g₀ hz hz' hT hT' hN.1
  have hsplit := GlobalTheory.T.lintegral_flagUnipotent_eq_stabilizer_times_section k r j β hN.2.2.2.1 hN.2.2.2.2.1
  have hB := fun R₀ hR₀ q => GlobalTheory.T.siegel_height_bound_section k r j hj z z' g₀ β c hz hz' hT hN De R₀ hDe hR₀ m hm q a ha
  have hY' := fun q => hY q a ha
  have hmul := (isClosedSub_GG (k := k) (r := r)).2.2.2.1
  have ht : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m ∈ GG k r := by
    refine hmul _ (UEmb.uEmb_mem _ ?_) _ (Rad.mEmb_mem m hm)
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    exact fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'
  generalize uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m = t at *
  have hae : ∀ᵐ ρ ∂(lebR0 k r j β), Matrix.of ρ ∈ Rset k r g₀ := ae_mem_range β hRc.2.1 hR.ge
  have hst : ∀ q : PSec k r j × (UToff β → ℂ), sEl k r j β q * t ∈ GG k r := fun q => hmul _ (sEl_mem β q).1 _ ht
  have hassoc : ∀ (q : PSec k r j × (UToff β → ℂ)) (ρ : Mt k r),
      (Matrix.of (rmulM t (rmulM (sEl k r j β q) ρ)) : Mat k r) = Matrix.of ρ * (sEl k r j β q * t) :=
    fun q ρ => by rw [of_rmulM, of_rmulM, Matrix.mul_assoc]
  have hYρ : ∀ (q : PSec k r j × (UToff β → ℂ)) (ρ : Mt k r), Matrix.of ρ ∈ Rset k r g₀ →
      Yj k r hj z z' g₀ (Matrix.of ρ * (sEl k r j β q * t)) =
        gramProj P₀ fun b : Fin j => m⁻¹ *ᵥ q.1.1 ⟨Fin.castLE hj b, b.2⟩ := fun q ρ hρ => by
    rw [(GlobalTheory.Amp.YjInv.yj_invariant k r j hj z z' g₀ hz hz' hN.1 _ (hst q)).2.2 _ hρ, hY' q]
  have htm : Measurable (rmulM t : Mt k r → Mt k r) := (continuous_rmulM t).measurable
  constructor
  · set S : Set (Mt k r) := {n | Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
      (fun x => Yj k r hj z z' g₀ (Matrix.of x)) (rmulM t n) = 0} with hS
    have hSm : MeasurableSet S := (hYm.comp htm) (measurableSet_singleton 0)
    refine measure_mono_null (t := S) (fun n hn => ?_) ?_
    · exact Set.indicator_apply_eq_zero.2 fun _ => hn
    rw [← lintegral_indicator_one hSm, hsplit _ (measurable_one.indicator hSm)]
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    have h0 : (volume : Measure (PSec k r j × (UToff β → ℂ)))
        (({B | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈
          {B : Fin j → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0}} ×ˢ Set.univ ×ˢ Set.univ) ×ˢ Set.univ) = 0 := by
      rw [vol_box, vol_reindex hj, hnull, zero_mul, zero_mul]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq
    refine lintegral_eq_zero_of_ae_eq_zero ?_
    filter_upwards [hae] with ρ hρ
    refine Set.indicator_of_notMem (fun hmem => hq ⟨⟨?_, trivial, trivial⟩, trivial⟩) _
    have hG : rmulM t (rmulM (sEl k r j β q) ρ) ∈ {x : Mt k r | Matrix.of x ∈ GG k r} := by
      rw [Set.mem_ofPred_eq, hassoc]; exact hmul _ hρ.1.1 _ (hst q)
    have h2 : Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
      (fun x => Yj k r hj z z' g₀ (Matrix.of x)) (rmulM t (rmulM (sEl k r j β q) ρ)) = 0 := hmem
    rw [Set.indicator_of_mem hG, hassoc, hYρ q ρ hρ] at h2
    exact h2
  · intro φ hφ R₀ y hR₀ hy
    have hM : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR₀) hDe.1
    have hB' := hB R₀ hR₀
    unfold fibVol0
    generalize R₀ ^ (2 * r) * De = M at *
    have hM0 : 0 ≤ M := zero_le_one.trans hM
    rw [hsplit (fun n => φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM t n)) (hφ.1.mul ((measurable_one.indicator (hEm R₀ y)).comp htm))]
    set Box : Set (PSec k r j × (UToff β → ℂ)) :=
      ({B | (fun b : Fin j => B ⟨Fin.castLE hj b, b.2⟩) ∈
          {B : Fin j → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ M) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y}} ×ˢ
        {x | ∀ p, ‖x p‖ ≤ 2 * r * M ^ 2} ×ˢ {x | ∀ p, |x p| ≤ 2 * r * M ^ 2}) ×ˢ {x | ∀ p, ‖x p‖ ≤ M} with hBox
    refine (lintegral_mono (g := Box.indicator 1) fun q => ?_).trans ((lintegral_indicator_one_le Box).trans ?_)
    · by_cases hq : q ∈ Box
      · rw [Set.indicator_of_mem hq]
        refine le_trans (lintegral_mono fun ρ => ?_) (hφ.2 (Matrix.of.symm (sEl k r j β q)) (sEl_mem β q))
        exact mul_le_of_le_one_right' (Set.indicator_le_self' (fun _ _ => zero_le_one) _)
      · rw [Set.indicator_of_notMem hq]
        refine (lintegral_eq_zero_of_ae_eq_zero ?_).le
        filter_upwards [hae] with ρ hρ
        refine mul_eq_zero_of_right _ (Set.indicator_of_notMem (fun hmem => hq ?_) _)
        obtain ⟨-, h1, h2, -, h3⟩ := hmem
        rw [hassoc] at h1 h2 h3
        rw [hYρ q ρ hρ] at h3
        rw [Sg2_N hz' hT' hρ.1 (hst q)] at h1
        have he : g₀ * (Matrix.of ρ * (sEl k r j β q * t)) =
            (g₀ * Matrix.of ρ * g₀⁻¹) * (g₀ * (sEl k r j β q * t)) := by
          rw [Matrix.mul_assoc (g₀ * Matrix.of ρ), Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_det_of_mem_GG hN.1),
            Matrix.mul_assoc]
        rw [he, Sg2_N hz hT hρ.2 (hmul _ hN.1 _ (hst q))] at h2
        obtain ⟨b1, b2, b3, b4⟩ := hB' q h1 (((TwoSided.Sg2_invariant_continuousOn_one_le_bounds k r z hz hT).2.2.2 _).2.1.trans h2)
        exact ⟨⟨⟨fun b => b2 _, h3⟩, b3, b4⟩, b1⟩
    · have hr : (0 : ℝ) ≤ 2 * r * M ^ 2 := by positivity
      rw [hBox, vol_box, vol_reindex hj, vol_discs _ hr, vol_ints _ hr, vol_discs _ hM0]
      refine (mul_le_mul_left (mul_le_mul_left (hvol M y hM hy) _) _).trans ?_
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have har := box_volume_arith r j (Fintype.card (UToff β)) (Fintype.card {p : UT r // p.1.1.val < j})
        (Fintype.card {a : Fin r // a.val < j}) M h1j hj
        ((Nat.mul_le_mul_left 2 (Fintype.card_subtype_le _)).trans (card_UT r))
        ((Nat.mul_le_mul_left 2 (Fintype.card_subtype_le _)).trans (card_UT r))
        ((Fintype.card_subtype_le _).trans (Fintype.card_fin r).le) hM
      have hK : (0 : ℝ) ≤ (Real.pi * Real.exp 1 / ((k - 1 - j : ℕ) : ℝ)) ^ (j * (k - 1 - j)) * (2 * y) ^ (2 * (k - 1 - j)) := by
        positivity
      refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_right har hK).trans (le_of_eq ?_)) <;> ring

end GlobalTheory.Amp.FibreNormal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentGramNullAndFibreVolumeNormalFormStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotent_gramNull_and_fibreVolume_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ), inWb k r z → inWb k r z' → 0 < Tz k r z → IsNormal0 k r hj β c z z' g₀ → 1 ≤ j → j + 2 ≤ k → ∀ De : ℝ, DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yj k r hj z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR0 k r j β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset0 k r hj z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
  first | exact @GlobalTheory.Amp.FibreNormal.fibre_volume | exact GlobalTheory.Amp.FibreNormal.fibre_volume | (intros; apply GlobalTheory.Amp.FibreNormal.fibre_volume <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeNormalFormStabiliser
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibreVolume

variable {k r : ℕ}

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1

theorem GG_one : (1 : Mat k r) ∈ GG k r := (uHGroup _ _ hpk_unit).1

theorem GG_mul {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r :=
  (uHGroup _ _ hpk_unit).2.1 a ha b hb

theorem GG_unit {a : Mat k r} (ha : a ∈ GG k r) : IsUnit a.det := ((uHGroup _ _ hpk_unit).2.2 a ha).1

theorem GG_inv {a : Mat k r} (ha : a ∈ GG k r) : a⁻¹ ∈ GG k r := ((uHGroup _ _ hpk_unit).2.2 a ha).2

theorem N_sub_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨GG_one, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩, n, hn, (one_mul n).symm⟩

theorem continuous_two (a b : Mat k r) : Continuous (fun x : Mt k r => (a * Matrix.of x * b : Mat k r)) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem measurable_two (a b : Mat k r) :
    Measurable (fun x : Mt k r => (Matrix.of.symm (a * Matrix.of x * b) : Mt k r)) :=
  Continuous.measurable (α := Mt k r) (γ := Mt k r) (continuous_two a b)

def twoEquiv (a b : Mat k r) (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := Matrix.of.symm (a * Matrix.of x * b)
  invFun x := Matrix.of.symm (a⁻¹ * Matrix.of x * b⁻¹)
  left_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul,
      Matrix.mul_nonsing_inv_cancel_right _ _ hb]
  right_inv x := by
    simp only [Equiv.apply_symm_apply, Equiv.symm_apply_eq]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul,
      Matrix.nonsing_inv_mul_cancel_right _ _ hb]
  measurable_toFun := measurable_two a b
  measurable_invFun := measurable_two _ _

theorem map_twoEquiv {μ : Measure (Mt k r)} {a b : Mat k r} (ha : IsUnit a.det) (hb : IsUnit b.det)
    (hl : μ.map (lmulM a) = μ) (hr : μ.map (rmulM b) = μ) : μ.map (twoEquiv a b ha hb) = μ := by
  have h1 : Measurable (lmulM a : Mt k r → Mt k r) :=
    Continuous.measurable (α := Mt k r) (γ := Mt k r)
      (continuous_const.matrix_mul (continuous_id (X := Mat k r)))
  have h2 : Measurable (rmulM b : Mt k r → Mt k r) := (continuous_rmulM b).measurable
  have : (twoEquiv a b ha hb : Mt k r → Mt k r) = rmulM b ∘ lmulM a := rfl
  rw [this, ← Measure.map_map h2 h1, hl, hr]

theorem Tz_eq {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} {c : ℂ} (hg : g ∈ GG k r) (hc : ‖c‖ = 1)
    (h : g *ᵥ z' = c • z) : Tz k r z' = Tz k r z := by
  have h1 : herm (Hpk k r) (g *ᵥ z') (g *ᵥ z') = herm (Hpk k r) z' z' := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    unfold herm
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']
  have h2 : herm (Hpk k r) (c • z) (c • z) = herm (Hpk k r) z z := by
    have hcc : star c * c = 1 := by
      rw [Complex.star_def, Complex.conj_mul', hc]; simp
    unfold herm
    rw [star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, hcc, one_smul]
  unfold Tz
  rw [← h1, h, h2]

theorem fibre_volume : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ j → j + 2 ≤ k → DeOK k r z z' γ De → 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yj k r hj z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset0 k r hj z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y / s) := by
  intro k r j hj z z' γ De s μR h1 h2 hDe hs hN g₁ hg₁
  obtain ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, rfl⟩ := hN
  obtain ⟨n₀, hn₀, a, ha, m, hm, κ, hκ, hg⟩ := GlobalTheory.T.iwasawa_decomposition_isotropic_flag k r g₁ hg₁
  have hT' : 0 < Tz k r z' := by rw [Tz_eq hg₀.1 hg₀.2.1 hg₀.2.2.1]; exact hT
  have hDe₀ : DeOK k r z z' g₀ De := by
    refine ⟨hDe.1, fun l hl => ?_⟩
    have := hDe.2 l hl
    rwa [dInv k r z z' hz hz' n₁ (N_sub_S z hn₁) n₂ (N_sub_S z' hn₂)] at this
  have key := GlobalTheory.T.flagUnipotent_gramNull_and_fibreVolume_normalForm k r j hj z z' g₀ β c hz hz' hT hg₀ h1 h2 De hDe₀ m hm a ha
  set A : Mat k r := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hA
  have hg' : g₁ = n₀ * A * κ := by rw [hg, hA]; simp only [Matrix.mul_assoc]
  clear_value A
  have u₀ := GG_unit hn₀.1
  have u₂ := GG_unit hn₂.1
  have uκ := GG_unit hκ.1
  have hAG : A ∈ GG k r := by
    have : A = n₀⁻¹ * g₁ * κ⁻¹ := by
      rw [hg', ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₀, Matrix.one_mul,
        Matrix.mul_nonsing_inv_cancel_right _ _ uκ]
    rw [this]; exact GG_mul (GG_mul (GG_inv hn₀.1) hg₁) (GG_inv hκ.1)
  have hH := GlobalTheory.T.flagUnipotentLebesgueMeasure_isHaarOn k r
  have hU := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT (lebN k r)).2.1 hH).1
  set T := twoEquiv n₂ n₀ u₂ u₀ with hTdef
  have hmap : (lebN k r).map T = lebN k r := map_twoEquiv u₂ u₀ (hH.2.2.2 _ hn₂) (hU.1 _ hn₀)
  have hae : ∀ᵐ n ∂(lebN k r), Matrix.of n ∈ Nset k r := hH.2.2.1
  have hTof : ∀ n, (Matrix.of (T n) : Mat k r) = n₂ * Matrix.of n * n₀ := fun n => rfl
  have hγ : n₁ * g₀ * n₂ ∈ GG k r := GG_mul (GG_mul hn₁.1 hg₀.1) hn₂.1
  have hY : ∀ n : Mt k r, Matrix.of n ∈ Nset k r →
      Yj k r hj z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = Yj k r hj z z' g₀ (Matrix.of (T n) * A) := by
    intro n hn
    rw [(GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' g₀ hz hz' hg₀.1 _ (GG_mul hn.1 hg₁)).2.1 n₁ hn₁ n₂ hn₂, hTof,
      ← (GlobalTheory.T.flagGramNumberNormalized_invariance k r j hj z z' g₀ hz hz' hg₀.1 _
        (GG_mul (GG_mul (GG_mul hn₂.1 hn.1) hn₀.1) hAG)).1 κ hκ, hg']
    simp only [Matrix.mul_assoc]
  refine ⟨?_, fun φ hφ R₀ y hR hy => ?_⟩
  · have h0 := key.1
    rw [← hmap, MeasurableEquiv.map_apply] at h0
    rw [← h0]
    apply measure_congr
    filter_upwards [hae] with n hn
    change (Yj k r hj z z' (n₁ * g₀ * n₂) (Matrix.of n * g₁) = 0) ↔ (Yj k r hj z z' g₀ (Matrix.of (T n) * A) = 0)
    rw [hY n hn]
  · have hE : ∀ n : Mt k r, Matrix.of n ∈ Nset k r →
        (rmulM g₁ n ∈ Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y ↔ rmulM A (T n) ∈ Eset0 k r hj z z' g₀ R₀ y) := by
      intro n hn
      have hx : Matrix.of (T n) * A ∈ GG k r := GG_mul (GG_mul (GG_mul hn₂.1 hn.1) hn₀.1) hAG
      have e1 : Sg2 k r z' (Matrix.of n * g₁) = Sg2 k r z' (Matrix.of (T n) * A) := by
        rw [← (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z' hz' hT').2.1 _ hx n₂⁻¹ (N_sub_S z' ((nSubgroup k r).2.2 _ hn₂)) κ hκ, hTof, hg']
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul]
      have e2 : Sg2 k r z (n₁ * g₀ * n₂ * (Matrix.of n * g₁)) = Sg2 k r z (g₀ * (Matrix.of (T n) * A)) := by
        rw [← (GlobalTheory.T.two_sided_size_function_pos_invariant_continuous k r z hz hT).2.1 _ (GG_mul hg₀.1 hx) n₁ (N_sub_S z hn₁) κ hκ, hTof, hg']
        simp only [Matrix.mul_assoc]
      simp only [Eset0, Set.mem_setOf_eq, of_rmulM]
      rw [e1, e2, hY n hn]
      exact and_congr_left fun _ => iff_of_true (GG_mul hn.1 hg₁) hx
    set ψ : Mt k r → ℝ≥0∞ := fun x =>
      ENNReal.ofReal s * φ (Matrix.of.symm (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁))) with hψ
    have hψT : ∀ n, ψ (T n) = ENNReal.ofReal s * φ (rmulM g₁ n) := by
      intro n
      have : n₂⁻¹ * Matrix.of (T n) * (n₀⁻¹ * g₁) = Matrix.of n * g₁ := by
        rw [hTof]
        simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ u₂, Matrix.one_mul,
          Matrix.mul_nonsing_inv_cancel_right _ _ u₀]
      simp only [hψ, this]; rfl
    have hsub : SubCut (Nset k r) (lebR0 k r j β) ψ := by
      refine ⟨(hφ.1.comp (measurable_two _ _)).const_mul _, fun x hx => ?_⟩
      have hw : n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁) ∈ GG k r :=
        GG_mul (GG_mul (GG_inv hn₂.1) hx.1) (GG_mul (GG_inv hn₀.1) hg₁)
      have h := hφ.2 (Matrix.of.symm (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁))) hw
      have hc : (conjM n₂⁻¹ : Mt k r → Mt k r) =
          twoEquiv n₂⁻¹ n₂⁻¹⁻¹ (GG_unit (GG_inv hn₂.1)) (GG_unit (GG_inv (GG_inv hn₂.1))) := rfl
      rw [hc, lintegral_map_equiv, lintegral_smul_measure, smul_eq_mul,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h
      refine le_of_eq_of_le (lintegral_congr fun ρ => ?_) h
      have : n₂⁻¹ * (Matrix.of ρ * Matrix.of x) * (n₀⁻¹ * g₁) =
          n₂⁻¹ * Matrix.of ρ * n₂⁻¹⁻¹ * (n₂⁻¹ * Matrix.of x * (n₀⁻¹ * g₁)) := by
        rw [Matrix.nonsing_inv_nonsing_inv _ u₂]
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ u₂]
      exact congrArg (fun w : Mat k r => ENNReal.ofReal s * φ (Matrix.of.symm w)) this
    have h := key.2 ψ hsub R₀ y hR hy
    rw [← hmap, lintegral_map_equiv] at h
    have h' : ENNReal.ofReal s * ∫⁻ n, φ (rmulM g₁ n) *
        (Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤
        ENNReal.ofReal (fibVol0 k r j R₀ De y) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) h
      filter_upwards [hae] with n hn
      rw [hψT, ← mul_assoc]
      refine congrArg (fun t => ENNReal.ofReal s * φ (rmulM g₁ n) * t) ?_
      by_cases hm : rmulM g₁ n ∈ Eset0 k r hj z z' (n₁ * g₀ * n₂) R₀ y
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem ((hE n hn).1 hm)]; rfl
      · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (fun h => hm ((hE n hn).2 h))]
    rw [ENNReal.ofReal_div_of_pos hs, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hs))
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact h'

end GlobalTheory.Amp.FibreVolume
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreVolumeNormalFormStabiliserStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreVolume_normalFormStabiliser : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (De s : ℝ) (μR : Measure (Mt k r)), 1 ≤ j → j + 2 ≤ k → DeOK k r z z' γ De → 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → ∀ g₁ ∈ GG k r, lebN k r {n | Yj k r hj z z' γ (Matrix.of n * g₁) = 0} = 0 ∧ ∀ φ, SubCut (GG k r) μR φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ (rmulM g₁ n) * (Eset0 k r hj z z' γ R₀ y).indicator 1 (rmulM g₁ n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol0 k r j R₀ De y / s) := by
  first | exact @GlobalTheory.Amp.FibreVolume.fibre_volume | exact GlobalTheory.Amp.FibreVolume.fibre_volume | (intros; apply GlobalTheory.Amp.FibreVolume.fibre_volume <;> assumption)
end
