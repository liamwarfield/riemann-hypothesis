module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Weight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelSpace
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelFun
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def blkMinor (ε : Fin n → Bool) (a : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (x.submatrix (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det


open Classical in
def mexp (ε : Fin n → Bool) (m : Fin n → ℤ) (a : Fin n) : ℤ :=
  if h : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).Nonempty then
    m a - m ((Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).min' h)
  else m a

def NonnegDom (ε : Fin n → Bool) (m : Fin n → ℤ) : Prop :=
  (∀ a b, a < b → ε a = ε b → m b ≤ m a) ∧ ∀ a, 0 ≤ m a

def f0 (ε : Fin n → Bool) (m : Fin n → ℤ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ a, blkMinor ε a x ^ (mexp ε m a).toNat

def f0K (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) : ℂ := f0 ε m (toMK k)

theorem mexp_nonneg (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) : 0 ≤ mexp ε m a := by
  unfold mexp
  split_ifs with h
  · have hb := (Finset.mem_filter.1 (Finset.min'_mem _ h)).2
    exact sub_nonneg.2 (hm.1 a _ hb.1 hb.2.symm)
  · exact hm.2 a

lemma hwmf_diff_entry (i j : Fin n) : Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => x i j) := by
  first
    | exact ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.proj i) :
        (Fin n → Fin n → ℂ) →L[ℂ] ℂ).differentiable
    | fun_prop
    | exact (differentiable_apply j).comp (differentiable_apply i)

lemma hwmf_diff_prod {ι : Type} (s : Finset ι) (g : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ i, Differentiable ℂ (g i)) : Differentiable ℂ (fun x => ∏ i ∈ s, g i x) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiable_const _
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact (h a).mul ih

lemma hwmf_diff_blkMinor (ε : Fin n → Bool) (a : Fin n) : Differentiable ℂ (blkMinor ε a) := by
  show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => blkMinor ε a x)
  simp only [blkMinor, Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
  first
    | (apply Differentiable.fun_sum
       intro σ _
       exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))
    | fun_prop
    | (apply Differentiable.sum
       intro σ _
       exact (differentiable_const _).mul (hwmf_diff_prod _ _ (fun i => hwmf_diff_entry _ _)))

theorem differentiable_highest_weight_fn (ε : Fin n → Bool) (m : Fin n → ℤ) : Differentiable ℂ (f0 ε m) := by
  show Differentiable ℂ (fun x : Matrix (Fin n) (Fin n) ℂ => f0 ε m x)
  simp only [f0]
  exact hwmf_diff_prod _ _ (fun a => (hwmf_diff_blkMinor ε a).pow _)

theorem highest_weight_fn_K_one (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m 1 = 1 := by
  have h1 : toMK (1 : KG ε) = 1 := by
    first
      | exact toMK_one
      | simp [toMK]
      | rfl
  unfold f0K f0 blkMinor
  rw [h1]
  simp [Matrix.submatrix_one _ Subtype.val_injective]

lemma hwmf_hasDerivAt_A (X Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => Y * NormedSpace.exp ((t : ℂ) • X)) (Y * X) 0 := by
  refine hasDerivAt_pi.2 fun i => ?_
  refine hasDerivAt_pi.2 fun j => ?_
  simp only [Matrix.mul_apply]
  refine HasDerivAt.fun_sum fun k _ => HasDerivAt.const_mul _ ?_
  have h := InhabA.hasDerivAt_exp_entry X k j
  have e : (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) k j) = fun t : ℝ => (NormedSpace.exp (t • X)) k j := by
    funext t; congr 3
  rw [e]; exact h

theorem hasDerivAt_f0K (ε : Fin n → Bool) (m : Fin n → ℤ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X)
    (x : KG ε) :
    HasDerivAt (fun t : ℝ => f0K ε m (x * kcurve ε X t)) (fderiv ℂ (f0 ε m) (toMK x) (toMK x * X)) 0 := by
  have hspec := (kcurve_spec ε hX).2.1
  have hmul : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := by
    intro a b
    first
      | exact toMK_mul a b
      | (simp [toMK, toM]; done)
      | (simp only [toMK]; exact map_mul _ _ _)
      | (simp only [toMK, toM]; rfl)
  have hfun : (fun t : ℝ => f0K ε m (x * kcurve ε X t)) =
      fun t : ℝ => f0 ε m (toMK x * NormedSpace.exp ((t : ℂ) • X)) := by
    funext t
    show f0 ε m (toMK (x * kcurve ε X t)) = _
    rw [hmul, hspec t]
  rw [hfun]
  have hd : HasFDerivAt (f0 ε m) (fderiv ℂ (f0 ε m) (toMK x))
      (toMK x * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) := by
    rw [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.mul_one]
    exact (differentiable_highest_weight_fn ε m (toMK x)).hasFDerivAt
  exact (hd.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) (hwmf_hasDerivAt_A X (toMK x))

lemma hwmf_cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    cpart1 ε Z + Complex.I • cpart2 ε Z = Z := by
  unfold cpart1 cpart2
  ext i j
  first
    | (simp
       linear_combination (-(1 / 2) * (Z i j + (Jm ε * Zᴴ * Jm ε) i j)) * Complex.I_sq)
    | (simp [Complex.I_sq]; ring)

private theorem inK_cp1_lemma (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart1 ε (bdPart ε Z)) := by
  unfold inK inG cpart1 Jm bdPart
  constructor <;> ext a b <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, map_div₀] <;>
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp [ha, hb, Complex.conj_ofNat, map_ofNat] <;> ring

private theorem inK_cp2_lemma_2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    inK ε (cpart2 ε (bdPart ε Z)) := by
  unfold inK inG cpart2 Jm bdPart
  constructor <;> ext a b <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Complex.star_def, map_div₀,
      Complex.conj_I] <;>
    rcases Bool.eq_false_or_eq_true (ε a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (ε b) with hb | hb <;>
    simp [ha, hb, Complex.conj_ofNat, map_ofNat] <;> ring

lemma hwmf_rdc (ε : Fin n → Bool) (m : Fin n → ℤ) (Z : Matrix (Fin n) (Fin n) ℂ) (x : KG ε) :
    rdc ε Z (f0K ε m) x = fderiv ℂ (f0 ε m) (toMK x) (toMK x * bdPart ε Z) := by
  have h1 := hasDerivAt_f0K ε m (inK_cp1_lemma ε Z) x
  have h2 := hasDerivAt_f0K ε m (inK_cp2_lemma_2 ε Z) x
  unfold rdc
  rw [h1.deriv, h2.deriv]
  rw [show Complex.I * fderiv ℂ (f0 ε m) (toMK x) (toMK x * cpart2 ε (bdPart ε Z)) =
      fderiv ℂ (f0 ε m) (toMK x) (Complex.I • (toMK x * cpart2 ε (bdPart ε Z))) from
      ((fderiv ℂ (f0 ε m) (toMK x)).map_smul Complex.I _).symm]
  rw [← map_add (f := _), ← Matrix.mul_smul, ← Matrix.mul_add, hwmf_cpart_sum]

lemma hwmf_line (ε : Fin n → Bool) (m : Fin n → ℤ) (x W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun s : ℂ => f0 ε m (x * (1 + s • W))) (fderiv ℂ (f0 ε m) x (x * W)) 0 := by
  have hin : HasDerivAt (fun s : ℂ => x * (1 + s • W)) (x * W) 0 := by
    have hfun : (fun s : ℂ => x * (1 + s • W)) = fun s => x + s • (x * W) := by
      funext s
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
    rw [hfun]
    have h := ((hasDerivAt_id' (0 : ℂ)).smul_const (x * W)).const_add x
    rw [one_smul] at h
    exact h
  have hd : HasFDerivAt (f0 ε m) (fderiv ℂ (f0 ε m) x) (x * (1 + (0 : ℂ) • W)) := by
    rw [zero_smul, add_zero, Matrix.mul_one]
    exact (differentiable_highest_weight_fn ε m x).hasFDerivAt
  exact hd.comp_hasDerivAt (0 : ℂ) hin

lemma hwmf_mul_tv (x : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) (s : ℂ) (r q : Fin n) :
    (x * (1 + s • single a b (1 : ℂ))) r q = x r q + (if q = b then s * x r a else 0) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  congr 1
  by_cases hq : q = b
  · subst hq
    rw [if_pos rfl, Matrix.mul_apply]
    simp [Matrix.single_apply]
  · rw [if_neg hq, Matrix.mul_apply]
    simp [Matrix.single_apply, Ne.symm hq]

lemma hwmf_blk_tv (ε : Fin n → Bool) {a b : Fin n} (hab : a < b) (he : ε a = ε b) (c : Fin n)
    (x : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    blkMinor ε c (x * (1 + s • single a b (1 : ℂ))) = blkMinor ε c x := by
  unfold blkMinor
  by_cases hb : ε b = ε c ∧ b ≤ c
  · obtain ⟨B, hB⟩ : ∃ B : {d : Fin n // ε d = ε c ∧ d ≤ c}, (B : Fin n) = b := ⟨⟨b, hb⟩, rfl⟩
    obtain ⟨A, hA⟩ : ∃ A : {d : Fin n // ε d = ε c ∧ d ≤ c}, (A : Fin n) = a :=
      ⟨⟨a, he.trans hb.1, hab.le.trans hb.2⟩, rfl⟩
    have hBA : B ≠ A := fun h => (ne_of_lt hab) (by rw [← hA, ← hB, h])
    have hM : (x * (1 + s • single a b (1 : ℂ))).submatrix
        (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) =
        (x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))).updateCol B
          (fun k => x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) k B +
            s • x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) k A) := by
      ext i j
      rw [Matrix.submatrix_apply, hwmf_mul_tv, Matrix.updateCol_apply]
      by_cases hj : j = B
      · subst hj
        simp [hB, hA, smul_eq_mul]
      · have hj' : (j : Fin n) ≠ b := fun h => hj (Subtype.ext (h.trans hB.symm))
        simp [hj, hj']
    rw [hM, Matrix.det_updateCol_add_smul_self _ hBA]
  · congr 1
    ext i j
    rw [Matrix.submatrix_apply, Matrix.submatrix_apply, hwmf_mul_tv]
    have hj : (j : Fin n) ≠ b := fun h => hb (h ▸ j.2)
    simp [hj]

lemma hwmf_mul_dg (x : Matrix (Fin n) (Fin n) ℂ) (a : Fin n) (s : ℂ) (r q : Fin n) :
    (x * (1 + s • single a a (1 : ℂ))) r q = x r q * (if q = a then 1 + s else 1) := by
  rw [hwmf_mul_tv]
  by_cases hq : q = a
  · subst hq
    rw [if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hq, if_neg hq]
    ring

lemma hwmf_blk_dg (ε : Fin n → Bool) (a c : Fin n) (x : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    blkMinor ε c (x * (1 + s • single a a (1 : ℂ))) =
      blkMinor ε c x * (if ε a = ε c ∧ a ≤ c then 1 + s else 1) := by
  unfold blkMinor
  have hx : (x * (1 + s • single a a (1 : ℂ))).submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))
      (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) =
      x.submatrix (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n))
        (fun d : {d : Fin n // ε d = ε c ∧ d ≤ c} => (d : Fin n)) *
      diagonal (fun q : {d : Fin n // ε d = ε c ∧ d ≤ c} => if (q : Fin n) = a then 1 + s else 1) := by
    ext r q
    simp only [Matrix.submatrix_apply, Matrix.mul_diagonal, hwmf_mul_dg]
  rw [hx, det_mul, det_diagonal]
  congr 1
  split_ifs with ha
  · rw [Fintype.prod_eq_single (⟨a, ha⟩ : {d : Fin n // ε d = ε c ∧ d ≤ c})]
    · simp
    · intro q hq
      have : (q : Fin n) ≠ a := fun h => hq (Subtype.ext h)
      simp [this]
  · apply Finset.prod_eq_one
    intro q _
    have : (q : Fin n) ≠ a := fun h => ha (h ▸ q.2)
    simp [this]

lemma hwmf_tele (ε : Fin n → Bool) (m : Fin n → ℤ) : ∀ k : ℕ, ∀ a : Fin n,
    (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).card = k →
    ∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), mexp ε m c = m a := by
  intro k
  refine Nat.strong_induction_on k ?_
  intro k ih a hk
  have hsplit : Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c) =
      insert a (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      rcases h2.lt_or_eq with h | h
      · exact Or.inr ⟨h, h1.symm⟩
      · exact Or.inl h.symm
    · rintro (h | ⟨h1, h2⟩)
      · subst h
        exact ⟨rfl, le_rfl⟩
      · exact ⟨h2.symm, h1.le⟩
  have hnot : a ∉ Finset.univ.filter (fun b : Fin n => a < b ∧ ε b = ε a) := by simp
  rw [hsplit, Finset.sum_insert hnot]
  by_cases hne : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).Nonempty
  · obtain ⟨a', ha'def⟩ : ∃ a', (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a).min' hne = a' :=
      ⟨_, rfl⟩
    have ha'mem : a < a' ∧ ε a' = ε a := by
      have := Finset.min'_mem _ hne
      rw [ha'def] at this
      exact (Finset.mem_filter.1 this).2
    have hset : (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) =
        Finset.univ.filter (fun c : Fin n => ε a' = ε c ∧ a' ≤ c) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨ha'mem.2.trans h2.symm, ?_⟩
        rw [← ha'def]
        exact Finset.min'_le _ _ (by simp [h1, h2])
      · rintro ⟨h1, h2⟩
        exact ⟨lt_of_lt_of_le ha'mem.1 h2, h1.symm.trans ha'mem.2⟩
    have hcard : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a').card < k := by
      rw [← hk]
      have hsub : (Finset.univ.filter fun b : Fin n => a' < b ∧ ε b = ε a') ⊆
          (Finset.univ.filter fun b : Fin n => a < b ∧ ε b = ε a) := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
        exact ⟨ha'mem.1.trans hc.1, hc.2.trans ha'mem.2⟩
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset hsub]
      exact ⟨a', by simp [ha'mem.1, ha'mem.2], by simp⟩
    rw [hset, ih _ hcard a' rfl]
    unfold mexp
    rw [dite_eq_left hne, ha'def]
    ring
  · have hemp := Finset.not_nonempty_iff_eq_empty.1 hne
    rw [hemp, Finset.sum_empty, add_zero]
    unfold mexp
    rw [dite_eq_right hne]

lemma hwmf_bd_single (ε : Fin n → Bool) {a b : Fin n} (he : ε a = ε b) :
    bdPart ε (single a b (1 : ℂ)) = single a b 1 := by
  ext i j
  simp only [bdPart, Matrix.of_apply]
  by_cases h : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos he]
  · rw [Matrix.single_apply, if_neg h, ite_self]

private theorem f0_dg_lemma (ε : Fin n → Bool) (m : Fin n → ℤ) (a : Fin n) (X : Matrix (Fin n) (Fin n) ℂ)
    (s : ℂ) : f0 ε m (X * (1 + s • single a a (1 : ℂ))) =
      f0 ε m X * (1 + s) ^ (∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c),
        (mexp ε m c).toNat) := by
  unfold f0
  simp only [hwmf_blk_dg, mul_pow, Finset.prod_mul_distrib, ite_pow, one_pow]
  congr 1
  rw [← Finset.prod_filter, Finset.prod_pow_eq_pow_sum]

theorem rdc_f0K_wt (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) (a : Fin n) (x : KG ε) :
    rdc ε (Matrix.single a a 1) (f0K ε m) x = ((m a : ℤ) : ℂ) * f0K ε m x := by
  rw [hwmf_rdc, hwmf_bd_single ε rfl]
  have h1 := hwmf_line ε m (toMK x) (single a a 1)
  have hc : (fun s : ℂ => f0 ε m (toMK x * (1 + s • single a a (1 : ℂ)))) = fun s =>
      f0 ε m (toMK x) * (1 + s) ^ (∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c),
        (mexp ε m c).toNat) := by
    funext s
    exact f0_dg_lemma ε m a (toMK x) s
  rw [hc] at h1
  have h2 := (((hasDerivAt_id' (0 : ℂ)).const_add 1).pow (∑ c ∈ Finset.univ.filter
    (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat)).const_mul (f0 ε m (toMK x))
  rw [h1.unique h2]
  have hsum : ((∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat : ℕ) : ℤ)
      = m a := by
    rw [Nat.cast_sum, ← hwmf_tele ε m _ a rfl]
    exact Finset.sum_congr rfl fun c _ => Int.toNat_of_nonneg (mexp_nonneg ε hm c)
  have hsumC : ((∑ c ∈ Finset.univ.filter (fun c : Fin n => ε a = ε c ∧ a ≤ c), (mexp ε m c).toNat : ℕ) : ℂ)
      = ((m a : ℤ) : ℂ) := by
    rw [← hsum, Int.cast_natCast]
  simp only [add_zero, one_pow, mul_one]
  rw [hsumC]
  unfold f0K
  ring

theorem rdc_f0K_hw (ε : Fin n → Bool) {m : Fin n → ℤ} (hm : NonnegDom ε m) {a b : Fin n} (hab : a < b)
    (he : ε a = ε b) (x : KG ε) : rdc ε (Matrix.single a b 1) (f0K ε m) x = 0 := by
  rw [hwmf_rdc, hwmf_bd_single ε he]
  have h1 := hwmf_line ε m (toMK x) (single a b 1)
  have hc : (fun s : ℂ => f0 ε m (toMK x * (1 + s • single a b (1 : ℂ)))) = fun _ => f0 ε m (toMK x) := by
    funext s
    unfold f0
    simp only [hwmf_blk_tv ε hab he]
  rw [hc] at h1
  exact h1.unique (hasDerivAt_const _ _)

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def rtr (ε : Fin n → Bool) (k : KG ε) : (KG ε → ℂ) →ₗ[ℂ] (KG ε → ℂ) where
  toFun f := fun x => f (x * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rtr_mul (ε : Fin n → Bool) (k₁ k₂ : KG ε) (f : KG ε → ℂ) : rtr ε (k₁ * k₂) f = rtr ε k₁ (rtr ε k₂ f) := by
  funext x
  show f (x * (k₁ * k₂)) = f (x * k₁ * k₂)
  rw [mul_assoc]

theorem rtr_one (ε : Fin n → Bool) (f : KG ε → ℂ) : rtr ε 1 f = f := by
  funext x
  show f (x * 1) = f x
  rw [mul_one]

def Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : Submodule ℂ (KG ε → ℂ) :=
  Submodule.span ℂ (Set.range fun k : KG ε => rtr ε k (f0K ε m))

theorem highest_weight_fn_mem_space (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m ∈ Vsp ε m := by
  have h : rtr ε 1 (f0K ε m) ∈ Vsp ε m := Submodule.subset_span ⟨1, rfl⟩
  rwa [rtr_one] at h

theorem rtr_mem (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    rtr ε k f ∈ Vsp ε m := by
  have h : Vsp ε m ≤ (Vsp ε m).comap (rtr ε k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k', rfl⟩
    show rtr ε k (rtr ε k' (f0K ε m)) ∈ Vsp ε m
    rw [← rtr_mul]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  exact h hf

def evalK (ε : Fin n → Bool) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] (KG ε → ℂ) :=
  MvPolynomial.aeval fun p : Fin n × Fin n => fun k : KG ε => toMK k p.1 p.2

def polyK (ε : Fin n → Bool) (D : ℕ) : Submodule ℂ (KG ε → ℂ) :=
  (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap

theorem evalK_apply (ε : Fin n → Bool) (Q : MvPolynomial (Fin n × Fin n) ℂ) (x : KG ε) :
    evalK ε Q x = MvPolynomial.aeval (fun p : Fin n × Fin n => toMK x p.1 p.2) Q := by
  induction Q using MvPolynomial.induction_on
  next a => simp [evalK]
  next p q hp hq => rw [map_add (f := _), map_add (f := _), Pi.add_apply, hp, hq]
  next p i hp =>
    rw [map_mul, map_mul, Pi.mul_apply, hp]
    simp [evalK]

def rsub (ε : Fin n → Bool) (k : KG ε) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℂ :=
  fun p => ∑ l, MvPolynomial.X (p.1, l) * MvPolynomial.C (toMK k l p.2)

theorem toMK_mul' (ε : Fin n → Bool) (x k : KG ε) : toMK (x * k) = toMK x * toMK k := rfl

theorem rtr_evalK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) := by
  funext x
  show evalK ε Q (x * k) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) x
  rw [evalK_apply, evalK_apply, MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g Q) ?_
  funext p
  simp [rsub, toMK_mul', Matrix.mul_apply]

theorem totalDegree_rsub (ε : Fin n → Bool) (k : KG ε) (p : Fin n × Fin n) :
    (rsub ε k p).totalDegree ≤ 1 := by
  simp only [rsub]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]

theorem totalDegree_bind₁_le {σ τ : Type*} (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial σ ℂ) : (MvPolynomial.bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  classical
  conv_lhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [MvPolynomial.bind₁_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (MvPolynomial.le_totalDegree hd)
  rw [Finsupp.sum]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc d i * (g i).totalDegree ≤ d i * 1 := Nat.mul_le_mul_left _ (hg i)
    _ = d i := mul_one _

theorem rtr_polyK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) ∈ polyK ε Q.totalDegree := by
  rw [rtr_evalK]
  exact Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree ..).mpr
    (totalDegree_bind₁_le _ (totalDegree_rsub ε k) Q))

def f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∏ a, ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).submatrix
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det ^ (mexp ε m a).toNat

theorem evalK_f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : evalK ε (f0P ε m) = f0K ε m := by
  funext k
  rw [evalK_apply]
  show _ = f0 ε m (toMK k)
  simp only [f0P, f0, blkMinor, map_prod, map_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem Vsp_le_polyK (ε : Fin n → Bool) (m : Fin n → ℤ) : ∃ D : ℕ, Vsp ε m ≤ polyK ε D := by
  refine ⟨(f0P ε m).totalDegree, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨k, rfl⟩
  show rtr ε k (f0K ε m) ∈ polyK ε _
  rw [← evalK_f0P]
  exact rtr_polyK ε k (f0P ε m)

theorem finiteDimensional_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (Vsp ε m) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  haveI : FiniteDimensional ℂ (polyK ε D) := by
    unfold polyK
    infer_instance
  exact Submodule.finiteDimensional_of_le hD

theorem differentiable_aeval_entries (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ =>
      MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q) := by
  induction Q using MvPolynomial.induction_on
  next a => simp
  next p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  next p i hp =>
    have hX : Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ => M i.1 i.2) := by
      fun_prop
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul hX

theorem Vsp_holo (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, Differentiable ℂ F ∧ ∀ k, f k = F (toMK k) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  have h' : f ∈ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap := hD hf
  obtain ⟨Q, -, rfl⟩ := Submodule.mem_map.mp h'
  exact ⟨fun M => MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q,
    differentiable_aeval_entries Q, fun k => evalK_apply ε Q k⟩

theorem continuous_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    Continuous f := by
  obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m hf
  have hfe : f = fun k => F (toMK k) := funext hfF
  rw [hfe]
  refine hF.continuous.comp ?_
  fun_prop

theorem hasDerivAt_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m)
    {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Differentiable ℂ F) (hfF : ∀ k, f k = F (toMK k))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (x : KG ε) :
    HasDerivAt (fun t : ℝ => f (x * kcurve ε X t)) (fderiv ℂ F (toMK x) (toMK x * X)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => toMK (kcurve ε X t)) X 0 := by
    have hk : ∀ t : ℝ, toMK (kcurve ε X t) = NormedSpace.exp ((t : ℝ) • X) := fun t => by
       unfold kcurve
       rw [dite_eq_left hX, Classical.choose_spec (exists_curve ε hX) t, Complex.coe_smul]
    simp only [hk]
    letI iR : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
    haveI : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ)
        (@PseudoMetricSpace.toUniformSpace _ (@MetricSpace.toPseudoMetricSpace _ (@NormedRing.toMetricSpace _ iR))) := by
      exact FiniteDimensional.complete ℂ _
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (toMK x))
  have hin : HasDerivAt (fun t : ℝ => L (toMK (kcurve ε X t))) (L X) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hc
  have h0 : toMK (kcurve ε X 0) = 1 := by
    unfold kcurve
    rw [dite_eq_left hX, Classical.choose_spec (exists_curve ε hX) 0]
    simp
  have hLx : L (toMK (kcurve ε X 0)) = toMK x := by
    rw [h0]
    exact mul_one _
  have hF' := ((hF (toMK x)).hasFDerivAt.restrictScalars ℝ)
  rw [← hLx] at hF'
  have hcomp := hF'.comp_hasDerivAt (0 : ℝ) hin
  have hfun : (fun t : ℝ => f (x * kcurve ε X t)) = fun t => F (L (toMK (kcurve ε X t))) := by
    funext t
    rw [hfF, toMK_mul']
    rfl
  rw [hfun]
  rw [hLx] at hcomp
  exact hcomp

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def MV (ε : Fin n → Bool) (m : Fin n → ℤ) : Type := ↥(Vsp ε m)

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : AddCommGroup (MV ε m) := inferInstanceAs (AddCommGroup ↥(Vsp ε m))

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : Module ℂ (MV ε m) := inferInstanceAs (Module ℂ ↥(Vsp ε m))

def MV.fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : KG ε → ℂ := ((show ↥(Vsp ε m) from f) : KG ε → ℂ)

def MV.mk {ε : Fin n → Bool} {m : Fin n → ℤ} (f : KG ε → ℂ) (hf : f ∈ Vsp ε m) : MV ε m :=
  (⟨f, hf⟩ : ↥(Vsp ε m))

theorem MV.mem {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : f.fn ∈ Vsp ε m := by
  exact (show ↥(Vsp ε m) from f).2

theorem MV.ext {ε : Fin n → Bool} {m : Fin n → ℤ} {f g : MV ε m} (h : f.fn = g.fn) : f = g := by
  exact Subtype.ext h

@[simp] theorem MV.fn_add {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : (f + g).fn = f.fn + g.fn := rfl

@[simp] theorem MV.fn_smul {ε : Fin n → Bool} {m : Fin n → ℤ} (c : ℂ) (f : MV ε m) : (c • f).fn = c • f.fn := rfl

@[simp] theorem MV.fn_zero {ε : Fin n → Bool} {m : Fin n → ℤ} : (0 : MV ε m).fn = 0 := rfl

def mvInner {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : ℂ :=
  ∫ x, starRingEnd ℂ (f.fn x) * g.fn x ∂(muK ε)

theorem MV.continuous_fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : Continuous f.fn := by
  exact continuous_of_mem_Vsp ε m f.mem

theorem integrable_of_continuous_KG {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    MeasureTheory.Integrable F (muK ε) := by

  have := compactSpace_KG ε
  exact hF.integrable_of_hasCompactSupport (isClosed_tsupport F).isCompact

theorem mvInner_integrable {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    MeasureTheory.Integrable (fun x => starRingEnd ℂ (f.fn x) * g.fn x) (muK ε) := by
  exact integrable_of_continuous_KG
    ((Complex.continuous_conj.comp f.continuous_fn).mul g.continuous_fn)

theorem mvInner_self_eq {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) :
    mvInner f f = ((∫ x, Complex.normSq (f.fn x) ∂(muK ε) : ℝ) : ℂ) := by
  unfold mvInner
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  exact integral_ofReal

theorem mvInner_conj {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    starRingEnd ℂ (mvInner g f) = mvInner f g := by
  unfold mvInner
  rw [← integral_conj]
  congr 1
  funext x
  simp only [map_mul, starRingEnd_apply, star_star]
  exact mul_comm _ _

theorem mvInner_re_nonneg {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : 0 ≤ (mvInner f f).re := by
  rw [mvInner_self_eq, Complex.ofReal_re]
  exact integral_nonneg fun x => Complex.normSq_nonneg _

theorem mvInner_add_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g h : MV ε m) :
    mvInner (f + g) h = mvInner f h + mvInner g h := by
  simp only [mvInner, MV.fn_add, Pi.add_apply, map_add (f := _), add_mul]
  exact integral_add (mvInner_integrable f h) (mvInner_integrable g h)

theorem mvInner_smul_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) (c : ℂ) :
    mvInner (c • f) g = starRingEnd ℂ c * mvInner f g := by
  simp only [mvInner, MV.fn_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  exact integral_const_mul _ _

theorem mvInner_definite {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) (h : mvInner f f = 0) : f = 0 := by

  have hc : Continuous fun x => Complex.normSq (f.fn x) :=
    Complex.continuous_normSq.comp f.continuous_fn
  rw [mvInner_self_eq, Complex.ofReal_eq_zero] at h
  have hae : (fun x => Complex.normSq (f.fn x)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _)
      (by
        have := compactSpace_KG ε
        exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact)).mp h
  have hz : (fun x => Complex.normSq (f.fn x)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hc continuous_const).mp hae
  apply MV.ext
  funext x
  simpa using congrFun hz x

@[instance_reducible]
def mvCore (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace.Core ℂ (MV ε m) where
  inner := mvInner
  conj_inner_symm := mvInner_conj
  re_inner_nonneg := mvInner_re_nonneg
  add_left := mvInner_add_left
  smul_left := mvInner_smul_left
  definite := mvInner_definite

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : NormedAddCommGroup (MV ε m) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (MV ε m) _ _ _ (mvCore ε m)

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace ℂ (MV ε m) :=
  InnerProductSpace.ofCore (mvCore ε m).toCore

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (MV ε m) :=
  finiteDimensional_Vsp ε m

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : CompleteSpace (MV ε m) := FiniteDimensional.complete ℂ _

end ReciprocityTheory.ChartRestriction.DS.HW
