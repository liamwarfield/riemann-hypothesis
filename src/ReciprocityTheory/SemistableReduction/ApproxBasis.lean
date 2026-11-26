module

public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement

@[expose] public section

section -- merged from ReciprocityTheory.SemistableReduction.ApproxBasisB
section -- merged from ReciprocityTheory.SemistableReduction.ApproxBasisA
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem approxB_jForm_smul_right (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) (a : ℂ) :
    jForm p x (a • y) = a * jForm p x y := by
  simp only [jForm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem approxB_jForm_sum_right (p : ℕ) {r : ℕ} {α : Type*} (s : Finset α) (x : Fin r → ℂ)
    (f : α → Fin r → ℂ) : jForm p x (∑ j ∈ s, f j) = ∑ j ∈ s, jForm p x (f j) := by
  simp only [jForm, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem approxB_jForm_smul_left (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) (a : ℂ) :
    jForm p (a • x) y = conj a * jForm p x y := by
  simp only [jForm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem approxB_jForm_sum_left (p : ℕ) {r : ℕ} {α : Type*} (s : Finset α) (y : Fin r → ℂ)
    (f : α → Fin r → ℂ) : jForm p (∑ j ∈ s, f j) y = ∑ j ∈ s, jForm p (f j) y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [jForm, Finset.sum_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

theorem approxB_jForm_conj (p : ℕ) {r : ℕ} (x y : Fin r → ℂ) : conj (jForm p x y) = jForm p y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [jForm, jForm, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : (k : ℕ) < p <;> simp [sgn, h, mul_comm]

theorem approxB_posSq_nonneg (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : 0 ≤ posSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity

theorem approxB_negSq_nonneg (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : 0 ≤ negSq p u := Finset.sum_nonneg fun k _ => by split_ifs <;> positivity

theorem approxB_normSq_nonneg {r : ℕ} (u : Fin r → ℂ) : 0 ≤ normSq u := Finset.sum_nonneg fun k _ => by positivity

theorem approxB_posSq_add_negSq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    posSq p u + negSq p u = normSq u := by
  rw [posSq, negSq, normSq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp

theorem approxB_jForm_self (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    jForm p u u = ((posSq p u - negSq p u : ℝ) : ℂ) := by
  rw [jForm, posSq, negSq, ← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.conj_mul']
  by_cases h : (k : ℕ) < p <;> simp [sgn, h]

theorem approxB_jForm_self_re (p : ℕ) {r : ℕ} (u : Fin r → ℂ) :
    (jForm p u u).re = posSq p u - negSq p u := by
  rw [approxB_jForm_self, Complex.ofReal_re]

theorem approxB_norm_jForm_self_le (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : ‖jForm p u u‖ ≤ normSq u := by
  rw [approxB_jForm_self, Complex.norm_real, Real.norm_eq_abs, ← approxB_posSq_add_negSq]
  have h1 := approxB_posSq_nonneg p u
  have h2 := approxB_negSq_nonneg p u
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem approxB_normSq_add_le {r : ℕ} (a b : Fin r → ℂ) :
    normSq (a + b) ≤ 2 * normSq a + 2 * normSq b := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  simp only [Pi.add_apply]
  have h1 : ‖a k + b k‖ ^ 2 ≤ (‖a k‖ + ‖b k‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
  nlinarith [sq_nonneg (‖a k‖ - ‖b k‖)]

theorem approxB_normSq_single {r : ℕ} (j : Fin r) (R : ℝ) :
    normSq ((R : ℂ) • (Pi.single j 1 : Fin r → ℂ)) = R ^ 2 := by
  unfold normSq
  rw [Finset.sum_eq_single j]
  · simp [sq_abs]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

abbrev ApproxPosIdx (r p : ℕ) := {j : Fin r // (j : ℕ) < p}

theorem approxB_sum_pos {M : Type*} [AddCommMonoid M] {r p : ℕ} (f : Fin r → M)
    (hf : ∀ j : Fin r, ¬ (j : ℕ) < p → f j = 0) : ∑ j, f j = ∑ k : ApproxPosIdx r p, f k := by
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.filter fun j : Fin r => (j : ℕ) < p))
    (fun j _ hj => hf j (by simpa using hj))]
  exact Finset.sum_subtype _ (fun j => by simp) f

theorem approxB_card_pos {r p : ℕ} (hp : p ≤ r) : Fintype.card (ApproxPosIdx r p) = p := by
  let e : ApproxPosIdx r p ≃ Fin p :=
    { toFun := fun j => ⟨j.1, j.2⟩
      invFun := fun i => ⟨⟨i, lt_of_lt_of_le i.2 hp⟩, i.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem approxB_card_neg {r p : ℕ} (hp : p ≤ r) :
    Fintype.card {j : Fin r // ¬ (j : ℕ) < p} = r - p := by
  rw [Fintype.card_subtype_compl, approxB_card_pos hp, Fintype.card_fin]

def approxPadPos {r p : ℕ} (x : ApproxPosIdx r p → ℂ) : Fin r → ℂ :=
  fun j => if h : (j : ℕ) < p then x ⟨j, h⟩ else 0

theorem approxB_pad_sum {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (X : Fin r → Fin r → ℂ) :
    ∑ j, approxPadPos x j • X j = ∑ k : ApproxPosIdx r p, x k • X k.1 := by
  rw [approxB_sum_pos (p := p) _ (fun j hj => by simp [approxPadPos, hj])]
  exact Finset.sum_congr rfl fun k _ => by simp [approxPadPos, k.2]

theorem approxB_pad_ne {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (hx : x ≠ 0) : approxPadPos x ≠ 0 := by
  intro h
  apply hx
  funext k
  have h1 := congr_fun h k.1
  simpa [approxPadPos, k.2] using h1

theorem approxB_pad_zero {r p : ℕ} (x : ApproxPosIdx r p → ℂ) (j : Fin r) (hj : p ≤ (j : ℕ)) :
    approxPadPos x j = 0 := by
  simp [approxPadPos, not_lt.mpr hj]

theorem approxB_graph_pos {r p : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) (X : Fin r → Fin r → ℂ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j)))
    (x : ApproxPosIdx r p → ℂ) :
    0 ≤ (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re ∧
    (x ≠ 0 → 0 < (jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1)).re) := by
  obtain ⟨h1, h2⟩ := hg (approxPadPos x) (fun j hj => approxB_pad_zero x j hj)
  rw [approxB_pad_sum] at h1 h2
  rw [approxB_jForm_self_re]
  have hρ' : (ρ / 3) ^ 2 ≤ 1 / 9 := by
    have h3 : ρ / 3 ≤ 1 / 3 := by linarith
    have h4 : 0 ≤ ρ / 3 := by linarith
    nlinarith
  have hp0 := approxB_posSq_nonneg p (∑ k, x k • X k.1)
  refine ⟨by nlinarith, fun hx => ?_⟩
  have h5 := h2 (approxB_pad_ne x hx)
  nlinarith

theorem approxB_gram_posSemidef {r p : ℕ} {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ : 0 < ρ) (X : Fin r → Fin r → ℂ)
    (hg : ∀ w : Fin r → ℂ, (∀ j : Fin r, p ≤ (j : ℕ) → w j = 0) →
      negSq p (∑ j, w j • X j) ≤ (ρ / 3) ^ 2 * posSq p (∑ j, w j • X j) ∧
      (w ≠ 0 → 0 < posSq p (∑ j, w j • X j))) :
    (Matrix.of fun k j : ApproxPosIdx r p => jForm p (X k.1) (X j.1)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext k j
    simp [Matrix.conjTranspose_apply, approxB_jForm_conj]
  · have e : star x ⬝ᵥ ((Matrix.of fun k j : ApproxPosIdx r p => jForm p (X k.1) (X j.1)) *ᵥ x) =
        jForm p (∑ k, x k • X k.1) (∑ k, x k • X k.1) := by
      rw [approxB_jForm_sum_left]
      simp only [approxB_jForm_smul_left, approxB_jForm_sum_right, approxB_jForm_smul_right]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, Finset.mul_sum,
        Complex.star_def]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [e, approxB_jForm_self]
    have h := (approxB_graph_pos hρ1 hρ X hg x).1
    rw [approxB_jForm_self_re] at h
    exact Complex.zero_le_real.mpr (by linarith)

theorem approxB_det_le_of_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n ℂ) (hN : N.PosSemidef)
    (c : ℝ) (hc : ∀ k, (N k k).re ≤ c) : ‖N.det‖ ≤ c ^ Fintype.card n := by
  classical
  have hH := hN.isHermitian
  have hdet : N.det = ∏ i, (hH.eigenvalues i : ℂ) := hH.det_eq_prod_eigenvalues
  have hl : ∀ i, 0 ≤ hH.eigenvalues i := hN.eigenvalues_nonneg
  have htr : ∑ i, hH.eigenvalues i = ∑ k, (N k k).re := by
    have h2 := congrArg Complex.re hH.trace_eq_sum_eigenvalues
    simp only [Matrix.trace, Matrix.diag, Complex.re_sum, Complex.ofReal_re] at h2
    exact h2.symm
  have hnorm : ‖N.det‖ = ∏ i, hH.eigenvalues i := by
    rw [hdet, norm_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [Complex.norm_real, Real.norm_of_nonneg (hl i)]
  rw [hnorm]
  have hsum : ∑ i, hH.eigenvalues i ≤ Fintype.card n * c := by
    rw [htr]
    calc ∑ k, (N k k).re ≤ ∑ _k : n, c := Finset.sum_le_sum fun k _ => hc k
      _ = Fintype.card n * c := by simp
  rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
    simp [h0]
  · have hm : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos
    have hAM := Real.geom_mean_le_arith_mean_weighted Finset.univ (fun _ => (1 : ℝ) / Fintype.card n)
      hH.eigenvalues (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp) (fun i _ => hl i)
    have h2 : ∑ i, (1 : ℝ) / Fintype.card n * hH.eigenvalues i ≤ c := by
      rw [← Finset.mul_sum, div_mul_eq_mul_div, one_mul, div_le_iff₀ hm]
      linarith
    have hG : 0 ≤ ∏ i, hH.eigenvalues i ^ ((1 : ℝ) / Fintype.card n) :=
      Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hl i) _
    calc ∏ i, hH.eigenvalues i = (∏ i, hH.eigenvalues i ^ ((1 : ℝ) / Fintype.card n)) ^ Fintype.card n := by
          rw [← Finset.prod_pow]
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [← Real.rpow_natCast, ← Real.rpow_mul (hl i), one_div_mul_cancel hm.ne', Real.rpow_one]
      _ ≤ c ^ Fintype.card n := pow_le_pow_left₀ hG (hAM.trans h2) _

end ReciprocityTheory.MultiplicativeHeights
end
end

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate

theorem approxB_h_add_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y + z) = S.h x y + S.h x z := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem approxB_h_smul_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) (a : K) : S.h x (a • y) = a * S.h x y := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring

theorem approxB_h_sub_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y z : Fin r → K) : S.h x (y - z) = S.h x y - S.h x z := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem approxB_h_zero_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x : Fin r → K) : S.h x 0 = 0 := by
  simp [ReciprocityTheory.MultiplicativeHeights.HermForm.h]

theorem approxB_h_sum_right {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {α : Type*} (s : Finset α) (x : Fin r → K) (f : α → Fin r → K) :
    S.h x (∑ j ∈ s, f j) = ∑ j ∈ s, S.h x (f j) := by
  exact map_sum (AddMonoidHom.mk' (S.h x) ((approxB_h_add_right S) x)) f s

theorem approxB_h_smul_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) (a : K) : S.h (a • x) y = S.c a * S.h x y := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

private theorem hermForm_h_add_left {K : Type} [Field K] [NumberField K] {r : ℕ}
    (S : HermForm K r) (x y z : Fin r → K) : S.h (x + y) z = S.h x z + S.h y z := by
  unfold ReciprocityTheory.MultiplicativeHeights.HermForm.h
  simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem approxB_h_sum_left {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    {α : Type*} (s : Finset α) (y : Fin r → K) (f : α → Fin r → K) :
    S.h (∑ j ∈ s, f j) y = ∑ j ∈ s, S.h (f j) y := by
  exact map_sum (AddMonoidHom.mk' (fun z => S.h z y) (fun a b => (hermForm_h_add_left S) a b y)) f s

theorem approxB_embVec_add {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (x y : Fin r → K) : embVec σ (x + y) = embVec σ x + embVec σ y := by
  funext a
  simp [embVec]

theorem approxB_embVec_sub {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (x y : Fin r → K) : embVec σ (x - y) = embVec σ x - embVec σ y := by
  funext a
  simp [embVec]

theorem approxB_embVec_smul {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (a : K) (x : Fin r → K) : embVec σ (a • x) = σ a • embVec σ x := by
  funext i
  simp [embVec]

theorem approxB_embVec_sum {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    {α : Type*} (s : Finset α) (f : α → Fin r → K) :
    embVec σ (∑ j ∈ s, f j) = ∑ j ∈ s, embVec σ (f j) := by
  exact map_sum (AddMonoidHom.mk' (embVec σ) (approxB_embVec_add σ)) f s

theorem approxB_split {K : Type} [Field K] [NumberField K] {r p : ℕ} (hp : p ≤ r) (S : HermForm K r)
    (L : Submodule (𝓞 K) (Fin r → K)) (hL : IsIntegralOn S L) (l v : Fin r → Fin r → K)
    (hl : ∀ j, l j ∈ L) (hvi : LinearIndependent K v)
    (hinj : ∀ g : ApproxPosIdx r p → K,
      (∀ k : ApproxPosIdx r p, S.h (l k.1) (∑ j : ApproxPosIdx r p, g j • l j.1) = 0) → g = 0) :
    ∃ (Δ : K) (coef : (Fin r → K) → ApproxPosIdx r p → K) (a : {j : Fin r // ¬ (j : ℕ) < p} → Fin r),
      Δ ≠ 0 ∧ Δ = (Matrix.of fun k j : ApproxPosIdx r p => S.h (l k.1) (l j.1)).det ∧
      (∀ x (k : ApproxPosIdx r p), S.h (l k.1) (Δ • x - ∑ k', coef x k' • l k'.1) = 0) ∧
      (∀ x ∈ L, Δ • x - ∑ k', coef x k' • l k'.1 ∈ L) ∧
      LinearIndependent K (fun j : Fin r => if h : (j : ℕ) < p then l j else
        Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l k'.1) := by
  classical
  set M : Matrix (ApproxPosIdx r p) (ApproxPosIdx r p) K := Matrix.of fun k j => S.h (l k.1) (l j.1) with hM
  set Δ := M.det with hΔdef
  let bv : (Fin r → K) → ApproxPosIdx r p → K := fun x k => S.h (l k.1) x
  let coef : (Fin r → K) → ApproxPosIdx r p → K := fun x => M.adjugate *ᵥ bv x
  let T : (Fin r → K) → (Fin r → K) := fun x => Δ • x - ∑ k', coef x k' • l k'.1

  have hMinj : ∀ g, M *ᵥ g = 0 → g = 0 := by
    intro g hg
    apply hinj g
    intro k
    have := congrFun hg k
    simp only [mulVec, dotProduct, hM, Matrix.of_apply, Pi.zero_apply] at this
    rw [approxB_h_sum_right]
    simpa [approxB_h_smul_right, mul_comm] using this
  have hΔ : Δ ≠ 0 := by
    intro h0
    obtain ⟨g, hg0, hg⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hg0 (hMinj g hg)

  have horth : ∀ x (k : ApproxPosIdx r p), S.h (l k.1) (T x) = 0 := by
    intro x k
    have hMc : M *ᵥ coef x = Δ • bv x := by
      simp only [coef, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec, hΔdef]
    have hk := congrFun hMc k
    simp only [mulVec, dotProduct, hM, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] at hk
    simp only [T, approxB_h_sub_right, approxB_h_smul_right, approxB_h_sum_right]
    rw [← hk]
    simp [bv, mul_comm]

  have hint : ∀ x ∈ L, T x ∈ L := by
    intro x hx
    let f := algebraMap (𝓞 K) K
    have hMi : ∀ k j, ∃ z : 𝓞 K, f z = M k j := fun k j => hL _ (hl _) _ (hl _)
    choose Mz hMz using hMi
    have hbi : ∀ k, ∃ z : 𝓞 K, f z = bv x k := fun k => hL _ (hl _) _ hx
    choose bz hbz using hbi
    have hMmap : f.mapMatrix (Matrix.of Mz) = M := by ext k j; simp [hMz]
    have hΔz : f (Matrix.of Mz).det = Δ := by rw [RingHom.map_det, hMmap]
    have hcz : ∀ k, f (((Matrix.of Mz).adjugate *ᵥ bz) k) = coef x k := by
      intro k
      rw [show coef x = M.adjugate *ᵥ bv x from rfl, ← hMmap, ← RingHom.map_adjugate]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, map_sum,
        map_mul, hbz]
    have hT : T x = (Matrix.of Mz).det • x -
        ∑ k', ((Matrix.of Mz).adjugate *ᵥ bz) k' • l k'.1 := by
      simp only [T, ← hΔz, ← hcz]
      simp only [f, algebraMap_smul]
    rw [hT]
    exact L.sub_mem (L.smul_mem _ hx) (L.sum_mem fun k _ => L.smul_mem _ (hl _))

  have hbadd : ∀ x y, bv (x + y) = bv x + bv y :=
    fun x y => funext fun k => approxB_h_add_right S _ x y
  have hbsmul : ∀ (c : K) x, bv (c • x) = c • bv x :=
    fun c x => funext fun k => by simp [bv, approxB_h_smul_right]
  let Tl : (Fin r → K) →ₗ[K] (Fin r → K) :=
    { toFun := T
      map_add' := fun x y => by
        simp only [T, coef, hbadd, mulVec_add, Pi.add_apply, add_smul, Finset.sum_add_distrib,
          smul_add]
        abel
      map_smul' := fun c x => by
        simp only [T, coef, hbsmul, mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_smul,
          ← Finset.smul_sum, RingHom.id_apply, smul_sub]
        rw [smul_comm Δ c x] }
  have hker : LinearMap.ker Tl ≤ Submodule.span K (Set.range fun k : ApproxPosIdx r p => l k.1) := by
    intro x hx
    have h0 : T x = 0 := LinearMap.mem_ker.mp hx
    have hx' : x = Δ⁻¹ • ∑ k', coef x k' • l k'.1 := by
      have h1 : Δ • x = ∑ k', coef x k' • l k'.1 := sub_eq_zero.mp h0
      rw [← h1, smul_smul, inv_mul_cancel₀ hΔ, one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hfk : Module.finrank K (LinearMap.ker Tl) ≤ p := by
    calc _ ≤ Module.finrank K (Submodule.span K (Set.range fun k : ApproxPosIdx r p => l k.1)) :=
          Submodule.finrank_mono hker
      _ ≤ Fintype.card (ApproxPosIdx r p) := finrank_range_le_card (R := K) _
      _ = p := approxB_card_pos hp
  have hrn := LinearMap.finrank_range_add_finrank_ker Tl
  rw [Module.finrank_fin_fun] at hrn
  have hfr : r - p ≤ Module.finrank K (LinearMap.range Tl) := by omega
  have hspan_v : Submodule.span K (Set.range v) = ⊤ :=
    hvi.span_eq_top_of_card_eq_finrank' (by simp)
  have hrange : Submodule.span K (Set.range (Tl ∘ v)) = LinearMap.range Tl := by
    rw [Set.range_comp, ← Submodule.map_span, hspan_v, Submodule.map_top]
  obtain ⟨κ, a0, ha0, hsp, hli⟩ := exists_linearIndependent' K (Tl ∘ v)
  have : Finite κ := Finite.of_injective a0 ha0
  have : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank K (LinearMap.range Tl) := by
    rw [← hrange, ← hsp, finrank_span_eq_card hli]
  have hle : Fintype.card {j : Fin r // ¬ (j : ℕ) < p} ≤ Fintype.card κ := by
    rw [approxB_card_neg hp, hcard]; exact hfr
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
  have hlia : LinearIndependent K (fun k => T (v (a0 (e k)))) := hli.comp e e.injective
  refine ⟨Δ, coef, fun k => a0 (e k), hΔ, rfl, horth, hint, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hsplit : ∑ k : ApproxPosIdx r p, g k.1 • l k.1 +
      ∑ k : {j : Fin r // ¬ (j : ℕ) < p}, g k.1 • T (v (a0 (e k))) = 0 := by
    rw [← hg, ← Fintype.sum_subtype_add_sum_subtype (fun j : Fin r => (j : ℕ) < p)]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => by simp only [dif_pos k.2]
    · exact Finset.sum_congr rfl fun k _ => by simp only [dif_neg k.2]; rfl
  have hBorth : ∀ k' : ApproxPosIdx r p,
      S.h (l k'.1) (∑ k : {j : Fin r // ¬ (j : ℕ) < p}, g k.1 • T (v (a0 (e k)))) = 0 := by
    intro k'
    rw [approxB_h_sum_right]
    exact Finset.sum_eq_zero fun k _ => by rw [approxB_h_smul_right, horth, mul_zero]
  have hApos : ∀ k' : ApproxPosIdx r p, S.h (l k'.1) (∑ k : ApproxPosIdx r p, g k.1 • l k.1) = 0 := by
    intro k'
    have := congrArg (S.h (l k'.1)) hsplit
    rw [approxB_h_add_right, hBorth, add_zero, approxB_h_zero_right] at this
    exact this
  have hg1 := hinj (fun k => g k.1) hApos
  have hA0 : ∑ k : ApproxPosIdx r p, g k.1 • l k.1 = 0 :=
    Finset.sum_eq_zero fun k _ => by rw [show g k.1 = 0 from congrFun hg1 k, zero_smul]
  rw [hA0, zero_add] at hsplit
  have hg2 := (Fintype.linearIndependent_iff.mp hlia) (fun k => g k.1) hsplit
  intro j
  by_cases hj : (j : ℕ) < p
  · exact congrFun hg1 ⟨j, hj⟩
  · exact hg2 ⟨j, hj⟩

end ReciprocityTheory.MultiplicativeHeights
end
end

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

private theorem normSq_smul_eq_norm_sq_mul {r : ℕ} (c : ℂ) (u : Fin r → ℂ) :
    normSq (c • u) = ‖c‖ ^ 2 * normSq u := by
  unfold normSq
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]

private theorem le_approxR {r : ℕ} (hr : 0 < r) {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) : μ ≤ approxR r μ ρ := by
  unfold approxR
  have h1 : (1 : ℝ) ≤ Real.sqrt r := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hr)
  rw [le_div_iff₀ hρ]
  nlinarith [mul_le_mul_of_nonneg_left hρ1 hμ.le, mul_le_mul_of_nonneg_left h1 hμ.le]

private theorem normSq_le_of_normSq_sub_approxR_single_le {r : ℕ} {μ ρ : ℝ} (hμ : 0 < μ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (j : Fin r) (x : Fin r → ℂ)
    (hx : normSq (x - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ)) ≤ μ ^ 2) :
    normSq x ≤ (2 * approxR r μ ρ) ^ 2 := by
  have hR := le_approxR j.pos hμ hρ hρ1
  have h := approxB_normSq_add_le (x - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
    ((approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
  rw [sub_add_cancel, approxB_normSq_single] at h
  nlinarith [mul_le_mul hR hR hμ.le (le_trans hμ.le hR)]

private theorem mulVec_embVec_sum_smul {K : Type} [Field K] [NumberField K] {r : ℕ} (σ : K →+* ℂ)
    (Q : Matrix (Fin r) (Fin r) ℂ) {α : Type*} (s : Finset α) (g : α → K) (f : α → Fin r → K) :
    Q *ᵥ embVec σ (∑ j ∈ s, g j • f j) = ∑ j ∈ s, σ (g j) • (Q *ᵥ embVec σ (f j)) := by
  rw [approxB_embVec_sum, Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [approxB_embVec_smul, Matrix.mulVec_smul]

theorem approxBasis_holds (hG : ApproxGraphStatement) : ApproxStatement := by
  unfold ApproxGraphStatement at hG
  unfold ApproxStatement
  intro K _ _ ι _ _ r p S σ Q L v μ ρ hp hμ hρ hρ1 hQ hS hInt hcov hvL hvi hvμ
  choose l0 hl0L hl0 using fun j : Fin r =>
    hcov (fun _ => (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
  obtain ⟨X, hX⟩ : ∃ X : ι → Fin r → Fin r → ℂ,
      ∀ i j, X i j = Q i *ᵥ embVec (σ i) (l0 j) := ⟨_, fun _ _ => rfl⟩
  have happ : ∀ i j, normSq (X i j - (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))
      ≤ μ ^ 2 := by
    intro i j
    rw [hX]
    refine le_trans ?_ (hl0 j)
    exact Finset.single_le_sum (f := fun i' => normSq (Q i' *ᵥ embVec (σ i') (l0 j) -
      (approxR r μ ρ : ℂ) • (Pi.single j 1 : Fin r → ℂ))) (fun i' _ => approxB_normSq_nonneg _)
      (Finset.mem_univ i)
  have hGi := fun i => hG r p μ ρ (X i) hp hμ hρ hρ1 (fun j _ => happ i j)
  have hdiag : ∀ i j, normSq (X i j) ≤ (2 * approxR r μ ρ) ^ 2 :=
    fun i j => normSq_le_of_normSq_sub_approxR_single_le hμ hρ hρ1 j _ (happ i j)
  have hinj : ∀ g : ApproxPosIdx r p → K,
      (∀ k : ApproxPosIdx r p, S.h (l0 k.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1) = 0) → g = 0 := by
    intro g hg
    by_contra hne
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hzz : S.h (∑ j : ApproxPosIdx r p, g j • l0 j.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1) = 0 := by
      rw [approxB_h_sum_left]
      exact Finset.sum_eq_zero fun j _ => by rw [approxB_h_smul_left, hg j, mul_zero]
    have h1 := hS i (∑ j : ApproxPosIdx r p, g j • l0 j.1) (∑ j : ApproxPosIdx r p, g j • l0 j.1)
    rw [hzz, map_zero, mulVec_embVec_sum_smul] at h1
    have hx : (fun k : ApproxPosIdx r p => σ i (g k)) ≠ 0 := by
      intro hx
      apply hne
      funext k
      exact (map_eq_zero (σ i)).mp (congrFun hx k)
    have h2 := (approxB_graph_pos hρ1 hρ (X i) (hGi i).1 (fun k => σ i (g k))).2 hx
    simp only [hX] at h2
    rw [← h1] at h2
    simp at h2
  obtain ⟨Δ, coef, a, hΔ0, hΔ, horth, hmem, hli⟩ :=
    approxB_split hp S L hInt l0 v hl0L hvi hinj
  obtain ⟨la, hla⟩ : ∃ la : Fin r → Fin r → K, la = fun j : Fin r => if h : (j : ℕ) < p then l0 j
      else Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l0 k'.1 := ⟨_, rfl⟩
  have hla_pos : ∀ (j : Fin r) (h : (j : ℕ) < p), la j = l0 j := fun j h => by
    rw [hla]; simp only [dif_pos h]
  have hla_neg : ∀ (j : Fin r) (h : ¬ (j : ℕ) < p), la j =
      Δ • v (a ⟨j, h⟩) - ∑ k', coef (v (a ⟨j, h⟩)) k' • l0 k'.1 := fun j h => by
    rw [hla]; simp only [dif_neg h]
  have hli' : LinearIndependent K la := by rw [hla]; exact hli
  have horth' : ∀ (k : Fin r), (k : ℕ) < p → ∀ j : Fin r, ¬ (j : ℕ) < p →
      S.h (l0 k) (la j) = 0 := fun k hk j hj => by
    rw [hla_neg j hj]; exact horth _ ⟨k, hk⟩
  have hdet : ∀ i, ((Matrix.of la).map (σ i)).det ≠ 0 := by
    intro i
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    have hu : IsUnit (Matrix.of la) :=
      (Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of la)).mp hli'
    exact (map_ne_zero (σ i)).mpr ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero
  have hcomb : ∀ i (w : Fin r → ℂ),
      Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) = ∑ j, w j • (Q i *ᵥ embVec (σ i) (la j)) := by
    intro i w
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun j _ => Matrix.mulVec_smul _ _ _
  have hne : ∀ i (w : Fin r → ℂ), w ≠ 0 → Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) ≠ 0 := by
    intro i w hw h0
    apply hw
    have h1 := Matrix.eq_zero_of_mulVec_eq_zero (hQ i) h0
    refine Matrix.eq_zero_of_vecMul_eq_zero (hdet i) ?_
    rw [← h1]
    funext b
    simp [Matrix.vecMul, dotProduct, embVec, Finset.sum_apply]
  refine ⟨la, fun j => ?_, hli', ?_, ?_, ?_, ?_, ?_⟩
  · by_cases h : (j : ℕ) < p
    · rw [hla_pos j h]; exact hl0L j
    · rw [hla_neg j h]; exact hmem _ (hvL _)
  · intro j k hj hk
    rw [hla_pos j hj]
    exact horth' j hj k (not_lt.mpr hk)
  · intro i w hw
    have hsum : Q i *ᵥ ∑ j, w j • embVec (σ i) (la j) = ∑ j, w j • X i j := by
      rw [hcomb]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : (j : ℕ) < p
      · rw [hla_pos j h, hX]
      · rw [hw j (not_lt.mp h), zero_smul, zero_smul]
    rw [hsum]
    obtain ⟨h1, h2⟩ := (hGi i).1 w hw
    refine ⟨h1, fun hw0 => ?_⟩
    have h3 := h2 hw0
    rw [approxB_jForm_self_re]
    have hq : (ρ / 3) ^ 2 < 1 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_right hq h3]
  · intro i w hw hw0
    refine (hGi i).2.1 _ (fun j hj => ?_) (hne i w hw0)
    rw [hcomb, approxB_jForm_sum_right]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [approxB_jForm_smul_right]
    by_cases hk : (k : ℕ) < p
    · rw [hw k hk, zero_mul]
    · rw [hX, ← hS, horth' j hj k hk, map_zero, mul_zero]
  · intro i j hj
    rw [hS i, hla_pos j hj, ← hX]
    exact le_trans (approxB_norm_jForm_self_le p _) (hdiag i j)
  · intro i j hj
    have hj' : ¬ (j : ℕ) < p := not_lt.mpr hj
    obtain ⟨x, hx⟩ : ∃ x, x = v (a ⟨j, hj'⟩) := ⟨_, rfl⟩
    rw [hS i, hla_neg j hj', ← hx]
    have hort : ∀ k : Fin r, (k : ℕ) < p → jForm p (X i k) (Q i *ᵥ embVec (σ i)
        (Δ • x - ∑ k', coef x k' • l0 k'.1)) = 0 := by
      intro k hk
      have h0 : S.h (l0 k) (Δ • x - ∑ k', coef x k' • l0 k'.1) = 0 := horth x ⟨k, hk⟩
      rw [hX, ← hS, h0, map_zero]
    have hspan : Q i *ᵥ embVec (σ i) (Δ • x) -
        Q i *ᵥ embVec (σ i) (Δ • x - ∑ k', coef x k' • l0 k'.1)
        ∈ Submodule.span ℂ (X i '' {j | (j : ℕ) < p}) := by
      rw [← Matrix.mulVec_sub, ← approxB_embVec_sub, sub_sub_cancel, mulVec_embVec_sum_smul]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k.1, k.2, hX i k.1⟩)
    have hb := (hGi i).2.2 _ _ hort hspan
    rw [approxB_embVec_smul, Matrix.mulVec_smul, normSq_smul_eq_norm_sq_mul] at hb
    have hxμ : normSq (Q i *ᵥ embVec (σ i) x) ≤ μ ^ 2 := by
      refine le_trans (Finset.single_le_sum (f := fun i' => normSq (Q i' *ᵥ embVec (σ i') x))
        (fun _ _ => approxB_normSq_nonneg _) (Finset.mem_univ i)) ?_
      rw [hx]
      exact hvμ _
    have hgram : (σ i).mapMatrix (Matrix.of fun k j : ApproxPosIdx r p => S.h (l0 k.1) (l0 j.1)) =
        Matrix.of fun k j : ApproxPosIdx r p => jForm p (X i k.1) (X i j.1) := by
      ext k j
      simp [RingHom.mapMatrix_apply, hS, hX]
    have hΔbd : ‖σ i Δ‖ ≤ ((2 * approxR r μ ρ) ^ 2) ^ p := by
      rw [hΔ, RingHom.map_det, hgram]
      have h := approxB_det_le_of_posSemidef _ (approxB_gram_posSemidef hρ1 hρ (X i) (hGi i).1)
        ((2 * approxR r μ ρ) ^ 2) fun k => by
          simp only [Matrix.of_apply]
          exact le_trans (Complex.re_le_norm _)
            (le_trans (approxB_norm_jForm_self_le p _) (hdiag i k.1))
      rwa [approxB_card_pos hp] at h
    have hsq : ‖σ i Δ‖ ^ 2 ≤ (((2 * approxR r μ ρ) ^ 2) ^ p) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hΔbd 2
    have hpow : (2 * approxR r μ ρ) ^ (4 * p) =
        (((2 * approxR r μ ρ) ^ 2) ^ p) ^ 2 := by
      rw [← pow_mul, ← pow_mul]; congr 1; ring
    rw [hpow]
    refine le_trans hb ?_
    have hs0 := approxB_normSq_nonneg (Q i *ᵥ embVec (σ i) x)
    nlinarith [mul_le_mul hsq hxμ hs0 (by positivity)]

end ReciprocityTheory.MultiplicativeHeights
