module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.InhabA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrableOfDecayVG

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private lemma tele_range (D : ℕ → ℂ) (hD : ∀ l, D l ≠ 0) (m : ℕ → ℤ) (N : ℕ) :
    ∏ i ∈ range N, (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1))) =
      (∏ l ∈ range N, D l ^ (-m l)) * (∏ l ∈ range N, D l) ^ m N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ (fun i => (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1)))) N, ih]
    simp only [Finset.prod_range_succ]
    have hP : (∏ l ∈ range N, D l) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hD l
    have hPd : (∏ l ∈ range N, D l) * D N ≠ 0 := mul_ne_zero hP (hD N)
    have h1 : ((∏ l ∈ range N, D l) * D N) ^ (-(m N - m (N + 1))) =
        ((∏ l ∈ range N, D l) * D N) ^ (-m N) * ((∏ l ∈ range N, D l) * D N) ^ (m (N + 1)) := by
      rw [← zpow_add₀ hPd]
      congr 1
      ring
    have h2 : ((∏ l ∈ range N, D l) * D N) ^ (-m N) =
        (∏ l ∈ range N, D l) ^ (-m N) * D N ^ (-m N) := mul_zpow _ _ _
    have h3 : (∏ l ∈ range N, D l) ^ m N * (∏ l ∈ range N, D l) ^ (-m N) = 1 := by
      rw [← zpow_add₀ hP, add_neg_cancel, zpow_zero]
    rw [h1, h2]
    linear_combination ((∏ l ∈ range N, D l ^ (-m l)) * D N ^ (-m N) *
      ((∏ l ∈ range N, D l) * D N) ^ m (N + 1)) * h3

private lemma filter_prod_eq_range (d : Fin n → ℂ) (k : ℕ) (hk : k ≤ n) :
    ∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < k), d l =
      ∏ j ∈ range k, (if h : j < n then d ⟨j, h⟩ else 1) := by
  have hr : range k = (range n).filter (fun j => j < k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor <;> intro h <;> omega
  rw [hr]
  simp only [Finset.prod_filter]
  rw [Finset.prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [l.2]

private lemma tele_fin (d : Fin n → ℂ) (hd : ∀ l, d l ≠ 0) (μ : Fin n → ℤ) :
    ∏ i : Fin n, (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), d l) ^ (-(μ i - muNext μ i)) =
      ∏ l, d l ^ (-μ l) := by
  set D : ℕ → ℂ := fun j => if h : j < n then d ⟨j, h⟩ else 1 with hDdef
  set m : ℕ → ℤ := fun j => if h : j < n then μ ⟨j, h⟩ else 0 with hmdef
  have hD : ∀ l, D l ≠ 0 := by
    intro l
    simp only [hDdef]
    split_ifs
    · exact hd _
    · exact one_ne_zero
  have h1 : ∀ i : Fin n, (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), d l) ^
      (-(μ i - muNext μ i)) = (∏ l ∈ range ((i : ℕ) + 1), D l) ^ (-(m i - m ((i : ℕ) + 1))) := by
    intro i
    rw [filter_prod_eq_range d _ (by have := i.2; omega)]
    congr 1
    all_goals first | rfl | simp [hmdef, muNext, i.2]
  rw [Finset.prod_congr rfl (fun i _ => h1 i),
    Fin.prod_univ_eq_prod_range (fun i => (∏ l ∈ range (i + 1), D l) ^ (-(m i - m (i + 1)))) n,
    tele_range D hD m n]
  have hmn : m n = 0 := by simp [hmdef]
  rw [hmn, zpow_zero, mul_one, Finset.prod_range (fun l => D l ^ (-m l))]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp [hDdef, hmdef, l.2]

private lemma lead_differentiable_lemma (i : ℕ) :
    Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  have hent : ∀ a b : Fin n, Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => z a b) := by
    intro a b
    let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun M => M a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap L).differentiable
  unfold lead
  split_ifs with h
  · simp only [Matrix.det_apply', Matrix.submatrix_apply]
    fun_prop
  · exact differentiable_const _

theorem isOpen_omega : IsOpen (OmegaSet n) := by
  have : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (lead_differentiable_lemma _).continuous continuous_const

theorem posSet_subset_omega : posSet n ⊆ OmegaSet n := by
  intro x hx i h
  have := (lead_posDef hx ((i : ℕ) + 1) (by have := i.2; omega)).1
  rw [h] at this
  simp at this

theorem phiM_differentiableOn (μ : Fin n → ℤ) : DifferentiableOn ℂ (PhiM μ) (OmegaSet n) := by
  intro z hz
  have hz' : ∀ i : Fin n, lead ((i : ℕ) + 1) z ≠ 0 := hz
  have hL : ∀ i : ℕ, Differentiable ℂ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) :=
    fun i => lead_differentiable_lemma i
  have hq : DifferentiableAt ℂ (PhiM μ) z := by
    unfold PhiM
    fun_prop (disch := exact Or.inl (hz' _))
  exact hq.differentiableWithinAt

theorem phiM_tri_mul (μ : Fin n → ℤ) {c z c' : Matrix (Fin n) (Fin n) ℂ} (hc : IsLowerTri c) (hc' : IsUpperTri c')
    (hcd : ∀ l, c l l ≠ 0) (hcd' : ∀ l, c' l l ≠ 0) (hz : z ∈ OmegaSet n) :
    c * z * c' ∈ OmegaSet n ∧
      PhiM μ (c * z * c') = (∏ l, (c l l * c' l l) ^ (-μ l)) * PhiM μ z := by
  have hd : ∀ l, c l l * c' l l ≠ 0 := fun l => mul_ne_zero (hcd l) (hcd' l)
  have hlead : ∀ i : Fin n, lead ((i : ℕ) + 1) (c * z * c') =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) * lead ((i : ℕ) + 1) z :=
    fun i => lead_tri_mul hc hc' _ i.isLt
  have hP : ∀ i : Fin n,
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) ≠ 0 :=
    fun i => prod_ne_zero_iff.mpr fun l _ => hd l
  refine ⟨fun i => by rw [hlead i]; exact mul_ne_zero (hP i) (hz i), ?_⟩
  have hterm : ∀ i : Fin n, lead ((i : ℕ) + 1) (c * z * c') ^ (-(μ i - muNext μ i)) =
      (∏ l ∈ univ.filter (fun l : Fin n => (l : ℕ) < (i : ℕ) + 1), c l l * c' l l) ^ (-(μ i - muNext μ i)) *
        lead ((i : ℕ) + 1) z ^ (-(μ i - muNext μ i)) := fun i => by rw [hlead i, mul_zpow]
  unfold PhiM
  rw [prod_congr rfl fun i _ => hterm i, prod_mul_distrib,
    tele_fin (fun l => c l l * c' l l) hd μ]

theorem phiM_posDef (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    0 < (PhiM μ x).re ∧ (PhiM μ x).im = 0 := by
  have hpos : ∀ i : Fin n, 0 < (lead ((i : ℕ) + 1) x).re :=
    fun i => (lead_posDef hx _ (by have := i.2; omega)).1
  have hr : ∀ i : Fin n, lead ((i : ℕ) + 1) x = ((lead ((i : ℕ) + 1) x).re : ℂ) := by
    intro i
    apply Complex.ext
    · simp
    · simp [(lead_posDef hx ((i : ℕ) + 1) (by have := i.2; omega)).2]
  have hP : PhiM μ x = ((∏ i : Fin n, (lead ((i : ℕ) + 1) x).re ^ (-(μ i - muNext μ i)) : ℝ) : ℂ) := by
    unfold PhiM
    push_cast
    exact Finset.prod_congr rfl fun i _ => by rw [← hr i]
  rw [hP, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨Finset.prod_pos fun i _ => zpow_pos (hpos i) _, rfl⟩

theorem phiM_one (μ : Fin n → ℤ) : PhiM μ (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold PhiM
  have h1 : ∀ i : Fin n, lead ((i : ℕ) + 1) (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    intro i
    unfold lead
    rw [dite_eq_left (by have := i.2; omega), Matrix.submatrix_one _ (Fin.castLE_injective _), Matrix.det_one]
  simp [h1]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DTauFacts
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem op_inv_eq_adjoint (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  rw [KType.op, map_inv, ← ContinuousLinearMap.star_eq_adjoint]
  first
  | rfl
  | simp [Unitary.star_eq_inv]
  | simp [unitary.star_eq_inv]

private lemma commute_Jm_of_isBlock {Y : Matrix (Fin n) (Fin n) ℂ} (hY : IsBlock ε Y) :
    Y * Jm ε = Jm ε * Y := by
  ext a b
  simp only [Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : ε a = ε b
  · rw [h, mul_comm]
  · simp [hY a b h]

lemma block_decomp {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    ∃ A B : Matrix (Fin n) (Fin n) ℂ, inK ε A ∧ inK ε B ∧ X = A + Complex.I • B ∧
      Xᴴ = -A + Complex.I • B := by
  have hXH : IsBlock ε Xᴴ := fun a b h => by
    rw [Matrix.conjTranspose_apply, hX b a (Ne.symm h), star_zero]
  have hc1 := commute_Jm_of_isBlock hX
  have hc2 := commute_Jm_of_isBlock hXH
  have hI : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I]
    norm_num
  have hIB : Complex.I • ((-Complex.I / 2) • (X + Xᴴ)) = (1 / 2 : ℂ) • (X + Xᴴ) := by
    rw [smul_smul, hI]
  have hs1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have hs2 : star (-Complex.I / 2) = Complex.I / 2 := by simp
  refine ⟨(1 / 2 : ℂ) • (X - Xᴴ), (-Complex.I / 2) • (X + Xᴴ), ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose,
      hs1, Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]
    module
  · rw [Matrix.smul_mul, Matrix.mul_smul, sub_mul, mul_sub, hc1, hc2]
  · unfold inG
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose,
      hs2, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]
    module
  · rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, hc1, hc2]
  · rw [hIB]
    module
  · rw [hIB]
    module

lemma inK_neg {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) : inK ε (-A) := by
  refine ⟨?_, by rw [neg_mul, mul_neg, hA.2]⟩
  have h := hA.1
  unfold inG at h ⊢
  rw [Matrix.conjTranspose_neg, neg_mul, mul_neg, ← neg_add, h, neg_zero]

lemma gamma_zero {γ : ℝ → KG ε} (hmul : ∀ s t, γ (s + t) = γ s * γ t) : γ 0 = 1 := by
  simpa using hmul 0 0

lemma dtau_skew (T : KType ε Λ) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    ContinuousLinearMap.adjoint (T.dτ A) = -T.dτ A := by
  obtain ⟨γ, -, hγ, hmul⟩ := exists_oneParam ε hA
  have h0 := gamma_zero hmul
  have hinv : ∀ t, γ (-t) = (γ t)⁻¹ := fun t =>
    eq_inv_of_mul_eq_one_left (by rw [← hmul, neg_add_cancel, h0])
  have h1 := T.hasDeriv A hA γ hγ
  have h2 := T.hasDeriv (-A) (inK_neg hA) (fun t => γ (-t)) (fun t => by
    rw [hγ]; congr 1; push_cast; rw [neg_smul, smul_neg])
  have h3 := h1.star
  simp only [ContinuousLinearMap.star_eq_adjoint] at h3
  have e : (fun t => ContinuousLinearMap.adjoint (T.op (γ t))) = fun t => T.op (γ (-t)) :=
    funext fun t => by rw [← op_inv_eq_adjoint, hinv]
  rw [e] at h3
  rw [h3.unique h2, map_neg]

theorem dtau_adj (T : KType ε Λ) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    ContinuousLinearMap.adjoint (T.dτ X) = T.dτ Xᴴ := by
  obtain ⟨A, B, hA, hB, hX1, hX2⟩ := block_decomp hX
  rw [hX2, hX1]
  simp [map_add (f := _), map_neg, map_smul, LinearIsometryEquiv.map_smulₛₗ, dtau_skew T hA, dtau_skew T hB,
    Complex.conj_I]

lemma inK_conj (k : KG ε) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    inK ε (toMK k * A * toMK k⁻¹) := by
  have hk : toMK k ∈ unitaryGroup (Fin n) ℂ ∧ toMK k * Jm ε = Jm ε * toMK k := k.2
  have hk' : toMK k⁻¹ ∈ unitaryGroup (Fin n) ℂ ∧ toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹ := (k⁻¹).2
  have e : toMK k * toMK k⁻¹ = 1 := by
    unfold toMK toM
    simp
  have hu : (toMK k)ᴴ * toMK k = 1 := by
    have h1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    simpa [Matrix.star_eq_conjTranspose] using h1
  have hUV : (toMK k)ᴴ = toMK k⁻¹ := by
    calc (toMK k)ᴴ = (toMK k)ᴴ * (toMK k * toMK k⁻¹) := by rw [e, Matrix.mul_one]
      _ = toMK k⁻¹ := by rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
  have hV : (toMK k⁻¹)ᴴ = toMK k := by
    rw [← hUV, Matrix.conjTranspose_conjTranspose]
  have hUJ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, toMK k * (Jm ε * Y) = Jm ε * (toMK k * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, hk.2, Matrix.mul_assoc]
  have hVJ : toMK k⁻¹ * Jm ε = Jm ε * toMK k⁻¹ := hk'.2
  have hA1 := hA.1
  unfold inG at hA1
  have hAJ : ∀ Y : Matrix (Fin n) (Fin n) ℂ, Aᴴ * (Jm ε * Y) = -(Jm ε * (A * Y)) := by
    intro Y
    rw [← Matrix.mul_assoc, eq_neg_of_add_eq_zero_left hA1, Matrix.neg_mul, Matrix.mul_assoc]
  have hAc : ∀ Y : Matrix (Fin n) (Fin n) ℂ, A * (Jm ε * Y) = Jm ε * (A * Y) := by
    intro Y
    rw [← Matrix.mul_assoc, hA.2, Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · unfold inG
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hV, hUV]
    simp only [Matrix.mul_assoc, hVJ, hAJ, Matrix.mul_neg, hUJ, neg_add_cancel]
  · simp only [Matrix.mul_assoc, hVJ, hAc, hUJ]

lemma dtau_conj_inK (T : KType ε Λ) (k : KG ε) {A : Matrix (Fin n) (Fin n) ℂ} (hA : inK ε A) :
    T.op k * T.dτ A * T.op k⁻¹ = T.dτ (toMK k * A * toMK k⁻¹) := by
  obtain ⟨γ, -, hγ, -⟩ := exists_oneParam ε hA
  have h1 := ((T.hasDeriv A hA γ hγ).const_mul (T.op k)).mul_const (T.op k⁻¹)
  have h2 := T.hasDeriv _ (inK_conj k hA) (fun t => k * γ t * k⁻¹) (fun t => by
    have e : toMK (k * γ t * k⁻¹) = toMK k * toMK (γ t) * toMK k⁻¹ := rfl
    rw [e, hγ, show ((t : ℂ) • (toMK k * A * toMK k⁻¹)) = toMK k * ((t : ℂ) • A) * toMK k⁻¹ by
      rw [Matrix.mul_smul, Matrix.smul_mul]]
    exact (Matrix.exp_units_conj ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) _).symm)
  have e : (fun t => T.op (k * γ t * k⁻¹)) = fun t => T.op k * T.op (γ t) * T.op k⁻¹ :=
    funext fun t => by simp only [KType.op, map_mul]; rfl
  rw [e] at h2
  exact h1.unique h2

theorem dtau_conj (T : KType ε Λ) (k : KG ε) {X : Matrix (Fin n) (Fin n) ℂ} (hX : IsBlock ε X) :
    T.op k * T.dτ X * T.op k⁻¹ = T.dτ (toMK k * X * toMK k⁻¹) := by
  obtain ⟨A, B, hA, hB, hX1, -⟩ := block_decomp hX
  subst hX1
  have e1 : toMK k * (A + Complex.I • B) * toMK k⁻¹ =
      toMK k * A * toMK k⁻¹ + Complex.I • (toMK k * B * toMK k⁻¹) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e1, map_add (f := _), map_smul, map_add (f := _), map_smul, ← dtau_conj_inK T k hA, ← dtau_conj_inK T k hB,
    mul_add, add_mul, mul_smul_comm, smul_mul_assoc]

theorem hasDerivAt_op (T : KType ε Λ) (k : KG ε) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inK ε Y) (γ : ℝ → KG ε)
    (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Y)) :
    HasDerivAt (fun t => T.op (k * γ t)) (T.op k * T.dτ Y) 0 := by
  have h1 := T.hasDeriv Y hY γ hγ
  have e : (fun t => T.op (k * γ t)) = fun t => T.op k * T.op (γ t) := by
    funext t
    exact congrArg Subtype.val (map_mul T.τ k (γ t))
  rw [e]
  exact h1.const_mul (T.op k)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IntegrVGA
noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

variable {ε : Fin n → Bool}

lemma exists_signVG (ε : Fin n → Bool) : ∃ s : Bool, Fintype.card (SgIxV ε s) = q0 ε := by
  unfold q0
  rcases le_total (pOf ε) (qOf ε) with h | h
  · refine ⟨true, ?_⟩
    rw [min_eq_left h]
    first
    | (rw [pOf, Fintype.card_subtype])
    | simp [SgIxV, pOf, Fintype.card_subtype]
  · refine ⟨false, ?_⟩
    rw [min_eq_right h]
    first
    | (rw [qOf, Fintype.card_subtype])
    | simp [SgIxV, qOf, Fintype.card_subtype]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.LocalA
noncomputable section

open Matrix Filter Topology

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LogL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma lcA_exp_strict :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
  first
  | exact hasStrictFDerivAt_exp_zero
  | exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero)
  | (rw [ContinuousLinearEquiv.coe_refl]; exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ))

lemma exists_local_matrix_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  have hf := lcA_exp_strict (n := n)
  refine ⟨hf.localInverse _ _ _, ?_, ?_, hf.eventually_left_inverse⟩
  · have h1 := hf.localInverse_continuousAt.tendsto
    have h2 := hf.localInverse_apply_image
    rw [NormedSpace.exp_zero] at h1 h2
    rwa [h2] at h1
  · have h := hf.eventually_right_inverse
    rwa [NormedSpace.exp_zero] at h

lemma continuous_matrix_exp_alt :
    Continuous (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) := by
  first
  | exact NormedSpace.exp_continuous
  | exact NormedSpace.exp_continuous (𝕂 := ℂ)
  | exact exp_continuous

end LogL

lemma lcA_exists_log : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ (∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), NormedSpace.exp (ℓ k) = k) ∧
      (∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ), ℓ (NormedSpace.exp Y) = Y) := by
  first
  | exact exists_local_matrix_log
  | exact exists_local_matrix_log (n := n)

lemma lcA_exists_klog (ε : Fin n → Bool) : ∃ ℓ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ,
    Tendsto ℓ (𝓝 1) (𝓝 0) ∧ ∀ᶠ k in 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ),
      k ∈ Kset ε → inK ε (ℓ k) ∧ NormedSpace.exp (ℓ k) = k := by
  obtain ⟨L, hL1, hL2, hL3⟩ := lcA_exists_log (n := n)
  refine ⟨L, hL1, ?_⟩
  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJinv : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hA : Tendsto (fun k => (L k)ᴴ) (𝓝 1) (𝓝 0) := by
    have h := hL1.star
    rw [star_zero] at h
    exact h
  have hB : Tendsto (fun k => -(L k)) (𝓝 1) (𝓝 0) := by
    have h := hL1.neg
    rw [neg_zero] at h
    exact h
  have hC : Tendsto (fun k => Jm ε * L k * Jm ε) (𝓝 1) (𝓝 0) := by
    have h := (hL1.const_mul (Jm ε)).mul_const (Jm ε)
    rw [mul_zero, zero_mul] at h
    exact h
  filter_upwards [hL2, hA.eventually hL3, hB.eventually hL3, hC.eventually hL3] with k h2 hA' hB' hC' hk
  have hk' : k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ k * Jm ε = Jm ε * k := hk
  have hkk : kᴴ * k = 1 := by
    have h := hk'.1
    rw [Matrix.mem_unitaryGroup_iff'] at h
    exact h
  have e1 : NormedSpace.exp ((L k)ᴴ) = kᴴ := by rw [Matrix.exp_conjTranspose, h2]
  have e2 : NormedSpace.exp (-(L k)) = kᴴ := by
    rw [Matrix.exp_neg, h2]
    exact Matrix.inv_eq_left_inv hkk
  have hstar : (L k)ᴴ = -(L k) := by
    rw [← hA', e1, ← e2, hB']
  have e3 : NormedSpace.exp (Jm ε * L k * Jm ε) = NormedSpace.exp (L k) := by
    have h := Matrix.exp_conj (Jm ε) (L k) hJu
    rw [hJinv] at h
    rw [h, h2, mul_assoc, hk'.2, ← mul_assoc, hJJ, one_mul]
  have e4 : Jm ε * L k * Jm ε = L k := by
    rw [← hC', e3, h2]
  have hcomm : L k * Jm ε = Jm ε * L k := by
    calc L k * Jm ε = Jm ε * L k * Jm ε * Jm ε := by rw [e4]
      _ = Jm ε * L k := by rw [mul_assoc, hJJ, mul_one]
  refine ⟨⟨?_, hcomm⟩, h2⟩
  show (L k)ᴴ * Jm ε + Jm ε * L k = 0
  rw [hstar, neg_mul, ← hcomm]
  first
  | exact neg_add_cancel _
  | simp

open scoped Matrix.Norms.L2Operator in
lemma lcA_polarL_continuousOn (ε : Fin n → Bool) :
    ContinuousOn (PolarDecomposition.polar_L (n := n)) {g | inUJ ε g} := by
  have h : ContinuousOn (fun g : Matrix (Fin n) (Fin n) ℂ => CFC.log (gᴴ * g)) {g | inUJ ε g} := by
    refine CFC.continuousOn_log.comp (by fun_prop) ?_
    intro g hg
    obtain ⟨hsa, hu, -⟩ := PolarDecomposition.polar_isSelfAdjoint_isUnit_spectrum_pos hg
    exact ⟨hsa, hu⟩
  exact h.const_smul (1 / 2 : ℝ)

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ByParts
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem kByParts {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (ε : Fin n → Bool) (F D : KG ε → E) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inK ε Z) (γ : ℝ → KG ε)
    (hγ : ∀ t, toMK (γ t) = NormedSpace.exp ((t : ℂ) • Z)) (hF : Continuous F) (hD : Continuous D)
    (hder : ∀ k, HasDerivAt (fun t => F (k * γ t)) (D k) 0) :
    ∫ k, D k ∂(muK ε) = 0 := by
  haveI := muK_rightInvariant ε
  haveI := compactSpace_KG ε
  obtain ⟨γ', -, hγ', hadd'⟩ := exists_oneParam ε hZ
  have hinj : ∀ a b : KG ε, toMK a = toMK b → a = b := by
    intro a b h
    exact Subtype.ext (Subtype.ext (Units.ext h))
  have hγγ : ∀ t, γ t = γ' t := fun t => hinj _ _ (by rw [hγ, hγ'])
  have hadd : ∀ s t, γ (s + t) = γ s * γ t := by
    intro s t
    rw [hγγ, hγγ, hγγ, hadd']
  have h0 : γ 0 = 1 := by
    have h00 := hadd 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (a := γ 0) (by rw [mul_one]; exact h00.symm)

  have hderiv : ∀ k t, HasDerivAt (fun u => F (k * γ u)) (D (k * γ t)) t := by
    intro k t
    have h1 := hder (k * γ t)
    have h2 : (fun s => F (k * γ t * γ s)) = fun s => F (k * γ (t + s)) := by
      funext s
      rw [hadd, mul_assoc]
    rw [h2] at h1
    have h3 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact h1)
    have h4 : (fun x => F (k * γ (t + (x - t)))) = fun u => F (k * γ u) := by
      funext x
      rw [show t + (x - t) = x by ring]
    rw [h4] at h3
    exact h3
  obtain ⟨C, hC⟩ : ∃ C, ∀ k, ‖D k‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_range hD.norm).bddAbove
    exact ⟨C, fun k => hC ⟨k, rfl⟩⟩
  have hFm : ∀ t, Continuous fun k : KG ε => F (k * γ t) := fun t =>
    hF.comp (continuous_mul_const _)
  have hDm : Continuous fun k : KG ε => D (k * γ 0) := hD.comp (continuous_mul_const _)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := muK ε)
    (F := fun t k => F (k * γ t)) (F' := fun t k => D (k * γ t)) (x₀ := (0 : ℝ))
    (bound := fun _ => C) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun t =>
      ((hFm t).stronglyMeasurable_of_hasCompactSupport (isClosed_tsupport _).isCompact).aestronglyMeasurable)
    ((hFm 0).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact)
    ((hDm.stronglyMeasurable_of_hasCompactSupport (isClosed_tsupport _).isCompact).aestronglyMeasurable)
    (ae_of_all _ fun k t _ => hC _) (integrable_const C)
    (ae_of_all _ fun k t _ => hderiv k t)
  have key2 : HasDerivAt (fun t => ∫ k, F (k * γ t) ∂(muK ε)) (∫ k, D (k * γ 0) ∂(muK ε)) 0 :=
    key.2
  have hconst : (fun t => ∫ k, F (k * γ t) ∂(muK ε)) = fun _ => ∫ k, F k ∂(muK ε) := by
    funext t
    exact integral_mul_right_eq_self (fun k => F k) (γ t)
  rw [hconst] at key2
  have huniq := key2.unique (hasDerivAt_const (0 : ℝ) (∫ k, F k ∂(muK ε)))
  simpa [h0] using huniq

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IdThmA
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ}

namespace IdA

lemma isOpen_omega : IsOpen (OmegaSet n) := by
  have e : OmegaSet n = ⋂ i : Fin n, {z | lead ((i : ℕ) + 1) z ≠ 0} := by
    ext z
    simp [OmegaSet]
  rw [e]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_ne_fun (contDiff_lead (m := 0) _).continuous continuous_const

lemma continuous_toMK : Continuous fun k : KG ε => toMK k :=
  (continuous_toM ε).comp continuous_subtype_val

lemma continuous_toMK_inv : Continuous fun k : KG ε => toMK k⁻¹ :=
  continuous_toMK.comp continuous_inv

lemma continuous_P (T : KType ε Λ) : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ := by
  have h : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  exact (h.mul continuous_const).mul (h.comp continuous_inv)

lemma continuous_cline (a b : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun p : ℂ × KG ε => toMK p.2⁻¹ * (a + p.1 • b) * toMK p.2 :=
  ((continuous_toMK_inv.comp continuous_snd).matrix_mul
    (continuous_const.add (continuous_fst.smul continuous_const))).matrix_mul
    (continuous_toMK.comp continuous_snd)

lemma cline_eq (k : KG ε) (a b : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    toMK k⁻¹ * (a + s • b) * toMK k = toMK k⁻¹ * a * toMK k + s • (toMK k⁻¹ * b * toMK k) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma hasDerivAt_cline (k : KG ε) (a b : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) :
    HasDerivAt (fun s : ℂ => toMK k⁻¹ * (a + s • b) * toMK k) (toMK k⁻¹ * b * toMK k) s := by
  have h := ((hasDerivAt_id s).smul_const (toMK k⁻¹ * b * toMK k)).const_add (toMK k⁻¹ * a * toMK k)
  simp only [id, one_smul] at h
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => cline_eq k a b s)

lemma hasDerivAt_intK [CompactSpace (KG ε)] (T : KType ε Λ) (F F' : ℂ → KG ε → (T.V →L[ℂ] T.V))
    {S : Set ℂ} (hS : IsOpen S)
    (hF : ContinuousOn (fun p : ℂ × KG ε => F p.1 p.2) (S ×ˢ Set.univ))
    (hF' : ContinuousOn (fun p : ℂ × KG ε => F' p.1 p.2) (S ×ˢ Set.univ))
    (hd : ∀ s ∈ S, ∀ k, HasDerivAt (fun s => F s k) (F' s k) s) {s0 : ℂ} (hs0 : s0 ∈ S) :
    HasDerivAt (fun s => ∫ k, F s k ∂(muK ε)) (∫ k, F' s0 k ∂(muK ε)) s0 := by
  have : IsFiniteMeasureOnCompacts (muK ε) := by unfold muK; infer_instance
  have : IsFiniteMeasure (muK ε) := inferInstance
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS s0 hs0
  have hcl : Metric.closedBall s0 (r / 2) ⊆ S :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hball
  have hK : IsCompact (Metric.closedBall s0 (r / 2) ×ˢ (Set.univ : Set (KG ε))) :=
    (isCompact_closedBall s0 _).prod isCompact_univ
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hF'.mono (Set.prod_mono hcl le_rfl))
  have hin : ∀ s ∈ Metric.ball s0 (r / 2), s ∈ S := fun s hs => hcl (Metric.ball_subset_closedBall hs)
  have hc : ∀ s ∈ S, Continuous (F s) := fun s hs =>
    hF.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs, trivial⟩
  have hc' : Continuous (F' s0) :=
    hF'.comp_continuous (continuous_const.prodMk continuous_id) fun _ => ⟨hs0, trivial⟩
  have hi : Integrable (F s0) (muK ε) :=
    integrableOn_univ.mp ((hc s0 hs0).continuousOn.integrableOn_compact isCompact_univ)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => C)
    (Metric.ball_mem_nhds s0 (half_pos hr))
    (Filter.eventually_of_mem (Metric.ball_mem_nhds s0 (half_pos hr))
      fun s hs => (hc s (hin s hs)).aestronglyMeasurable)
    hi hc'.aestronglyMeasurable
    (Filter.Eventually.of_forall fun k s hs => hC (s, k) ⟨Metric.ball_subset_closedBall hs, trivial⟩)
    (integrable_const C)
    (Filter.Eventually.of_forall fun k s hs => hd s (hin s hs) k)).2

def dPhi2 (μ : Fin n → ℤ) (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  fderiv ℂ (PhiM μ) p.1 p.2

lemma contDiffAt_dPhi2 (μ : Fin n → ℤ) {p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ}
    (hp : p.1 ∈ OmegaSet n) : ContDiffAt ℂ 1 (dPhi2 μ) p := by
  have hf : ContDiffAt ℂ 2 (Function.uncurry fun (_ : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ)
      (y : Matrix (Fin n) (Fin n) ℂ) => PhiM μ y) (p, p.1) :=
    (contDiffAt_phiM μ hp (m := 2)).comp (p, p.1) contDiffAt_snd
  exact (hf.fderiv contDiffAt_fst (by norm_num)).clm_apply contDiffAt_snd

lemma continuousOn_dPhi2 (μ : Fin n → ℤ) : ContinuousOn (dPhi2 μ) (OmegaSet n ×ˢ Set.univ) :=
  fun p hp => (contDiffAt_dPhi2 μ hp.1).continuousAt.continuousWithinAt

lemma continuousOn_fderiv_dPhi2 (μ : Fin n → ℤ) :
    ContinuousOn (fderiv ℂ (dPhi2 μ)) (OmegaSet n ×ˢ Set.univ) :=
  ContDiffOn.continuousOn_fderiv_of_isOpen (fun p hp => (contDiffAt_dPhi2 μ hp.1).contDiffWithinAt)
    (isOpen_omega.prod isOpen_univ) le_rfl

end IdA

theorem line_int_differentiableAt (T : KType ε Λ) (μ : Fin n → ℤ) {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hUo : IsOpen U) (hU : ∀ z ∈ U, ∀ k : KG ε, toMK k⁻¹ * z * toMK k ∈ OmegaSet n)
    (a₀ a₁ b₀ b₁ : Matrix (Fin n) (Fin n) ℂ) {s₀ : ℂ} (hs₀ : a₀ + s₀ • a₁ ∈ U) :
    DifferentiableAt ℂ (fun s : ℂ => ∫ k, IdA.dPhi2 μ (toMK k⁻¹ * (a₀ + s • a₁) * toMK k,
      toMK k⁻¹ * (b₀ + s • b₁) * toMK k) • (T.op k * projW T * T.op k⁻¹) ∂(muK ε)) s₀ := by
  have := compactSpace_KG ε
  have hS : IsOpen ((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) :=
    hUo.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have hγ : Continuous fun p : ℂ × KG ε =>
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) :=
    (IdA.continuous_cline a₀ a₁).prodMk (IdA.continuous_cline b₀ b₁)
  have hmaps : Set.MapsTo (fun p : ℂ × KG ε =>
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) (OmegaSet n ×ˢ Set.univ) :=
    fun p hp => ⟨hU _ hp.1 p.2, trivial⟩
  have hP : ContinuousOn (fun p : ℂ × KG ε => T.op p.2 * projW T * T.op p.2⁻¹)
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    ((IdA.continuous_P T).comp continuous_snd).continuousOn
  have hd1 : Continuous fun p : ℂ × KG ε => (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2) :=
    (((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (IdA.continuous_toMK.comp continuous_snd)).prodMk
    (((IdA.continuous_toMK_inv.comp continuous_snd).matrix_mul continuous_const).matrix_mul
      (IdA.continuous_toMK.comp continuous_snd))
  have hF : ContinuousOn (fun p : ℂ × KG ε => IdA.dPhi2 μ (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2,
      toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    ((IdA.continuousOn_dPhi2 μ).comp hγ.continuousOn hmaps).smul hP
  have hF' : ContinuousOn (fun p : ℂ × KG ε => fderiv ℂ (IdA.dPhi2 μ)
      (toMK p.2⁻¹ * (a₀ + p.1 • a₁) * toMK p.2, toMK p.2⁻¹ * (b₀ + p.1 • b₁) * toMK p.2)
      (toMK p.2⁻¹ * a₁ * toMK p.2, toMK p.2⁻¹ * b₁ * toMK p.2) • (T.op p.2 * projW T * T.op p.2⁻¹))
      (((fun s : ℂ => a₀ + s • a₁) ⁻¹' U) ×ˢ Set.univ) :=
    (((IdA.continuousOn_fderiv_dPhi2 μ).comp hγ.continuousOn hmaps).clm_apply hd1.continuousOn).smul hP
  have hd : ∀ s ∈ (fun s : ℂ => a₀ + s • a₁) ⁻¹' U, ∀ k : KG ε, HasDerivAt
      (fun s => IdA.dPhi2 μ (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k) •
        (T.op k * projW T * T.op k⁻¹))
      (fderiv ℂ (IdA.dPhi2 μ) (toMK k⁻¹ * (a₀ + s • a₁) * toMK k, toMK k⁻¹ * (b₀ + s • b₁) * toMK k)
        (toMK k⁻¹ * a₁ * toMK k, toMK k⁻¹ * b₁ * toMK k) • (T.op k * projW T * T.op k⁻¹)) s := by
    intro s hs k
    have hq := (IdA.hasDerivAt_cline k a₀ a₁ s).prodMk (IdA.hasDerivAt_cline k b₀ b₁ s)
    have hD := ((IdA.contDiffAt_dPhi2 μ (p := (toMK k⁻¹ * (a₀ + s • a₁) * toMK k,
      toMK k⁻¹ * (b₀ + s • b₁) * toMK k)) (hU _ hs k)).differentiableAt one_ne_zero).hasFDerivAt
    exact (hD.comp_hasDerivAt s hq).smul_const (T.op k * projW T * T.op k⁻¹)
  exact (IdA.hasDerivAt_intK T _ _ hS hF hF' hd hs₀).differentiableAt

end ReciprocityTheory.ChartRestriction.DS.S7
end
end
