module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatBoxDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlCSurjectiveAndLinearIndependentBLie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFunctionTwistedCoinvariantRank

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankFiltrationStep
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankBoxFunctionStable
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientIntegralRowReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientIntegralRowReduction
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem exists_KO_row_zero_of_rank_lt (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
    (X : Matrix A D k) (hX : X.rank < Fintype.card A) :
    ∃ g ∈ GlobalTheory.SplitWeil.KO k A, ∃ i₀ : A, ∀ j, (g.val * X) i₀ j = 0 := by

  have hdep : ¬ LinearIndependent k X.row := by
    intro h
    rw [linearIndependent_iff_card_eq_finrank_span] at h
    rw [rank_eq_finrank_span_row] at hX
    exact (lt_irrefl _) (h ▸ hX)
  obtain ⟨c, hc, i₁, hi₁⟩ := Fintype.not_linearIndependent_iff.1 hdep
  have hcj : ∀ j, ∑ i, c i * X i j = 0 := by
    intro j
    have := congrFun hc j
    simpa [Finset.sum_apply, Matrix.row] using this

  obtain ⟨i₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => valuation k (c i))
    ⟨i₁, Finset.mem_univ _⟩
  have hc0 : c i₀ ≠ 0 := by
    intro h0
    have := hmax i₁ (Finset.mem_univ _)
    rw [h0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact hi₁ this
  set c' : A → k := fun i => c i / c i₀ with hc'
  have hc'int : ∀ i, c' i ∈ 𝒪[k] := by
    intro i
    rw [Valuation.mem_integer_iff, hc', map_div₀]
    have hpos : 0 < valuation k (c i₀) := by
      rw [zero_lt_iff]; exact (Valuation.ne_zero_iff _).2 hc0
    exact (div_le_one₀ hpos).2 (hmax i (Finset.mem_univ _))
  have hc'0 : c' i₀ = 1 := div_self hc0

  let E : Matrix A A k := Matrix.of fun i j => if i = i₀ ∧ j ≠ i₀ then c' j else 0
  have hEE : E * E = 0 := by
    ext i j
    simp only [Matrix.mul_apply, E, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = i₀
    · simp [hl]
    · simp [hl]
  have hEint : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [E, Matrix.of_apply]
    split_ifs
    · exact hc'int j
    · exact zero_mem _
  have h1int : ∀ i j, (1 : Matrix A A k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  let g : GL A k := ⟨1 + E, 1 - E, by rw [add_mul, one_mul, mul_sub, mul_one, hEE]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, hEE]; abel⟩
  refine ⟨g, ?_, i₀, fun j => ?_⟩
  · rw [GlobalTheory.SplitFlip.mem_KO_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      exact add_mem (h1int i j) (hEint i j)
    · show (1 - E) i j ∈ 𝒪[k]
      exact sub_mem (h1int i j) (hEint i j)
  · show (((1 : Matrix A A k) + E) * X) i₀ j = 0
    have hrow : ∀ l, (1 + E) i₀ l = c' l := by
      intro l
      by_cases hl : l = i₀
      · subst hl; simp [E, hc'0]
      · simp [E, hl, Matrix.one_apply, Ne.symm hl]
    rw [Matrix.mul_apply]
    simp_rw [hrow, hc', div_mul_eq_mul_div, ← Finset.sum_div, hcj j, zero_div]

end GlobalTheory.RankCoinv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankDeficientIntegralRowReductionStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_deficient_integral_row_reduction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (X : Matrix A D k), X.rank < Fintype.card A → ∃ g ∈ GlobalTheory.SplitWeil.KO k A, ∃ i₀ : A, ∀ j, (g.val * X) i₀ j = 0 := by
  first | exact @GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt | exact GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt | (intros; apply GlobalTheory.RankCoinv.exists_KO_row_zero_of_rank_lt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRightInverseNormalization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRightInverseNormalization
open ValuativeRel Matrix

namespace GlobalTheory

theorem frame_normalise_integral (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (s : ℕ)
    (Y : Matrix (Fin s) D k) (Q' : Matrix D (Fin s) k) (hYQ : Y * Q' = 1) :
    ∃ (h : Matrix (Fin s) (Fin s) k) (Q : Matrix D (Fin s) k),
      (∀ i j, (h * Y) i j ∈ 𝒪[k]) ∧ (∀ i j, Q i j ∈ 𝒪[k]) ∧ h * Y * Q = 1 := by
  classical

  have key : (Y * Q').det = ∑ p : Fin s → D, (∏ i, Q' (p i) i) * (Y.submatrix id p).det := by
    simp only [det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
      submatrix_apply, id]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_mul_distrib]; ring
  rw [hYQ, det_one] at key
  obtain ⟨p₀, -, hp₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero (key ▸ one_ne_zero)
  haveI : Nonempty (Fin s → D) := ⟨p₀⟩
  obtain ⟨κ, hκ⟩ := Finite.exists_max (fun p : Fin s → D => valuation k (Y.submatrix id p).det)
  have hne : (Y.submatrix id κ).det ≠ 0 := by
    intro h0
    have := hκ p₀
    rw [h0, map_zero] at this
    exact right_ne_zero_of_mul hp₀ ((valuation k).zero_iff.mp (le_antisymm this zero_le'))
  set h := (Y.submatrix id κ)⁻¹ with hh
  have hsub : ∀ p : Fin s → D, (h * Y).submatrix id p = h * Y.submatrix id p := by
    intro p; ext r c; simp [Matrix.mul_apply]
  have hone : (h * Y).submatrix id κ = 1 := by
    rw [hsub, hh]
    exact nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hne)
  refine ⟨h, Matrix.of fun j l => if j = κ l then 1 else 0, ?_, ?_, ?_⟩
  · intro i j
    have e : (h * Y) i j = ((h * Y).submatrix id (Function.update κ i j)).det := by
      have : (h * Y).submatrix id (Function.update κ i j) =
          (1 : Matrix (Fin s) (Fin s) k).updateCol i (fun r => (h * Y) r j) := by
        ext r c
        by_cases hc : c = i
        · subst hc; simp
        · rw [updateCol_ne hc, ← hone]
          simp [Function.update_of_ne hc]
      rw [this, ← cramer_apply, cramer_one]; rfl
    rw [Valuation.mem_integer_iff, e, hsub, det_mul, hh, det_nonsing_inv, Ring.inverse_eq_inv',
      map_mul, map_inv₀]
    have hpos : 0 < valuation k (Y.submatrix id κ).det :=
      lt_of_le_of_ne zero_le' (Ne.symm ((valuation k).ne_zero_iff.mpr hne))
    rw [mul_comm, ← div_eq_mul_inv, div_le_one₀ hpos]
    exact hκ _
  · intro i j
    rw [Matrix.of_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · have : h * Y * (Matrix.of fun j l => if j = κ l then (1 : k) else 0 : Matrix D (Fin s) k) =
        (h * Y).submatrix id κ := by
      ext r l; simp [Matrix.mul_apply]
    rw [this, hone]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRightInverseNormalizationStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_right_inverse_normalization : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (D : Type) [Fintype D] [DecidableEq D] (s : ℕ) (Y : Matrix (Fin s) D k) (Q' : Matrix D (Fin s) k), Y * Q' = 1 → ∃ (h : Matrix (Fin s) (Fin s) k) (Q : Matrix D (Fin s) k), (∀ i j, (h * Y) i j ∈ 𝒪[k]) ∧ (∀ i j, Q i j ∈ 𝒪[k]) ∧ h * Y * Q = 1 := by
  first | exact @GlobalTheory.frame_normalise_integral | exact GlobalTheory.frame_normalise_integral | (intros; apply GlobalTheory.frame_normalise_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankBoxFunctionStable
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.RankCoinv.Nbhd

section
variable {k : Type} [Field k] {Γ : Type*} [LinearOrderedCommMonoidWithZero Γ] (v : Valuation k Γ)
variable {X Y W : Type} [Fintype Y]

theorem val_mul_le {P : Matrix X Y k} {Z : Matrix Y W k} {s t : Γ} (hP : ∀ i a, v (P i a) ≤ s)
    (hZ : ∀ a j, v (Z a j) ≤ t) (i : X) (j : W) : v ((P * Z) i j) ≤ s * t := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun a _ => ?_
  rw [map_mul]; exact mul_le_mul' (hP i a) (hZ a j)
end

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_inv_pow (ϖ : kˣ) (c : ℕ) :
    valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) = (valuation k (ϖ : k))⁻¹ ^ c := by
  simp [Units.val_inv_eq_inv_val, map_inv₀, map_pow, inv_pow]

theorem exists_le_inv_pow {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) (x : k) :
    ∃ c : ℕ, valuation k x ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  by_cases h : valuation k x ≤ 1
  · exact ⟨0, by simpa using h⟩
  · have hx : x ≠ 0 := by rintro rfl; simp at h
    have h0 : 0 < valuation k x := zero_lt_iff.2 (by simpa using hx)
    have hy : valuation k x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      calc (valuation k x)⁻¹ = (valuation k x)⁻¹ * 1 := (mul_one _).symm
        _ ≤ (valuation k x)⁻¹ * valuation k x := mul_le_mul' le_rfl (le_of_not_ge h)
        _ = 1 := inv_mul_cancel₀ h0.ne'
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (R := 𝒪[k])
      (x := ⟨x⁻¹, hy⟩) (fun h' => hx (inv_eq_zero.1 (congrArg Subtype.val h'))) hϖ.irreducible
    refine ⟨n, ?_⟩
    have h1 : valuation k (algebraMap 𝒪[k] k u) = 1 :=
      (Valuation.integer.integers (valuation k)).one_of_isUnit u.isUnit
    have h2 : valuation k x⁻¹ = valuation k (ϖ : k) ^ n := by
      have := congrArg (fun y : 𝒪[k] => valuation k (y : k)) hu
      simp only [Subring.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow] at this
      rw [this]
      have h1' : valuation k ((u : 𝒪[k]) : k) = 1 := h1
      rw [h1', one_mul]
    rw [valuation_inv_pow, inv_pow, ← h2, map_inv₀, inv_inv]

theorem exists_bound {ϖ : kˣ} (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ) {R S : Type} [Fintype R] [Fintype S]
    (H : Matrix R S k) : ∃ c : ℕ, ∀ l i, valuation k (H l i) ≤ valuation k (((ϖ ^ c)⁻¹ : kˣ) : k) := by
  choose f hf using fun p : R × S => exists_le_inv_pow hϖ (H p.1 p.2)
  refine ⟨Finset.univ.sup f, fun l i => (hf (l, i)).trans ?_⟩
  rw [valuation_inv_pow, valuation_inv_pow]
  have hle : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  have h0 : valuation k (ϖ : k) ≠ 0 := by simp
  have h1 : 1 ≤ (valuation k (ϖ : k))⁻¹ :=
    calc (1 : _) = valuation k (ϖ : k) * (valuation k (ϖ : k))⁻¹ := (mul_inv_cancel₀ h0).symm
      _ ≤ 1 * (valuation k (ϖ : k))⁻¹ := mul_le_mul' hle le_rfl
      _ = _ := one_mul _
  exact pow_le_pow_right₀ h1 (Finset.le_sup (f := f) (Finset.mem_univ (l, i)))

theorem exists_int_inv_one_add {n : Type} [Fintype n] [DecidableEq n] (E : Matrix n n k)
    (hE : ∀ i j, valuation k (E i j) < 1) :
    ∃ N : Matrix n n k, (∀ i j, N i j ∈ 𝒪[k]) ∧ (1 + E) * N = 1 := by
  have hI : ∀ i j, (1 + E) i j ∈ 𝒪[k] := fun i j => by
    rw [Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ (hE i j).le
    rw [Matrix.one_apply]; split_ifs <;> simp
  have hEI : ∀ i j, E i j ∈ 𝒪[k] := fun i j => (Valuation.mem_integer_iff _ _).2 (hE i j).le
  let M : Matrix n n 𝒪[k] := fun i j => ⟨(1 + E) i j, hI i j⟩
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, map_apply]
    have : M i j - (1 : Matrix n n 𝒪[k]) i j = ⟨E i j, hEI i j⟩ := by
      apply Subtype.ext
      by_cases h : i = j <;> simp [M, Matrix.one_apply, h]
    have hm : M i j - (1 : Matrix n n 𝒪[k]) i j ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
      rw [this, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]
      exact hE i j
    have e2 : (IsLocalRing.residue 𝒪[k]) (M i j) = (IsLocalRing.residue 𝒪[k]) ((1 : Matrix n n 𝒪[k]) i j) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hm
    rw [e2]; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have hdet : IsUnit M.det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, hres, det_one]
    exact one_ne_zero
  refine ⟨(algebraMap 𝒪[k] k).mapMatrix M⁻¹, fun i j => (M⁻¹ i j).2, ?_⟩
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = 1 + E := rfl
  rw [← hM, ← map_mul, Matrix.mul_nonsing_inv M hdet, map_one]

end GlobalTheory.RankCoinv.Nbhd

namespace GlobalTheory.RankCoinv.Nbhd
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

theorem inv_mul_mem_box_iff {g : GL A k} (hg : g ∈ KO k A) (ϖ : kˣ) (C X : Matrix A D k) (m : ℕ) :
    (g⁻¹).val * X ∈ box ϖ C (fun _ => m) ↔ X ∈ box ϖ (g.val * C) (fun _ => m) := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff g).1 hg
  have h1' : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h1 i a)
  have h2' : ∀ i a, valuation k ((g⁻¹).val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (h2 i a)
  simp only [box, Set.mem_setOf_eq]
  constructor
  · intro hZ i j
    have e : X i j - (g.val * C) i j = (g.val * ((g⁻¹).val * X - C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h1' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)
  · intro hZ i j
    have e : ((g⁻¹).val * X) i j - C i j = ((g⁻¹).val * (X - g.val * C)) i j := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.sub_apply]
    rw [e]
    exact (val_mul_le (valuation k) h2' (fun a j => by rw [Matrix.sub_apply]; exact hZ a j) i j).trans_eq (one_mul _)

theorem omA_boxFn {g : GL A k} (hg : g ∈ KO k A) (ν β : kˣ →* ℂˣ) (ϖ : kˣ) (C : Matrix A D k) (m : ℕ) :
    ∃ s : ℂ, omA ν β g 1 (boxFn ϖ C (fun _ => m)) = s • boxFn ϖ (g.val * C) (fun _ => m) := by
  refine ⟨(((ν (gdet g))⁻¹ : ℂˣ) : ℂ) * apow (gdet g) (-(Fintype.card D : ℂ) / 2), funext fun X => ?_⟩
  rw [omA_one_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  by_cases h : X ∈ box ϖ (g.val * C) (fun _ => m)
  · simp only [boxFn]
    rw [Set.indicator_of_mem h, Set.indicator_of_mem ((inv_mul_mem_box_iff hg ϖ C X m).2 h)]
    rfl
  · simp only [boxFn]
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((inv_mul_mem_box_iff hg ϖ C X m).1 h'))]

end GlobalTheory.RankCoinv.Nbhd


open GlobalTheory.RankCoinv.Nbhd GlobalTheory.SplitFlip GlobalTheory.SplitWeil in
theorem GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hνϖ r X₀ hrank hr
  obtain ⟨g, hg, i₀, hi₀⟩ := GlobalTheory.T.rank_deficient_integral_row_reduction k A D X₀ (hrank ▸ hr)
  have hgint := (GlobalTheory.SplitFlip.mem_KO_iff g).1 hg
  have hg1 : ∀ i a, valuation k (g.val i a) ≤ 1 := fun i a => (Valuation.mem_integer_iff _ _).1 (hgint.1 i a)
  have hYr : (g.val * X₀).rank = r := by
    rw [← hrank]
    exact Matrix.rank_mul_eq_right_of_isUnit_det _ _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  obtain ⟨H₁, Q₁, hHQ⟩ : ∃ (H₁ : Matrix (Fin r) A k) (Q₁ : Matrix D (Fin r) k), H₁ * (g.val * X₀) * Q₁ = 1 := by
    rw [← hYr]; exact GlobalTheory.T.matrix_rank_normal_form k A D _
  let H₂ : Matrix (Fin r) A k := Matrix.of fun l i => if i = i₀ then 0 else H₁ l i
  have hH₂Y : H₂ * (g.val * X₀) = H₁ * (g.val * X₀) := by
    ext l j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [H₂, Matrix.of_apply]
    split_ifs with h
    · rw [h, hi₀ j, zero_mul, mul_zero]
    · rfl
  obtain ⟨h, Q₀, hhY, hQ₀, hhYQ⟩ := GlobalTheory.T.integral_right_inverse_normalization k D r (H₂ * (g.val * X₀)) Q₁ (by rw [hH₂Y, hHQ])
  let H := h * H₂
  have hHi₀ : ∀ l, H l i₀ = 0 := fun l => by simp [H, H₂, Matrix.mul_apply]
  obtain ⟨c, hc⟩ := exists_bound hϖ H
  refine ⟨c + 1, fun m hm C hC => ?_⟩
  have hϖ0 : valuation k (ϖ : k) ≠ 0 := by simp
  have hϖlt : valuation k (ϖ : k) < 1 := hϖ ▸ uniformizer_lt_one
  have hCX : ∀ a j, valuation k ((C - X₀) a j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun a j => by
    rw [Matrix.sub_apply]; simpa using hC a j
  have hgCX : ∀ i j, valuation k ((g.val * (C - X₀)) i j) ≤ valuation k (ϖ : k) ^ (c + 1) := fun i j => by
    simpa using val_mul_le (valuation k) hg1 hCX i j
  have hc' : ∀ l i, valuation k (H l i) ≤ (valuation k (ϖ : k))⁻¹ ^ c := fun l i => by
    rw [← valuation_inv_pow]; exact hc l i
  have hprod : (valuation k (ϖ : k))⁻¹ ^ c * valuation k (ϖ : k) ^ (c + 1) = valuation k (ϖ : k) := by
    rw [inv_pow, pow_succ, inv_mul_cancel_left₀ (pow_ne_zero _ hϖ0)]
  have hEb : ∀ l j, valuation k ((H * (g.val * (C - X₀))) l j) ≤ valuation k (ϖ : k) := fun l j => by
    rw [← hprod]; exact val_mul_le (valuation k) hc' hgCX l j
  have hsplit : g.val * C = g.val * X₀ + g.val * (C - X₀) := by rw [Matrix.mul_sub]; abel
  have hHY : H * (g.val * X₀) = h * (H₂ * (g.val * X₀)) := Matrix.mul_assoc _ _ _
  have hHC : H * (g.val * C) = H * (g.val * X₀) + H * (g.val * (C - X₀)) := by rw [hsplit, Matrix.mul_add]
  have hHCint : ∀ l j, (H * (g.val * C)) l j ∈ 𝒪[k] := fun l j => by
    rw [hHC, Valuation.mem_integer_iff, Matrix.add_apply]
    refine Valuation.map_add_le _ ?_ ((hEb l j).trans hϖlt.le)
    rw [hHY]; exact hhY l j
  have hQ₀' : ∀ j l, valuation k (Q₀ j l) ≤ 1 := fun j l => (Valuation.mem_integer_iff _ _).1 (hQ₀ j l)
  set E := H * (g.val * (C - X₀)) * Q₀ with hE
  have hEv : ∀ i j, valuation k (E i j) < 1 := fun i j =>
    lt_of_le_of_lt (by simpa using val_mul_le (valuation k) hEb hQ₀' i j) hϖlt
  have hHCQ : H * (g.val * C) * Q₀ = 1 + E := by
    rw [hHC, Matrix.add_mul, hHY, hhYQ]
  obtain ⟨N, hN, hN1⟩ := exists_int_inv_one_add E hEv
  have hN' : ∀ i j, valuation k (N i j) ≤ 1 := fun i j => (Valuation.mem_integer_iff _ _).1 (hN i j)
  have hQint : ∀ j l, (Q₀ * N) j l ∈ 𝒪[k] := fun j l => by
    rw [Valuation.mem_integer_iff]; simpa using val_mul_le (valuation k) hQ₀' hN' j l
  have hHCQ' : H * (g.val * C) * (Q₀ * N) = 1 := by rw [← Matrix.mul_assoc, hHCQ, hN1]
  have hrow : ∀ j, valuation k ((g.val * C) i₀ j) ≤ valuation k ((ϖ ^ (c + 1) : kˣ) : k) := fun j => by
    rw [hsplit, Matrix.add_apply, hi₀ j, zero_add]; simpa using hgCX i₀ j
  have hmem := GlobalTheory.T.box_function_twisted_coinvariant_rank k A D ϖ hϖ ν β hν hνϖ i₀ r c m (g.val * C) H (Q₀ * N) hHi₀ hc (by omega)
    hHCint hQint hHCQ' hrow
  obtain ⟨s, hs⟩ := omA_boxFn hg ν β ϖ C m
  have hΦ := boxFn_mem_SB ϖ C (fun _ => m)
  have h1 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    rw [hs]; exact Submodule.smul_mem _ _ hmem
  have h2 : omA ν β g 1 (boxFn ϖ C (fun _ => m)) - boxFn ϖ C (fun _ => m) ∈ lowRank (r + 1) ⊔ twistSpan ν β :=
    Submodule.mem_sup_right (sub_mem_twistSpan ν β g hΦ)
  simpa using sub_mem h1 h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankBoxFunctionStableStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_rank_box_function_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ) (X₀ : Matrix A D k), X₀.rank = r → r < Fintype.card A → ∃ m₀ : ℕ, ∀ m ≥ m₀, ∀ C ∈ GlobalTheory.RankCoinv.box ϖ X₀ (fun _ => m₀), GlobalTheory.RankCoinv.boxFn ϖ C (fun _ => m) ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan | exact GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan | (intros; apply GlobalTheory.RankCoinv.exists_boxFn_mem_lowRank_sup_twistSpan <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankFiltrationStep
open ValuativeRel Matrix

namespace GlobalTheory.RankCoinv

theorem mem_lowRank_succ_sup_twistSpan_of_mem_lowRank : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ), r < Fintype.card A → ∀ Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix A D k → ℂ)), Φ ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  intro k _ _ _ _ A D _ _ _ _ ϖ hϖ ν β hν hνϖ r hr Φ hΦ
  obtain ⟨⟨hlc, hcs⟩, hvan⟩ := hΦ
  classical

  have hSclosed : IsClosed {X : Matrix A D k | Φ X ≠ 0} := by
    have : {X : Matrix A D k | Φ X ≠ 0} = (Φ ⁻¹' {0})ᶜ := by ext; simp
    rw [this]; exact (hlc.isOpen_fiber 0).isClosed_compl
  have hScpt : IsCompact {X : Matrix A D k | Φ X ≠ 0} :=
    hcs.isCompact.of_isClosed_subset hSclosed (fun X hX => subset_tsupport Φ hX)

  let m₀ : Matrix A D k → ℕ := fun X =>
    if h : X.rank = r then Classical.choose (GlobalTheory.T.low_rank_box_function_stable k A D ϖ hϖ ν β hν hνϖ r X h hr) else 0
  have hm₀ : ∀ X : Matrix A D k, ∀ h : X.rank = r, ∀ m ≥ m₀ X, ∀ C ∈ box ϖ X (fun _ => m₀ X),
      boxFn ϖ C (fun _ => m) ∈ lowRank (r + 1) ⊔ twistSpan ν β := by
    intro X h
    have := Classical.choose_spec (GlobalTheory.T.low_rank_box_function_stable k A D ϖ hϖ ν β hν hνϖ r X h hr)
    simpa [m₀, h] using this
  let U : Matrix A D k → Set (Matrix A D k) := fun X =>
    if X.rank ≤ r then box ϖ X (fun _ => m₀ X) else {Y | r + 1 ≤ Y.rank}
  have hU : ∀ X ∈ {X : Matrix A D k | Φ X ≠ 0}, U X ∈ nhds X := by
    intro X _
    by_cases h : X.rank ≤ r
    · simp only [U, h, if_true]
      refine (isClopen_box ϖ X _).isOpen.mem_nhds ?_
      intro i j; simp
    · simp only [U, h, if_false]
      exact (GlobalTheory.T.isOpen_rank_ge k A D (r + 1)).mem_nhds (by simp only [Set.mem_setOf_eq]; omega)
  obtain ⟨t, htS, hcover⟩ := hScpt.elim_nhds_subcover U hU
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.schwartz_bruhat_box_decomposition k A D ϖ hϖ Φ ⟨hlc, hcs⟩
  obtain ⟨s, hdec, hconst⟩ := hm₁ (max m₁ (t.sup m₀)) (le_max_left _ _)
  set m := max m₁ (t.sup m₀) with hm
  rw [hdec]
  refine Submodule.sum_mem _ fun c hc => ?_
  by_cases hex : ∃ X₂ ∈ box ϖ c (fun _ => m), X₂.rank ≤ r
  · obtain ⟨X₂, hX₂, hX₂r⟩ := hex
    by_cases hc0 : Φ c = 0
    · rw [hc0, zero_smul]; exact zero_mem _
    refine Submodule.smul_mem _ _ ?_
    have hX₂S : Φ X₂ ≠ 0 := by rw [hconst c hc X₂ hX₂]; exact hc0
    have hX₂eq : X₂.rank = r := by
      by_contra hne
      exact hX₂S (hvan X₂ (lt_of_le_of_ne hX₂r hne))
    obtain ⟨x, hxt, hxU⟩ := Set.mem_iUnion₂.1 (hcover hX₂S)
    have hxS : Φ x ≠ 0 := htS x hxt
    by_cases hxr : x.rank ≤ r
    · simp only [U, hxr, if_true] at hxU
      have hxeq : x.rank = r := by
        by_contra hne
        exact hxS (hvan x (lt_of_le_of_ne hxr hne))
      have hmx : m₀ x ≤ m := le_trans (Finset.le_sup (f := m₀) hxt) (le_max_right _ _)
      rw [← boxFn_eq_of_mem hX₂]
      exact hm₀ x hxeq m hmx X₂ hxU
    · simp only [U, hxr, if_false, Set.mem_setOf_eq] at hxU
      omega
  · push_neg at hex
    refine Submodule.smul_mem _ _ (Submodule.mem_sup_left ?_)
    refine ⟨boxFn_mem_SB ϖ c _, fun Y hY => ?_⟩
    have hYn : Y ∉ box ϖ c (fun _ => m) := fun hYb => by
      have := hex Y hYb; omega
    simp [boxFn, Set.indicator_of_notMem hYn]

end GlobalTheory.RankCoinv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowRankFiltrationStepStatement
open ValuativeRel Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_rank_filtration_step : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (ν β : kˣ →* ℂˣ), (∀ x, ‖(ν x : ℂ)‖ = 1) → ν ϖ ≠ 1 → ∀ (r : ℕ), r < Fintype.card A → ∀ Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix A D k → ℂ)), Φ ∈ GlobalTheory.RankCoinv.lowRank (r + 1) ⊔ GlobalTheory.RankCoinv.twistSpan ν β := by
  first | exact @GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank | exact GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank | (intros; apply GlobalTheory.RankCoinv.mem_lowRank_succ_sup_twistSpan_of_mem_lowRank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRankDeficientReduction
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), ∃ Φ₀ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Φ₀ Y = 0) ∧
      Φ - Φ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} := by
  intro k _ _ _ _ a d _ ν β _ hν ϖ hϖ hνϖ Φ hΦ
  have key : ∀ r ≤ a, Φ ∈ (GlobalTheory.RankCoinv.lowRank r : Submodule ℂ (Matrix (Fin a) (Fin d) k → ℂ)) ⊔
      GlobalTheory.RankCoinv.twistSpan ν β := by
    intro r hr
    induction r with
    | zero => exact Submodule.mem_sup_left ⟨hΦ, fun Y hY => absurd hY (Nat.not_lt_zero _)⟩
    | succ r ih =>
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 (ih (by omega))
      have := GlobalTheory.T.low_rank_filtration_step k (Fin a) (Fin d) ϖ hϖ ν β hν hνϖ r (by simpa using hr) x hx
      exact Submodule.add_mem _ this (Submodule.mem_sup_right hy)
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (key a le_rfl)
  refine ⟨x, hx.1, fun Y hY => hx.2 Y (lt_of_le_of_ne (by simpa using Y.rank_le_card_height) hY), ?_⟩
  have e : Φ - x = y := by rw [← hxy]; abel
  rw [e]; exact hy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRankDeficientReductionStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_rank_deficient_reduction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ), a ≤ d →
    ∀ (ν β : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ν ϖ ≠ 1 →
    ∀ Φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k), ∃ Φ₀ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k),
      (∀ Y : Matrix (Fin a) (Fin d) k, Y.rank ≠ a → Φ₀ Y = 0) ∧
      Φ - Φ₀ ∈ Submodule.span ℂ {z | ∃ (g : GL (Fin a) k) (Ψ : Matrix (Fin a) (Fin d) k → ℂ),
        Ψ ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin d) k) ∧ z = GlobalTheory.SplitFlip.omA ν β g 1 Ψ - Ψ} := by
  first | exact @GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan | exact GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan | (intros; apply GlobalTheory.RankCoinv.exists_fullRank_sub_mem_twistSpan <;> assumption)
end
