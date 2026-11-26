module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.BertiniNoether

open Polynomial in
private lemma mem_of_gauss_valuation_eq_one {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L)
    (V : ValuationSubring F) (W : ValuationSubring L)
    (hG : ∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) →
      (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W.valuation (Polynomial.aeval t P) = 1) :
    t ∈ W := by
  have h := hG X (fun i => by
      rw [coeff_X]; split_ifs
      · exact V.one_mem
      · exact V.zero_mem)
    ⟨1, by simp, by simpa using V.one_mem, by simpa using V.one_mem⟩
  rw [aeval_X] at h
  rw [← W.valuation_le_one_iff, h]

open Polynomial in
private lemma mem_of_monic_root_coeff_mem {L : Type} [Field L] (W : ValuationSubring L) (ψ : L[X])
    (hψ : ψ.Monic) (hc : ∀ i, ψ.coeff i ∈ W) (ω : L) (hω : ψ.eval ω = 0) : ω ∈ W := by
  have hl : ψ ∈ lifts (algebraMap W L) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hψ
  have hint : IsIntegral W ω := ⟨q, hqm, by rw [← eval_map, hq, hω]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  rw [← hy]
  exact y.2

open Polynomial in
private lemma aeval_mem_of_coeff_mem {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L)
    (V : ValuationSubring F) (W : ValuationSubring L) (hF : ∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V)
    (ht : t ∈ W) (P : F[X]) (hP : ∀ i, P.coeff i ∈ V) : aeval t P ∈ W := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def]
  exact mul_mem ((hF _).2 (hP i)) (pow_mem ht i)

open Polynomial in
private lemma mem_of_monic_bipoly_root {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L)
    (V : ValuationSubring F) (W : ValuationSubring L) (hF : ∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V)
    (ht : t ∈ W) (Φ : Polynomial (Polynomial F)) (ω : L) (hΦ : Φ.Monic)
    (hΦV : ∀ i j, (Φ.coeff i).coeff j ∈ V) (hΦω : Φ.eval₂ (aeval t).toRingHom ω = 0) : ω ∈ W :=
  mem_of_monic_root_coeff_mem W (Φ.map (aeval t).toRingHom) (hΦ.map _)
    (fun i => by rw [coeff_map]; exact aeval_mem_of_coeff_mem t V W hF ht _ (hΦV i)) ω
    (by rw [eval_map, hΦω])

open Polynomial in
private lemma exists_mul_mem_finset_and_eq_one {F : Type} [Field F] (V : ValuationSubring F) (s : Finset F)
    (hs : ∃ a ∈ s, a ≠ 0) : ∃ c : F, c ≠ 0 ∧ (∀ a ∈ s, c * a ∈ V) ∧ ∃ a ∈ s, c * a = 1 := by
  obtain ⟨a, ha, ha0⟩ := hs
  obtain ⟨b, hb, hmax⟩ := s.exists_max_image V.valuation ⟨a, ha⟩
  have hb0 : b ≠ 0 := by
    intro hb0
    have := hmax a ha
    rw [hb0, map_zero, le_zero_iff, Valuation.zero_iff] at this
    exact ha0 this
  refine ⟨b⁻¹, inv_ne_zero hb0, fun x hx => ?_, b, hb, inv_mul_cancel₀ hb0⟩
  rw [← V.valuation_le_one_iff, map_mul, map_inv₀]
  have hvb : V.valuation b ≠ 0 := (Valuation.ne_zero_iff _).2 hb0
  rw [inv_mul_le_iff₀ (zero_lt_iff.2 hvb), mul_one]
  exact hmax x hx

open Polynomial in
private lemma exists_mul_coeff_mem_and_eq_one {F : Type} [Field F] (V : ValuationSubring F) (P : F[X])
    (hP : P ≠ 0) : ∃ c : F, c ≠ 0 ∧ (∀ i, c * P.coeff i ∈ V) ∧ ∃ i, c * P.coeff i = 1 := by
  classical
  obtain ⟨c, hc0, hcV, a, ha, hca⟩ := exists_mul_mem_finset_and_eq_one V (P.support.image P.coeff) (by
    obtain ⟨i, hi⟩ := Polynomial.support_nonempty.2 hP
    exact ⟨_, Finset.mem_image_of_mem _ hi, Polynomial.mem_support_iff.1 hi⟩)
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
  refine ⟨c, hc0, fun j => ?_, i, hca⟩
  by_cases hj : P.coeff j = 0
  · rw [hj, mul_zero]; exact V.zero_mem
  · exact hcV _ (Finset.mem_image_of_mem _ (Polynomial.mem_support_iff.2 hj))

open Polynomial in
private lemma exists_mul_coeff_coeff_mem_and_eq_one {F : Type} [Field F] (V : ValuationSubring F)
    (P : Polynomial (Polynomial F)) (hP : P ≠ 0) :
    ∃ c : F, c ≠ 0 ∧ (∀ i j, c * (P.coeff i).coeff j ∈ V) ∧ ∃ i j, c * (P.coeff i).coeff j = 1 := by
  classical
  obtain ⟨c, hc0, hcV, a, ha, hca⟩ := exists_mul_mem_finset_and_eq_one V
    (P.support.biUnion fun i => (P.coeff i).support.image (P.coeff i).coeff) (by
      obtain ⟨i, hi⟩ := Polynomial.support_nonempty.2 hP
      obtain ⟨j, hj⟩ := Polynomial.support_nonempty.2 (Polynomial.mem_support_iff.1 hi)
      exact ⟨_, Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image_of_mem _ hj⟩,
        Polynomial.mem_support_iff.1 hj⟩)
  obtain ⟨i, -, ha⟩ := Finset.mem_biUnion.1 ha
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ha
  refine ⟨c, hc0, fun k l => ?_, i, j, hca⟩
  by_cases hkl : (P.coeff k).coeff l = 0
  · rw [hkl, mul_zero]; exact V.zero_mem
  · have hk : P.coeff k ≠ 0 := fun h => hkl (by rw [h, Polynomial.coeff_zero])
    exact hcV _ (Finset.mem_biUnion.2 ⟨k, Polynomial.mem_support_iff.2 hk,
      Finset.mem_image_of_mem _ (Polynomial.mem_support_iff.2 hkl)⟩)

open Polynomial in
private lemma eval₂_aeval_mem_of_coeff_coeff_mem {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L)
    (V : ValuationSubring F) (W : ValuationSubring L) (hF : ∀ a : F, algebraMap F L a ∈ W ↔ a ∈ V)
    (ht : t ∈ W) (ω : L) (hω : ω ∈ W) (P : Polynomial (Polynomial F))
    (hP : ∀ i j, (P.coeff i).coeff j ∈ V) : P.eval₂ (aeval t).toRingHom ω ∈ W := by
  rw [eval₂_eq_sum_range]
  exact sum_mem fun i _ => mul_mem (aeval_mem_of_coeff_mem t V W hF ht _ (hP i)) (pow_mem hω i)

open Polynomial in
theorem _root_.GlobalTheory.BertiniNoether.le_of_residue_independent : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic → (∀ i j, (Φ.coeff i).coeff j ∈ V) → Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω) → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → (∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W₁.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits) → W₁ ≤ W₂ := by
  intro F _ L _ _ t V Φ ω hΦ hΦV hΦω hrep W₁ W₂ ⟨h₁F, h₁G⟩ ⟨h₂F, h₂G⟩ hmin y hy
  obtain ⟨Q, hQ0, R, hQR⟩ := hrep y
  have ht₂ : t ∈ W₂ := mem_of_gauss_valuation_eq_one t V W₂ h₂G
  have hω₂ : ω ∈ W₂ := mem_of_monic_bipoly_root t V W₂ h₂F ht₂ Φ ω hΦ hΦV hΦω
  have hΦ1 : Φ ≠ 1 := by
    rintro rfl
    simp at hΦω

  obtain ⟨d, hd0, hdV, i₀, hdi₀⟩ := exists_mul_coeff_mem_and_eq_one V Q hQ0
  set Q' : F[X] := C d * Q with hQ'
  have hQ'V : ∀ i, Q'.coeff i ∈ V := fun i => by rw [hQ', coeff_C_mul]; exact hdV i
  have hQ'prim : ∃ i, Q'.coeff i ≠ 0 ∧ Q'.coeff i ∈ V ∧ (Q'.coeff i)⁻¹ ∈ V :=
    ⟨i₀, by rw [hQ', coeff_C_mul, hdi₀]; exact one_ne_zero,
      by rw [hQ', coeff_C_mul, hdi₀]; exact V.one_mem,
      by rw [hQ', coeff_C_mul, hdi₀, inv_one]; exact V.one_mem⟩
  have hv₁Q := h₁G Q' hQ'V hQ'prim
  have hv₂Q := h₂G Q' hQ'V hQ'prim
  have hQ'eval : aeval t Q' = algebraMap F L d * aeval t Q := by
    rw [hQ', map_mul, aeval_C]

  set R₀ := R %ₘ Φ with hR₀def
  have hR₀ : R₀.eval₂ (aeval t).toRingHom ω = R.eval₂ (aeval t).toRingHom ω := by
    conv_rhs => rw [← modByMonic_add_div R Φ]
    rw [eval₂_add, eval₂_mul, hΦω, zero_mul, add_zero]
  have hdeg : R₀.natDegree < Φ.natDegree := natDegree_modByMonic_lt R hΦ hΦ1
  by_cases hR0 : R₀ = 0
  · have hy0 : y = 0 := by
      have hQne : aeval t Q' ≠ 0 := by
        intro h
        rw [h, map_zero] at hv₁Q
        exact zero_ne_one hv₁Q
      have : aeval t Q' * y = 0 := by
        rw [hQ'eval, mul_assoc, hQR, ← hR₀, hR0, eval₂_zero, mul_zero]
      exact (mul_eq_zero.1 this).resolve_left hQne
    rw [hy0]
    exact W₂.zero_mem
  obtain ⟨c, hc0, hcV, i₁, j₁, hci₁⟩ := exists_mul_coeff_coeff_mem_and_eq_one V R₀ hR0
  set R' : Polynomial (Polynomial F) := C (C c) * R₀ with hR'
  have hR'coeff : ∀ i j, (R'.coeff i).coeff j = c * (R₀.coeff i).coeff j := fun i j => by
    rw [hR', coeff_C_mul, coeff_C_mul]
  have hR'V : ∀ i j, (R'.coeff i).coeff j ∈ V := fun i j => by rw [hR'coeff]; exact hcV i j
  have hR'deg : R'.natDegree < Φ.natDegree := lt_of_le_of_lt (natDegree_C_mul_le _ _) hdeg
  have hR'unit : ¬ R'.eval₂ (aeval t).toRingHom ω ∈ W₁.nonunits := by
    intro h
    have := V.mem_nonunits_iff.1 (hmin R' hR'deg hR'V h i₁ j₁)
    rw [hR'coeff, hci₁, map_one] at this
    exact lt_irrefl _ this
  have hR'eval : R'.eval₂ (aeval t).toRingHom ω = algebraMap F L c * R₀.eval₂ (aeval t).toRingHom ω := by
    rw [hR', eval₂_mul, eval₂_C]
    simp

  set u : F := d * c⁻¹ with hu
  have hrel : aeval t Q' * y = algebraMap F L u * R'.eval₂ (aeval t).toRingHom ω := by
    rw [hQ'eval, mul_assoc, hQR, ← hR₀, hR'eval, hu, map_mul, map_inv₀]
    have : algebraMap F L c ≠ 0 := (_root_.map_ne_zero _).2 hc0
    field_simp
  have hval : ∀ W : ValuationSubring L, W.valuation (aeval t Q') = 1 →
      W.valuation y = W.valuation (algebraMap F L u) * W.valuation (R'.eval₂ (aeval t).toRingHom ω) := by
    intro W hW
    have := congrArg W.valuation hrel
    rwa [Valuation.map_mul, Valuation.map_mul, hW, one_mul] at this
  have hu₁ : algebraMap F L u ∈ W₁ := by
    rw [← W₁.valuation_le_one_iff]
    have h1 : 1 ≤ W₁.valuation (R'.eval₂ (aeval t).toRingHom ω) := by
      rw [W₁.mem_nonunits_iff, not_lt] at hR'unit
      exact hR'unit
    calc W₁.valuation (algebraMap F L u)
        ≤ W₁.valuation (algebraMap F L u) * W₁.valuation (R'.eval₂ (aeval t).toRingHom ω) :=
          le_mul_of_one_le_right' h1
      _ = W₁.valuation y := (hval W₁ hv₁Q).symm
      _ ≤ 1 := (W₁.valuation_le_one_iff y).2 hy
  have hu₂ : algebraMap F L u ∈ W₂ := (h₂F u).2 ((h₁F u).1 hu₁)
  have hR'₂ : R'.eval₂ (aeval t).toRingHom ω ∈ W₂ := eval₂_aeval_mem_of_coeff_coeff_mem t V W₂ h₂F ht₂ ω hω₂ R' hR'V
  rw [← W₂.valuation_le_one_iff, hval W₂ hv₂Q]
  exact mul_le_one' ((W₂.valuation_le_one_iff _).2 hu₂) ((W₂.valuation_le_one_iff _).2 hR'₂)

end GlobalTheory.BertiniNoether
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependentStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_le_of_residue_independent : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic → (∀ i j, (Φ.coeff i).coeff j ∈ V) → Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω) → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → (∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W₁.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits) → W₁ ≤ W₂ := by
  first | exact @GlobalTheory.BertiniNoether.le_of_residue_independent | exact GlobalTheory.BertiniNoether.le_of_residue_independent | (intros; apply GlobalTheory.BertiniNoether.le_of_residue_independent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterRankOnePerturbation
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterRankOnePerturbation
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem det_leadingBlock_one_add_vecMulVec_rankOne {k : Type} [Field k] {n : ℕ} (p q : Fin n → k) (a : Fin n) (c : k)
    (hpq : ∀ i, p i * q i = if i = a then c else 0) (m : Fin n) :
    ((1 + Matrix.vecMulVec p q).toSquareBlockProp fun i => i ≤ m).det = if a ≤ m then 1 + c else 1 := by
  have hM : ((1 + Matrix.vecMulVec p q).toSquareBlockProp fun i => i ≤ m) =
      1 + Matrix.replicateCol Unit (fun i : {i // i ≤ m} => p i) * Matrix.replicateRow Unit (fun i : {i // i ≤ m} => q i) := by
    ext i j
    simp [Matrix.toSquareBlockProp_def, Matrix.one_apply, Subtype.ext_iff, Matrix.vecMulVec_apply, Matrix.mul_apply]
  rw [hM, Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hs : (fun i : {i // i ≤ m} => q i) ⬝ᵥ (fun i : {i // i ≤ m} => p i) = ∑ i : {i // i ≤ m}, (if (i : Fin n) = a then c else 0) := by
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm, hpq]
  rw [hs]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro e; exact hb (Subtype.ext e)
    · simp
  · rw [Finset.sum_eq_zero]
    · simp
    · intro b _
      rw [if_neg]
      intro e; exact h (e ▸ b.2)

theorem rankOne_ev_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ) :
    ev χ (1 : k) = 1 := by
  unfold ev
  rw [dif_pos (by simp)]
  have : Units.mk0 (1 : k) one_ne_zero = 1 := by ext; simp
  simp [this]

theorem rankOne_ev_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (χ : kˣ →* ℂˣ)
    (u : kˣ) (hu : valuation k (u : k) = 1) : ev χ (u : k) = (χ u : ℂ) := by
  unfold ev
  rw [dif_pos hu]
  simp

theorem rankOne_telescope {G : Type} [CommGroup G] (n : ℕ) (F : ℕ → G) (hF : F n = 1) (a : ℕ) (ha : a < n) :
    ∏ i ∈ Finset.range n, (if a ≤ i then F i / F (i + 1) else 1) = F a := by
  rw [← Finset.prod_filter]
  have hfil : (Finset.range n).filter (fun i => a ≤ i) = Finset.Ico a n := by
    ext i; simp [Finset.mem_Ico, and_comm]
  rw [hfil]
  have h2 : ∀ i, F i / F (i + 1) = (F (i + 1))⁻¹ / (F i)⁻¹ := fun i => by
    rw [div_eq_mul_inv, div_eq_mul_inv, inv_inv, mul_comm]
  simp_rw [h2]
  rw [Finset.prod_Ico_div (f := fun i => (F i)⁻¹) ha.le, hF]
  simp

theorem theta_rankOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (p q : Fin n → k) (a : Fin n) (u : kˣ), valuation k (u : k) = 1 → g.val = 1 + Matrix.vecMulVec p q → (∀ i, p i * q i = if i = a then (u : k) - 1 else 0) → theta ψ g = (ψ a u : ℂ) := by
  intro k _ _ _ _ n ψ g p q a u hu hg hpq
  have hmin : ∀ m, minor g m = if a ≤ m then (u : k) else 1 := by
    intro m
    unfold minor
    rw [hg, det_leadingBlock_one_add_vecMulVec_rankOne p q a _ hpq m]
    simp
  let F : ℕ → ℂˣ := fun j => if h : j < n then ψ ⟨j, h⟩ u else 1
  have hterm : ∀ m : Fin n, ev (ψ m / nxt ψ m) (minor g m) = ((if a ≤ m then F m / F (m + 1) else 1 : ℂˣ) : ℂ) := by
    intro m
    rw [hmin]
    split_ifs with h
    · rw [rankOne_ev_unit _ _ hu]
      congr 1
      simp only [F, MonoidHom.div_apply, dif_pos m.2]
      congr 1
      unfold nxt
      split_ifs <;> rfl
    · rw [rankOne_ev_one]; simp
  unfold theta
  simp_rw [hterm, Fin.le_iff_val_le_val]
  rw [← Units.coe_prod, Fin.prod_univ_eq_prod_range (fun i => if (a : ℕ) ≤ i then F i / F (i + 1) else 1) n]
  · rw [rankOne_telescope n F (by simp [F]) a a.2]
    simp [F]

end GlobalTheory.PsType
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrincipalSeriesTypeCharacterRankOnePerturbationStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalSeriesTypeCharacter_rankOne_perturbation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ψ : Fin n → kˣ →* ℂˣ) (g : GL (Fin n) k) (p q : Fin n → k) (a : Fin n) (u : kˣ), valuation k (u : k) = 1 → g.val = 1 + Matrix.vecMulVec p q → (∀ i, p i * q i = if i = a then (u : k) - 1 else 0) → theta ψ g = (ψ a u : ℂ) := by
  first | exact @GlobalTheory.PsType.theta_rankOne | exact GlobalTheory.PsType.theta_rankOne | (intros; apply GlobalTheory.PsType.theta_rankOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulSqrtNegOddPolynomialIdentity
open Polynomial PeriodPair

namespace GlobalTheory

lemma exists_monic_sq_eq_of_mul_eq_sq {D G P : ℂ[X]} (hD : D.Monic) (hc : IsCoprime D G)
    (h : D * G = P ^ 2) : ∃ h : ℂ[X], h.Monic ∧ D = h ^ 2 := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hc h
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD.ne_zero (by simpa using hd.symm)
  refine ⟨normalize d, monic_normalize hd0, ?_⟩
  refine eq_of_monic_of_associated hD ((monic_normalize hd0).pow 2) ?_
  exact hd.symm.trans ((associated_normalize d).pow_pow)

theorem exists_mul_sqrt_neg_odd_polynomial_identity (L : PeriodPair) (α : ℂ) (m : ℕ)
    (k : Subfield ℂ) (hα2 : α ^ 2 = -(2 * (m : ℂ) + 1))
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice)
    (hind : (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
      L.lattice.toAddSubgroup = 2 * m + 1)
    (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L.lattice → L.weierstrassP t ∈ k) :
    ∃ n h : ℂ[X], n.Monic ∧ h.Monic ∧ n.natDegree = 2 * m + 1 ∧ h.natDegree = m ∧
      IsCoprime n h ∧ (∀ i, n.coeff i ∈ k) ∧
      (∀ x, h.IsRoot x → ∃ t ∉ L.lattice, α * t ∈ L.lattice ∧ L.weierstrassP t = x) ∧
      (X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4)) * (derivative n * h - 2 * n * derivative h) ^ 2 =
        n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * h ^ 4 + C (α ^ 6 * (-L.g₃ / 4)) * h ^ 6 := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h0 : ((2 * m + 1 : ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination hα2
    exact absurd (Nat.cast_eq_zero.mp h0) (by omega)
  obtain ⟨A, D, c1, -, c3, c4, c5, c6, c7, c8, c9⟩ :=
    exists_weierstrassP_mul_eq_div hα0 hα k h₂ h₃ hαk hk
  set F : ℂ[X] := X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4) with hF
  set n : ℂ[X] := C (α ^ 2) * A with hn
  have hα20 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα0
  have hFe : ∀ z ∉ L.lattice, F.eval (℘[L] z) = ℘'[L] z ^ 2 / 4 := by
    intro z hz
    rw [L.derivWeierstrassP_sq z hz]
    simp only [hF, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring
  have hnD : IsCoprime n D := by
    rw [hn]
    exact (isCoprime_mul_unit_left_left (isUnit_C.mpr (IsUnit.mk0 _ hα20)) A D).mpr c5
  have key : F * (derivative n * D - n * derivative D) ^ 2 =
      D * (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    refine mul_left_cancel₀ c3.ne_zero (Polynomial.funext fun x ↦ ?_)
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_cases h0 : D.eval (℘[L] z) = 0
    · simp [h0]
    have hz' := (c8 z hz).not.mp h0
    have e1 := derivWeierstrassP_mul_eq hα c9 hz' h0
    have e2 := L.derivWeierstrassP_sq _ hz'
    rw [c9 z hz'] at e2
    rw [eval_mul, eval_mul, eval_mul (p := D), hFe z hz]
    congr 1
    simp only [hn, derivative_mul, derivative_C, eval_add, eval_mul, eval_pow, eval_sub, eval_C,
      zero_mul, zero_add] at e1 ⊢
    have e3 := congrArg (· ^ 2) e1
    simp only [mul_pow] at e3
    rw [e2] at e3
    field_simp at e3
    field_simp
    linear_combination (-1 : ℂ) * e3
  have hDF : IsCoprime D F := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    intro x
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_contra! hc
    simp only [coe_aeval_eq_eval] at hc
    have h1 := (c8 z hz).mp hc.1
    have h2 : ℘'[L] z = 0 := by
      have := hc.2
      rw [hFe z hz] at this
      simpa using this
    rw [derivWeierstrassP_eq_zero_iff L hz] at h2
    refine hz ?_
    have h3 := sub_mem (neg_mem (hα _ h1)) (nsmul_mem h2 m)
    convert h3 using 1
    rw [nsmul_eq_mul]
    linear_combination z * hα2
  have hDG : IsCoprime D
      (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    have : n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3 =
        n ^ 3 + D * (C (α ^ 4 * (-L.g₂ / 4)) * n * D + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 2) := by ring
    rw [this]
    exact (hnD.symm.pow_right).add_mul_left_right _
  obtain ⟨h, hm, hD⟩ := exists_monic_sq_eq_of_mul_eq_sq c3 (hDG.mul_right hDF)
    (P := F * (derivative n * D - n * derivative D)) (by linear_combination (-F) * key)
  have hdn : n.natDegree = 2 * m + 1 := by rw [hn, natDegree_C_mul hα20, c6, hind]
  refine ⟨n, h, ?_, hm, hdn, ?_, ?_, fun i ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · rw [Monic, hn, leadingCoeff_mul, leadingCoeff_C, c4, mul_inv_cancel₀ hα20]
  · rw [c6, hind, hD, natDegree_pow] at c7
    omega
  · rw [hD] at hnD
    exact (IsCoprime.pow_right_iff (by norm_num)).mp hnD
  · rw [hn, coeff_C_mul]
    exact mul_mem (pow_mem hαk 2) (c1 i)
  · obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    refine ⟨z, hz, (c8 z hz).mp ?_, rfl⟩
    rw [hD, eval_pow, hx.eq_zero]
    norm_num
  · refine mul_left_cancel₀ (pow_ne_zero 2 hm.ne_zero) ?_
    rw [hD, derivative_sq] at key
    have h2 : (C 2 : ℂ[X]) = 2 := rfl
    rw [h2] at key
    linear_combination key

end GlobalTheory
end
