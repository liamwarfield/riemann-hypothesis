module

public import Formalism.FlagUnipotentLattices.IdealCountLeW
public import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm

@[expose] public section

section -- merged from Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LocalIntegralStructure
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false

namespace Formalism.HermitianLatticeCounting.P

theorem card_range_nsmul_mul_card_le : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TorsionIndex := Formalism.SLP.Final.torsionIndex

theorem orthogonal_complement_formula : PerpCompl := by
  intro K U _ _ _ _ σ hσ B hR hL r A A' hU hA hA' hsup
  have mem : ∀ (S : Submodule K U) (x : U), x ∈ perpR B S ↔ ∀ a ∈ S, B a x = 0 := by
    intro S x; simp [perpR, Submodule.mem_iInf]
  have lower : ∀ S : Submodule K U, finrank K S = r + 1 → r + 1 ≤ finrank K (perpR B S) := by
    intro S hS
    let bs := Module.finBasisOfFinrankEq K S hS
    let Φ : U →ₗ[K] (Fin (r + 1) → K) :=
      { toFun := fun x i => σ (B (bs i : U) x)
        map_add' := by intro x y; ext i; simp
        map_smul' := by intro k x; ext i; simp [hσ] }
    have hker : LinearMap.ker Φ = perpR B S := by
      ext x; rw [LinearMap.mem_ker, mem]; constructor
      · intro h a ha
        have hi : ∀ i, B (bs i : U) x = 0 := by
          intro i
          have h2 : σ (B (bs i : U) x) = 0 := congrFun h i
          exact (map_eq_zero σ).mp h2
        have h3 : a = ∑ i, (bs.repr ⟨a, ha⟩ i) • (bs i : U) := by
          have h4 := congrArg (S.subtype) (bs.sum_repr ⟨a, ha⟩)
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum] at h4
          simpa only [map_smul, Submodule.subtype_apply] using h4.symm
        rw [h3]; simp [hi]
      · intro h; ext i
        show σ (B (bs i : U) x) = 0
        rw [h _ (bs i).2, map_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have hr : finrank K (LinearMap.range Φ) ≤ r + 1 := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    rw [hker] at h1; omega
  have hinf : perpR B A ⊓ perpR B A' = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨h1, h2⟩ := hx
    have h1' := (mem A x).mp h1
    have h2' := (mem A' x).mp h2
    refine (Submodule.mem_bot K).mpr (hR x fun y => ?_)
    have hy : y ∈ A ⊔ A' := by rw [hsup]; trivial
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hy
    simp [h1' a ha, h2' a' ha']
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (perpR B A) (perpR B A')
  rw [hinf, finrank_bot, add_zero] at hs
  have hle := Submodule.finrank_le (perpR B A ⊔ perpR B A')
  have l1 := lower A hA
  have l2 := lower A' hA'
  refine ⟨by omega, by omega, ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr ?_⟩⟩
  exact Submodule.eq_top_of_finrank_eq (by omega)

theorem cofactor_vector_formula : CofactorVec := by
  intro R _ r Z
  refine ⟨fun a => ?_, ?_⟩
  · have h := congrFun (congrFun (Matrix.adjugate_mul Z) (Fin.last r)) a
    rw [Matrix.mul_apply] at h
    rw [h]
    by_cases ha : a = Fin.last r
    · subst ha
      simp
    · simp [Matrix.one_apply, ha, Ne.symm ha]
  · rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
    have h2 : ((-1 : R) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    rw [h2, one_mul]

section GramAll
open Matrix Polynomial

section Gram
variable {R : Type} [CommRing R]

lemma det_add_smul_single {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R) (i j : n) (c : R) :
    (M + c • Matrix.single i j (1 : R)).det = M.det + c * M.adjugate j i := by
  have hM : M + c • Matrix.single i j (1 : R) = M.updateRow i (M i + c • Pi.single j 1) := by
    ext a b
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = j
      · subst hb
        simp
      · simp [Matrix.single_apply, Pi.single_apply, hb, Ne.symm hb]
    · simp [Matrix.single_apply, Matrix.updateRow_ne ha, ha, Ne.symm ha]
  rw [hM, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    Matrix.adjugate_apply]

lemma det_swap_blocks_alt {n : Type} [Fintype n] [DecidableEq n] :
    (fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R)).det =
      (-1) ^ Fintype.card n := by
  have h : (fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R)) =
      fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks (-1) 0 0 1 := by
    simp [fromBlocks_multiply]
  rw [h]
  simp [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_neg]

lemma det_from_blocks_single_regular (r : ℕ) (W Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (l : Fin (r + 1))
    (t t' : R) (hreg : IsRegular W.det) :
    (fromBlocks W ((-t) • Matrix.single l l (1 : R)) ((-t') • Matrix.single l l (1 : R)) Z).det =
      W.det * Z.det - t * t' * W.adjugate l l * Z.adjugate l l := by
  set A := (-t) • Matrix.single l l (1 : R) with hA
  set D := (-t') • Matrix.single l l (1 : R) with hD
  set δ := W.det with hδ
  have h : fromBlocks W A D Z * fromBlocks W.adjugate (-(W.adjugate * A)) 0 (δ • 1) =
      fromBlocks (δ • 1) 0 (D * W.adjugate) (δ • Z - D * W.adjugate * A) := by
    rw [fromBlocks_multiply]
    congr 1
    · simp [mul_adjugate, hδ]
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, mul_adjugate]; simp [hδ]
    · simp
    · simp [Matrix.mul_assoc]; abel
  have hDA : D * W.adjugate * A = (t * t' * W.adjugate l l) • Matrix.single l l (1 : R) := by
    rw [hA, hD]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.single_mul_mul_single, smul_smul]
    ext a b
    simp [Matrix.single_apply]
  have h2 := congrArg det h
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, hDA, sub_eq_add_neg, ← neg_smul,
    det_add_smul_single, det_adjugate, det_smul, det_smul, adjugate_smul] at h2
  simp only [Fintype.card_fin, add_tsub_cancel_right, det_one, mul_one, Matrix.smul_apply,
    smul_eq_mul] at h2
  apply (hreg.pow (2 * r + 1)).left
  simp only
  linear_combination h2

lemma det_from_blocks_single (r : ℕ) (W Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (l : Fin (r + 1))
    (t t' : R) :
    (fromBlocks W ((-t) • Matrix.single l l (1 : R)) ((-t') • Matrix.single l l (1 : R)) Z).det =
      W.det * Z.det - t * t' * W.adjugate l l * Z.adjugate l l := by
  let φ : R[X] →+* R := Polynomial.evalRingHom (0 : R)
  have hW : φ.mapMatrix (charmatrix (-W)) = W := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [φ, charmatrix_apply]
    · simp [φ, charmatrix_apply, hab]
  have hZ : φ.mapMatrix (C.mapMatrix Z) = Z := by
    ext a b; simp [φ]
  have hs : ∀ c : R, φ.mapMatrix ((-(C c)) • Matrix.single l l (1 : R[X])) =
      (-c) • Matrix.single l l (1 : R) := by
    intro c; ext a b
    by_cases h : l = a ∧ l = b
    · obtain ⟨rfl, rfl⟩ := h; simp [φ]
    · simp [φ, Matrix.single_apply, h]
  have key := det_from_blocks_single_regular r (charmatrix (-W)) (C.mapMatrix Z) l (C t) (C t')
    (charpoly_monic (-W)).isRegular
  have key2 := congrArg φ key
  rw [RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map] at key2
  simp only [← RingHom.mapMatrix_apply] at key2
  rw [hW, hZ, hs, hs] at key2
  rw [key2]
  have ha : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) R[X],
      φ (M.adjugate l l) = (φ.mapMatrix M).adjugate l l := by
    intro M; rw [← RingHom.map_adjugate]; rfl
  simp only [map_sub, map_mul, RingHom.map_det, ha, hW, hZ]
  simp [φ]

theorem gram_determinant_general : GramDetGen := by
  intro R _ r Z W t t'
  have hdiag : ∀ s : R, (Matrix.diagonal fun i : Fin (r + 1) => if i = Fin.last r then -s else 0) =
      (-s) • Matrix.single (Fin.last r) (Fin.last r) (1 : R) := by
    intro s
    ext i j
    by_cases hi : i = Fin.last r
    · subst hi
      by_cases hj : j = Fin.last r
      · subst hj
        simp
      · simp [Matrix.diagonal_apply, Matrix.single_apply, Ne.symm hj]
    · simp [Matrix.diagonal_apply, Matrix.single_apply, hi, Ne.symm hi]
  have hS : Matrix.fromBlocks (Matrix.diagonal fun i : Fin (r + 1) => if i = Fin.last r then -t else 0) W Z
      (Matrix.diagonal fun i : Fin (r + 1) => if i = Fin.last r then -t' else 0) *
      Matrix.fromBlocks 0 1 1 0 =
      Matrix.fromBlocks W ((-t) • Matrix.single (Fin.last r) (Fin.last r) (1 : R))
        ((-t') • Matrix.single (Fin.last r) (Fin.last r) (1 : R)) Z := by
    rw [hdiag t, hdiag t', Matrix.fromBlocks_multiply]
    simp
  have hdetS := det_swap_blocks_alt (R := R) (n := Fin (r + 1))
  have hB := det_from_blocks_single r W Z (Fin.last r) t t'
  have hcW := (cofactor_vector_formula R r W).2
  have hcZ := (cofactor_vector_formula R r Z).2
  have h1 := congrArg Matrix.det hS
  rw [Matrix.det_mul, hdetS, Fintype.card_fin, hB, hcW, hcZ] at h1
  have hsq : ((-1 : R) ^ (r + 1)) * ((-1) ^ (r + 1)) = 1 := by
    rw [← mul_pow]
    simp
  have key : ∀ x : R, x * (-1) ^ (r + 1) = W.det * Z.det - t * t' *
      (W.submatrix Fin.castSucc Fin.castSucc).det * (Z.submatrix Fin.castSucc Fin.castSucc).det →
      x = (-1) ^ (r + 1) * (Z.det * W.det - t * t' * (Z.submatrix Fin.castSucc Fin.castSucc).det *
        (W.submatrix Fin.castSucc Fin.castSucc).det) := by
    intro x hx
    linear_combination ((-1 : R) ^ (r + 1)) * hx - x * hsq
  exact key _ h1

end Gram

theorem gram_matrix_nondegenerate : GramNondeg := by
  intro K V ι _ _ _ _ _ σ B v hdet
  have right : ∀ c : ι → K, (∀ j, B (v j) (∑ i, c i • v i) = 0) → c = 0 := by
    intro c hc
    have h1 : (Matrix.of fun i j => B (v i) (v j)).mulVec (fun i => σ (c i)) = 0 := by
      funext j
      have hj := hc j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at hj
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul] at hj
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      rw [← hj]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1
    funext i
    have h3 := congrFun h2 i
    simp only [Pi.zero_apply] at h3
    exact (map_eq_zero σ).1 h3
  have left : ∀ c : ι → K, (∀ j, B (∑ i, c i • v i) (v j) = 0) → c = 0 := by
    intro c hc
    have h1 : Matrix.vecMul c (Matrix.of fun i j => B (v i) (v j)) = 0 := by
      funext j
      have hj := hc j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply] at hj
      simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at hj
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact hj
    exact Matrix.eq_zero_of_vecMul_eq_zero hdet h1
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg0 := right g (fun j => by rw [hg, map_zero])
    intro i
    exact congrFun hg0 i
  refine ⟨hli, finrank_span_eq_card hli, ?_, ?_⟩
  · intro x hx hB
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    have hc := right c (fun j => hB (v j) (Submodule.subset_span ⟨j, rfl⟩))
    simp [hc]
  · intro x hx hB
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    have hc := left c (fun j => hB (v j) (Submodule.subset_span ⟨j, rfl⟩))
    simp [hc]

end GramAll

lemma pow_two_div_sq_identity (g : ℝ) (e f : ℕ) : ((2 / g) ^ (e * f)) ^ 2 = 4 ^ (e * f) / g ^ (2 * f * e) := by
  rw [← pow_mul, div_pow, show e * f * 2 = 2 * f * e by ring]
  congr 1
  rw [show 2 * f * e = 2 * (e * f) by ring, pow_mul]
  norm_num

theorem L4_arithmetic_square : DetIndexProductInequalitySq := by
  intro detM dLa₁ dLa₂ dPs₁ dPs₂ i₁ i₂ G0₁ G0₂ g e f hP₁ hP₂ hg hi₁ hi₂ hL₁ hL₂ hdet hG₁ hG₂ hgP
  have hq : 0 < g ^ (2 * f * e) := pow_pos hg _
  have hP : 0 < dPs₁ * dPs₂ := mul_pos hP₁ hP₂
  have hc : 0 ≤ (2 / g) ^ (e * f) := pow_nonneg (div_nonneg (by norm_num) hg.le) _
  have ha : 0 ≤ dLa₁ * i₁ ^ 2 := mul_nonneg hL₁ (sq_nonneg _)
  have hb : 0 ≤ dLa₂ * i₂ ^ 2 := mul_nonneg hL₂ (sq_nonneg _)
  have hab : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ G0₁ * G0₂ :=
    mul_le_mul hG₁ hG₂ hb (ha.trans hG₁)
  have hG : 0 ≤ G0₁ * G0₂ := (mul_nonneg ha hb).trans hab
  have hF : 1 ≤ 4 ^ (e * f) * (dPs₁ * dPs₂) / g ^ (2 * f * e) := by
    rw [← mul_assoc]
    first
      | exact (one_le_div hq).2 hgP
      | exact (one_le_div₀ hq).2 hgP
      | exact (le_div_iff₀ hq).2 (by rw [one_mul]; exact hgP)
  have e1 : (detM * i₁ * i₂) ^ 2 = (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / (dPs₁ * dPs₂) := by
    rw [show (detM * i₁ * i₂) ^ 2 = detM ^ 2 * i₁ ^ 2 * i₂ ^ 2 by ring, hdet]
    ring
  have hsq : (detM * i₁ * i₂) ^ 2 ≤ ((2 / g) ^ (e * f)) ^ 2 * (G0₁ * G0₂) := by
    rw [pow_two_div_sq_identity g e f, e1]
    have h4 : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤
        4 ^ (e * f) / g ^ (2 * f * e) * (G0₁ * G0₂) * (dPs₁ * dPs₂) :=
      calc (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ G0₁ * G0₂ := hab
        _ ≤ (G0₁ * G0₂) * (4 ^ (e * f) * (dPs₁ * dPs₂) / g ^ (2 * f * e)) :=
          le_mul_of_one_le_right hG hF
        _ = 4 ^ (e * f) / g ^ (2 * f * e) * (G0₁ * G0₂) * (dPs₁ * dPs₂) := by ring
    first
      | exact (div_le_iff₀ hP).2 h4
      | exact (div_le_iff hP).2 h4
  by_cases h : detM ≤ 0
  · have h0 : detM * i₁ * i₂ ≤ 0 := by
      rw [mul_assoc]
      exact mul_nonpos_iff.2 (Or.inr ⟨h, mul_nonneg hi₁ hi₂⟩)
    exact h0.trans (mul_nonneg hc (Real.sqrt_nonneg _))
  · have hL : 0 ≤ detM * i₁ * i₂ := mul_nonneg (mul_nonneg (not_le.mp h).le hi₁) hi₂
    have hs : Real.sqrt ((detM * i₁ * i₂) ^ 2) ≤
        Real.sqrt (((2 / g) ^ (e * f)) ^ 2 * (G0₁ * G0₂)) := by
      first
        | exact Real.sqrt_le_sqrt hsq
        | gcongr
    rw [Real.sqrt_sq hL, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc] at hs
    exact hs

theorem L5_arithmetic_square : DetIndexProductPlacesInequalitySq := by
  intro detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ e f
    hP₁ hP₂ hQ₁ hQ₂ hg hi₁ hi₂ hL₁ hL₂ hNT hK₁ hK₂ hN₁ hN₂ hdet hd₁ hd₂ hG₁ hG₂ hT₁ hT₂ hgQ
  have hq : 0 < g ^ (2 * f * e) := pow_pos hg _
  have hc : 0 ≤ (2 / g) ^ (e * f) := pow_nonneg (div_nonneg (by norm_num) hg.le) _
  have ha : 0 ≤ dLa₁ * i₁ ^ 2 := mul_nonneg hL₁ (sq_nonneg _)
  have hb : 0 ≤ dLa₂ * i₂ ^ 2 := mul_nonneg hL₂ (sq_nonneg _)
  have hA : dLa₁ * i₁ ^ 2 * Nr₁ ≤ G0₁ := by
    have h := mul_le_mul_of_nonneg_right hG₁ hN₁.le
    rwa [div_mul_cancel₀ _ hN₁.ne'] at h
  have hB : dLa₂ * i₂ ^ 2 * Nr₂ ≤ G0₂ := by
    have h := mul_le_mul_of_nonneg_right hG₂ hN₂.le
    rwa [div_mul_cancel₀ _ hN₂.ne'] at h
  have hk₂ : 0 < Nr₂ * K₂ ^ 2 := mul_pos hN₂ (pow_pos hK₂ 2)
  have hk₁ : 0 < Nr₁ * K₁ ^ 2 := mul_pos hN₁ (pow_pos hK₁ 2)
  have hp1 : NT ≤ P₁ * (Nr₂ * K₂ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hT₁ hk₂.le
    rwa [div_mul_cancel₀ _ hk₂.ne'] at h
  have hp2 : NT ≤ P₂ * (Nr₁ * K₁ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hT₂ hk₁.le
    rwa [div_mul_cancel₀ _ hk₁.ne'] at h
  have hG1 : 0 ≤ G0₁ := le_trans (mul_nonneg ha hN₁.le) hA
  have hG2 : 0 ≤ G0₂ := le_trans (mul_nonneg hb hN₂.le) hB
  have hG : 0 ≤ G0₁ * G0₂ := mul_nonneg hG1 hG2
  have hPP : 0 < P₁ * P₂ := mul_pos hP₁ hP₂
  have hF : 1 ≤ 4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e) := by
    rw [← mul_assoc]
    first
      | exact (one_le_div hq).2 hgQ
      | exact (one_le_div₀ hq).2 hgQ
  have hNN : NT * NT ≤ (P₁ * (Nr₂ * K₂ ^ 2)) * (P₂ * (Nr₁ * K₁ ^ 2)) :=
    mul_le_mul hp1 hp2 hNT.le (le_trans hNT.le hp1)
  have key : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) * (NT * NT) ≤
      (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e)) := by
    calc (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) * (NT * NT)
        ≤ (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) * ((P₁ * (Nr₂ * K₂ ^ 2)) * (P₂ * (Nr₁ * K₁ ^ 2))) :=
          mul_le_mul_of_nonneg_left hNN (mul_nonneg ha hb)
      _ = ((dLa₁ * i₁ ^ 2 * Nr₁) * (dLa₂ * i₂ ^ 2 * Nr₂)) * ((K₁ * K₂) ^ 2 * (P₁ * P₂)) := by ring
      _ ≤ (G0₁ * G0₂) * ((K₁ * K₂) ^ 2 * (P₁ * P₂)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hA hB (mul_nonneg hb hN₂.le) hG1)
            (mul_nonneg (sq_nonneg _) hPP.le)
      _ = (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * 1 := by ring
      _ ≤ (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e)) :=
          mul_le_mul_of_nonneg_left hF (mul_nonneg (mul_nonneg hG (sq_nonneg _)) hPP.le)
  have hR : ((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 * (G0₁ * G0₂) =
      ((G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e))
        / (NT * NT)) / ((P₁ * dQ₁) * (P₂ * dQ₂)) := by
    rw [show ((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 =
      ((2 / g) ^ (e * f)) ^ 2 * (K₁ * K₂) ^ 2 / (NT * NT) by ring, pow_two_div_sq_identity]
    field_simp [hP₁.ne', hP₂.ne', hQ₁.ne', hQ₂.ne', hNT.ne', hq.ne'] <;> ring
  have hL2 : (detM * i₁ * i₂) ^ 2 =
      (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / ((P₁ * dQ₁) * (P₂ * dQ₂)) := by
    rw [show (detM * i₁ * i₂) ^ 2 = detM ^ 2 * i₁ ^ 2 * i₂ ^ 2 by ring, hdet, hd₁, hd₂]
    ring
  have hPQ : 0 < (P₁ * dQ₁) * (P₂ * dQ₂) := mul_pos (mul_pos hP₁ hQ₁) (mul_pos hP₂ hQ₂)
  have hNT2 : 0 < NT * NT := mul_pos hNT hNT
  have hk : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤
      (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e))
        / (NT * NT) := (le_div_iff₀ hNT2).2 key
  have hsq : (detM * i₁ * i₂) ^ 2 ≤ ((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 * (G0₁ * G0₂) := by
    rw [hL2, hR]
    first
      | exact div_le_div_of_nonneg_right hk hPQ.le
      | exact (div_le_div_iff_of_pos_right hPQ).2 hk
      | exact div_le_div_of_le_right hk hPQ
  have hRc : 0 ≤ (2 / g) ^ (e * f) * K₁ * K₂ / NT :=
    div_nonneg (mul_nonneg (mul_nonneg hc hK₁.le) hK₂.le) hNT.le
  by_cases h : detM ≤ 0
  · have h0 : detM * i₁ * i₂ ≤ 0 := by
      rw [mul_assoc]
      exact mul_nonpos_iff.2 (Or.inr ⟨h, mul_nonneg hi₁ hi₂⟩)
    exact h0.trans (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _))
      hK₁.le) hK₂.le) hNT.le)
  · have hL : 0 ≤ detM * i₁ * i₂ := mul_nonneg (mul_nonneg (not_le.mp h).le hi₁) hi₂
    have hs : Real.sqrt ((detM * i₁ * i₂) ^ 2) ≤
        Real.sqrt (((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 * (G0₁ * G0₂)) := by
      first
        | exact Real.sqrt_le_sqrt hsq
        | gcongr
    rw [Real.sqrt_sq hL, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hRc] at hs
    calc detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * K₁ * K₂ / NT * Real.sqrt (G0₁ * G0₂) := hs
      _ = (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT := by ring

section NF
variable {E : Type} [Field E] [NumberField E]

end NF

end Formalism.HermitianLatticeCounting.P
end

section -- merged from Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ComplexMultiplicationRoot
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure

namespace Formalism.HermitianLatticeCounting.P

theorem integer_group_preservation : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ZZgPreserve := by
  intro E _ _ g a b c d h
  have hI : ∀ y : 𝓞 E, IsInt (y : E) := fun y => by unfold IsInt; exact ⟨y, rfl⟩
  have mem : ∀ x y : E, IsInt x → IsInt y → (∃ w : 𝓞 E, x + y = (g : E) * (w : E)) →
      (x, y) ∈ (ZZ g : Set (E × E)) := by
    intro x y hx hy hw
    simp only [ZZ, Set.mem_setOf_eq]
    exact ⟨hx, hy, hw⟩
  have out : ∀ x y : E, (x, y) ∈ (ZZ g : Set (E × E)) → IsInt x ∧ IsInt y := by
    intro x y hxy
    simp only [ZZ, Set.mem_setOf_eq] at hxy
    exact ⟨hxy.1, hxy.2.1⟩
  have hg : IsInt (g : E) := by simpa using hI (g : 𝓞 E)
  have h0 : IsInt (0 : E) := by simpa using hI 0
  have h1 : IsInt (1 : E) := by simpa using hI 1
  have hm1 : IsInt (-1 : E) := by simpa using hI (-1)
  have p1 := out _ _ (h _ (mem _ _ hg h0 ⟨1, by simp⟩))
  have p2 := out _ _ (h _ (mem _ _ h0 hg ⟨1, by simp⟩))
  have p3 := out _ _ (h _ (mem _ _ h1 hm1 ⟨0, by simp⟩))
  simp only [mul_zero, add_zero, zero_add, mul_one, mul_neg, ← sub_eq_add_neg] at p1 p2 p3
  refine ⟨?_, ?_, ?_, ?_, p3.1, p3.2⟩
  · rw [mul_comm]; exact p1.1
  · rw [mul_comm]; exact p2.1
  · rw [mul_comm]; exact p1.2
  · rw [mul_comm]; exact p2.2

theorem local_congruence_condition : Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocalCongr := by
  intro E _ _ P T T' a b c d hP hT hT' h
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hT'0 : (T' : E) ≠ 0 := Nat.cast_ne_zero.mpr hT'.ne'
  have h1P : (1 : 𝓞 E) ∉ P := (Ideal.ne_top_iff_one P).mp hP.ne_top
  have one : ∀ x : E, x = 1 → LocIn P x 1 := by
    intro x hx; unfold LocIn
    exact ⟨1, 1, h1P, by simp [hx]⟩
  have zer : ∀ x : E, x = 0 → LocIn P x 1 := by
    intro x hx; unfold LocIn
    exact ⟨1, 0, h1P, by simp [hx]⟩
  have back : ∀ (x : E) (N : ℕ), (N : E) ≠ 0 → LocIn P (x * (1 / (N : E))) 1 → LocIn P x N := by
    intro x N hN hx
    unfold LocIn at hx ⊢
    obtain ⟨y, z, hy, hyz⟩ := hx
    refine ⟨y, z, hy, ?_⟩
    have e : (y : E) * x = (N : E) * ((y : E) * (x * (1 / (N : E)))) := by
      first
      | field_simp
      | rw [mul_one_div, mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hN]
    rw [e, hyz]; simp
  obtain ⟨ha, hc⟩ := h (1 / (T : E)) 0 (one _ (by field_simp)) (zer _ (by simp))
  obtain ⟨hb, hd⟩ := h 0 (1 / (T' : E)) (zer _ (by simp)) (one _ (by field_simp))
  simp only [mul_zero, add_zero, zero_add] at ha hc hb hd
  exact ⟨back _ _ hT0 ha, back _ _ hT0 hc, back _ _ hT'0 hb, back _ _ hT'0 hd⟩

theorem complex_multiplication_root : Formalism.HermitianLatticeCounting.LocalIntegralStructure.CMRoot := by
  intro E _ _ q x hc hq hx h
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    NumberField.InfinitePlace.mult_isComplex ⟨w, hc w⟩
  have hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  simp only [hm] at h
  rw [hn] at h
  have hP : ∏ w : InfinitePlace E, (x w ^ 2) ^ 2 = (∏ w : InfinitePlace E, x w) ^ 4 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun w _ => by ring)
  have hA : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 =
      q ^ (2 * Fintype.card (InfinitePlace E)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have key : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 ≤ (∏ w : InfinitePlace E, x w) ^ 4 := by
    rw [hA, ← hP]; exact h
  have h0 : 0 ≤ ∏ w : InfinitePlace E, x w := Finset.prod_nonneg fun w _ => hx w
  have hq0 : 0 ≤ q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2) := (Real.rpow_pos_of_pos hq _).le
  first
  | exact le_of_pow_le_pow_left₀ (by norm_num) h0 key
  | exact (pow_le_pow_iff_left₀ hq0 h0 (by norm_num)).mp key
  | exact le_of_pow_le_pow_left (by norm_num) h0 key
  | exact (pow_le_pow_iff_left hq0 h0 (by norm_num)).mp key

namespace IntegralityLocalGlobal

variable {E : Type} [Field E] [NumberField E]

lemma isInt_mul {a b : E} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  first
  | exact ha.mul hb
  | exact IsIntegral.mul ha hb
  | (obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; exact ⟨x * y, by rw [← hx, ← hy]; push_cast; ring⟩)
lemma isInt_add {a b : E} (ha : IsInt a) (hb : IsInt b) : IsInt (a + b) := by
  first
  | exact ha.add hb
  | exact IsIntegral.add ha hb
  | (obtain ⟨x, hx⟩ := ha; obtain ⟨y, hy⟩ := hb; exact ⟨x + y, by rw [← hx, ← hy]; push_cast; ring⟩)
lemma isInt_coe (y : 𝓞 E) : IsInt (y : E) := by
  first
  | exact y.2
  | exact ⟨y, rfl⟩
  | exact NumberField.RingOfIntegers.isIntegral_coe y
lemma isInt_map (σ : E →+* E) {a : E} (ha : IsInt a) : IsInt (σ a) := by
  obtain ⟨x, rfl⟩ := ha
  first
  | exact ⟨⟨σ x, (NumberField.RingOfIntegers.isIntegral_coe x).map σ.toIntAlgHom⟩, rfl⟩
  | exact ⟨⟨σ x, x.2.map σ.toIntAlgHom⟩, rfl⟩
  | exact ⟨NumberField.RingOfIntegers.mapRingHom σ x, rfl⟩

lemma locGlob (x : E) (h : ∀ P : Ideal (𝓞 E), P.IsPrime → ∃ y : 𝓞 E, y ∉ P ∧ IsInt ((y : E) * x)) :
    IsInt x := by
  let I : Ideal (𝓞 E) :=
    { carrier := {y | IsInt ((y : E) * x)}
      add_mem' := fun {a b} ha hb => by
        show IsInt (((a + b : 𝓞 E) : E) * x)
        convert isInt_add ha hb using 1
        push_cast; ring
      zero_mem' := by
        show IsInt (((0 : 𝓞 E) : E) * x)
        convert isInt_coe (0 : 𝓞 E) using 1
        push_cast; ring
      smul_mem' := fun c y hy => by
        show IsInt (((c • y : 𝓞 E) : E) * x)
        convert isInt_mul (isInt_coe c) hy using 1
        rw [smul_eq_mul]; push_cast; ring }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨y, hy, hyx⟩ := h M hM.isPrime
    exact hy (hIM (show y ∈ I from hyx))
  have h1 : (1 : 𝓞 E) ∈ I := by rw [hI]; exact Submodule.mem_top
  have h1' : IsInt (((1 : 𝓞 E) : E) * x) := h1
  convert h1' using 1
  push_cast; ring

lemma divGlob (e : E) (N : ℕ) (hN : 0 < N) (he : IsInt e)
    (h : ∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P e N) :
    ∃ β : 𝓞 E, e = (N : E) * (β : E) := by
  have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hx : IsInt (e / (N : E)) := by
    apply locGlob
    intro P hP
    by_cases hNP : (N : 𝓞 E) ∈ P
    · obtain ⟨y, z, hy, hyz⟩ := h P hP hNP
      refine ⟨y, hy, ?_⟩
      convert isInt_coe z using 1
      rw [mul_div_assoc', hyz]
      field_simp
    · refine ⟨(N : 𝓞 E), hNP, ?_⟩
      convert he using 1
      push_cast
      field_simp
  obtain ⟨β, hβ⟩ := hx
  refine ⟨β, ?_⟩
  rw [hβ]
  field_simp

end IntegralityLocalGlobal

open IntegralityLocalGlobal

private theorem exists_not_mem_prime_mul_eq_of_locIn {E : Type} [Field E] [NumberField E] (σ : E →+* E) (M M' g : ℕ) (u e : E)
    (hM : 0 < M) (he : e = (g : E) ^ 2 * ((M' : E) * u * σ u / (M : E)))
    (hu : ∀ P : Ideal (𝓞 E), P.IsPrime → (M : 𝓞 E) ∈ P → LocIn P u M)
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hMP : (M : 𝓞 E) ∈ P) :
    ∃ y z : 𝓞 E, y ∉ P ∧ (y : E) * e = (M : E) * (M' : E) * (g : E) ^ 2 * (z : E) := by
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  let f : 𝓞 E →+* 𝓞 E := NumberField.RingOfIntegers.mapRingHom σ
  have hf : ∀ y : 𝓞 E, ((f y : 𝓞 E) : E) = σ (y : E) := fun y => rfl
  have hQ : (P.comap f).IsPrime := by
    haveI := hP
    first
    | exact Ideal.comap_isPrime f P
    | exact Ideal.IsPrime.comap f
    | infer_instance
  have hMQ : (M : 𝓞 E) ∈ P.comap f := by
    rw [Ideal.mem_comap, map_natCast]; exact hMP
  obtain ⟨y1, z1, hy1, h1⟩ := hu P hP hMP
  obtain ⟨y2, z2, hy2, h2⟩ := hu _ hQ hMQ
  have h2' : ((f y2 : 𝓞 E) : E) * σ u = (M : E) * ((f z2 : 𝓞 E) : E) := by
    have h3 := congrArg σ h2
    rw [map_mul, map_mul, map_natCast] at h3
    rw [hf, hf]; exact h3
  have hE : e * (M : E) = (g : E) ^ 2 * ((M' : E) * u * σ u) := by
    rw [he]
    first
    | rw [mul_div_assoc', div_mul_cancel₀ _ hM0]
    | field_simp
  have c1 : ((y1 * f y2 : 𝓞 E) : E) = (y1 : E) * ((f y2 : 𝓞 E) : E) := by
    first | rfl | (push_cast; rfl) | simp
  have c2 : ((z1 * f z2 : 𝓞 E) : E) = (z1 : E) * ((f z2 : 𝓞 E) : E) := by
    first | rfl | (push_cast; rfl) | simp
  refine ⟨y1 * f y2, z1 * f z2, ?_, ?_⟩
  · intro hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact hy1 h
    · exact hy2 (Ideal.mem_comap.mpr h)
  · rw [c1, c2]
    apply mul_right_cancel₀ hM0
    linear_combination ((y1 : E) * ((f y2 : 𝓞 E) : E)) * hE
      + ((g : E) ^ 2 * (M' : E) * (((f y2 : 𝓞 E) : E) * σ u)) * h1
      + ((g : E) ^ 2 * (M' : E) * (M : E) * (z1 : E)) * h2'

theorem s_integrality : Formalism.HermitianLatticeCounting.LocalIntegralStructure.SInt := by
  intro E _ _ σ T T' g s b c hT hT' hs1 hs2 hgb hgc hc hb
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hTT : 0 < T * T' := Nat.mul_pos hT hT'
  have e1 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T' : E) * c * σ c / (T : E)) := by rw [hs1]
  have e2 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T : E) * b * σ b / (T' : E)) := by rw [hs2]
  have hint : IsInt ((g : E) ^ 2 * s) := by
    apply locGlob
    intro P hP
    by_cases hTP : (T : 𝓞 E) ∈ P
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP hTP
      refine ⟨y, hy, ?_⟩
      rw [hyz]
      convert isInt_coe ((T : 𝓞 E) * (T' : 𝓞 E) * (g : 𝓞 E) ^ 2 * z) using 1
      push_cast; ring
    · refine ⟨(T : 𝓞 E), hTP, ?_⟩
      have hh := isInt_mul (isInt_mul (isInt_coe (T' : 𝓞 E)) hgc) (isInt_map σ hgc)
      convert hh using 1
      rw [hs1, map_mul, map_natCast]
      push_cast
      first
      | (rw [mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hT0]; ring)
      | (field_simp; ring)
      | field_simp
  have hloc : ∀ P : Ideal (𝓞 E), P.IsPrime → ((T * T' : ℕ) : 𝓞 E) ∈ P →
      LocIn P ((g : E) ^ 2 * s) (T * T') := by
    intro P hP hmem
    rw [Nat.cast_mul] at hmem
    unfold LocIn
    rcases hP.mem_or_mem hmem with h | h
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP h
      refine ⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩
      rw [hyz]; push_cast; ring
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T' T g b _ hT' e2 hb P hP h
      refine ⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩
      rw [hyz]; push_cast; ring
  obtain ⟨β, hβ⟩ := divGlob _ (T * T') hTT hint hloc
  refine ⟨β, ?_⟩
  rw [hβ]; push_cast; ring

namespace IntegralityLocalGlobal

lemma formEq (a b c d : ℂ) (T T' : ℝ)
    (h : ∀ u v : ℂ, T * ‖a * u + b * v‖ ^ 2 - T' * ‖c * u + d * v‖ ^ 2 = T * ‖u‖ ^ 2 - T' * ‖v‖ ^ 2) :
    T ^ 2 * ‖b‖ ^ 2 = T' ^ 2 * ‖c‖ ^ 2 := by
  have h1 := h 1 0
  have h2 := h 0 1
  have h3 := h 1 1
  have h4 := h 1 Complex.I
  first
  | simp only [← Complex.normSq_eq_norm_sq] at h1 h2 h3 h4 ⊢
  | simp only [Complex.sq_norm] at h1 h2 h3 h4 ⊢
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.zero_re, Complex.zero_im, Complex.I_re,
    Complex.I_im] at h1 h2 h3 h4 ⊢
  linear_combination
    (T * (a.re * b.re + a.im * b.im) + T' * (c.re * d.re + c.im * d.im)) / 2 * (h3 - h1 - h2)
    + (T * (a.im * b.re - a.re * b.im) + T' * (c.im * d.re - c.re * d.im)) / 2 * (h4 - h1 - h2)
    - T * (b.re * b.re + b.im * b.im) * h1 - T' * (c.re * c.re + c.im * c.im) * h2

end IntegralityLocalGlobal

theorem theorem_B_statement : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ThmB := by
  intro E _ _ σ hσ hcx T T' g a b c d x hT hT' hg hiso hZZ hloc hx hxw
  have hTpos : 0 < T := by omega
  have hT'pos : 0 < T' := by omega
  have hTr : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hT'r : (0 : ℝ) < T' := by exact_mod_cast hT'pos
  have hgr : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    NumberField.InfinitePlace.mult_isComplex ⟨w, hcx w⟩
  have hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hne : Nonempty (InfinitePlace E) := by
    first
    | infer_instance
    | (apply Fintype.card_pos_iff.mp
       have := Module.finrank_pos (R := ℚ) (M := E)
       omega)
  obtain ⟨w0⟩ := hne
  have hcard : 1 ≤ Fintype.card (InfinitePlace E) := Fintype.card_pos_iff.mpr ⟨w0⟩
  have hnw : ∀ (w : InfinitePlace E) (y : E), w y = ‖w.embedding y‖ := fun w y =>
    (NumberField.InfinitePlace.norm_embedding_eq w y).symm
  have hI : ∀ y : 𝓞 E, IsInt (y : E) := fun y => by unfold IsInt; exact ⟨y, rfl⟩
  have hm1 : IsInt (-1 : E) := by simpa using hI (-1)
  have h1 : IsInt (1 : E) := by simpa using hI 1
  have normge : ∀ β : 𝓞 E, β ≠ 0 → 1 ≤ ∏ w : InfinitePlace E, (w (β : E)) ^ 2 := by
    intro β hβ
    have hp := NumberField.InfinitePlace.prod_eq_abs_norm (β : E)
    simp only [hm] at hp
    rw [hp, ← Algebra.coe_norm_int]
    have hn0 : Algebra.norm ℤ β ≠ 0 := Algebra.norm_ne_zero_iff.mpr hβ
    have h2 : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs hn0
    exact_mod_cast h2
  have hwn : ∀ w : InfinitePlace E,
      (T : ℝ) ^ 2 * ‖w.embedding b‖ ^ 2 = (T' : ℝ) ^ 2 * ‖w.embedding c‖ ^ 2 := fun w =>
    formEq _ _ _ _ _ _ (hiso w.embedding)
  have zz := integer_group_preservation E g a b c d hZZ
  have unit1 : ∀ (y : E) (N : ℕ), 3 ≤ N → IsInt (y - 1) →
      (∀ P : Ideal (𝓞 E), P.IsPrime → (N : 𝓞 E) ∈ P → LocIn P (y - 1) N) →
      (∀ w : InfinitePlace E, ‖w.embedding y‖ = 1) → y = 1 := by
    intro y N hN hi hl hy
    obtain ⟨β, hβ⟩ := divGlob (y - 1) N (by omega) hi hl
    by_contra hne
    have hβ0 : β ≠ 0 := by
      rintro rfl
      apply hne
      have h0 : y - 1 = 0 := by rw [hβ]; simp
      exact sub_eq_zero.mp h0
    have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have hb : ∀ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ 4 / 9 := by
      intro w
      have h5 : w.embedding y - 1 = (N : ℂ) * w.embedding (β : E) := by
        rw [← map_one w.embedding, ← map_sub, hβ, map_mul, map_natCast]
      have e1 : (N : ℝ) * ‖w.embedding (β : E)‖ = ‖w.embedding y - 1‖ := by
        rw [h5, norm_mul]
        simp
      have e2 : ‖w.embedding y - 1‖ ≤ 2 := by
        calc ‖w.embedding y - 1‖ ≤ ‖w.embedding y‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by rw [hy w, norm_one]; norm_num
      have e3 : 0 ≤ ‖w.embedding (β : E)‖ := norm_nonneg _
      have e4 : ‖w.embedding (β : E)‖ ≤ 2 / 3 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hNr) e3]
      rw [hnw]
      nlinarith [mul_nonneg e3 (sub_nonneg.mpr e4)]
    have hprod : ∏ w : InfinitePlace E, (w (β : E)) ^ 2 ≤ ∏ _w : InfinitePlace E, (4 / 9 : ℝ) :=
      Finset.prod_le_prod₀ (fun w _ => sq_nonneg _) (fun w _ => hb w)
    rw [Finset.prod_const, Finset.card_univ] at hprod
    have h49 : (4 / 9 : ℝ) ^ Fintype.card (InfinitePlace E) ≤ 4 / 9 :=
      pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith [normge β hβ0]
  by_cases hc0 : c = 0
  · left
    have hb0 : b = 0 := by
      have h := hwn w0
      rw [hc0, map_zero, norm_zero] at h
      have h2 : ‖w0.embedding b‖ ^ 2 = 0 :=
        mul_left_cancel₀ (pow_ne_zero 2 hTr.ne') (by rw [h]; ring)
      have h3 : w0.embedding b = 0 := norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
      exact (map_eq_zero_iff _ w0.embedding.injective).mp h3
    have ha1 : ∀ w : InfinitePlace E, ‖w.embedding a‖ = 1 := by
      intro w
      have h := hiso w.embedding 1 0
      rw [hb0, hc0] at h
      simp only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h
      have h2 : (T : ℝ) * (‖w.embedding a‖ ^ 2 - 1) = 0 := by linear_combination h
      have h3 := (mul_eq_zero.mp h2).resolve_left hTr.ne'
      nlinarith [norm_nonneg (w.embedding a)]
    have hd1 : ∀ w : InfinitePlace E, ‖w.embedding d‖ = 1 := by
      intro w
      have h := hiso w.embedding 0 1
      rw [hb0, hc0] at h
      simp only [map_zero, mul_one, mul_zero, zero_mul, add_zero, zero_add, norm_zero, norm_one] at h
      have h2 : (T' : ℝ) * (‖w.embedding d‖ ^ 2 - 1) = 0 := by linear_combination -h
      have h3 := (mul_eq_zero.mp h2).resolve_left hT'r.ne'
      nlinarith [norm_nonneg (w.embedding d)]
    have ha : a = 1 := unit1 a T hT
      (by convert isInt_add zz.2.2.2.2.1 hm1 using 1; rw [hb0]; ring)
      (fun P hP h => (hloc P hP (Or.inl h)).1) ha1
    have hd : d = 1 := unit1 d T' hT'
      (by convert isInt_mul hm1 (isInt_add zz.2.2.2.2.2 h1) using 1; rw [hc0]; ring)
      (fun P hP h => (hloc P hP (Or.inr h)).2.2.2) hd1
    exact ⟨ha, hb0, hc0, hd⟩
  · right
    obtain ⟨s, hs1⟩ : ∃ s : E, s = (T' : E) * c * σ c / (T : E) := ⟨_, rfl⟩
    have hs2 : s = (T : E) * b * σ b / (T' : E) := by
      rw [hs1]
      apply w0.embedding.injective
      have hconj : ∀ z : E,
          w0.embedding z * w0.embedding (σ z) = ((‖w0.embedding z‖ ^ 2 : ℝ) : ℂ) := by
        intro z
        rw [hσ, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      simp only [map_div₀, map_mul, map_natCast]
      rw [mul_assoc, mul_assoc, hconj, hconj]
      have hTc : (T : ℂ) ≠ 0 := by exact_mod_cast hTpos.ne'
      have hT'c : (T' : ℂ) ≠ 0 := by exact_mod_cast hT'pos.ne'
      rw [div_eq_div_iff hTc hT'c]
      have h' := congrArg (fun r : ℝ => (r : ℂ)) (hwn w0)
      push_cast at h' ⊢
      linear_combination -h'
    obtain ⟨β, hβ⟩ := s_integrality E σ T T' g s b c hTpos hT'pos hs1 hs2 zz.2.1 zz.2.2.1
      (fun P hP h => (hloc P hP (Or.inl h)).2.1) (fun P hP h => (hloc P hP (Or.inr h)).2.2.1)
    have hs0 : s ≠ 0 := by
      rw [hs1]
      have hσc : σ c ≠ 0 := fun h => hc0 (σ.injective (by rw [h, map_zero]))
      have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hTpos.ne'
      have hT'0 : (T' : E) ≠ 0 := Nat.cast_ne_zero.mpr hT'pos.ne'
      exact div_ne_zero (mul_ne_zero (mul_ne_zero hT'0 hc0) hσc) hT0
    have hβ0 : β ≠ 0 := by
      rintro rfl
      have hg0 : (g : E) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have h0 : (g : E) ^ 2 * s = 0 := by rw [hβ]; simp
      exact hs0 ((mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hg0))
    set q : ℝ := (T : ℝ) * T' / (g : ℝ) ^ 2 with hq_def
    have hq : 0 < q := div_pos (mul_pos hTr hT'r) (pow_pos hgr 2)
    have key : ∀ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤ (x w ^ 2) ^ 2 := by
      intro w
      have A : (g : ℝ) ^ 2 * ‖w.embedding s‖ = (T : ℝ) * T' * ‖w.embedding (β : E)‖ := by
        have h := congrArg (fun y => ‖w.embedding y‖) hβ
        simpa [map_mul, map_pow, map_natCast, norm_mul, norm_pow] using h
      have B : ‖w.embedding s‖ = (T' : ℝ) * ‖w.embedding c‖ ^ 2 / T := by
        rw [hs1]
        simp [hσ, norm_div] <;> ring
      have C := hxw w
      rw [hnw w c] at C
      have hs_le : ‖w.embedding s‖ ≤ x w ^ 2 := by rw [B]; exact C
      have hs_eq : ‖w.embedding s‖ = q * ‖w.embedding (β : E)‖ := by
        rw [hq_def, div_mul_eq_mul_div, eq_div_iff (pow_ne_zero 2 hgr.ne')]
        linear_combination A
      rw [hnw w, ← mul_pow, ← hs_eq]
      first
      | exact pow_le_pow_left (norm_nonneg _) hs_le 2
      | exact pow_le_pow_left₀ (norm_nonneg _) hs_le 2
      | nlinarith [norm_nonneg (w.embedding s)]
    apply complex_multiplication_root E q x hcx hq hx
    simp only [hm]
    rw [hn, pow_mul]
    have hprod : ∏ w : InfinitePlace E, q ^ 2 * (w (β : E)) ^ 2 ≤
        ∏ w : InfinitePlace E, (x w ^ 2) ^ 2 :=
      Finset.prod_le_prod₀ (fun w _ => by positivity) (fun w _ => key w)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ] at hprod
    have hqn : 0 ≤ (q ^ 2) ^ Fintype.card (InfinitePlace E) := by positivity
    have h3 := mul_le_mul_of_nonneg_left (normge β hβ0) hqn
    rw [mul_one] at h3
    linarith

end Formalism.HermitianLatticeCounting.P
end

namespace Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure

theorem torsionIndex : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TorsionIndex := Formalism.HermitianLatticeCounting.P.card_range_nsmul_mul_card_le
theorem perpCompl : Formalism.HermitianLatticeCounting.LocalIntegralStructure.PerpCompl := Formalism.HermitianLatticeCounting.P.orthogonal_complement_formula
theorem cofactorVec : Formalism.HermitianLatticeCounting.LocalIntegralStructure.CofactorVec := Formalism.HermitianLatticeCounting.P.cofactor_vector_formula
theorem localCongr : Formalism.HermitianLatticeCounting.LocalIntegralStructure.LocalCongr := Formalism.HermitianLatticeCounting.P.local_congruence_condition
theorem thmB : Formalism.HermitianLatticeCounting.LocalIntegralStructure.ThmB := Formalism.HermitianLatticeCounting.P.theorem_B_statement

theorem gramDetGen : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramDetGen := Formalism.HermitianLatticeCounting.P.gram_determinant_general
theorem gramNondeg : Formalism.HermitianLatticeCounting.LocalIntegralStructure.GramNondeg := Formalism.HermitianLatticeCounting.P.gram_matrix_nondegenerate
theorem arithmetic_square_bound_fourth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductInequalitySq := Formalism.HermitianLatticeCounting.P.L4_arithmetic_square
theorem arithmetic_square_bound_fifth : Formalism.HermitianLatticeCounting.LocalIntegralStructure.DetIndexProductPlacesInequalitySq := Formalism.HermitianLatticeCounting.P.L5_arithmetic_square

end Formalism.HermitianLatticeCounting.Final.LocalIntegralStructure
