module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelMultiplicativeEqProdDiagonalValuations
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonBorelJacquetOfCuspidalSegmentJacquet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InjectiveOfIndep
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelFormValueTorusGeneratorFirstGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedFormTorusTranslateVacuumValue

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelMultiplicativeEqProdDiagonalValuationsStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.borelMultiplicative_eq_prod_diagonal_valuations : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (f : GU σ n → ℂ), (∀ b b', IsBorelU b → IsBorelU b' → f (b * b') = f b * f b') → (∀ k ∈ KU σ n, IsBorelU k → f k = 1) → ∀ y : Fin (n / 2) → ℂ, (∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → f t = y k) → ∀ b, IsBorelU b → f b = ∏ k, y k ^ ordL (b.1.1 (lo n k) (lo n k)) := by
  first | exact @GlobalTheory.BorelChar.borel_char | exact GlobalTheory.BorelChar.borel_char | (intros; apply GlobalTheory.BorelChar.borel_char <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumDiagOrderEqOfIntegralTranslateIndicatorRelati
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumDiagOrderEqOfIntegralTranslateIndicatorRelati
noncomputable section

open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta.IntTranslate

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

theorem mem_int {α β : Type} {A : Matrix α β L} : A ∈ intMat L α β ↔ ∀ i j, A i j ∈ intL L := Iff.rfl

theorem int_mul {A B : Matrix (Fin m) (Fin m) L} (hA : A ∈ intMat L (Fin m) (Fin m))
    (hB : B ∈ intMat L (Fin m) (Fin m)) : A * B ∈ intMat L (Fin m) (Fin m) := by
  rw [mem_int] at hA hB ⊢
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hB k j)

theorem one_int : (1 : Matrix (Fin m) (Fin m) L) ∈ intMat L (Fin m) (Fin m) := by
  rw [mem_int]
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact Subring.one_mem _
  · exact Subring.zero_mem _

theorem int_transpose {A : Matrix (Fin m) (Fin m) L} :
    Aᵀ ∈ intMat L (Fin m) (Fin m) ↔ A ∈ intMat L (Fin m) (Fin m) := by
  simp only [mem_int, Matrix.transpose_apply]
  exact ⟨fun h i j => h j i, fun h i j => h j i⟩

def IsIntUnit (g : GL (Fin m) L) : Prop :=
  g.1 ∈ intMat L (Fin m) (Fin m) ∧ (g⁻¹).1 ∈ intMat L (Fin m) (Fin m)

theorem IsIntUnit.left {g : GL (Fin m) L} (hg : IsIntUnit g) (X : Matrix (Fin m) (Fin m) L) :
    g.1 * X ∈ intMat L (Fin m) (Fin m) ↔ X ∈ intMat L (Fin m) (Fin m) := by
  unfold IsIntUnit at hg
  constructor
  · intro h
    have e : X = (g⁻¹).1 * (g.1 * X) := by rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact int_mul hg.2 h
  · intro h
    exact int_mul hg.1 h

theorem IsIntUnit.right {g : GL (Fin m) L} (hg : IsIntUnit g) (X : Matrix (Fin m) (Fin m) L) :
    X * g.1 ∈ intMat L (Fin m) (Fin m) ↔ X ∈ intMat L (Fin m) (Fin m) := by
  unfold IsIntUnit at hg
  constructor
  · intro h
    have e : X = (X * g.1) * (g⁻¹).1 := by rw [mul_assoc, Units.mul_inv, mul_one]
    rw [e]
    exact int_mul h hg.2
  · intro h
    exact int_mul h hg.1

theorem isIntUnit_of_mem {g : GL (Fin m) L} (h : g ∈ GLint (Fin m) (intL L)) : IsIntUnit g := by
  unfold IsIntUnit
  exact ⟨mem_int.2 fun i j => P.cartan_entries_of_mem (intL L) g h i j,
    mem_int.2 fun i j => P.cartan_entries_of_mem (intL L) g⁻¹ (inv_mem h) i j⟩

theorem antiJ_transpose : (antiJ L m)ᵀ = antiJ L m := by
  ext i j
  simp only [Matrix.transpose_apply, antiJ]
  rw [Nat.add_comm j.val i.val]

theorem isIntUnit_antiG : IsIntUnit (antiG L m) := by
  have hJ : antiJ L m ∈ intMat L (Fin m) (Fin m) := by
    rw [mem_int]
    intro i j
    simp only [antiJ]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  exact And.intro hJ hJ

def glT (g : GL (Fin m) L) : GL (Fin m) L :=
  ⟨g.1ᵀ, (g⁻¹).1ᵀ, by rw [← Matrix.transpose_mul, g.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]⟩

theorem IsIntUnit.glT {g : GL (Fin m) L} (hg : IsIntUnit g) : IsIntUnit (glT g) := by
  unfold IsIntUnit at hg ⊢
  exact ⟨int_transpose.2 hg.1, int_transpose.2 hg.2⟩

theorem ordL_congr {x y : L} (h : Valued.v x = Valued.v y) : ordL x = ordL y := by
  simp only [ordL, h]

theorem diag_mul {A B : Matrix (Fin m) (Fin m) L} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id)
    (r : Fin m) : (A * B) r r = A r r * B r r := by
  rw [Matrix.mul_apply, Finset.sum_eq_single r]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA (show id k < id r from h), zero_mul]
    · rw [hB (show id r < id k from h), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ r) h

private lemma valued_v_le_one_of_mem_intL {x : L} (h : x ∈ intL L) : Valued.v x ≤ 1 := h

theorem v_diag_le {A B : GL (Fin m) L} (hA : A.1.BlockTriangular id) (hB : B.1.BlockTriangular id)
    (h : (A⁻¹).1 * B.1 ∈ intMat L (Fin m) (Fin m)) (r : Fin m) : Valued.v (B.1 r r) ≤ Valued.v (A.1 r r) := by
  have hAi : (A⁻¹).1.BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hA
  have h1 : (A⁻¹).1 r r * A.1 r r = 1 := by
    rw [← diag_mul hAi hA r, Units.inv_mul, Matrix.one_apply_eq]
  have h2 : Valued.v ((A⁻¹).1 r r * B.1 r r) ≤ 1 := by
    rw [← diag_mul hAi hB r]
    exact valued_v_le_one_of_mem_intL ((mem_int.1 h) r r)
  have h3 : Valued.v ((A⁻¹).1 r r) * Valued.v (A.1 r r) = 1 := by
    rw [← map_mul, h1, map_one]
  calc Valued.v (B.1 r r) = Valued.v ((A⁻¹).1 r r * B.1 r r) * Valued.v (A.1 r r) := by
        rw [map_mul, mul_comm (Valued.v ((A⁻¹).1 r r)) (Valued.v (B.1 r r)), mul_assoc, h3, mul_one]
    _ ≤ 1 * Valued.v (A.1 r r) := by gcongr
    _ = Valued.v (A.1 r r) := one_mul _

theorem ordL_diag_eq {A B : GL (Fin m) L} (hA : A.1.BlockTriangular id) (hB : B.1.BlockTriangular id)
    (h1 : (A⁻¹).1 * B.1 ∈ intMat L (Fin m) (Fin m)) (h2 : (B⁻¹).1 * A.1 ∈ intMat L (Fin m) (Fin m)) (r : Fin m) :
    ordL (A.1 r r) = ordL (B.1 r r) := by
  apply ordL_congr
  exact le_antisymm (v_diag_le hB hA h2 r) (v_diag_le hA hB h1 r)

end GlobalTheory.SphTheta.IntTranslate

namespace GlobalTheory.SphTheta.IntTranslate

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

theorem exists_min_of_preorder {κ : Type} (R : κ → κ → Prop) (hR : ∀ x, R x x)
    (ht : ∀ x y z, R x y → R y z → R x z) :
    ∀ s : Finset κ, s.Nonempty → ∃ k ∈ s, ∀ l ∈ s, R l k → R k l := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro h
    simp at h
  | @insert a s ha ih =>
    intro _
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, by simp, fun l hl _ => ?_⟩
      simp at hl
      subst hl
      exact hR _
    · obtain ⟨k, hk, hmin⟩ := ih hs
      by_cases hak : R a k ∧ ¬ R k a
      · refine ⟨a, Finset.mem_insert_self a s, fun l hl hla => ?_⟩
        rw [Finset.mem_insert] at hl
        rcases hl with rfl | hl
        · exact hR _
        · exact ht _ _ _ hak.1 (hmin l hl (ht _ _ _ hla hak.1))
      · refine ⟨k, Finset.mem_insert_of_mem hk, fun l hl hlk => ?_⟩
        rw [Finset.mem_insert] at hl
        rcases hl with rfl | hl
        · by_contra hc
          exact hak ⟨hlk, hc⟩
        · exact hmin l hl hlk

theorem mem_iff_of_mutual {A B : GL (Fin m) L} (h1 : (A⁻¹).1 * B.1 ∈ intMat L (Fin m) (Fin m))
    (h2 : (B⁻¹).1 * A.1 ∈ intMat L (Fin m) (Fin m)) (t : Matrix (Fin m) (Fin m) L) :
    t * B.1 ∈ intMat L (Fin m) (Fin m) ↔ t * A.1 ∈ intMat L (Fin m) (Fin m) := by
  constructor
  · intro h
    have e : t * A.1 = (t * B.1) * ((B⁻¹).1 * A.1) := by
      rw [mul_assoc, ← mul_assoc B.1, Units.mul_inv, one_mul]
    rw [e]
    exact int_mul h h2
  · intro h
    have e : t * B.1 = (t * A.1) * ((A⁻¹).1 * B.1) := by
      rw [mul_assoc, ← mul_assoc A.1, Units.mul_inv, one_mul]
    rw [e]
    exact int_mul h h1

theorem sum_mul_eq_zero_of_indicator {κ : Type} (a : κ → ℂ) (W : κ → GL (Fin m) L) (g : κ → ℂ)
    (hg : ∀ k l, ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m) →
      ((W l)⁻¹).1 * (W k).1 ∈ intMat L (Fin m) (Fin m) → g k = g l) :
    ∀ s : Finset κ, (∀ t : GL (Fin m) L,
      ∑ k ∈ s, a k * (if t.1 * (W k).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = 0) →
      ∑ k ∈ s, a k * g k = 0 := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro H
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      simp
    · obtain ⟨k, hk, hmax⟩ := exists_min_of_preorder
        (fun x y => ((W y)⁻¹).1 * (W x).1 ∈ intMat L (Fin m) (Fin m))
        (fun x => by simp only [Units.inv_mul]; exact one_int)
        (fun x y z hxy hyz => by
          have := int_mul hyz hxy
          rwa [mul_assoc, ← mul_assoc (W y).1, Units.mul_inv, one_mul] at this)
        s hs
      have hsum : ∑ l ∈ s.filter (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)), a l = 0 := by
        have := H (W k)⁻¹
        simp only [mul_ite, mul_one, mul_zero] at this
        rw [← Finset.sum_filter] at this
        exact this
      have hsub : ∀ t : GL (Fin m) L,
          ∑ l ∈ s.filter (fun l => ¬ (((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m))),
            a l * (if t.1 * (W l).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = 0 := by
        intro t
        have e : ∀ l ∈ s.filter (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)),
            a l * (if t.1 * (W l).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) =
              a l * (if t.1 * (W k).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) := by
          intro l hl
          rw [Finset.mem_filter] at hl
          rw [mem_iff_of_mutual hl.2 (hmax l hl.1 hl.2)]
        have h0 : ∑ l ∈ s.filter (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)),
            a l * (if t.1 * (W l).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = 0 := by
          rw [Finset.sum_congr rfl e, ← Finset.sum_mul, hsum, zero_mul]
        have := H t
        rw [← Finset.sum_filter_add_sum_filter_not s
          (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)), h0, zero_add] at this
        exact this
      have hrest := ih _ (Finset.filter_ssubset.2 ⟨k, hk, by
        simp only [not_not, Units.inv_mul]
        exact one_int⟩) hsub
      have e : ∀ l ∈ s.filter (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)),
          a l * g l = a l * g k := by
        intro l hl
        rw [Finset.mem_filter] at hl
        rw [hg k l hl.2 (hmax l hl.1 hl.2)]
      rw [← Finset.sum_filter_add_sum_filter_not s
        (fun l => ((W k)⁻¹).1 * (W l).1 ∈ intMat L (Fin m) (Fin m)), hrest, add_zero,
        Finset.sum_congr rfl e, ← Finset.sum_mul, hsum, zero_mul]

end GlobalTheory.SphTheta.IntTranslate

namespace GlobalTheory.SphTheta.IntTranslate

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {m : ℕ}

theorem glT_val (g : GL (Fin m) L) : (glT g).1 = g.1ᵀ := rfl

theorem antiG_val : (antiG L m).1 = antiJ L m := rfl

def leftSum {ι : Type} [Fintype ι] (c : ι → ℂ) (U : ι → GL (Fin m) L) (t : GL (Fin m) L) : ℂ :=
  ∑ i, c i * (if t.1 * (U i).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)

def rightSum {κ : Type} [Fintype κ] (c' : κ → ℂ) (V : κ → GL (Fin m) L) (t : GL (Fin m) L) : ℂ :=
  ∑ j, c' j * (if (V j).1 * t.1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)

theorem leftSum_mul {ι : Type} [Fintype ι] (c : ι → ℂ) (U : ι → GL (Fin m) L) {g : GL (Fin m) L}
    (hg : IsIntUnit g) (t : GL (Fin m) L) : leftSum c U (g * t) = leftSum c U t := by
  simp only [leftSum, Units.val_mul, mul_assoc, hg.left]

theorem rightSum_mul {κ : Type} [Fintype κ] (c' : κ → ℂ) (V : κ → GL (Fin m) L) {g : GL (Fin m) L}
    (hg : IsIntUnit g) (t : GL (Fin m) L) : rightSum c' V (t * g) = rightSum c' V t := by
  simp only [rightSum, Units.val_mul, ← mul_assoc, hg.right]

private lemma glT_mul (x y : GL (Fin m) L) : glT (x * y) = glT y * glT x := by
  ext1
  simp only [glT_val, Units.val_mul, Matrix.transpose_mul]

private lemma mul_antiG_glT_mem_intMat_iff (t X : GL (Fin m) L) :
    t.1 * (antiG L m * glT X * antiG L m).1 ∈ intMat L (Fin m) (Fin m) ↔
      X.1 * (antiG L m * glT t).1 ∈ intMat L (Fin m) (Fin m) := by
  rw [← int_transpose, ← (isIntUnit_antiG (L := L) (m := m)).left (X.1 * (antiG L m * glT t).1)]
  simp only [Units.val_mul, glT_val, antiG_val, Matrix.transpose_mul, Matrix.transpose_transpose,
    antiJ_transpose, mul_assoc]

theorem leftSum_eq_swap {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) {ι κ : Type} [Fintype ι] [Fintype κ]
    (c : ι → ℂ) (c' : κ → ℂ) (U : ι → GL (Fin m) L) (V : κ → GL (Fin m) L)
    (H : ∀ t : GL (Fin m) L, leftSum c U t = rightSum c' V t) (t : GL (Fin m) L) :
    leftSum c U t = leftSum c' (fun j => antiG L m * glT (V j) * antiG L m) t := by
  have hR : ∀ x g : GL (Fin m) L, IsIntUnit g → leftSum c U (x * g) = leftSum c U x :=
    fun x g hg => by rw [H, H, rightSum_mul c' V hg]
  have hT : leftSum c U (glT t) = leftSum c U t := by
    obtain ⟨a, -, k₁, hk₁, k₂, hk₂, e⟩ := GlobalTheory.LFun.UnitaryDiv.exists_cartan hU t
    obtain ⟨D, hD⟩ : ∃ D : GL (Fin m) L, D = k₁⁻¹ * t * k₂⁻¹ := ⟨_, rfl⟩
    have htD : t = k₁ * D * k₂ := by
      rw [hD]
      group
    have hDv : D.1 = Matrix.diagonal (fun i => ϖ ^ a i) := by
      rw [hD, Units.val_mul, Units.val_mul, e]
      simp only [← mul_assoc, Units.inv_mul, one_mul]
      rw [mul_assoc, Units.mul_inv, mul_one]
    have hDT : glT D = D := by
      ext1
      rw [glT_val, hDv, Matrix.diagonal_transpose]
    calc leftSum c U (glT t) = leftSum c U (glT k₂ * (D * glT k₁)) := by
          rw [htD, glT_mul, glT_mul, hDT]
      _ = leftSum c U (D * glT k₁) := leftSum_mul c U (IsIntUnit.glT (isIntUnit_of_mem hk₂)) _
      _ = leftSum c U D := hR _ _ (IsIntUnit.glT (isIntUnit_of_mem hk₁))
      _ = leftSum c U (D * k₂) := (hR _ _ (isIntUnit_of_mem hk₂)).symm
      _ = leftSum c U (k₁ * (D * k₂)) := (leftSum_mul c U (isIntUnit_of_mem hk₁) _).symm
      _ = leftSum c U t := by rw [htD, mul_assoc]
  have hsw : leftSum c' (fun j => antiG L m * glT (V j) * antiG L m) t =
      rightSum c' V (antiG L m * glT t) := by
    dsimp only [leftSum, rightSum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_antiG_glT_mem_intMat_iff]
  rw [hsw, ← H, leftSum_mul c U isIntUnit_antiG, hT]

private lemma antiJ_mul_mul_antiJ_apply (M : Matrix (Fin m) (Fin m) L) (r s : Fin m) :
    (antiJ L m * M * antiJ L m) r s = M r.rev s.rev := by
  have hl : ∀ (N : Matrix (Fin m) (Fin m) L) (r s : Fin m), (antiJ L m * N) r s = N r.rev s := by
    intro N r s
    rw [Matrix.mul_apply, Finset.sum_eq_single r.rev]
    · have h1 : r.val + r.rev.val + 1 = m := by
        rw [Fin.val_rev]
        have := r.isLt
        omega
      simp only [antiJ]
      rw [if_pos h1, one_mul]
    · intro b _ hb
      have h2 : ¬ (r.val + b.val + 1 = m) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      simp only [antiJ]
      rw [if_neg h2, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hr : ∀ (N : Matrix (Fin m) (Fin m) L) (r s : Fin m), (N * antiJ L m) r s = N r s.rev := by
    intro N r s
    rw [Matrix.mul_apply, Finset.sum_eq_single s.rev]
    · have h1 : s.rev.val + s.val + 1 = m := by
        rw [Fin.val_rev]
        have := s.isLt
        omega
      simp only [antiJ]
      rw [if_pos h1, mul_one]
    · intro b _ hb
      have h2 : ¬ (b.val + s.val + 1 = m) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      simp only [antiJ]
      rw [if_neg h2, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hr, hl]

end GlobalTheory.SphTheta.IntTranslate

namespace GlobalTheory.SphTheta


open IntTranslate in
theorem sum_ordL_diag_eq_of_indicator : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (m : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ] (c : ι → ℂ)
    (c' : κ → ℂ) (U : ι → GL (Fin m) L) (V : κ → GL (Fin m) L), (∀ i, (U i).1.BlockTriangular id) →
    (∀ j, (V j).1.BlockTriangular id) → (∀ t : GL (Fin m) L, ∑ i, c i * (if t.1 * (U i).1 ∈ intMat L (Fin m) (Fin m)
      then 1 else 0) = ∑ j, c' j * (if (V j).1 * t.1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)) →
    ∀ f : (Fin m → ℤ) → ℂ, ∑ i, c i * f (fun r => ordL ((U i).1 r r)) =
      ∑ j, c' j * f (fun r => ordL ((V j).1 r.rev r.rev)) := by
  intro L _ _ ϖ σ q hU m ι κ _ _ c c' U V hUt hVt H f
  have hsw : ∀ t : GL (Fin m) L, leftSum c U t = leftSum c' (fun j => antiG L m * glT (V j) * antiG L m) t :=
    fun t => leftSum_eq_swap hU c c' U V H t
  have htri : ∀ k, (Sum.elim U (fun j => antiG L m * glT (V j) * antiG L m) k).1.BlockTriangular id := by
    rintro (i | j)
    · exact hUt i
    · intro r s hrs
      simp only [Sum.elim_inr, Units.val_mul, glT_val, antiG_val]
      rw [GlobalTheory.SphTheta.IntTranslate.antiJ_mul_mul_antiJ_apply, Matrix.transpose_apply]
      exact hVt j (show id r.rev < id s.rev from Fin.rev_lt_rev.2 hrs)
  have hd : ∀ j r, (antiG L m * glT (V j) * antiG L m).1 r r = (V j).1 r.rev r.rev := by
    intro j r
    simp only [Units.val_mul, glT_val, antiG_val]
    rw [GlobalTheory.SphTheta.IntTranslate.antiJ_mul_mul_antiJ_apply, Matrix.transpose_apply]
  have hz : ∀ t : GL (Fin m) L, ∑ k ∈ Finset.univ, Sum.elim c (fun j => -c' j) k *
      (if t.1 * (Sum.elim U (fun j => antiG L m * glT (V j) * antiG L m) k).1 ∈ intMat L (Fin m) (Fin m)
        then 1 else 0) = 0 := by
    intro t
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
    exact sub_eq_zero.2 (hsw t)
  have key := sum_mul_eq_zero_of_indicator (Sum.elim c (fun j => -c' j))
    (Sum.elim U (fun j => antiG L m * glT (V j) * antiG L m))
    (fun k => f (fun r => ordL ((Sum.elim U (fun j => antiG L m * glT (V j) * antiG L m) k).1 r r)))
    (fun k l h1 h2 => congrArg f (funext fun r => ordL_diag_eq (htri k) (htri l) h1 h2 r))
    Finset.univ hz
  rw [Fintype.sum_sum_type] at key
  simp only [Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib, hd, ← sub_eq_add_neg] at key
  exact sub_eq_zero.1 key

end GlobalTheory.SphTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumDiagOrderEqOfIntegralTranslateIndicatorRelatiStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_diag_order_eq_of_integralTranslateIndicator_relation : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (m : ℕ) (ι κ : Type) [Fintype ι] [Fintype κ] (c : ι → ℂ) (c' : κ → ℂ) (U : ι → GL (Fin m) L) (V : κ → GL (Fin m) L), (∀ i, (U i).1.BlockTriangular id) → (∀ j, (V j).1.BlockTriangular id) → (∀ t : GL (Fin m) L, ∑ i, c i * (if t.1 * (U i).1 ∈ intMat L (Fin m) (Fin m) then 1 else 0) = ∑ j, c' j * (if (V j).1 * t.1 ∈ intMat L (Fin m) (Fin m) then 1 else 0)) → ∀ f : (Fin m → ℤ) → ℂ, ∑ i, c i * f (fun r => ordL ((U i).1 r r)) = ∑ j, c' j * f (fun r => ordL ((V j).1 r.rev r.rev)) := by
  first | exact @GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator | exact GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator | (intros; apply GlobalTheory.SphTheta.sum_ordL_diag_eq_of_indicator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeVecSatakeSumUnitaryBorelRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeVecSatakeSumUnitaryBorelRepresentatives
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SatBorel

theorem heckeVec_satU_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ), ∀ h ∈ Hecke ℂ (KU σ n), ∃ (ι : Type) (_ : Fintype ι) (b : ι → GU σ n), (∀ i, IsBorelU (b i)) ∧ (∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (s : M), (∀ k ∈ KU σ n, π k s = s) → heckeVec π (KU σ n) h s = ∑ i, h (b i) • π (b i) s) ∧ ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = ∑ i, h (b i) * ∏ k : Fin (n / 2), ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((b i).1.1 (lo n k) (lo n k)) := by
  intro L _ _ _ ϖ σ q hU n h hh
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have hfin := P.finite_support_cosets hK hh.2
  have hI : ∀ c : GU σ n ⧸ KU σ n, ∃ b : GU σ n, IsBorelU b ∧ (b : GU σ n ⧸ KU σ n) = c := by
    intro c
    obtain ⟨b, k, hb, hk, e⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 c.out
    refine ⟨b, hb, ?_⟩
    conv_rhs => rw [← QuotientGroup.out_eq' c, e]
    exact QuotientGroup.eq.2 (by simpa using hk)
  choose s hsB hs using hI
  have hhs : ∀ c, h (s c) = h c.out := by
    intro c
    have hk : (c.out)⁻¹ * s c ∈ KU σ n := QuotientGroup.eq.1 (c.out_eq'.trans (hs c).symm)
    have e : s c = 1 * c.out * ((c.out)⁻¹ * s c) := by group
    rw [e]
    exact hh.1 1 ⟨_, hk⟩ c.out
  have c1 : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (x : M),
      (∀ k ∈ KU σ n, π k x = x) →
      heckeVec π (KU σ n) h x = ∑ i : hfin.toFinset, h (s i.1) • π (s i.1) x := by
    intro M _ _ π x hx
    rw [GlobalTheory.LFun.heckeVec_eq_of_section hh.1 (GlobalTheory.LGrp.mem_fixed.2 hx) s hs,
      finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_, ← Finset.sum_coe_sort]
    intro c hc
    rw [Set.Finite.coe_toFinset, Set.mem_setOf_eq, ← hhs]
    intro h0
    exact hc (by simp [h0])
  refine ⟨hfin.toFinset, inferInstance, fun i => s i.1, fun i => hsB _, c1, fun α => ?_⟩
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega)
    (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have e := congrFun (Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
    (fun i => (α i).ne_zero) h hh φ hφ) 1
  have hfix : ∀ k ∈ KU σ n, GlobalTheory.PRep.rightReg ℂ (GU σ n) ℂ k φ = φ := by
    intro k hk
    funext g
    change φ (g * k) = φ g
    simpa [GlobalTheory.LFun.chiDeltaU_one] using hφ 1 g k GlobalTheory.LFun.isBorelU_one hk
  rw [← GlobalTheory.LFun.heckeVec_rightReg hK hh, c1 _ _ φ hfix] at e
  have hχ : ∀ i : hfin.toFinset, φ (s i.1) = ∏ k : Fin (n / 2),
      ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((s i.1).1.1 (lo n k) (lo n k)) := by
    intro i
    have := hφ (s i.1) 1 1 (hsB _) (one_mem _)
    simp only [mul_one, h1] at this
    rw [this]
    unfold chiDeltaU
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [dite_eq_left (by omega), mul_zpow, ← _root_.zpow_mul]
    have hl : lo n k = ⟨k.1, by omega⟩ := rfl
    rw [hl]
    congr 2
    ring
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h1, mul_one] at e
  rw [← e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hχ i]
  exact congrArg (h (s i.1) * ·) (congrArg φ (one_mul _))

end GlobalTheory.SatBorel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeVecSatakeSumUnitaryBorelRepresentativesStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeVec_satake_sum_unitaryBorel_representatives : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ), ∀ h ∈ Hecke ℂ (KU σ n), ∃ (ι : Type) (_ : Fintype ι) (b : ι → GU σ n), (∀ i, IsBorelU (b i)) ∧ (∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GU σ n) M) (s : M), (∀ k ∈ KU σ n, π k s = s) → heckeVec π (KU σ n) h s = ∑ i, h (b i) • π (b i) s) ∧ ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = ∑ i, h (b i) * ∏ k : Fin (n / 2), ((α k : ℂ) * (q : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k.1 : ℤ)))) ^ ordL ((b i).1.1 (lo n k) (lo n k)) := by
  first | exact @GlobalTheory.SatBorel.heckeVec_satU_borel | exact GlobalTheory.SatBorel.heckeVec_satU_borel | (intros; apply GlobalTheory.SatBorel.heckeVec_satU_borel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperTriangularUnitaryLowerHalfBlockTriangular
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperTriangularUnitaryLowerHalfBlockTriangular
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SphTheta.LowBlocks

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ordL_congr_v {x y : L} (h : Valued.v x = Valued.v y) : Formalism.UG.ordL x = Formalism.UG.ordL y := by
  unfold Formalism.UG.ordL
  by_cases hx : Valued.v x = 0
  · have hy : Valued.v y = 0 := h ▸ hx
    rw [dite_eq_left hx, dite_eq_left hy]
  · have hy : Valued.v y ≠ 0 := h ▸ hx
    rw [dite_eq_right hx, dite_eq_right hy]
    congr 2
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, WithZero.coe_unzero, h]

theorem ordL_one_eq : Formalism.UG.ordL (1 : L) = 0 :=
  Formalism.UG.P.fIwasawa_ordL_unit 1 1 (by simp) (by simp) (by simp)

theorem ordL_of_mul_eq_one {x y : L} (h : x * y = 1) : Formalism.UG.ordL y = - Formalism.UG.ordL x := by
  have hx : x ≠ 0 := left_ne_zero_of_mul_eq_one h
  have hy : y ≠ 0 := right_ne_zero_of_mul_eq_one h
  have := Formalism.UG.P.fIwasawa_ordL_mul x y hx hy
  rw [h, ordL_one_eq] at this
  omega

variable {σ : L →+* L} {n : ℕ}

theorem ordL_rev_diag (hv : ∀ x, Valued.v (σ x) = Valued.v x) {b : GU σ n} (hb : IsBorelU b) (i : Fin n) :
    Formalism.UG.ordL (b.1.1 i.rev i.rev) = - Formalism.UG.ordL (b.1.1 i i) := by
  rw [ordL_of_mul_eq_one (Formalism.UG.P.fSatake_unit_diag hb i), ordL_congr_v (hv _)]

theorem diag_ne_zero {b : GU σ n} (hb : IsBorelU b) (i : Fin n) : b.1.1 i i ≠ 0 := fun h0 => by
  have := Formalism.UG.P.fSatake_unit_diag hb i
  rw [show (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 0 from h0, map_zero, zero_mul] at this
  exact zero_ne_one this

theorem lowBlock_tri {M : Matrix (Fin n) (Fin n) L} (hM : ∀ i j : Fin n, j < i → M i j = 0) :
    (lowBlock M).BlockTriangular id := fun i j hij => by
  apply hM
  rw [Fin.lt_def] at hij ⊢
  simp only [hi, id] at *
  omega

theorem hi_eq_rev_lo (r : Fin (n / 2)) : hi n r = (lo n r.rev).rev := by
  ext; simp only [hi, lo, Fin.val_rev]; omega

end GlobalTheory.SphTheta.LowBlocks


open GlobalTheory.SphTheta.LowBlocks in
theorem GlobalTheory.SphTheta.lowBlocks_borel : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (hn : n ≤ n'), (∀ g : GU σ n, IsBorelU g → ∃ U : GL (Fin (n / 2)) L, U.1 = lowBlock g.1.1 ∧ U.1.BlockTriangular id ∧ ∀ r, ordL (U.1 r r) = -ordL (g.1.1 (lo n r.rev) (lo n r.rev))) ∧ ∀ h : GU σ n', IsBorelU h → ∃ V : GL (Fin (n / 2)) L, V.1.BlockTriangular id ∧ (∀ r : Fin (n / 2), ordL (V.1 r.rev r.rev) = ordL (h.1.1 (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩) (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩))) ∧ ∀ t : Matrix (Fin (n / 2)) (Fin (n / 2)) L, lowBlock (h⁻¹).1.1 * (Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0) = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then (V.1 * t) ⟨r.1, e⟩ c else 0 := by
  intro L _ _ ϖ σ q hU n n' hn
  have hv : ∀ x, Valued.v (σ x) = Valued.v x := hU.2.1
  refine ⟨fun g hg => ?_, fun h hh => ?_⟩
  · have htri : (lowBlock g.1.1).BlockTriangular id := lowBlock_tri hg
    have hdet : (lowBlock g.1.1).det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]
      intro r _
      exact diag_ne_zero hg _
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, rfl, htri, fun r => ?_⟩
    show Formalism.UG.ordL (g.1.1 (hi n r) (hi n r)) = _
    rw [hi_eq_rev_lo, ordL_rev_diag hv hg]
  · have hle : n / 2 ≤ n' / 2 := Nat.div_le_div_right hn
    have hb' : IsBorelU h⁻¹ := Formalism.UG.P.fSatake_borel_inv hh
    set W := lowBlock (h⁻¹).1.1 with hW
    have hWt : W.BlockTriangular id := lowBlock_tri hb'
    set V0 : Matrix (Fin (n / 2)) (Fin (n / 2)) L := W.submatrix (Fin.castLE hle) (Fin.castLE hle) with hV0
    have htri : V0.BlockTriangular id := fun i j hij => hWt (by rw [Fin.lt_def] at hij ⊢; exact hij)
    have hdet : V0.det ≠ 0 := by
      rw [Matrix.det_of_upperTriangular htri, Finset.prod_ne_zero_iff]
      intro r _
      exact diag_ne_zero hb' _
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet, htri, fun r => ?_, fun t => ?_⟩
    · show Formalism.UG.ordL ((h⁻¹).1.1 (hi n' (Fin.castLE hle r.rev)) (hi n' (Fin.castLE hle r.rev))) = _
      have e : hi n' (Fin.castLE hle r.rev) = (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev := by
        ext; simp only [hi, lo, Fin.val_rev, Fin.coe_castLE]; omega
      rw [e]
      have a := ordL_of_mul_eq_one (Formalism.UG.P.fSatake_borel_diag_inv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩).rev)
      have b := ordL_rev_diag hv hh (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩)
      change Formalism.UG.ordL (h.1.1 _ _) = - Formalism.UG.ordL ((h⁻¹).1.1 _ _) at a
      linarith
    · ext r c
      simp only [Matrix.mul_apply, Matrix.of_apply]
      split_ifs with hr
      · have hr' : (Fin.castLE hle ⟨r.1, hr⟩ : Fin (n' / 2)) = r := Fin.ext rfl
        let emb : Fin (n / 2) ↪ Fin (n' / 2) := ⟨Fin.castLE hle, Fin.castLE_injective hle⟩
        rw [← Finset.sum_subset (s₁ := Finset.univ.map emb) (Finset.subset_univ _), Finset.sum_map]
        · refine Finset.sum_congr rfl fun k _ => ?_
          have hk : ((emb k : Fin (n' / 2)) : ℕ) < n / 2 := k.2
          rw [dite_eq_left hk]
          show W r (Fin.castLE hle k) * t ⟨k.1, hk⟩ c = W (Fin.castLE hle ⟨r.1, hr⟩) (Fin.castLE hle k) * t k c
          rw [hr']
        · intro k _ hk
          have : ¬ (k : ℕ) < n / 2 := fun e => hk (Finset.mem_map.2 ⟨⟨k.1, e⟩, Finset.mem_univ _, Fin.ext rfl⟩)
          rw [dite_eq_right this, mul_zero]
      · refine Finset.sum_eq_zero fun k _ => ?_
        split_ifs with hk
        · rw [hWt (show k < r by rw [Fin.lt_def]; omega), zero_mul]
        · rw [mul_zero]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpperTriangularUnitaryLowerHalfBlockTriangularStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperTriangularUnitary_lowerHalfBlock_triangular : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n n' : ℕ) (hn : n ≤ n'), (∀ g : GU σ n, IsBorelU g → ∃ U : GL (Fin (n / 2)) L, U.1 = lowBlock g.1.1 ∧ U.1.BlockTriangular id ∧ ∀ r, ordL (U.1 r r) = -ordL (g.1.1 (lo n r.rev) (lo n r.rev))) ∧ ∀ h : GU σ n', IsBorelU h → ∃ V : GL (Fin (n / 2)) L, V.1.BlockTriangular id ∧ (∀ r : Fin (n / 2), ordL (V.1 r.rev r.rev) = ordL (h.1.1 (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩) (lo n' ⟨n' / 2 - n / 2 + r.1, by omega⟩))) ∧ ∀ t : Matrix (Fin (n / 2)) (Fin (n / 2)) L, lowBlock (h⁻¹).1.1 * (Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0) = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then (V.1 * t) ⟨r.1, e⟩ c else 0 := by
  first | exact @GlobalTheory.SphTheta.lowBlocks_borel | exact GlobalTheory.SphTheta.lowBlocks_borel | (intros; apply GlobalTheory.SphTheta.lowBlocks_borel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTransformEqAtThetaLiftOfVacuumEq
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct

namespace GlobalTheory.SphTheta

theorem prodId1 : ∀ (n : ℕ) (qu : ℂˣ) (Y : ℂ), Y ≠ 0 → ∀ (α : Fin (n / 2) → ℂˣ) (d : Fin (n / 2) → ℤ), (∏ k, Y ^ d k) * ∏ r : Fin (n / 2), (Y * (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ (-d r.rev) = ∏ k, ((α k : ℂ) * (qu : ℂ) ^ (-((n : ℤ) - 1 - 2 * (k : ℤ)))) ^ d k := by
  intro n qu Y hY α d
  have hq := qu.ne_zero
  have hα : ∀ k, (α k : ℂ) ≠ 0 := fun k => (α k).ne_zero
  rw [← Equiv.prod_comp Fin.revPerm]
  conv_rhs => rw [← Equiv.prod_comp Fin.revPerm]
  simp only [Fin.revPerm_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [_root_.zpow_neg, ← div_eq_mul_inv, ← div_zpow]
  congr 1
  have e : ((n / 2 : ℕ) : ℤ) - 1 - ((k : ℕ) : ℤ) = ((k.rev : ℕ) : ℤ) := by
    have := k.isLt
    rw [Fin.val_rev]; omega
  rw [e, _root_.zpow_neg]
  have := hα k.rev
  have := zpow_ne_zero ((n : ℤ) - 1 - 2 * ((k.rev : ℕ) : ℤ)) hq
  field_simp

theorem prodId2 : ∀ (n n' : ℕ) (hn : n ≤ n') (qu : ℂˣ) (α : Fin (n / 2) → ℂˣ) (d : Fin (n' / 2) → ℤ), (∏ k, ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) ^ d k) * ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') * (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ d ⟨n' / 2 - n / 2 + r.1, by omega⟩ = ∏ k, ((liftPar qu n n' α k : ℂ) * (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ)))) ^ d k := by
  intro n n' hn qu α d
  have hq := qu.ne_zero
  have hfac : ∀ k : Fin (n' / 2), ((liftPar qu n n' α k : ℂ) * (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ)))) =
      ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) * (if h : n' / 2 - n / 2 ≤ k.1 then
        ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
          (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - ((k.1 - (n' / 2 - n / 2) : ℕ) : ℤ))) /
          (α (Fin.rev ⟨k.1 - (n' / 2 - n / 2), by omega⟩) : ℂ)) else 1) := by
    intro k
    unfold liftPar
    split_ifs with h1 h2 h2
    · omega
    · push_cast
      rw [mul_one, mul_assoc, ← zpow_add₀ hq]
      congr 2; ring
    · have e : (Fin.rev ⟨k.1 - (n' / 2 - n / 2), by omega⟩ : Fin (n / 2)) = ⟨n' / 2 - 1 - k.1, by omega⟩ :=
        Fin.ext (by simp only [Fin.val_rev]; omega)
      rw [e]
      have e2 : (qu : ℂ) ^ (-((n' : ℤ) - 1 - 2 * (k : ℤ))) = (qu : ℂ) ^ (-(n : ℤ)) * ((qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
          (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - ((k.1 - (n' / 2 - n / 2) : ℕ) : ℤ)))) := by
        rw [← zpow_add₀ hq, ← zpow_add₀ hq]
        congr 1
        have := k.isLt
        omega
      rw [e2]
      push_cast
      rw [pow_add]
      have := (α ⟨n' / 2 - 1 - k.1, by omega⟩).ne_zero
      field_simp
    · omega
  simp only [hfac, mul_zpow, Finset.prod_mul_distrib]
  congr 1
  symm
  rw [← Fin.prod_congr' _ (show n' / 2 - n / 2 + n / 2 = n' / 2 by omega), Fin.prod_univ_add]
  rw [Finset.prod_eq_one (fun i _ => ?_), one_mul]
  · refine Finset.prod_congr rfl fun r _ => ?_
    have e : Fin.cast (show n' / 2 - n / 2 + n / 2 = n' / 2 by omega) (Fin.natAdd (n' / 2 - n / 2) r) =
        ⟨n' / 2 - n / 2 + r.1, by omega⟩ := Fin.ext (by simp)
    rw [e, dite_eq_left (by simp)]
    simp only [Fin.val_mk, Nat.add_sub_cancel_left, Fin.eta]
  · rw [dite_eq_right (by simp; omega), _root_.one_zpow]

theorem satU_eq_satU_liftPar_of_heckeVec_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → n ≤ n' → ∀ h ∈ Hecke ℂ (KU σ n), ∀ h' ∈ Hecke ℂ (KU σ n'), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s → ∀ qu : ℂˣ, (qu : ℂ) = q → ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h' (fun i => (liftPar qu n n' α i : ℂ)) := by
  intro L _ _ _ ϖ σ q δ ψ n n' M _ _ ρ ω s hS hC hC' hnn h hh h' hh' hE qu hqu α
  have hU := hS.1.unr
  obtain ⟨ℓ, hℓs, hℓa, hℓ0, hℓu, hℓz⟩ := GlobalTheory.T.exists_mixedModelSelfDualLattice_invariant_linearForm L ϖ σ q δ ψ n n' M ρ ω s hS
  have hvac : LocVac ρ s := hS.2.2.1
  have hb1 : ∀ {N : ℕ}, IsBorelU (1 : GU σ N) := fun i j hij => by
    simp [Matrix.one_apply_ne (ne_of_gt hij)]
  have hmix := GlobalTheory.T.mixedModelInvariantForm_upperTriangular_pair_action L ϖ σ q δ ψ n n' M ρ ω s hS ℓ hℓa hℓu
  have hμ : ∀ b : GU σ n, IsBorelU b → ℓ (ω (b, 1) s) =
      ∏ k, ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n')) ^ ordL (b.1.1 (lo n k) (lo n k)) := by
    refine GlobalTheory.T.borelMultiplicative_eq_prod_diagonal_valuations L ϖ σ q hU n (fun g => ℓ (ω (g, 1) s)) ?_ ?_ _ ?_
    · intro b b' hb hb'
      have : ω (b * b', 1) s = ω (b, 1) (ω (b', 1) s) := by
        rw [show ((b * b', 1) : GU σ n × GU σ n') = (b, 1) * (b', 1) by simp, map_mul, Module.End.mul_apply]
      simp only [this]
      exact (hmix b 1 hb hb1).1 _
    · intro k hk _
      exact (congrArg ℓ (hS.1.fix k 1 (mem_KU_iff.1 hk) (by simpa using one_mem _) s hvac)).trans hℓs
    · intro k t ht
      rw [GlobalTheory.T.mixedModelForm_value_torusGenerator_firstGroup L ϖ σ q δ ψ n n' M ρ ω s hS hC ℓ hℓs hℓa hℓ0 k t ht, hqu]
  have hμ' : ∀ b : GU σ n', IsBorelU b → ℓ (ω (1, b) s) =
      ∏ k, ((-1) ^ n * (qu : ℂ) ^ (-(n : ℤ))) ^ ordL (b.1.1 (lo n' k) (lo n' k)) := by
    refine GlobalTheory.T.borelMultiplicative_eq_prod_diagonal_valuations L ϖ σ q hU n' (fun g => ℓ (ω (1, g) s)) ?_ ?_ _ ?_
    · intro b b' hb hb'
      have : ω (1, b * b') s = ω (1, b) (ω (1, b') s) := by
        rw [show ((1, b * b') : GU σ n × GU σ n') = (1, b) * (1, b') by simp, map_mul, Module.End.mul_apply]
      simp only [this]
      exact (hmix 1 b hb1 hb).1 _
    · intro k hk _
      exact (congrArg ℓ (hS.1.fix 1 k (by simpa using one_mem _) (mem_KU_iff.1 hk) s hvac)).trans hℓs
    · intro k t ht
      rw [GlobalTheory.T.mixedForm_torusTranslate_vacuum_value L ϖ σ q δ ψ n n' M ρ ω s hS hC' ℓ hℓs hℓa hℓ0 k t ht, hqu]
  obtain ⟨ι, _, b, hb, hvec, hsat⟩ := GlobalTheory.T.heckeVec_satake_sum_unitaryBorel_representatives L ϖ σ q hU n h hh
  obtain ⟨κ, _, b', hb', hvec', hsat'⟩ := GlobalTheory.T.heckeVec_satake_sum_unitaryBorel_representatives L ϖ σ q hU n' h' hh'
  have E := hE
  rw [hvec M (ω.comp (MonoidHom.inl _ _)) s (fun k hk => hS.1.fix k 1 (mem_KU_iff.1 hk) (by simpa using one_mem _) s hvac),
    hvec' M (ω.comp (MonoidHom.inr _ _)) s (fun k hk => hS.1.fix 1 k (by simpa using one_mem _) (mem_KU_iff.1 hk) s hvac)] at E
  simp only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply] at E
  obtain ⟨hbl1, hbl2⟩ := GlobalTheory.T.upperTriangularUnitary_lowerHalfBlock_triangular L ϖ σ q hU n n' hnn
  choose U hU1 hU2 hU3 using fun i => hbl1 (b i) (hb i)
  choose V hVt hV2 hV3 using fun j => hbl2 (b' j) (hb' j)
  obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin (n / 2)) (Fin (n / 2)) L → Matrix (Fin (n' / 2)) (Fin (n / 2)) L,
      ∀ t, Z t = Matrix.of fun (r : Fin (n' / 2)) (c : Fin (n / 2)) => if e : r.1 < n / 2 then t ⟨r.1, e⟩ c else 0 :=
    ⟨_, fun _ => rfl⟩
  have hZmul : ∀ t A, Z t * A = Z (t * A) := by
    intro t A; ext r c
    simp only [hZ, Matrix.mul_apply, Matrix.of_apply]
    split_ifs <;> simp
  have hZint : ∀ t, Z t ∈ intMat L (Fin (n' / 2)) (Fin (n / 2)) ↔ t ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) := by
    intro t
    constructor
    · intro ht i j
      have := ht ⟨i.1, by omega⟩ j
      simpa [hZ] using this
    · intro ht i j
      simp only [hZ, Matrix.of_apply]
      split_ifs
      exacts [ht _ _, zero_mem _]
  have hlow1 : ∀ N : ℕ, lowBlock (((1 : GU σ N) : GL (Fin N) L) : Matrix (Fin N) (Fin N) L) = 1 := by
    intro N
    simp only [OneMemClass.coe_one, Units.val_one, lowBlock]
    exact Matrix.submatrix_one _ (fun a b e => by simp [hi, Fin.ext_iff] at e; exact Fin.ext (by omega))
  have key : ∀ t : GL (Fin (n / 2)) L,
      ∑ i, (h (b i) * ℓ (ω (b i, 1) s)) * (if t.1 * (U i).1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) =
      ∑ j, (h' (b' j) * ℓ (ω (1, b' j) s)) * (if (V j).1 * t.1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
    intro t
    have l1 : ∀ i, ℓ (ρ (embLow n' n (Z t.1)) (ω (b i, 1) s)) =
        ℓ (ω (b i, 1) s) * (if t.1 * (U i).1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
      intro i
      rw [(hmix (b i) 1 (hb i) hb1).2, inv_one, hlow1, Matrix.one_mul, ← hU1 i, hZmul, hℓz, hZint]
    have l2 : ∀ j, ℓ (ρ (embLow n' n (Z t.1)) (ω (1, b' j) s)) =
        ℓ (ω (1, b' j) s) * (if (V j).1 * t.1 ∈ intMat L (Fin (n / 2)) (Fin (n / 2)) then 1 else 0) := by
      intro j
      have e3 := hV3 j t.1
      simp only [← hZ] at e3
      rw [(hmix 1 (b' j) hb1 (hb' j)).2, hlow1, Matrix.mul_one, e3, hℓz, hZint]
    have := congrArg (fun v => ℓ (ρ (embLow n' n (Z t.1)) v)) E
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, l1, l2] at this
    simpa only [mul_assoc] using this
  have G := GlobalTheory.T.sum_diag_order_eq_of_integralTranslateIndicator_relation L ϖ σ q hU (n / 2) ι κ _ _ U V hU2 hVt key
    (fun d => ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
      (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ d r)
  have hY : ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') : ℂ) ≠ 0 := by
    have := qu.ne_zero
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (zpow_ne_zero _ this)
  rw [hsat α, hsat' (liftPar qu n n' α)]
  simp only [← hqu]
  calc _ = ∑ i, (h (b i) * ℓ (ω (b i, 1) s)) * ∏ r : Fin (n / 2), ((-1) ^ n' * (qu : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') *
        (qu : ℂ) ^ ((n : ℤ) - 1 - 2 * (((n / 2 : ℕ) : ℤ) - 1 - (r : ℤ))) / (α r.rev : ℂ)) ^ ordL ((U i).1 r r) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hμ _ (hb i), mul_assoc, ← prodId1 n qu _ hY α]
        simp only [hU3]
    _ = _ := G
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hμ' _ (hb' j), mul_assoc, ← prodId2 n n' hnn qu α]
        simp only [hV2]

end GlobalTheory.SphTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeTransformEqAtThetaLiftOfVacuumEqStatement
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.satakeTransform_eq_at_thetaLift_of_vacuum_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → CayleyRule q n ρ (ω.comp (MonoidHom.inr _ _)) s → n ≤ n' → ∀ h ∈ Hecke ℂ (KU σ n), ∀ h' ∈ Hecke ℂ (KU σ n'), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s → ∀ qu : ℂˣ, (qu : ℂ) = q → ∀ α : Fin (n / 2) → ℂˣ, SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h' (fun i => (liftPar qu n n' α i : ℂ)) := by
  first | exact @GlobalTheory.SphTheta.satU_eq_satU_liftPar_of_heckeVec_eq | exact GlobalTheory.SphTheta.satU_eq_satU_liftPar_of_heckeVec_eq | (intros; apply GlobalTheory.SphTheta.satU_eq_satU_liftPar_of_heckeVec_eq <;> assumption)
end
