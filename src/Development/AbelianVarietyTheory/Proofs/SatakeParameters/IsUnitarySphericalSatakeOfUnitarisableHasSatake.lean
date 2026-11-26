module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondIffRhoOfGoodPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapDiagUniformizerElementarySublattice
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapDiagUniformizerElementarySublattice
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

noncomputable section

namespace GlobalTheory.DiagElem

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) :
    x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

theorem mem_std {n : ℕ} (x : Fin n → w.adicCompletion E) :
    x ∈ (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      ∀ i, Valued.v (x i) ≤ 1 := by
  constructor
  · intro hx
    refine Submodule.span_induction (p := fun x _ => ∀ i, Valued.v (x i) ≤ 1) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨j, rfl⟩ i
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_apply, h]
    · intro i; simp
    · intro a b _ _ ha hb i
      simpa using (Valued.v.map_add (a i) (b i)).trans (max_le (ha i) (hb i))
    · intro c a _ ha i
      have hc : Valued.v (c : w.adicCompletion E) ≤ 1 := c.2
      show Valued.v ((c : w.adicCompletion E) * a i) ≤ 1
      rw [map_mul]
      exact mul_le_one' hc (ha i)
  · intro hx
    have e : x = ∑ i, (⟨x i, hx i⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_apply, Ne.symm hb]) (by simp)]
      simp only [Pi.basisFun_apply, Pi.smul_apply, Pi.single_eq_same]
      rw [Algebra.smul_def]
      simp
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

def dEnt {n : ℕ} (ϖ : w.adicCompletion E) (S : Finset (Fin n)) (i : Fin n) : w.adicCompletion E :=
  if i ∈ S then ϖ else 1

theorem mem_glMap_diag {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (S : Finset (Fin n))
    (d : GL (Fin n) (w.adicCompletion E))
    (hd : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (dEnt w ϖ S))
    (x : Fin n → w.adicCompletion E) :
    x ∈ glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔
      ∀ i, Valued.v (x i) ≤ Valued.v (dEnt w ϖ S i) := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by simp [IsUnifV, h0] at hϖ
  have hf0 : ∀ i, dEnt w ϖ S i ≠ 0 := fun i => by unfold dEnt; split_ifs <;> simp [hϖ0]
  simp only [glMap, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.toLin'_apply, hd,
    Matrix.mulVec_diagonal, mem_std]
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    rw [Matrix.mulVec_diagonal, map_mul]
    exact mul_le_of_le_one_right' (hy i)
  · intro hx
    refine ⟨fun i => x i / dEnt w ϖ S i, fun i => ?_, ?_⟩
    · rw [map_div₀]
      exact div_le_one_of_le₀ (hx i) zero_le
    · funext i
      rw [Matrix.mulVec_diagonal, mul_div_cancel₀ _ (hf0 i)]

end GlobalTheory.DiagElem

namespace GlobalTheory.DiagElem

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

def redS {n : ℕ} (S : Finset (Fin n)) :
    (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 →ₗ[w.adicCompletionIntegers E]
      (S → IsLocalRing.ResidueField (w.adicCompletionIntegers E)) where
  toFun x i := IsLocalRing.residue _ ⟨x.1 i, (mem_std w x.1).1 x.2 i⟩
  map_add' x y := by
    funext i
    rw [Pi.add_apply, ← map_add (f := _)]
    rfl
  map_smul' c x := by
    funext i
    rw [Pi.smul_apply, RingHom.id_apply, Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
      ← map_mul]
    congr 1

theorem redS_surjective {n : ℕ} (S : Finset (Fin n)) : Function.Surjective (redS w S) := by
  intro c
  choose a ha using fun i : S => IsLocalRing.residue_surjective (c i)
  refine ⟨⟨fun j => if h : j ∈ S then (a ⟨j, h⟩ : w.adicCompletion E) else 0,
    (mem_std w _).2 fun j => ?_⟩, ?_⟩
  · split_ifs
    · exact (a _).2
    · simp
  · funext ⟨i, hi⟩
    change IsLocalRing.residue _ _ = _
    rw [← ha]
    congr 1
    ext
    simp [hi]

theorem glMap_diag_mem_subElem :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
      (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ →
      ∀ (S : Finset (Fin n)) (d : GL (Fin n) (w.adicCompletion E)),
        (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
          Matrix.diagonal (fun i => if i ∈ S then ϖ else 1) →
        (haveI := GlobalTheory.RowSatakeBound.finite_residue w
         glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
           Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n)) := by
  intro E _ _ w n ϖ hϖ S d hd
  have hd' : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (dEnt w ϖ S) := hd
  have hϖle : Valued.v ϖ ≤ WithZero.exp (-1 : ℤ) := hϖ.le
  have hexp : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  refine ⟨⟨_, glMap_isLattice d (std _ _ n)⟩, ⟨⟨?_, ?_⟩, ?_⟩, rfl⟩
  · intro x hx
    rw [mem_glMap_diag w hϖ S d hd' x] at hx
    rw [mem_std]
    intro i
    refine (hx i).trans ?_
    unfold dEnt
    split_ifs
    · exact hϖle.trans hexp.le
    · simp
  · have hk : (glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1).comap
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1.subtype =
        LinearMap.ker (redS w S) := by
      ext x
      rw [Submodule.mem_comap, Submodule.subtype_apply, mem_glMap_diag w hϖ S d hd',
        LinearMap.mem_ker]
      have hx := (mem_std w x.1).1 x.2
      constructor
      · intro h
        funext ⟨i, hi⟩
        change IsLocalRing.residue _ _ = 0
        rw [IsLocalRing.residue_eq_zero_iff]
        apply Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr
        have := h i
        unfold dEnt at this
        rw [if_pos hi] at this
        exact lt_of_le_of_lt (this.trans hϖle) hexp
      · intro h i
        unfold dEnt
        split_ifs with hi
        · have := congrFun h ⟨i, hi⟩
          change IsLocalRing.residue _ _ = 0 at this
          rw [IsLocalRing.residue_eq_zero_iff] at this
          rw [hϖ]
          exact le_exp_neg_one_of_lt_one (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp this)
        · rw [map_one]; exact hx i
    change Nat.card ((std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ⧸
      (glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1).comap
        (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1.subtype) = _
    rw [hk, Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ (redS_surjective w S)).toEquiv,
      Nat.card_fun, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]
    rfl
  · rw [Submodule.smul_le]
    intro r hr x hx
    rw [mem_glMap_diag w hϖ S d hd']
    rw [mem_std] at hx
    have hr1 : Valued.v (r : w.adicCompletion E) < 1 :=
      Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hr
    intro i
    have hri : Valued.v ((r • x) i) < 1 := by
      change Valued.v ((r : w.adicCompletion E) * x i) < 1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (hx i)) hr1
    unfold dEnt
    split_ifs
    · rw [hϖ]; exact le_exp_neg_one_of_lt_one hri
    · rw [map_one]; exact hri.le

end GlobalTheory.DiagElem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GlMapDiagUniformizerElementarySublatticeStatement
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glMap_diagUniformizer_elementarySublattice : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (S : Finset (Fin n)) (d : GL (Fin n) (w.adicCompletion E)), (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i => if i ∈ S then ϖ else 1) → haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) := by
  first | exact @GlobalTheory.DiagElem.glMap_diag_mem_subElem | exact GlobalTheory.DiagElem.glMap_diag_mem_subElem | (intros; apply GlobalTheory.DiagElem.glMap_diag_mem_subElem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCartanDoubleCosetOfLatticeBetweenUniformizer
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsMore
namespace GlobalTheory.ClosedSubgroupCriterion

theorem main : ∀ {n j : ℕ} (a : Fin n → ℤ), Antitone a → (∀ (i : Fin n), a i = (0 : ℤ) ∨ a i = (1 : ℤ)) →
    Finset.card {i : Fin n | a i = (1 : ℤ)} = j → ∀ (i : Fin n), a i = (1 : ℤ) ↔ (↑i : ℕ) < j := by
  intro n j a ha h01 hj i
  constructor
  · intro hi
    by_contra hlt
    push_neg at hlt
    have hsub : Finset.Iic i ⊆ ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) := by
      intro k hk
      rw [Finset.mem_Iic] at hk
      have := ha hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases h01 k with h | h
      · rw [h, hi] at this; norm_num at this
      · exact h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic, hj] at this
    omega
  · intro hi
    rcases h01 i with h | h
    · exfalso
      have hsub : ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) ⊆ Finset.Iio i := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [Finset.mem_Iio]
        by_contra hle
        push_neg at hle
        have := ha hle
        rw [h, hk] at this; norm_num at this
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio, hj] at this
      omega
    · exact h

end GlobalTheory.ClosedSubgroupCriterion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCartanDoubleCosetOfLatticeBetweenUniformizer
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG

namespace GlobalTheory.ElemCartan

section Dvr

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {r : ℕ}

theorem coord_of_mem_std {x : Fin r → K} (hx : x ∈ (std O K r).1) (i : Fin r) :
    ∃ a : O, algebraMap O K a = x i := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases h : i = j
    · exact ⟨1, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

end Dvr

section Adic

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem zpow_mem_iff {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (m : ℤ) :
    ϖ ^ m ∈ w.adicCompletionIntegers E ↔ 0 ≤ m := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_zpow₀, hϖ, ← WithZero.coe_zpow,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zero, Multiplicative.ofAdd_le,
    smul_eq_mul]
  omega

theorem ne_zero_of_unif {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) : ϖ ≠ 0 := by
  intro h
  rw [IsUnifV, h, map_zero] at hϖ
  exact WithZero.zero_ne_coe hϖ

theorem antitone_zero_one {n j : ℕ} (a : Fin n → ℤ) (ha : Antitone a)
    (h01 : ∀ i, a i = 0 ∨ a i = 1)
    (hS : (Finset.univ.filter fun i => a i = 1).card = j) (i : Fin n) :
    a i = 1 ↔ (i : ℕ) < j := by
  rw [← hS]
  refine (Fin.lt_card_filter_univ_iff_apply_of_imp (fun k => a k = 1) ?_).symm
  intro k l hlk hk
  have hle := ha hlk
  rcases h01 l with hl | hl <;> omega

end Adic

theorem mem_doubleCoset_of_subElem :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
      (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ →
      ∀ (j : ℕ), j ≤ n → ∀ (g : GL (Fin n) (w.adicCompletion E)),
        (haveI := GlobalTheory.RowSatakeBound.finite_residue w
         glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
           Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) →
         ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
           (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
             (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * diagJ n ϖ j *
               (b : Matrix (Fin n) (Fin n) (w.adicCompletion E))) := by
  intro E _ _ w n ϖ hϖ j _ g hg
  have := GlobalTheory.RowSatakeBound.finite_residue w
  obtain ⟨M₀, hM, hMg⟩ := hg
  set L := std (w.adicCompletionIntegers E) (w.adicCompletion E) n with hLdef
  set M : Lat (w.adicCompletionIntegers E) (w.adicCompletion E) n := M₀ with hMdef
  have hϖ0 := ne_zero_of_unif w hϖ
  have hϖO : ϖ ∈ Ov E w := by
    have := (zpow_mem_iff w hϖ 1).2 zero_le_one
    simpa using this
  obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, e⟩ := Formalism.UG.Final.CartanDecomp E w n ϖ hϖO hϖ g
  have hs₁ : glMap k₁⁻¹ L.1 = L.1 := (GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n k₁⁻¹).2 (inv_mem hk₁)
  have hs₂ : glMap k₂⁻¹ L.1 = L.1 := (GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n k₂⁻¹).2 (inv_mem hk₂)
  set D : GL (Fin n) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hDdef
  have hD : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = diagPow E w ϖ a := by
    rw [hDdef, Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

  have hDL : glMap D L.1 = (k₁⁻¹ • M).1 := by
    rw [smul_def, glLat_val, hMg, hDdef, glMap_mul, glMap_mul, hs₂]
  have hMD : k₁⁻¹ • M ∈ subElem j L := by
    have h := (smul_mem_subElem_iff k₁⁻¹ j M L).2 hM
    have hL : k₁⁻¹ • L = L := Subtype.ext (by rw [smul_def, glLat_val, hs₁])
    rwa [hL] at h
  obtain ⟨⟨hle, hidx⟩, hmax⟩ := hMD
  rw [← hDL] at hle hidx hmax
  have hDe : ∀ (x : Fin n → w.adicCompletion E) (i : Fin n),
      Matrix.toLin' (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) x i = ϖ ^ (a i) * x i := by
    intro x i
    rw [Matrix.toLin'_apply, hD, diagPow, Matrix.mulVec_diagonal]

  have hpos : ∀ i, 0 ≤ a i := by
    intro i
    have hmem : Matrix.toLin' (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (Pi.basisFun (w.adicCompletion E) (Fin n) i) ∈ glMap D L.1 :=
      ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := coord_of_mem_std (hle hmem) i
    rw [hDe] at hc
    simp only [Pi.basisFun_apply, Pi.single_eq_same, mul_one] at hc
    rw [← zpow_mem_iff w hϖ, ← hc]
    exact c.2

  have hle1 : ∀ i, a i ≤ 1 := by
    intro i
    have hϖm : (⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) := by
      apply (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))))).2
      show Valued.v ϖ < 1
      rw [hϖ, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt]
      omega
    have hmem : (⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) • L.1 :=
      Submodule.smul_mem_smul hϖm (Submodule.subset_span ⟨i, rfl⟩)
    obtain ⟨x, hx, hxe⟩ := hmax hmem
    obtain ⟨c, hc⟩ := coord_of_mem_std hx i
    have hxi := congrFun hxe i
    simp only [LinearMap.coe_restrictScalars] at hxi
    rw [hDe] at hxi
    have hval : (((⟨ϖ, hϖO⟩ : w.adicCompletionIntegers E) • Pi.basisFun (w.adicCompletion E) (Fin n) i) i) = ϖ := by
      simp [Algebra.smul_def]
    rw [hval] at hxi
    have hx' : x i = ϖ ^ (1 - a i) := by
      rw [zpow_sub₀ hϖ0, zpow_one, eq_div_iff (zpow_ne_zero (a i) hϖ0), mul_comm]
      exact hxi
    rw [← sub_nonneg, ← zpow_mem_iff w hϖ, ← hx', ← hc]
    exact c.2
  have h01 : ∀ i, a i = 0 ∨ a i = 1 := fun i => by
    have := hpos i; have := hle1 i; omega

  set S : Finset (Fin n) := Finset.univ.filter fun i => a i = 1 with hSdef
  have hdiag : (fun i => ϖ ^ (a i)) = fun i => if i ∈ S then ϖ else 1 := by
    funext i
    rcases h01 i with h | h <;> simp [hSdef, h]
  have hD' : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal fun i => if i ∈ S then ϖ else 1 := by
    rw [hD, diagPow, hdiag]
  obtain ⟨M₂, ⟨⟨-, hidx₂⟩, -⟩, hM₂⟩ := GlobalTheory.T.glMap_diagUniformizer_elementarySublattice E w n ϖ hϖ S D hD'
  rw [hM₂] at hidx₂
  have hcard : S.card = j := by
    have h := hidx₂.symm.trans hidx
    exact Nat.pow_right_injective (two_le_qRes (O := w.adicCompletionIntegers E)) h
  have hkey := antitone_zero_one a ha h01 hcard
  refine ⟨k₁, hk₁, k₂, hk₂, ?_⟩
  rw [e]
  congr 2
  rw [diagPow, diagJ]
  congr 1
  funext i
  by_cases hi : (i : ℕ) < j
  · rw [ite_eq_left hi, (hkey i).2 hi, zpow_one]
  · rw [ite_eq_right hi]
    have : a i = 0 := (h01 i).resolve_right fun h => hi ((hkey i).1 h)
    rw [this, zpow_zero]

end GlobalTheory.ElemCartan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemCartanDoubleCosetOfLatticeBetweenUniformizerStatement
open NumberField IsDedekindDomain GlobalTheory.LatHecke Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_cartanDoubleCoset_of_lattice_between_uniformizer : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ (j : ℕ), j ≤ n → ∀ (g : GL (Fin n) (w.adicCompletion E)), haveI := GlobalTheory.RowSatakeBound.finite_residue w; glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈ Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) → ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w), (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
  first | exact @GlobalTheory.ElemCartan.mem_doubleCoset_of_subElem | exact GlobalTheory.ElemCartan.mem_doubleCoset_of_subElem | (intros; apply GlobalTheory.ElemCartan.mem_doubleCoset_of_subElem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatake
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

noncomputable section

namespace GlobalTheory.SatHecke

open GlobalTheory.LatHecke GlobalTheory.LFun Formalism.UG

section Lemmas

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))


variable {w} in
theorem diagJ_det_ne {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    (diagJ n ϖ j).det ≠ 0 := by
  have h0 : ϖ ≠ 0 := fun e => by simp [IsUnifV, e] at hϖ
  rw [diagJ, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs <;> simp [h0]

theorem stab_iff (n : ℕ) (g : GL (Fin n) (w.adicCompletion E)) :
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 =
      (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ↔ g ∈ GLint (Fin n) (Ov E w) :=
  GlobalTheory.T.glMap_standardLattice_eq_iff_mem_GLint_adic E w n g

theorem coset_of_elem (n : ℕ) (ϖ : w.adicCompletion E) (hϖ : IsUnifV E w ϖ) (j : ℕ) (hj : j ≤ n)
    (g : GL (Fin n) (w.adicCompletion E)) :
    haveI := GlobalTheory.RowSatakeBound.finite_residue w
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
      Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) →
    ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _) :=
  GlobalTheory.T.mem_cartanDoubleCoset_of_lattice_between_uniformizer E w n ϖ hϖ j hj g

theorem diag_elem (n : ℕ) (ϖ : w.adicCompletion E) (hϖ : IsUnifV E w ϖ) (S : Finset (Fin n))
    (d : GL (Fin n) (w.adicCompletion E))
    (hd : (d : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i => if i ∈ S then ϖ else 1)) :
    haveI := GlobalTheory.RowSatakeBound.finite_residue w
    glMap d (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
      Subtype.val '' subElem S.card (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) :=
  GlobalTheory.T.glMap_diagUniformizer_elementarySublattice E w n ϖ hϖ S d hd

theorem elem_of_coset (n : ℕ) (ϖ : w.adicCompletion E) (hϖ : IsUnifV E w ϖ) (j : ℕ) (hj : j ≤ n)
    (g : GL (Fin n) (w.adicCompletion E)) :
    haveI := GlobalTheory.RowSatakeBound.finite_residue w
    (∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
      (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _)) →
    glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 ∈
      Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n) := by
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  rintro ⟨a, ha, b, hb, e⟩
  set S : Finset (Fin n) := Finset.univ.filter fun i => (i : ℕ) < j
  have hS : S.card = j := by
    have : S = (Finset.range j).attachFin (n := n) (fun m hm => lt_of_lt_of_le (Finset.mem_range.1 hm) hj) := by
      ext i; simp [S]
    rw [this, Finset.card_attachFin, Finset.card_range]
  set D := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (diagJ_det_ne hϖ j)
  have hg : g = a * D * b := Units.ext (by rw [e]; simp [D, Matrix.GeneralLinearGroup.mkOfDetNeZero])
  obtain ⟨M, hM, hM'⟩ := diag_elem w n ϖ hϖ S D (by simp [D, Matrix.GeneralLinearGroup.mkOfDetNeZero, diagJ, S])
  rw [hS] at hM
  have hstd : ∀ k ∈ GLint (Fin n) (Ov E w), k • std (w.adicCompletionIntegers E) (w.adicCompletion E) n =
      std (w.adicCompletionIntegers E) (w.adicCompletion E) n := fun k hk => Subtype.ext ((stab_iff w n k).2 hk)
  refine ⟨glLat a M, ?_, ?_⟩
  · have := (smul_mem_subElem_iff a j M (std (w.adicCompletionIntegers E) (w.adicCompletion E) n)).2 hM
    rw [hstd a ha] at this
    exact this
  · rw [hg, glMap_mul, glMap_mul, (stab_iff w n b).2 hb, ← hM']
    rfl

end Lemmas

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}

theorem Tj_eq_dosetInd {n : ℕ} {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) (j : ℕ) :
    Tj ℂ n (Ov E w) ϖ j = dosetInd ℂ (GLint (Fin n) (Ov E w))
      (Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (diagJ_det_ne hϖ j)) := by
  unfold Tj dosetInd
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
  refine exists_congr fun a => and_congr_right fun _ => exists_congr fun b => and_congr_right fun _ => ?_
  rw [Units.ext_iff]
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero]

theorem heckeVec_Tj_eq_sum {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) {x : V} (hx : x ∈ fixed ρ (KGL w (n := n)))
    {ϖ : w.adicCompletion E} (hϖ : IsUnifV E w ϖ) {j : ℕ} (hj : j ≤ n)
    (s : Finset (GL (Fin n) (w.adicCompletion E)))
    (hs : haveI := GlobalTheory.RowSatakeBound.finite_residue w
      Set.BijOn (fun g => glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1) s
        (Subtype.val '' subElem j (std (w.adicCompletionIntegers E) (w.adicCompletion E) n))) :
    heckeVec ρ (KGL w (n := n)) (Tj ℂ n (Ov E w) ϖ j) x = ∑ g ∈ s, ρ g x := by
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  set D := Matrix.GeneralLinearGroup.mkOfDetNeZero (diagJ n ϖ j) (diagJ_det_ne hϖ j)
  have hD : ∀ g : GL (Fin n) (w.adicCompletion E), g ∈ DoubleCoset.doubleCoset D (KGL w (n := n) : Set _) (KGL w (n := n)) ↔
      ∃ a ∈ GLint (Fin n) (Ov E w), ∃ b ∈ GLint (Fin n) (Ov E w),
        (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _) := by
    intro g
    simp only [DoubleCoset.mem_doubleCoset, SetLike.mem_coe]
    refine exists_congr fun a => and_congr_right fun _ => exists_congr fun b => and_congr_right fun _ => ?_
    rw [Units.ext_iff]
    simp [D, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  rw [Tj_eq_dosetInd hϖ j]
  refine heckeVec_dosetInd hx (fun γ hγ => (hD γ).2 (coset_of_elem w n ϖ hϖ j hj γ (hs.mapsTo hγ)))
    fun g hg => ?_
  obtain ⟨γ, hγ, e⟩ := hs.surjOn (elem_of_coset w n ϖ hϖ j hj g ((hD g).1 hg))
  have hmem : ∀ γ' : GL (Fin n) (w.adicCompletion E),
      γ'⁻¹ * g ∈ KGL w (n := n) ↔ glMap γ' (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 =
        glMap g (std (w.adicCompletionIntegers E) (w.adicCompletion E) n).1 := fun γ' => by
    rw [← stab_iff w n, glMap_mul]
    constructor
    · intro h
      conv_lhs => rw [← h]
      rw [← glMap_mul, mul_inv_cancel, glMap_one]
    · intro h
      rw [← h, ← glMap_mul, inv_mul_cancel, glMap_one]
  refine ⟨γ, ⟨hγ, (hmem γ).2 e⟩, fun γ' ⟨hγ', h'⟩ => hs.injOn hγ' hγ ?_⟩
  exact ((hmem γ').1 h').trans e.symm

end GlobalTheory.SatHecke

namespace GlobalTheory.SatHecke

open GlobalTheory.LatHecke GlobalTheory.LFun Formalism.UG

def formCore {X : Type} [AddCommGroup X] [Module ℂ X] (B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ)
    (hB : ∀ v w, B w v = starRingEnd ℂ (B v w)) (hp : ∀ v, v ≠ 0 → 0 < (B v v).re) :
    InnerProductSpace.Core ℂ X where
  inner x y := B y x
  conj_inner_symm x y := (hB x y).symm
  re_inner_nonneg x := by
    by_cases h : x = 0
    · simp [h]
    · exact (hp x h).le
  add_left x y z := by change B z (x + y) = B z x + B z y; simp
  smul_left x y r := by change B y (r • x) = _ * B y x; simp
  definite x h := by
    by_contra h0
    have := hp x h0
    change B x x = 0 at h
    rw [h] at this
    simp at this

end GlobalTheory.SatHecke

namespace GlobalTheory.SatHecke

theorem isUnitarySatakeAt_of_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), letI := GlobalTheory.LocalData.complRel w; haveI := GlobalTheory.LocalData.isLocalField w; ∀ (π : Irr (w.adicCompletion E) n) (α : Fin n → ℂˣ), HasSatake π.π α → IsUnitarisable π.π → GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  intro E _ _ w n
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  intro π α hS hU
  have hG : GlobalTheory.LGrp.HasSatakeGL π.π (Finset.univ.val.map α) :=
    (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ π.π _).2 ⟨α, rfl, hS⟩
  obtain ⟨x, hx⟩ := (GlobalTheory.LFun.SatCompare.hasSatGL_of_hasSatakeGL hG).exists_vec
  obtain ⟨B, hB, hpos, hi⟩ := hU
  letI cd : InnerProductSpace.Core ℂ π.V := formCore B hB hpos
  letI : NormedAddCommGroup π.V := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ π.V := InnerProductSpace.ofCore cd.toCore
  haveI := GlobalTheory.RowSatakeBound.finite_residue w
  have hn : ∀ y : π.V, ‖y‖ ^ 2 = (B y y).re := fun y => by
    rw [← @inner_self_eq_norm_sq ℂ]
    rfl
  refine ⟨by simp, π.V, inferInstance, inferInstance, π.π, x, fun g y => ?_, hx.1, fun g hg => ?_, fun k hk s hs => ?_⟩
  · have h2 : ‖π.π g y‖ ^ 2 = ‖y‖ ^ 2 := by rw [hn, hn, hi]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2
  · exact GlobalTheory.LGrp.mem_fixed.1 hx.2.1 g ((stab_iff w n g).1 hg)
  · obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
    rw [← heckeVec_Tj_eq_sum π.π hx.2.1 hϖ hk s hs, hx.2.2.2 ϖ hϖ k hk, GlobalTheory.LFun.satEig, Multiset.map_map]
    congr 2
    rw [GlobalTheory.RowSatakeBound.qRes_eq_normV w]
    have hq : (Formalism.UG.qV E w : ℕ) = normV w := by
      unfold Formalism.UG.qV normV
      exact Ideal.absNorm_eq_natCard _
    rw [Complex.ofReal_cpow (Nat.cast_nonneg _), hq]
    push_cast
    rfl

end GlobalTheory.SatHecke
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatakeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), letI := GlobalTheory.LocalData.complRel w; haveI := GlobalTheory.LocalData.isLocalField w; ∀ (π : Irr (w.adicCompletion E) n) (α : Fin n → ℂˣ), HasSatake π.π α → IsUnitarisable π.π → GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  first | exact @GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | exact GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | (intros; apply GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake <;> assumption)
end
