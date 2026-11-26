module

public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvolutionInvariants
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PlaceRankTwoOne

@[expose] public section

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
open MeasureTheory Matrix Topology
open scoped NNReal ENNReal

noncomputable section

namespace Formalism.REAL

def indefiniteUnitaryMk {n : ℕ} (ε : Fin n → Bool) (m : Matrix (Fin n) (Fin n) ℂ) (h : inUJ ε m) : UJ ε :=
  ⟨⟨m, Jm ε * mᴴ * Jm ε, (indefinite_unitary_inv_closed n ε m h).1, (indefinite_unitary_inv_closed n ε m h).2⟩, h⟩

lemma indefiniteUnitaryMk_val {n : ℕ} (ε : Fin n → Bool) (m : Matrix (Fin n) (Fin n) ℂ) (h : inUJ ε m) :
    (((indefiniteUnitaryMk ε m h : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = m := rfl

lemma indefinite_unitary_ext {n : ℕ} {ε : Fin n → Bool} {g h : UJ ε}
    (e : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      ((h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) : g = h :=
  Subtype.ext (Units.ext e)

abbrev modularCharacterAlt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : ℝ≥0 := Measure.modularCharacterFun g

lemma map_mul_right_haar_modular_alt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) :
    Measure.map (fun x => x * g) (muG ε) = modularCharacterAlt ε g • muG ε := by
  rw [modularCharacterAlt, Measure.modularCharacterFun_eq_haarScalarFactor (muG ε) g]
  exact Measure.isMulLeftInvariant_eq_smul _ _

lemma modularCharacter_mul {n : ℕ} (ε : Fin n → Bool) (g h : UJ ε) :
    modularCharacterAlt ε (g * h) = modularCharacterAlt ε g * modularCharacterAlt ε h :=
  Measure.modularCharacterFun_map_mul g h

lemma modularCharacter_one {n : ℕ} (ε : Fin n → Bool) : modularCharacterAlt ε 1 = 1 :=
  Measure.modularCharacterFun_map_one

lemma continuous_frobenius_on_group {n : ℕ} (ε : Fin n → Bool) : Continuous (hsG (ε := ε)) :=
  continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)

lemma frobenius_ball_compact_pos_finite {n : ℕ} (ε : Fin n → Bool) :
    IsCompact {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧ 0 < muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧
      muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} < ⊤ := by
  have hc : IsCompact {g : UJ ε | hsG g ≤ (n : ℝ) + 1} := by
    have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage ((hermitian_small_ball n ε).1 ((n : ℝ) + 1))
    convert h using 1
    ext g
    exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩
  refine ⟨hc, ?_, hc.measure_lt_top⟩
  have hU : IsOpen {g : UJ ε | hsG g < (n : ℝ) + 1} :=
    isOpen_lt (continuous_frobenius_on_group ε) continuous_const
  have h1 : (1 : UJ ε) ∈ {g : UJ ε | hsG g < (n : ℝ) + 1} := by
    show hs (1 : Matrix (Fin n) (Fin n) ℂ) < (n : ℝ) + 1
    rw [f1auxiliary_hs_one]; linarith
  exact (hU.measure_pos (muG ε) ⟨1, h1⟩).trans_le
    (measure_mono fun g (hg : hsG g < (n : ℝ) + 1) => hg.le)

lemma modularCharacter_eq_one_on_compact {n : ℕ} (ε : Fin n → Bool) (g : UJ ε)
    (hk : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    modularCharacterAlt ε g = 1 := by
  obtain ⟨hc, hpos, hfin⟩ := frobenius_ball_compact_pos_finite ε
  set B := {g : UJ ε | hsG g ≤ (n : ℝ) + 1} with hB
  have hBm : MeasurableSet B := hc.isClosed.measurableSet
  have hpre : (fun x => x * g) ⁻¹' B = B := by
    ext x
    simp only [hB, Set.mem_preimage, Set.mem_ofPred_eq, hsG, Subgroup.coe_mul, Units.val_mul]
    rw [((hermitian_small_ball n ε).2 _ _ hk).1]
  have h1 := map_mul_right_haar_modular_alt ε g
  have h2 : (Measure.map (fun x => x * g) (muG ε)) B = muG ε B := by
    rw [Measure.map_apply (measurable_mul_const g) hBm, hpre]
  rw [h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((modularCharacterAlt ε g : ℝ≥0∞)) * muG ε B = 1 * muG ε B := by rw [h2, one_mul]
  rw [ENNReal.mul_left_inj hpos.ne' hfin.ne] at h3
  exact_mod_cast h3

lemma signature_mem_indefinite_unitary {n : ℕ} (ε : Fin n → Bool) : inUJ ε (Jm ε) :=
  (maximal_compact_facts n ε).1 _ (maximal_compact_facts n ε).2.2.1

lemma modularCharacter_eq_one_on_exp_hermitian {n : ℕ} (ε : Fin n → Bool) (p : UJ ε) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X)
    (hp : ((p : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp X) :
    modularCharacterAlt ε p = 1 := by
  set j := indefiniteUnitaryMk ε (Jm ε) (signature_mem_indefinite_unitary ε) with hj
  have hDj : modularCharacterAlt ε j = 1 := modularCharacter_eq_one_on_compact ε j (maximal_compact_facts n ε).2.2.1
  have hherm : (NormedSpace.exp X)ᴴ = NormedSpace.exp X :=
    exp_conjTranspose_of_hermitian (((parabolic_character_holds n ε X).1.mp hX).1)
  have hconj : j * p * j = p⁻¹ := by
    apply indefinite_unitary_ext
    have hinv := coeMatrix_inv_eq ε p
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    rw [hinv, hj, indefiniteUnitaryMk_val]
    show Jm ε * _ * Jm ε = Jm ε * (coeMatrixAlt ε p)ᴴ * Jm ε
    rw [show coeMatrixAlt ε p = NormedSpace.exp X from hp, hp, hherm]
  have h1 : modularCharacterAlt ε p⁻¹ = modularCharacterAlt ε p := by
    rw [← hconj, modularCharacter_mul, modularCharacter_mul, hDj, one_mul, mul_one]
  have h2 : modularCharacterAlt ε p * modularCharacterAlt ε p = 1 := by
    rw [← modularCharacter_one ε, ← mul_inv_cancel p, modularCharacter_mul, h1]
  have h3 : ((modularCharacterAlt ε p : ℝ≥0) : ℝ) * (modularCharacterAlt ε p : ℝ) = 1 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (modularCharacterAlt ε p : ℝ) := (modularCharacterAlt ε p).2
  have h5 : ((modularCharacterAlt ε p : ℝ≥0) : ℝ) = 1 := by nlinarith
  exact_mod_cast h5

lemma modularCharacter_eq_one_alt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : modularCharacterAlt ε g = 1 := by
  have hgU : inUJ ε ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := g.2
  obtain ⟨k, X, hk, hX, hg⟩ := (polar_decomposition_holds n ε).1 _ hgU
  have hkU : inUJ ε k := (maximal_compact_facts n ε).1 k hk
  have hEU : inUJ ε (NormedSpace.exp X) := by
    have h := exp_indefinite_unitary_holds n ε X hX.1 1
    rwa [Complex.ofReal_one, one_smul] at h
  have hdec : g = indefiniteUnitaryMk ε k hkU * indefiniteUnitaryMk ε _ hEU := by
    apply indefinite_unitary_ext
    rw [Subgroup.coe_mul, Units.val_mul, indefiniteUnitaryMk_val, indefiniteUnitaryMk_val]
    exact hg
  have hk' : (((indefiniteUnitaryMk ε k hkU : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      ∈ Kset ε := hk
  rw [hdec, modularCharacter_mul, modularCharacter_eq_one_on_compact ε _ hk', modularCharacter_eq_one_on_exp_hermitian ε _ X hX (indefiniteUnitaryMk_val ε _ hEU), one_mul]

theorem indefinite_unitary_unimodular : Unimodular := by
  intro n ε g
  rw [map_mul_right_haar_modular_alt, modularCharacter_eq_one_alt, one_smul]

theorem invInvariant_of (h : Unimodular) : InvInvariant :=
  _root_.UpperTheory.Reformulated.B.InvolutionInvariants.invInvariant_of h

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
open Finset

noncomputable section

namespace Formalism.REAL

lemma shiftedGenerator_eq_ite_smul_add {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ)
    (a b : Fin n) : Tm E x a b = (if a = b then x else 0) • (1 : A) + E a b := by
  unfold Tm
  split_ifs <;> simp [Algebra.algebraMap_eq_smul_one]

lemma ite_zero_eq_mul_ite (P : Prop) [Decidable P] (x : ℂ) :
    (if P then x else 0) = x * (if P then 1 else 0) := by
  split_ifs <;> simp

lemma ite_zero_eq_ite_smul {A : Type*} [Ring A] [Algebra ℂ A] (P : Prop) [Decidable P] (X : A) :
    (if P then X else 0) = (if P then (1 : ℂ) else 0) • X := by
  split_ifs <;> simp

private theorem Tm_eq_smul_one_add {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
    (E : Fin n → Fin n → A) (x : ℂ) (a b : Fin n) :
    Tm E x a b = (x * (if a = b then (1 : ℂ) else 0)) • (1 : A) + E a b := by
  rw [shiftedGenerator_eq_ite_smul_add, ite_zero_eq_mul_ite]

lemma shiftedGenerator_quadratic {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (x y : ℂ) (hxy : x - y = 1) (p q c d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d + Tm E x p d * Tm E y q c
      - Tm E x q d * Tm E y p c = 0 := by
  have hx : x = y + 1 := eq_add_of_sub_eq' hxy
  subst hx
  have h1 : E p c * E q d = E q d * E p c + ((if q = c then (1 : ℂ) else 0) • E p d
      - (if p = d then (1 : ℂ) else 0) • E q c) := by
    rw [eq_add_of_sub_eq' (hE p c q d)]
    congr 1
    rcases eq_or_ne c q with h | h
    · subst h
      rcases eq_or_ne d p with h' | h'
      · subst h'; simp
      · simp [h', h'.symm]
    · rcases eq_or_ne d p with h' | h'
      · subst h'; simp [h, h.symm]
      · simp [h, h.symm, h', h'.symm]
  have h2 : E p d * E q c = E q c * E p d + ((if q = d then (1 : ℂ) else 0) • E p c
      - (if p = c then (1 : ℂ) else 0) • E q d) := by
    rw [eq_add_of_sub_eq' (hE p d q c)]
    congr 1
    rcases eq_or_ne d q with h | h
    · subst h
      rcases eq_or_ne c p with h' | h'
      · subst h'; simp
      · simp [h', h'.symm]
    · rcases eq_or_ne c p with h' | h'
      · subst h'; simp [h, h.symm]
      · simp [h, h.symm, h', h'.symm]
  simp only [Tm_eq_smul_one_add]
  generalize (if p = c then (1 : ℂ) else 0) = δpc at h2 ⊢
  generalize (if q = d then (1 : ℂ) else 0) = δqd at h2 ⊢
  generalize (if q = c then (1 : ℂ) else 0) = δqc at h1 ⊢
  generalize (if p = d then (1 : ℂ) else 0) = δpd at h1 ⊢
  generalize E p c = Epc at h1 h2 ⊢
  generalize E q d = Eqd at h1 h2 ⊢
  generalize E q c = Eqc at h1 h2 ⊢
  generalize E p d = Epd at h1 h2 ⊢
  simp only [add_mul, mul_add]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  rw [h1, h2]
  module

lemma prod_ofFn_split_pair {M : Type*} [Monoid M] {t : ℕ} (f : Fin t → M) (i : ℕ) (hi : i + 1 < t) :
    (List.ofFn f).prod = ((List.ofFn f).take i).prod * (f ⟨i, by omega⟩ * f ⟨i + 1, hi⟩) *
      ((List.ofFn f).drop (i + 2)).prod := by
  have h0 : i < (List.ofFn f).length := by simp; omega
  have h1 : i + 1 < (List.ofFn f).length := by simp; omega
  conv_lhs => rw [← List.take_append_drop i (List.ofFn f)]
  rw [List.prod_append, List.drop_eq_getElem_cons h0, List.drop_eq_getElem_cons h1,
    show i + 2 = i + 1 + 1 from rfl]
  simp only [List.prod_cons, List.getElem_ofFn, mul_assoc]

lemma take_ofFn_congr {α : Type*} {t : ℕ} (f g : Fin t → α) (i : ℕ)
    (h : ∀ k : Fin t, (k : ℕ) < i → f k = g k) :
    (List.ofFn f).take i = (List.ofFn g).take i := by
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    simp only [List.getElem_take, List.getElem_ofFn]
    apply h
    simp only [List.length_take, List.length_ofFn] at hk₁
    show k < i
    omega

lemma drop_ofFn_congr {α : Type*} {t : ℕ} (f g : Fin t → α) (i : ℕ)
    (h : ∀ k : Fin t, i ≤ (k : ℕ) → f k = g k) :
    (List.ofFn f).drop i = (List.ofFn g).drop i := by
  apply List.ext_getElem
  · simp
  · intro k hk₁ hk₂
    simp only [List.getElem_drop, List.getElem_ofFn]
    apply h
    exact Nat.le_add_right _ _

lemma sandwich_alternating_sum {A : Type*} [Ring A] (L R a1 a2 a3 a4 : A) :
    L * a1 * R - L * a2 * R + L * a3 * R - L * a4 * R = L * (a1 - a2 + a3 - a4) * R := by
  simp only [mul_sub, mul_add, sub_mul, add_mul]

lemma prod_ofFn_alternating_sum {A : Type*} [Ring A] {t : ℕ} (f₁ f₂ f₃ f₄ : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h₂ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₂ k = f₁ k)
    (h₃ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₃ k = f₁ k)
    (h₄ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₄ k = f₁ k)
    (hmid : f₁ ⟨i, by omega⟩ * f₁ ⟨i + 1, hi⟩ - f₂ ⟨i, by omega⟩ * f₂ ⟨i + 1, hi⟩
      + f₃ ⟨i, by omega⟩ * f₃ ⟨i + 1, hi⟩ - f₄ ⟨i, by omega⟩ * f₄ ⟨i + 1, hi⟩ = 0) :
    (List.ofFn f₁).prod - (List.ofFn f₂).prod + (List.ofFn f₃).prod - (List.ofFn f₄).prod = 0 := by
  rw [prod_ofFn_split_pair f₁ i hi, prod_ofFn_split_pair f₂ i hi, prod_ofFn_split_pair f₃ i hi,
    prod_ofFn_split_pair f₄ i hi,
    take_ofFn_congr f₂ f₁ i (fun k hk => h₂ k (by omega) (by omega)),
    take_ofFn_congr f₃ f₁ i (fun k hk => h₃ k (by omega) (by omega)),
    take_ofFn_congr f₄ f₁ i (fun k hk => h₄ k (by omega) (by omega)),
    drop_ofFn_congr f₂ f₁ (i + 2) (fun k hk => h₂ k (by omega) (by omega)),
    drop_ofFn_congr f₃ f₁ (i + 2) (fun k hk => h₃ k (by omega) (by omega)),
    drop_ofFn_congr f₄ f₁ (i + 2) (fun k hk => h₄ k (by omega) (by omega)),
    sandwich_alternating_sum, hmid, mul_zero, zero_mul]

def exchangeTwo_self_eq_one {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin t)) : A :=
  (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (a (σ k)) (b k)).prod

lemma quantumMinor_eq_sum_term {A : Type*} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) (u : ℂ) :
    qminor E a b u = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * exchangeTwo_self_eq_one E a b u σ := rfl

lemma quantumMinorTerm_adjacent_swap {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1))) :
    exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
      + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
      - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) = 0 := by
  unfold exchangeTwo_self_eq_one
  have hi : (i : ℕ) + 1 < m + 1 := by omega
  have hfix : ∀ k : Fin (m + 1), (k : ℕ) ≠ i → (k : ℕ) ≠ (i : ℕ) + 1 →
      Equiv.swap i.castSucc i.succ k = k := by
    intro k hk₁ hk₂
    exact Equiv.swap_apply_of_ne_of_ne (fun h => hk₁ (by rw [h, Fin.val_castSucc]))
      (fun h => hk₂ (by rw [h, Fin.val_succ]))
  refine prod_ofFn_alternating_sum _ _ _ _ (i : ℕ) hi ?_ ?_ ?_ ?_
  · intro k hk₁ hk₂
    simp only [Equiv.Perm.mul_apply, hfix k hk₁ hk₂]
  · intro k hk₁ hk₂
    simp only [Function.comp_apply, hfix k hk₁ hk₂]
  · intro k hk₁ hk₂
    simp only [Equiv.Perm.mul_apply, Function.comp_apply, hfix k hk₁ hk₂]
  · have key := shiftedGenerator_quadratic E hE (u - ((i : ℕ) : ℂ)) (u - (((i : ℕ) + 1 : ℕ) : ℂ))
      (by push_cast; ring) (a (σ i.castSucc)) (a (σ i.succ)) (b i.castSucc) (b i.succ)
    have e0 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := rfl
    have e1 : (⟨(i : ℕ) + 1, hi⟩ : Fin (m + 1)) = i.succ := rfl
    simp only [e0, e1, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right]
    exact key

lemma eq_zero_of_add_self_eq_zero {A : Type*} [Ring A] [Algebra ℂ A] (X : A) (h : X + X = 0) : X = 0 := by
  calc X = ((2 : ℂ)⁻¹ * 2) • X := by rw [inv_mul_cancel₀ two_ne_zero, one_smul]
    _ = (2 : ℂ)⁻¹ • (X + X) := by rw [mul_smul, two_smul]
    _ = 0 := by rw [h, smul_zero]

lemma quantumMinor_adjacent_col_swap {A : Type*} [Ring A] [Algebra ℂ A] {n m : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E)
    (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) :
    qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u = - qminor E a b u := by
  have hsgn : Equiv.Perm.sign (Equiv.swap i.castSucc i.succ) = -1 :=
    Equiv.Perm.sign_swap (ne_of_lt Fin.castSucc_lt_succ)
  have reindex : ∀ bb : Fin (m + 1) → Fin n,
      ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
        exchangeTwo_self_eq_one E a bb u (σ * Equiv.swap i.castSucc i.succ) = - qminor E a bb u := by
    intro bb
    rw [quantumMinor_eq_sum_term, ← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.mulRight (Equiv.swap i.castSucc i.succ)) _ _ (fun σ => ?_)
    simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, hsgn, Units.val_neg, Int.cast_neg, mul_neg,
      mul_one, neg_mul, neg_neg]
  have hsum : ∑ σ : Equiv.Perm (Fin (m + 1)), ((Equiv.Perm.sign σ : ℤ) : A) *
      (exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
        + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
        - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ)) = 0 := by
    refine Finset.sum_eq_zero (fun σ _ => ?_)
    rw [quantumMinorTerm_adjacent_swap E hE a b i u σ, mul_zero]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum
  rw [reindex, reindex, ← quantumMinor_eq_sum_term, ← quantumMinor_eq_sum_term] at hsum
  have hX : qminor E a b u + qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u = 0 := by
    apply eq_zero_of_add_self_eq_zero
    convert hsum using 1
    abel
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact hX

theorem quantumMinorColSkew_holds : QSkewCol := by
  intro A _ _ n t E hE a b τ u
  cases t with
  | zero =>
    have hτ : τ = 1 := Subsingleton.elim _ _
    subst hτ
    simp
  | succ m =>
    have hτ : τ ∈ Submonoid.closure (Set.range fun i : Fin m => Equiv.swap i.castSucc i.succ) := by
      rw [Equiv.Perm.mclosure_swap_castSucc_succ]
      exact Submonoid.mem_top τ
    revert b
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro b
      have hs : i.castSucc ≠ i.succ := ne_of_lt Fin.castSucc_lt_succ
      rw [quantumMinor_adjacent_col_swap E hE a b i u, Equiv.Perm.sign_swap hs]
      simp
    | one =>
      intro b
      simp
    | mul x y _ _ hx hy =>
      intro b
      rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, hy (b ∘ ⇑x), hx b, ← mul_assoc,
        Equiv.Perm.sign_mul, mul_comm (Equiv.Perm.sign x), Units.val_mul, Int.cast_mul]

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
open Finset

noncomputable section

namespace Formalism.REAL

theorem quantumMinorRowSkew_holds : QSkewRow := by
  intro A _ _ n t E a b τ u
  unfold qminor
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => ?_)
  simp only [Equiv.coe_mulLeft]
  have hs : ((Equiv.Perm.sign τ : ℤ) : A) * ((Equiv.Perm.sign (τ * σ) : ℤ) : A) =
      ((Equiv.Perm.sign σ : ℤ) : A) := by
    rw [← Int.cast_mul, Equiv.Perm.sign_mul, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [← mul_assoc, hs]
  rfl

theorem prod_ofFn_apply_of_eigen {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V),
      (∀ k, F k v = c k • v) → (List.ofFn F).prod v = (∏ k, c k) • v := by
  intro m
  induction m with
  | zero => intro F c v _; simp
  | succ m ih =>
    intro F c v h
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply,
      ih (fun i => F i.succ) (fun i => c i.succ) v (fun i => h i.succ), map_smul, h 0, smul_smul,
      Fin.prod_univ_succ, mul_comm (c 0)]

theorem prod_ofFn_apply_eq_zero {V : Type*} [AddCommGroup V] [Module ℂ V] :
    ∀ (m : ℕ) (F : Fin m → Module.End ℂ V) (c : Fin m → ℂ) (v : V) (j : Fin m),
      F j v = 0 → (∀ k, j < k → F k v = c k • v) → (List.ofFn F).prod v = 0 := by
  intro m
  induction m with
  | zero => intro F c v j; exact j.elim0
  | succ m ih =>
    intro F c v j hj hk
    rw [List.ofFn_succ, List.prod_cons, Module.End.mul_apply]
    cases j using Fin.cases with
    | zero =>
      rw [prod_ofFn_apply_of_eigen m (fun i => F i.succ) (fun i => c i.succ) v (fun i => hk i.succ (Fin.succ_pos i)),
        map_smul, hj, smul_zero]
    | succ j' =>
      rw [ih (fun i => F i.succ) (fun i => c i.succ) v j' hj
        (fun i hi => hk i.succ (Fin.succ_lt_succ_iff.mpr hi)), map_zero]

theorem quantumDetHighestWeight_holds : QDetHW := by
  intro V _ _ n E ν v hE hv u
  obtain ⟨hdiag, hup⟩ := hv
  have hdiag' : ∀ k : Fin n, Tm E (u - (k : ℂ)) k k v = (u - (k : ℂ) + ν k) • v := by
    intro k
    rw [Tm, if_pos rfl, LinearMap.add_apply, Module.algebraMap_end_apply, hdiag k, add_smul]
  have hoff : ∀ j k : Fin n, j < k → Tm E (u - (k : ℂ)) j k v = 0 := by
    intro j k hjk
    simp [Tm, ne_of_lt hjk, hup j k hjk]
  unfold qdet qminor
  rw [LinearMap.sum_apply, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, id_eq, Equiv.Perm.one_apply]
    exact prod_ofFn_apply_of_eigen n _ _ v hdiag'
  · intro σ _ hσ
    have hne : (Finset.univ.filter fun k => σ k ≠ k).Nonempty := by
      by_contra hc
      apply hσ
      refine Equiv.ext fun k => ?_
      by_contra hk
      exact hc ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    set j := (Finset.univ.filter fun k => σ k ≠ k).max' hne with hj
    have hjmove : σ j ≠ j := (Finset.mem_filter.mp (Finset.max'_mem _ hne)).2
    have hfix : ∀ k, j < k → σ k = k := by
      intro k hk
      by_contra h
      have := Finset.le_max' (Finset.univ.filter fun k => σ k ≠ k) k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      exact (not_lt.mpr this) hk
    have hlt : σ j < j := by
      rcases lt_or_gt_of_ne hjmove with h | h
      · exact h
      · exact absurd (σ.injective (hfix (σ j) h)) hjmove
    have hP : (List.ofFn fun k : Fin n => Tm E (u - (k : ℂ)) (id (σ k)) (id k)).prod v = 0 := by
      apply prod_ofFn_apply_eq_zero n _ (fun k => u - (k : ℂ) + ν k) v j
      · exact hoff _ _ hlt
      · intro k hk
        simp only [id_eq, hfix k hk]
        exact hdiag' k
    rw [Module.End.mul_apply, hP, map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end Formalism.REAL
end
end

section -- merged from Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
open MeasureTheory Matrix Topology Metric Kronecker

noncomputable section

namespace Formalism.REAL

lemma stdBasis_repr_apply (n : ℕ) (x : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr x (i, j) = x i j := by
  simp [Matrix.stdBasis, Module.Basis.map_repr, Pi.basis_repr, Pi.basisFun_repr]

lemma det_mulLeft_complex {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (LinearMap.mulLeft ℂ g) = g.det ^ n := by
  classical
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  have : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)) (Matrix.stdBasis ℂ (Fin n) (Fin n))
      (LinearMap.mulLeft ℂ g) = g ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, stdBasis_repr_apply]
    simp only [Matrix.stdBasis_eq_single, Matrix.kroneckerMap_apply, Matrix.one_apply,
      LinearMap.mulLeft_apply, Matrix.mul_apply, Matrix.single_apply]
    by_cases h : j = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [this, Matrix.det_kronecker]
  simp

lemma det_leftMul_restrictScalars {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det ((LinearMap.mulLeft ℂ g).restrictScalars ℝ) = Complex.normSq g.det ^ n := by
  rw [LinearMap.det_restrictScalars, det_mulLeft_complex, map_pow, Algebra.norm_complex_apply]

lemma normSq_det_indefinite_unitary {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Complex.normSq g.det = 1 := by
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hJ : (Jm ε).det ≠ 0 := by
    have := congrArg Matrix.det (Jm_mul_self ε)
    rw [Matrix.det_mul, Matrix.det_one] at this
    intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this
  have h2 : star g.det * g.det = 1 := by
    have : (star g.det * g.det - 1) * (Jm ε).det = 0 := by linear_combination h
    rcases mul_eq_zero.1 this with h3 | h3
    · linear_combination h3
    · exact absurd h3 hJ
  rw [Complex.star_def] at h2
  have h3 : (Complex.normSq g.det : ℂ) = 1 := by rw [Complex.normSq_eq_conj_mul_self]; exact h2
  exact_mod_cast h3

abbrev MatrixCoordinates (n : ℕ) := Fin n → Fin n → ℂ

def matrixCoordinatesEquiv (n : ℕ) : MatrixCoordinates n ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := Matrix.ofLinearEquiv ℝ

def leftMulReal {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : MatrixCoordinates n →ₗ[ℝ] MatrixCoordinates n :=
  ((matrixCoordinatesEquiv n).symm : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] MatrixCoordinates n) ∘ₗ
    ((LinearMap.mulLeft ℂ g).restrictScalars ℝ) ∘ₗ
    ((matrixCoordinatesEquiv n : MatrixCoordinates n ≃ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ) :
      MatrixCoordinates n →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ)

lemma leftMulReal_apply {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (x : MatrixCoordinates n) :
    leftMulReal g x = Matrix.of.symm (g * Matrix.of x) := rfl

lemma det_leftMulReal_eq_one {n : ℕ} {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    LinearMap.det (leftMulReal g) = 1 := by
  unfold leftMulReal
  have := LinearMap.det_conj ((LinearMap.mulLeft ℂ g).restrictScalars ℝ)
    (matrixCoordinatesEquiv n).symm
  rw [LinearEquiv.symm_symm] at this
  rw [this, det_leftMul_restrictScalars, normSq_det_indefinite_unitary hg, one_pow]

section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

lemma frobenius_eq_norm_sq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : hs A = ‖A‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [hs]

lemma sqrt_frobenius_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Real.sqrt (hs A) = ‖A‖ := by
  rw [frobenius_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

lemma sqrt_frobenius_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (hs (A * B)) ≤ Real.sqrt (hs A) * Real.sqrt (hs B) := by
  simp only [sqrt_frobenius_eq_norm]; exact Matrix.frobenius_norm_mul A B

lemma sqrt_frobenius_add_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Real.sqrt (hs (A + B)) ≤ Real.sqrt (hs A) + Real.sqrt (hs B) := by
  simp only [sqrt_frobenius_eq_norm]; exact norm_add_le A B

end frob

lemma of_leftMulReal_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x : MatrixCoordinates n) :
    Matrix.of (leftMulReal A x) = A * Matrix.of x := by
  rw [leftMulReal_apply, Equiv.apply_symm_apply]

lemma determinant_character_mul {n : ℕ} {ε : Fin n → Bool} (g h : UJ ε) :
    coeMatrixAlt ε (g * h) = coeMatrixAlt ε g * coeMatrixAlt ε h := rfl

lemma determinant_character_mul_inv {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) :
    coeMatrixAlt ε g * coeMatrixAlt ε g⁻¹ = 1 := by
  rw [← determinant_character_mul, mul_inv_cancel]; rfl

section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

lemma norm_one_matrix_eq_sqrt (n : ℕ) : ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ = Real.sqrt n := by
  rw [← sqrt_frobenius_eq_norm, f1auxiliary_hs_one]

lemma norm_sub_one_lt_half {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : hs (u - 1) < 1 / 4) :
    ‖u - 1‖ < 1 / 2 := by
  rw [frobenius_eq_norm_sq] at hu
  nlinarith [norm_nonneg (u - 1)]

lemma norm_le_of_near_one {n : ℕ} {u : Matrix (Fin n) (Fin n) ℂ} (hu : hs (u - 1) < 1 / 4) :
    ‖u‖ ≤ Real.sqrt n + 1 / 2 := by
  have h1 := norm_sub_one_lt_half hu
  have h2 : ‖u‖ ≤ ‖(1 : Matrix (Fin n) (Fin n) ℂ)‖ + ‖u - 1‖ := by
    calc ‖u‖ = ‖1 + (u - 1)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [norm_one_matrix_eq_sqrt] at h2
  linarith

lemma frobenius_bound_of_mul_near_one {n : ℕ} {k u v : Matrix (Fin n) (Fin n) ℂ} (hu : hs (u - 1) < 1 / 4)
    (hv : hs (v - 1) < 1 / 4) (h : k * u = v) : hs k ≤ (2 * Real.sqrt n + 1) ^ 2 := by
  have e : k = v + k * (1 - u) := by rw [Matrix.mul_sub, Matrix.mul_one, h]; abel
  have h1 : ‖k‖ ≤ ‖v‖ + ‖k‖ * ‖1 - u‖ := by
    calc ‖k‖ = ‖v + k * (1 - u)‖ := by rw [← e]
      _ ≤ ‖v‖ + ‖k * (1 - u)‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact Matrix.frobenius_norm_mul _ _
  rw [norm_sub_rev] at h1
  have h2 := norm_sub_one_lt_half hu
  have h3 := norm_le_of_near_one hv
  have hk : ‖k‖ ≤ 2 * Real.sqrt n + 1 := by nlinarith [norm_nonneg k, norm_nonneg (u - 1)]
  rw [frobenius_eq_norm_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) hk 2

lemma norm_entry_mul_near_one_le {n : ℕ} {g u : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hg : hs g ≤ R ^ 2) (hu : hs (u - 1) < 1 / 4) (i j : Fin n) :
    ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  have hg' : ‖g‖ ≤ R := by
    rw [frobenius_eq_norm_sq] at hg
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 hg
  have hu' := norm_le_of_near_one hu
  have he : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have := f1auxiliary_entry_le (g * u) i j
    rw [frobenius_eq_norm_sq] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  calc ‖(g * u) i j‖ ≤ ‖g * u‖ := he
    _ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
    _ ≤ R * (Real.sqrt n + 1 / 2) := by gcongr
    _ ≤ R * (Real.sqrt n + 1) := by gcongr; norm_num

end frob

theorem ball_finite_measure_holds : BallFinite := by
  intro n ε R
  have hc : IsCompact {g : UJ ε | hsG g ≤ R} := by
    have := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage ((hermitian_small_ball n ε).1 R)
    convert this using 1
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hsG]
    exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩
  exact hc.measure_lt_top

theorem volume_growth : VolGrowth :=
  _root_.UpperTheory.Reformulated.B.placeRankTwoOne.volume_growth

end Formalism.REAL
end
end
