module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNEqSumCoeff
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HtDualExists
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ZetaSeriesLeafMainTermCurveSystem
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightGaugeSubMainTermLeaf
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeSubMainTermIntegralLowBidegree
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IndependentModFirstCoeffChainLastStep
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowAdditiveAndRoots
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.FrobRoot

variable {C : Type} [Field C] {V : VF C}

def intRing (V : VF C) : Subring C where
  carrier := {x | V.Ge 0 x}
  mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' := fun ha hb => VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' := fun ha => VF.Ge.neg ha

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos

theorem mm_of_ge_one {a : C} (ha : V.Ge 1 a) : V.MM a := by
  refine lt_of_lt_of_le ?_ ha
  exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)

theorem mm_pow {a : C} (ha : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by
  unfold VF.MM at *
  rw [V.v.map_pow]
  exact nsmul_pos ha hn

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (ha : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  unfold VF.Ge at *
  rw [V.v.map_pow] at ha
  rw [WithTop.coe_zero] at ha ⊢
  by_contra h
  exact absurd ha (not_le.mpr (nsmul_neg (not_le.mp h) hn))

theorem mm_add_pow (e : ℕ) {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) :
    V.MM ((a + b) ^ (V.l ^ e) - (a ^ (V.l ^ e) + b ^ (V.l ^ e))) := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime
    (⟨a, ha⟩ : intRing V) (⟨b, hb⟩ : intRing V) e
  have h := congrArg (Subtype.val) hr
  push_cast at h
  rw [h, add_sub_cancel_left]
  apply mm_of_ge_one
  have hr0 : V.Ge 0 (r : C) := r.2
  first
    | simpa using hr0.l_mul
    | simpa [mul_assoc] using (ha.mul_int (hb.mul_int hr0)).l_mul

theorem mm_sum_pow (e : ℕ) {ι : Type} (s : Finset ι) (x : ι → C) (hx : ∀ i ∈ s, V.Ge 0 (x i)) :
    V.MM ((∑ i ∈ s, x i) ^ (V.l ^ e) - ∑ i ∈ s, x i ^ (V.l ^ e)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero e V.l_prime.ne_zero), sub_zero]
    exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hs : ∀ i ∈ s, V.Ge 0 (x i) := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have h := mm_add (mm_add_pow e (hx a (Finset.mem_insert_self a s)) (VF.Ge.sum hs)) (ih hs)
    convert h using 1
    ring

end GlobalTheory.FrobRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IndependentModFirstCoeffChainLastStep
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot

namespace GlobalTheory.LastStep

theorem mm_mul_int {C : Type} [Field C] {V : VF C} {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) :
    V.MM (a * b) := by
  unfold VF.MM VF.Ge at *
  rw [V.v.map_mul]
  exact add_pos_of_pos_of_nonneg ha (by simpa using hb)

theorem mm_sum {C : Type} [Field C] {V : VF C} {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  have mm_zero : V.MM (0 : C) := by
    unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos
  have mm_add : ∀ {a b : C}, V.MM a → V.MM b → V.MM (a + b) :=
    fun ha hb => V.v.map_lt_add ha hb
  induction s using Finset.induction_on with
  | empty => simpa using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mm_of_tan {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
    {G : Cart V d I J} (S : Sys G) (w : I → C) (h : ∀ k, V.MM (∑ c, w c * S.tan c k)) (c : I) :
    V.MM (w c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have e : w c = ∑ k, (∑ b, w b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, w b * S.tan b k * S.U⁻¹ k c = w b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [Sys.U, Matrix.of_apply]; ring
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [e]
  exact mm_sum _ _ fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)

theorem indepMod_first_coeff : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by
  intro C _ V d _ I J _ _ X hA g a ha i S Z D hD s hs m y hy hind co hco hsum
  have mm_add : ∀ {a b : C}, V.MM a → V.MM b → V.MM (a + b) :=
    fun ha hb => V.v.map_lt_add ha hb
  have mm_pow : ∀ {a : C}, V.MM a → ∀ {n : ℕ}, n ≠ 0 → V.MM (a ^ n) := by
    intro a ha n hn
    unfold VF.MM at *
    rw [V.v.map_pow]
    exact nsmul_pos ha hn
  have ge_of_pow : ∀ {a : C} {n : ℕ}, n ≠ 0 → V.Ge 0 (a ^ n) → V.Ge 0 a := by
    intro a n hn ha
    unfold VF.Ge at *
    rw [V.v.map_pow] at ha
    rw [WithTop.coe_zero] at ha ⊢
    by_contra h
    exact absurd ha (not_le.mpr (nsmul_neg (not_le.mp h) hn))
  let R : Subring C := {
    carrier := {x | V.Ge 0 x}
    mul_mem' := fun ha hb => VF.Ge.mul_int ha hb
    one_mem' := VF.Ge.one
    add_mem' := fun ha hb => VF.Ge.add ha hb
    zero_mem' := VF.Ge.zero 0
    neg_mem' := fun ha => VF.Ge.neg ha }
  have mm_add_pow : ∀ (e : ℕ) {a b : C}, V.Ge 0 a → V.Ge 0 b →
      V.MM ((a + b) ^ (V.l ^ e) - (a ^ (V.l ^ e) + b ^ (V.l ^ e))) := by
    intro e a b ha hb
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨a, ha⟩ : R) (⟨b, hb⟩ : R) e
    have h := congrArg (Subtype.val) hr
    push_cast at h
    rw [h, add_sub_cancel_left]
    have hr0 : V.Ge 0 (r : C) := r.2
    have mm_of_ge_one : ∀ {x : C}, V.Ge 1 x → V.MM x := by
      intro x hx
      refine lt_of_lt_of_le ?_ hx
      exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)
    apply mm_of_ge_one
    first
      | simpa using hr0.l_mul
      | simpa [mul_assoc] using (ha.mul_int (hb.mul_int hr0)).l_mul
  have mm_sum_pow : ∀ (e : ℕ) {ι : Type} (s : Finset ι) (x : ι → C),
      (∀ i ∈ s, V.Ge 0 (x i)) →
      V.MM ((∑ i ∈ s, x i) ^ (V.l ^ e) - ∑ i ∈ s, x i ^ (V.l ^ e)) := by
    intro e ι s x hx
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, zero_pow (pow_ne_zero e V.l_prime.ne_zero), sub_zero]
      unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have hs : ∀ i ∈ s, V.Ge 0 (x i) := fun i hi => hx i (Finset.mem_insert_of_mem hi)
      have h := mm_add (mm_add_pow e (hx a (Finset.mem_insert_self a s)) (VF.Ge.sum hs)) (ih hs)
      convert h using 1 <;> ring
  haveI := X.algClosed
  have hl : V.l ≠ 0 := V.l_prime.ne_zero
  choose r hr using fun δ => IsAlgClosed.exists_pow_nat_eq (co δ) (Nat.pos_of_ne_zero hl)
  have hr0 : ∀ δ, V.Ge 0 (r δ) := fun δ => ge_of_pow hl (by rw [hr]; exact hco δ)
  set w : I g → C := fun c => ∑ δ, r δ * y δ c with hw
  have hw0 : ∀ c, V.Ge 0 (w c) := fun c => VF.Ge.sum fun δ _ => (hr0 δ).mul_int (hy δ c)
  set T := Finset.univ.filter (fun c => D.lev c = s) with hT
  have hbig : X.big g (a + ((2 * s : ℕ) : ZMod d)) :=
    (S4.parity_of_alt (X.big g) (CharacteristicFromRanks.alt_step X.big X.big_compl hA g) a ha (2 * s)).2 (even_two_mul s)
  have hgood : ∀ c ∈ T, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 : D.lev c = s := (Finset.mem_filter.1 hc).2
    have h2 : D.lev c < Formalism.BaseCaseIdentities.Kn i := h1 ▸ hs
    have h3 := hD.2.2.2.2 c h2
    rw [h1] at h3
    rw [← h3]
    exact hD.good (D.pure_good c (by rw [hD.2.2.1]; exact h2))
  have hG := Cart.Good.comb T (co := w) (fun c _ => hw0 c) hgood
  have hR := X.R2 hA g _ hbig _ _ hG (by
    intro κ
    rw [Cart.c0'_comb]
    have h1 : V.MM (∑ c ∈ T, (w c ^ V.l - ∑ δ, (r δ * y δ c) ^ V.l) * ((V.l : C) * S.be c 1 κ)) := by
      refine mm_sum _ _ fun c _ => mm_mul_int ?_ (l_mul_be_one_int S c κ)
      have := mm_sum_pow 1 Finset.univ (fun δ => r δ * y δ c) (fun δ _ => (hr0 δ).mul_int (hy δ c))
      simpa only [pow_one] using this
    have h2 := mm_add h1 (hsum κ)
    convert h2 using 1
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ) (t := T), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [mul_pow, hr, sub_mul, Finset.sum_mul, mul_assoc, sub_add_cancel]
    rfl)
  have hwm : ∀ c, V.MM (if D.lev c = s then w c else 0) := by
    refine mm_of_tan S _ fun k => ?_
    convert hR k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT, Finset.sum_filter, ite_mul, zero_mul]
  intro δ
  rw [← hr δ]
  refine mm_pow (hind r hr0 (fun c => ?_) δ) hl
  convert hwm c using 1
  by_cases hc : D.lev c = s <;> simp [hw, hc]

end GlobalTheory.LastStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IndependentModFirstCoeffChainLastStepStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.independentMod_firstCoeff_chainLastStep : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → IndepMod V (fun δ (κ : J g) => ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), y δ c ^ V.l * ((V.l : C) * S.be c 1 κ)) := by
  first | exact @GlobalTheory.LastStep.indepMod_first_coeff | exact GlobalTheory.LastStep.indepMod_first_coeff | (intros; apply GlobalTheory.LastStep.indepMod_first_coeff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsUnimodularMulEqNegOfIndependentModMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearIndependentSumElimOfFinrankEq
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory

theorem exists_linearIndependent_sumElim_of_finrank_eq {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] {n₀ n' : ℕ} (hV : Module.finrank k V = n₀ + n')
    (v : Fin n₀ → V) (hv : LinearIndependent k v) :
    ∃ w : Fin n' → V, LinearIndependent k (Sum.elim v w) := by
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range v))
  have h1 := Submodule.finrank_add_eq_of_isCompl hQ
  rw [finrank_span_eq_card hv, Fintype.card_fin, hV] at h1
  have h2 : Module.finrank k Q = n' := by omega
  let b := Module.finBasisOfFinrankEq k Q h2
  refine ⟨fun j => (b j : V), hv.sum_type (b.linearIndependent.map' Q.subtype Q.ker_subtype) ?_⟩
  refine hQ.disjoint.mono_right ?_
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact (b j).2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsUnimodularMulEqNegOfIndependentModMaximal
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory

theorem exists_isUnit_det_mul_eq_neg_of_linearIndependent_residue {R : Type} [CommRing R]
    [IsLocalRing R] (n n0 : ℕ) (Φ : Fin n → Fin n0 → R)
    (h : LinearIndependent (IsLocalRing.ResidueField R)
      (fun (c : Fin n0) (b : Fin n) => IsLocalRing.residue R (Φ b c))) :
    n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) R, IsUnit Y.det ∧
      ∀ (b : Fin n) (c : Fin n0), ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  have hle : n0 ≤ n := by simpa using h.fintype_card_le_finrank
  refine ⟨hle, ?_⟩
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨w, hw⟩ := exists_linearIndependent_sumElim_of_finrank_eq (n' := n') (by simp) _ h
  choose s hs using IsLocalRing.residue_surjective (R := R)
  let M : Matrix (Fin (n0 + n')) (Fin (n0 + n')) R := Matrix.of fun i j =>
    Sum.elim (Φ i) (fun j' => s (w j' i)) (finSumFinEquiv.symm j)
  have hcol : (M.map (IsLocalRing.residue R)).col =
      Sum.elim (fun (c : Fin n0) (b : Fin (n0 + n')) => IsLocalRing.residue R (Φ b c)) w ∘
        finSumFinEquiv.symm := by
    funext j i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases j with j | j
    · simp [M, Matrix.col]
    · simp [M, Matrix.col, hs]
  have hu : IsUnit (M.map (IsLocalRing.residue R)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact hw.comp _ finSumFinEquiv.symm.injective
  have hdet : IsUnit M.det := by
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    have : (M.map (IsLocalRing.residue R)).det = IsLocalRing.residue R M.det :=
      (RingHom.map_det (IsLocalRing.residue R) M).symm
    rw [this] at hu
    exact (isUnit_map_iff (IsLocalRing.residue R) _).mp hu
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  refine ⟨-M⁻¹, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det M hdet)).neg
  · intro b c
    have hij : ∑ b', M⁻¹ b b' * Φ b' c = (M⁻¹ * M) b (Fin.castAdd n' c) := by
      simp [M, Matrix.mul_apply]
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hij, hinv, Matrix.one_apply]
    by_cases hbc : b.val = c.val
    · rw [if_pos hbc, if_pos (Fin.ext hbc)]
    · rw [if_neg hbc, if_neg (fun e => hbc (by rw [e]; rfl)), neg_zero]

theorem exists_unimodular_mul_eq_neg_of_indepMod : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  intro C _ V n n0 Φ hΦ hind
  let O : ValuationSubring C := (AddValuation.toValuation V.v).valuationSubring
  have hmem : ∀ x : C, x ∈ O ↔ 0 ≤ V.v x := fun _ => Iff.rfl
  have hge : ∀ x : C, V.Ge 0 x ↔ 0 ≤ V.v x := fun _ => Iff.rfl
  have hunit : ∀ x : O, IsUnit x ↔ V.v (x : C) = 0 := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hx.exists_right_inv
      have h1 : V.v (x : C) + V.v (y : C) = 0 := by
        rw [← V.v.map_mul, ← V.v.map_one]
        exact congrArg (fun z : O => V.v (z : C)) hy
      have h2 := (hmem _).1 x.2
      have h3 := (hmem _).1 y.2
      exact le_antisymm (by
        calc V.v (x : C) = V.v (x : C) + 0 := (add_zero _).symm
          _ ≤ V.v (x : C) + V.v (y : C) := by gcongr
          _ = 0 := h1) h2
    · intro hx
      have hx0 : (x : C) ≠ 0 := by
        intro h0
        rw [h0, V.v.map_zero] at hx
        exact WithTop.top_ne_zero hx
      have h1 : V.v (x : C)⁻¹ = 0 := by
        have := V.v.map_mul (x : C) (x : C)⁻¹
        rw [mul_inv_cancel₀ hx0, V.v.map_one, hx, zero_add] at this
        exact this.symm
      exact IsUnit.of_mul_eq_one (⟨(x : C)⁻¹, (hmem _).2 h1.ge⟩ : O)
        (Subtype.ext (mul_inv_cancel₀ hx0))
  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ V.MM (x : C) := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    exact ⟨fun h => lt_of_le_of_ne ((hmem _).1 x.2) (Ne.symm h), fun h => ne_of_gt h⟩
  let Ψ : Fin n → Fin n0 → O := fun b c => ⟨Φ b c, (hmem _).2 ((hge _).1 (hΦ b c))⟩
  have hli : LinearIndependent (IsLocalRing.ResidueField O)
      (fun (c : Fin n0) (b : Fin n) => IsLocalRing.residue O (Ψ b c)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg ν
    choose s hs using IsLocalRing.residue_surjective (R := O)
    rw [← hs (g ν), hres]
    refine hind (fun ν => (s (g ν) : C)) (fun ν => (hge _).2 ((hmem _).1 (s (g ν)).2)) (fun x => ?_) ν
    have h1 : IsLocalRing.residue O (∑ ν, s (g ν) * Ψ x ν) = 0 := by
      have := congrFun hg x
      simpa [hs, Finset.sum_apply] using this
    rw [hres] at h1
    simpa [Ψ] using h1
  obtain ⟨hle, Y, hY, hYΦ⟩ := exists_isUnit_det_mul_eq_neg_of_linearIndependent_residue n n0 Ψ hli
  refine ⟨hle, Y.map O.subtype, fun b b' => (hge _).2 ((hmem _).1 (Y b b').2), ?_, fun b c _ => ?_⟩
  · have : (Y.map O.subtype).det = O.subtype Y.det := (RingHom.map_det O.subtype Y).symm
    rw [this]
    exact (hunit _).1 hY
  · have := congrArg O.subtype (hYΦ b c)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_mul, apply_ite O.subtype, map_neg, map_one, map_zero] at this
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsUnimodularMulEqNegOfIndependentModMaximalStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unimodular_mul_eq_neg_of_independent_mod_maximal : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  first | exact @GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | exact GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod | (intros; apply GlobalTheory.exists_unimodular_mul_eq_neg_of_indepMod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSemilinearRankNullityModMaxIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSemilinearRankNullityModMaxIdeal
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.SemilinearNullity

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have ha' : (0 : WithTop ℝ) ≤ V.v a := ha
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]
  refine V.v.map_lt_add ha ?_
  rw [V.v.map_neg]; exact hb

theorem ge_of_pow {a : C} {n : ℕ} (hn : n ≠ 0) (h : V.Ge 0 (a ^ n)) : V.Ge 0 a := by
  have h' : (0 : WithTop ℝ) ≤ V.v (a ^ n) := h
  show (0 : WithTop ℝ) ≤ V.v a
  rw [V.v.map_pow] at h'
  by_contra hc
  exact absurd (nsmul_neg (not_le.mp hc) hn) (not_lt.mpr h')

theorem ge_inv {a : C} (h : ¬ V.MM a) : V.Ge 0 a⁻¹ := by
  have h0 : a ≠ 0 := by rintro rfl; exact h mm_zero
  show (0 : WithTop ℝ) ≤ V.v a⁻¹
  have e : V.v a⁻¹ + V.v a = 0 := by rw [← V.v.map_mul, inv_mul_cancel₀ h0, V.v.map_one]
  have h1 : V.v a ≤ 0 := not_lt.mp h
  calc (0 : WithTop ℝ) = V.v a⁻¹ + V.v a := e.symm
    _ ≤ V.v a⁻¹ := add_le_of_nonpos_right h1

def IndepOn (V : VF C) {m : ℕ} {σ : Type} (Y : Fin m → σ → C) (T : Finset (Fin m)) : Prop :=
  ∀ c : Fin m → C, (∀ δ, V.Ge 0 (c δ)) → (∀ δ, δ ∉ T → c δ = 0) →
    (∀ s, V.MM (∑ δ, c δ * Y δ s)) → ∀ δ, V.MM (c δ)

theorem IndepOn.indepMod {m : ℕ} {σ : Type} {Y : Fin m → σ → C} {T : Finset (Fin m)}
    (h : IndepOn V Y T) {N : ℕ} (f : Fin N ↪ Fin m) (hf : ∀ ν, f ν ∈ T) :
    IndepMod V (fun ν => Y (f ν)) := by
  intro c hc hs ν
  have key := h (fun δ => ∑ ν, if f ν = δ then c ν else 0) (fun δ => VF.Ge.sum fun ν _ => by
      split_ifs
      · exact hc ν
      · exact VF.Ge.zero 0)
    (fun δ hδ => Finset.sum_eq_zero fun ν _ => if_neg (by rintro rfl; exact hδ (hf ν)))
    (fun s => by
      convert hs s using 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp) (f ν)
  simpa using key

theorem exists_relation {m : ℕ} {σ : Type} {Y : Fin m → σ → C} (hY : ∀ δ x, V.Ge 0 (Y δ x))
    {T : Finset (Fin m)} (hT : IndepOn V Y T) {δ : Fin m}
    (hn : ¬ IndepOn V Y (insert δ T)) :
    ∃ r : Fin m → C, (∀ ε, V.Ge 0 (r ε)) ∧ r δ = 1 ∧ (∀ ε, ε ∉ T → ε ≠ δ → r ε = 0) ∧
      ∀ s, V.MM (∑ ε, r ε * Y ε s) := by
  unfold IndepOn at hn
  push Not at hn
  obtain ⟨c, hc, hc0, hs, ε₀, hε₀⟩ := hn
  have hcd : ¬ V.MM (c δ) := by
    intro hm
    have key := hT (fun ε => if ε = δ then 0 else c ε) (fun ε => by
        split_ifs
        · exact VF.Ge.zero 0
        · exact hc ε)
      (fun ε hε => by
        split_ifs with h
        · rfl
        · exact hc0 ε (by simp [h, hε]))
      (fun s => by
        have h1 : V.MM (Y δ s * c δ) := mm_int_mul (hY δ s) hm
        convert mm_sub (hs s) h1 using 1
        rw [eq_sub_iff_add_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ δ),
          ← Finset.add_sum_erase _ (fun ε => c ε * Y ε s) (Finset.mem_univ δ)]
        rw [Finset.sum_congr rfl (g := fun ε => c ε * Y ε s)
          (fun ε hε => by rw [if_neg (Finset.ne_of_mem_erase hε)])]
        simp only [if_true]
        ring) ε₀
    by_cases h : ε₀ = δ
    · exact hε₀ (h ▸ hm)
    · exact hε₀ (by simpa [h] using key)
  have h0 : c δ ≠ 0 := by intro h; exact hcd (h ▸ mm_zero)
  refine ⟨fun ε => (c δ)⁻¹ * c ε, fun ε => (ge_inv hcd).mul_int (hc ε), inv_mul_cancel₀ h0,
    fun ε h1 h2 => ?_, fun s => ?_⟩
  · simp only [hc0 ε (by simp [h1, h2]), mul_zero]
  · convert mm_int_mul (ge_inv hcd) (hs s) using 1
    simp only [Finset.mul_sum, mul_assoc]

theorem rank_nullity : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) (m k Q : ℕ), 1 ≤ Q → ∀ Y : Fin m → σ → C, (∀ δ x, V.Ge 0 (Y δ x)) → (∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν s, V.MM (∑ δ, x ν δ ^ Q * Y δ s)) → N ≤ k) → ∃ (m' : ℕ) (cc : Fin m' ↪ Fin m), m ≤ m' + k ∧ IndepMod V (fun ν => Y (cc ν)) := by
  intro C _ _ V σ m k Q hQ Y hY hk
  have hQ0 : Q ≠ 0 := by omega
  obtain ⟨T, hT, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun T : Finset (Fin m) => IndepOn V Y T) Finset.card
    ⟨∅, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro c _ h0 _ δ
      rw [h0 δ (by simp)]
      exact mm_zero⟩
  have hT' : IndepOn V Y T := (Finset.mem_filter.1 hT).2
  have hn : ∀ δ, δ ∉ T → ¬ IndepOn V Y (insert δ T) := fun δ hδ h => by
    have := hmax _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
    rw [Finset.card_insert_of_notMem hδ] at this
    omega
  have hrt : ∀ a : C, ∃ z : C, z ^ Q = a ∧ (a = 1 → z = 1) ∧ (a = 0 → z = 0) := by
    intro a
    by_cases h : a = 1
    · exact ⟨1, by simp [h], fun _ => rfl, fun h0 => absurd (h.symm.trans h0) one_ne_zero⟩
    · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq a (Nat.pos_of_ne_zero hQ0)
      exact ⟨z, hz, fun h1 => absurd h1 h, fun h0 => pow_eq_zero_iff hQ0 |>.mp (hz.trans h0)⟩
  choose rt hrt hrt1 hrt0 using hrt
  let e : Fin Tᶜ.card ↪ Fin m := (Tᶜ.orderEmbOfFin rfl).toEmbedding
  have he : ∀ ν, e ν ∉ T := fun ν => Finset.mem_compl.1 (Finset.orderEmbOfFin_mem _ rfl ν)
  choose r hr hr1 hr0 hrs using fun ν => exists_relation hY hT' (hn _ (he ν))
  have hle := hk Tᶜ.card (fun ν δ => rt (r ν δ))
    (fun ν δ => ge_of_pow hQ0 (by rw [hrt]; exact hr ν δ))
    (fun c _ hs ν => by
      have h1 : V.MM (∑ b, c b * rt (r b (e ν))) := hs (e ν)
      rw [Finset.sum_eq_single ν (fun b _ hb => by
        rw [hrt0 _ (hr0 b _ (he ν) (fun h => hb (e.injective h).symm)), mul_zero])
        (fun h => absurd (Finset.mem_univ _) h), hrt1 _ (hr1 ν), mul_one] at h1
      exact h1)
    (fun ν s => by simp only [hrt]; exact hrs ν s)
  refine ⟨T.card, (T.orderEmbOfFin rfl).toEmbedding, ?_,
    hT'.indepMod _ fun ν => Finset.orderEmbOfFin_mem _ rfl ν⟩
  rw [Finset.card_compl, Fintype.card_fin] at hle
  omega

end GlobalTheory.SemilinearNullity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PowerSemilinearRankNullityModMaxIdealStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (σ : Type) (m k Q : ℕ), 1 ≤ Q → ∀ Y : Fin m → σ → C, (∀ δ x, V.Ge 0 (Y δ x)) → (∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν s, V.MM (∑ δ, x ν δ ^ Q * Y δ s)) → N ≤ k) → ∃ (m' : ℕ) (cc : Fin m' ↪ Fin m), m ≤ m' + k ∧ IndepMod V (fun ν => Y (cc ν)) := by
  first | exact @GlobalTheory.SemilinearNullity.rank_nullity | exact GlobalTheory.SemilinearNullity.rank_nullity | (intros; apply GlobalTheory.SemilinearNullity.rank_nullity <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainStepKernelRankLeModMaxIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainStepKernelRankLeModMaxIdeal
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

noncomputable section

namespace GlobalTheory.ChainStep

variable {C : Type} [Field C] {V : VF C}

theorem mm_zero : V.MM (0 : C) := by simp [VF.MM]

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) :
    V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  unfold VF.Ge at hb
  rw [V.v.map_mul]
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right (by simpa using hb))

theorem int_mul_mm {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM
  rw [V.v_l]
  exact zero_lt_one

def intRing (V : VF C) : Subring C where
  carrier := {a | V.Ge 0 a}
  mul_mem' ha hb := VF.Ge.mul_int ha hb
  one_mem' := VF.Ge.one
  add_mem' ha hb := VF.Ge.add ha hb
  zero_mem' := VF.Ge.zero 0
  neg_mem' ha := VF.Ge.neg ha

theorem add_pow_congr {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (n : ℕ) :
    V.MM ((a + b) ^ (V.l ^ n) - (a ^ (V.l ^ n) + b ^ (V.l ^ n))) := by
  have h : ∃ r : intRing V, ((⟨a, ha⟩ : intRing V) + ⟨b, hb⟩) ^ (V.l ^ n) =
      (⟨a, ha⟩ : intRing V) ^ (V.l ^ n) + (⟨b, hb⟩ : intRing V) ^ (V.l ^ n) + (V.l : intRing V) * r := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq V.l_prime (⟨a, ha⟩ : intRing V) ⟨b, hb⟩ n
    first
      | exact ⟨r, hr⟩
      | exact ⟨_, by rw [hr, mul_assoc, mul_assoc]⟩
  obtain ⟨r, hr⟩ := h
  have h2 := congrArg (fun z : intRing V => (z : C)) hr
  push_cast at h2
  rw [h2, add_sub_cancel_left]
  exact mm_mul_int mm_l r.2

theorem sum_pow_congr {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.Ge 0 (f i)) (n : ℕ) :
    V.MM ((∑ i ∈ s, f i) ^ (V.l ^ n) - ∑ i ∈ s, f i ^ (V.l ^ n)) := by
  induction s using Finset.induction_on with
  | empty => simpa [V.l_prime.ne_zero] using mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h' := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h1 := add_pow_congr (h a (Finset.mem_insert_self a s)) (VF.Ge.sum h') n
    have h2 := mm_add h1 (ih h')
    convert h2 using 1
    ring

theorem even_val_add {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) (s : ℕ) :
    Even (a + ((2 * s : ℕ) : ZMod d)).val ↔ Even a.val := by
  have h2 : 2 ∣ d := hd.two_dvd
  rw [ZMod.val_add, ZMod.val_natCast, Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2,
    Nat.add_mod, Nat.mod_mod_of_dvd _ h2]
  simp

theorem big_add {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (h : X.big g a) (s : ℕ) :
    X.big g (a + ((2 * s : ℕ) : ZMod d)) := by
  fin_cases g
  · exact (hA.2 _).2 ((even_val_add hA.1 a s).2 ((hA.2 _).1 h))
  · have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
    refine (h1 _).2 fun h2 => (h1 _).1 h ?_
    exact (hA.2 _).2 ((even_val_add hA.1 a s).1 ((hA.2 _).1 h2))

theorem mm_of_tan {d : ℕ} {I J : Type} [Fintype I] [Fintype J] {G : Cart V d I J} (S : Sys G)
    (z : I → C) (h : ∀ k, V.MM (∑ c, z c * S.tan c k)) (c : I) : V.MM (z c) := by
  have h1 : S.U * S.U⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr S.U_det_ne)
  have h2 : z c = ∑ k, (∑ b, z b * S.tan b k) * S.U⁻¹ k c := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ k, z b * S.tan b k * S.U⁻¹ k c = z b * (S.U * S.U⁻¹) b c := by
      intro b
      rw [Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp [Sys.U, mul_assoc]
    simp only [this, h1, Matrix.one_apply]
    simp
  rw [h2]
  exact mm_sum fun k _ => mm_mul_int (h k) (inv_int S.U S.U_int S.unimod k c)

theorem rank_le : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → ∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν e, D.lev e = s + 1 → V.MM (∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2))) → N ≤ X.j' := by
  intro C _ V d _ I J _ _ X hA g a hbig i S Z D hD s hs m y hy hyi N x hx hxi hker
  set F : Finset (I g) := Finset.univ.filter (fun c => D.lev c = s) with hF
  have hFm : ∀ c, c ∈ F ↔ D.lev c = s := fun c => by simp [hF]
  have hDi : D.i = i := hD.2.2.1
  have hDl : D.l = V.l := hD.2.1
  have hDv : D.v = V.v := hD.1
  have hgood : ∀ c ∈ F, D.good c := fun c hc =>
    D.pure_good c (by rw [(hFm c).1 hc, hDi]; omega)
  let w : Fin N → I g → C := fun ν c => ∑ δ, x ν δ * y δ c
  have hw : ∀ ν c, V.Ge 0 (w ν c) := fun ν c => VF.Ge.sum fun δ _ => (hx ν δ).mul_int (hy δ c)
  have hG : ∀ c ∈ F, (X.G g).Good (a + ((2 * s : ℕ) : ZMod d)) (S.tan c) (S.cur c) := by
    intro c hc
    have h1 := hD.good (hgood c hc)
    rwa [hD.2.2.2.2 c (by rw [(hFm c).1 hc]; omega), (hFm c).1 hc] at h1
  have hal : ∀ c ∈ F, ∀ e, V.Ge 0 ((V.l : C) * D.al c 2 e) := fun c hc e =>
    hDl ▸ hD.l_mul_al_two_int (hgood c hc) e
  have key := X.R1 hA g _ (big_add X hA g a hbig s) N
    (fun ν => ∑ c ∈ F, w ν c • S.tan c) (fun ν => ∑ c ∈ F, teich V.l (w ν c) (S.cur c))
    (fun ν => Cart.Good.comb F (fun c _ => hw ν c) hG) ?_ ?_
  · omega
  · intro ν k
    rw [Cart.scaledSecond_sum]
    have e1 : ∑ c ∈ F, w ν c ^ (V.l ^ 2) * (X.G g).V2 (S.cur c) k =
        ∑ e, (∑ c ∈ F, w ν c ^ (V.l ^ 2) * ((V.l : C) * D.al c 2 e)) * S.tan e k := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 := hD.2.2.2.1 c 2 k (by norm_num)
      simp only [Sys.al, Sys.cur_zero_inl] at h1
      simp only [Cart.V2, h1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [e1]
    refine mm_sum fun e _ => mm_mul_int ?_ (tan_int S e k)
    by_cases he : D.lev e = s + 1
    · have h1 := hker ν e he
      have h2 : V.MM (∑ c ∈ F, (w ν c ^ (V.l ^ 2) - ∑ δ, (x ν δ * y δ c) ^ (V.l ^ 2)) *
          ((V.l : C) * D.al c 2 e)) :=
        mm_sum fun c hc => mm_mul_int
          (sum_pow_congr (fun δ _ => (hx ν δ).mul_int (hy δ c)) 2) (hal c hc e)
      have e2 : ∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ F, (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2) =
          ∑ c ∈ F, (∑ δ, (x ν δ * y δ c) ^ (V.l ^ 2)) * ((V.l : C) * D.al c 2 e) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun δ _ => by
          rw [mul_pow]; ring
      convert mm_add h1 h2 using 1
      rw [e2, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun c _ => by ring
    · refine mm_sum fun c hc => int_mul_mm ((hw ν c).pow _) ?_
      have hc' := (hFm c).1 hc
      rw [D.al_two c (by rw [hc', hDi]; omega) e,
        D.g_supp c (by rw [hc', hDi]; omega) e (by rw [hc']; exact he), hDl, zero_add,
        mul_inv_cancel_left₀ VF.l_ne_zero]
      refine mm_mul_int mm_l ?_
      have := D.lam_int c e
      rw [hDv] at this
      simpa [VF.Ge] using this
  · intro co hco hmm
    refine hxi co hco (hyi (fun δ => ∑ ν, co ν * x ν δ)
      (fun δ => VF.Ge.sum fun ν _ => (hco ν).mul_int (hx ν δ)) ?_)
    refine mm_of_tan S _ fun k => ?_
    convert hmm k using 1
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hF, Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : D.lev c = s
    · simp only [hc, if_true, w, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun δ _ => by ring
    · simp [hc]

end GlobalTheory.ChainStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ChainStepKernelRankLeModMaxIdealStatement
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chainStep_kernel_rank_le_mod_maxIdeal : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → ∀ (g : Fin 2) (a : ZMod d), X.big g a → ∀ (i : ℕ) (S : Sys (X.G g)) (Z : Type) (D : Formalism.BaseCaseIdentities.Data C Z (I g)), Adapted S D a i → ∀ s : ℕ, s + 1 < Formalism.BaseCaseIdentities.Kn i → ∀ (m : ℕ) (y : Fin m → I g → C), (∀ δ c, V.Ge 0 (y δ c)) → IndepMod V (fun δ c => if D.lev c = s then y δ c else 0) → ∀ (N : ℕ) (x : Fin N → Fin m → C), (∀ ν δ, V.Ge 0 (x ν δ)) → IndepMod V x → (∀ ν e, D.lev e = s + 1 → V.MM (∑ δ, x ν δ ^ (V.l ^ 2) * ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s), (V.l : C) * D.al c 2 e * y δ c ^ (V.l ^ 2))) → N ≤ X.j' := by
  first | exact @GlobalTheory.ChainStep.rank_le | exact GlobalTheory.ChainStep.rank_le | (intros; apply GlobalTheory.ChainStep.rank_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataMainTermNormalFormAndLevelOne
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

open Formalism.BaseCaseIdentities (Data Kn s0)

noncomputable section

namespace GlobalTheory.MainTerm

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem mm_neg_iff {x : C} : V.MM (-x) ↔ V.MM x := by
  unfold VF.MM
  rw [V.v.map_neg]

theorem chain_rank (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (hb : X.big g a)
    (i : ℕ) (S : Sys (X.G g)) {Z : Type} (D : Data C Z (I g)) (h : Adapted S D a i)
    (N : ℕ) (em : Fin N ↪ I g) (hem : ∀ δ, D.lev (em δ) = 0) (s : ℕ) (hs : s < Kn i) :
    ∃ (m : ℕ) (cc : Fin m ↪ Fin N), N ≤ m + s * X.j' ∧
      IndepMod V (fun δ c => if D.lev c = s then chainMat D s c (em (cc δ)) else 0) := by
  haveI := X.algClosed
  induction s with
  | zero =>
    refine ⟨N, Function.Embedding.refl _, by omega, fun co _ hco ν => ?_⟩
    have := hco (em ν)
    simpa [hem, chainMat_zero] using this
  | succ s ih =>
    obtain ⟨m, cc, hm, hI⟩ := ih (by omega)
    have hsK : s < Kn D.i := by rw [h.2.2.1]; omega
    obtain ⟨m', cc', hm', hI'⟩ := GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal C V (I g) m X.j' (V.l ^ 2)
      (Nat.one_le_pow _ _ V.l_prime.pos)
      (fun δ c => if D.lev c = s + 1 then chainMat D (s + 1) c (em (cc δ)) else 0)
      (by
        intro δ c
        split_ifs
        · exact h.chainMat_int _ _ _
        · exact VF.Ge.zero 0)
      (by
        intro N' x hx hxI hxM
        refine GlobalTheory.T.chainStep_kernel_rank_le_mod_maxIdeal C V d I J X hA g a hb i S Z D h s hs m
          (fun δ c => chainMat D s c (em (cc δ))) (fun δ c => h.chainMat_int _ _ _) hI N' x hx hxI ?_
        intro ν e he
        have := hxM ν e
        simpa [he, chainMat_succ, hsK, h.2.1] using this)
    exact ⟨m', cc'.trans cc, by rw [Nat.succ_mul]; omega, hI'⟩

theorem mainVec_rank (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d) (hb : X.big g a)
    (i : ℕ) (S : Sys (X.G g)) {Z : Type} (D : Data C Z (I g)) (h : Adapted S D a i)
    (N : ℕ) (em : Fin N ↪ I g) (hem : ∀ δ, D.lev (em δ) = 0) :
    ∃ (m : ℕ) (cc : Fin m ↪ Fin N), N ≤ m + s0 i * X.j' ∧
      IndepMod V (fun δ => mainVec S D (em (cc δ))) := by
  have hi : Odd i := h.2.2.1 ▸ D.i_odd
  obtain ⟨m, cc, hm, hI⟩ := chain_rank X hA g a hb i S D h N em hem (s0 i) (chainStartIndex_lt_chainLength_of_odd hi)
  refine ⟨m, cc, hm, fun co hco hM => ?_⟩
  refine GlobalTheory.T.independentMod_firstCoeff_chainLastStep C V d I J X hA g a hb i S Z D h (s0 i) (chainStartIndex_lt_chainLength_of_odd hi) m
    (fun δ c => chainMat D (s0 i) c (em (cc δ))) (fun δ c => h.chainMat_int _ _ _) hI co hco ?_
  intro κ
  have h1 := hM κ
  simp only [mainVec, h.2.2.1, h.2.1, chainStartIndex_lt_chainLength_of_odd hi, and_true] at h1
  rcases neg_one_pow_eq_or C (s0 i + 1) with h2 | h2
  · simpa [h2] using h1
  · rw [← mm_neg_iff]
    simpa [h2] using h1

theorem not_big_add_odd (X : RowData C V d I J) (hA : X.Alt) (g : Fin 2) (a : ZMod d)
    (hb : X.big g a) {i : ℕ} (hi : Odd i) : ¬ X.big g (a + (i : ZMod d)) := by
  have hpar : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    obtain ⟨e, he⟩ := hA.1
    have h2 : 2 ∣ d := ⟨e, by omega⟩
    have h3 : (a + (i : ZMod d)).val % 2 = (a.val + i) % 2 := by
      rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_mod_of_dvd _ h2, Nat.add_mod,
        Nat.mod_mod_of_dvd _ h2, ← Nat.add_mod]
    obtain ⟨k, rfl⟩ := hi
    simp only [Nat.even_iff]
    omega
  have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
  have hg : g = 0 ∨ g = 1 := by omega
  rcases hg with rfl | rfl
  · rw [hA.2, hpar, not_not]; exact (hA.2 a).1 hb
  · rw [h1, not_not, hA.2, hpar, ← hA.2]; exact (h1 a).1 hb

theorem both (X : RowData C V d I J) (hA : X.Alt) (h5 : 5 ≤ V.l) (g : Fin 2) (a : ZMod d)
    (hb : X.big g a) (i : ℕ) (hi : Odd i) (hid : i < d) (U : Fin X.n → I g → C)
    (U' : Fin X.n → I (1 - g) → C) (hU : X.SatIn g a U)
    (hU' : X.SatIn (1 - g) (a + (i : ZMod d)) U') :
    ∃ (n0 : ℕ) (e : Fin n0 → I g → C) (v' : Fin X.n → I (1 - g) → C) (Φ : Fin X.n → Fin n0 → C),
      X.MConcl g a i U U' n0 e v' Φ ∧ X.CurveSystemVanishing g a i n0 e v' Φ ∧
        (i = 1 → X.MPlusConcl g a n0 e v' Φ) := by
  haveI := X.algClosed
  haveI := X.charZero
  obtain ⟨S, N1, D, hv, hl, hDi, hal, hty, hN1, A, hAint, hAeq⟩ :=
    GlobalTheory.T.rowData_adaptedChainData C V d I J X hA g a hb i hi hid U hU
  have h : Adapted S D a i := ⟨hv, hl, hDi, hal, hty⟩
  obtain ⟨m, c1, hm, hI1⟩ := mainVec_rank X hA g a hb i S D h N1 ⟨D.ι, D.ι_inj⟩ D.ι_lev
  have hΨint : ∀ c0 (u : I (1 - g) → C), (∀ k, V.Ge 0 (u k)) →
      V.Ge 0 (∑ κ : J g, ∑ k : I (1 - g), mainVec S D c0 κ * X.pair g κ k * u k) :=
    fun c0 u hu => VF.Ge.sum fun κ _ => VF.Ge.sum fun k _ =>
      ((h.mainVec_int c0 κ).mul_int (X.pair_int g κ k)).mul_int (hu k)
  obtain ⟨n0, c2, hn0, hI2⟩ := GlobalTheory.T.powerSemilinear_rank_nullity_mod_maxIdeal C V (Fin X.n) m X.j 1 le_rfl
    (fun δ b => ∑ κ : J g, ∑ k : I (1 - g), mainVec S D (D.ι (c1 δ)) κ * X.pair g κ k * U' b k)
    (fun δ b => hΨint _ _ (hU'.1.1 b))
    (by
      intro N x hx hxI hxM
      refine GlobalTheory.T.pairing_kernel_le_of_saturated_submodule C V d I J X g _ (not_big_add_odd X hA g a hb hi) U' hU' N
        (fun ν κ => ∑ δ, x ν δ * mainVec S D (D.ι (c1 δ)) κ)
        (fun ν κ => VF.Ge.sum fun δ _ => (hx ν δ).mul_int (h.mainVec_int _ _)) ?_ ?_ ?_
      · intro ν κ hκ
        simp [h.mainVec_pure _ κ hκ]
      · intro co hco hM
        refine hxI co hco (hI1 (fun δ => ∑ ν, co ν * x ν δ)
          (fun δ => VF.Ge.sum fun ν _ => (hco ν).mul_int (hx ν δ)) fun κ => ?_)
        convert hM κ using 1
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      · intro ν b
        convert hxM ν b using 1
        simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc, pow_one]
        rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
        refine Finset.sum_congr rfl fun κ _ => Finset.sum_comm)
  let em : Fin n0 ↪ I g := (c2.trans c1).trans ⟨D.ι, D.ι_inj⟩
  have hem : ∀ δ, D.lev (em δ) = 0 := fun δ => D.ι_lev _
  have hK : 0 < Kn i := by rw [Kn_eq hi]; omega
  have hemty : ∀ δ, (X.G g).ty (Sum.inl (em δ)) = a := fun δ => by
    rw [hty _ (by rw [hem]; exact hK), hem]; simp
  have hemal : ∀ δ x, S.al (em δ) 1 x = 0 := fun δ x =>
    h.al_one (D.pure_good _ (by rw [hem, hDi]; exact hK)) x
  obtain ⟨hn0n, Y, hYint, hYdet, hYΦ⟩ := GlobalTheory.T.exists_unimodular_mul_eq_neg_of_independent_mod_maximal C V X.n n0
    (fun b c => ∑ κ : J g, ∑ k : I (1 - g), mainVec S D (em c) κ * X.pair g κ k * U' b k)
    (fun b c => hΨint _ _ (hU'.1.1 b)) hI2
  let v' : Fin X.n → I (1 - g) → C := fun b x => ∑ b', Y b b' * U' b' x
  have hv'int : ∀ b k, V.Ge 0 (v' b k) := fun b k =>
    VF.Ge.sum fun b' _ => (hYint b b').mul_int (hU'.1.1 b' k)
  have hv'ty : ∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0 :=
    fun b k hk => by simp [v', hU'.2 _ k hk]
  have hety : ∀ c x, (X.G g).ty (Sum.inl x) ≠ a → S.tan (em c) x = 0 := fun c x hx =>
    tan_pure S _ x (by rw [hemty]; exact hx)
  have hS0 : ∀ g', Nonempty (Sys (X.G g')) := fun g' => by
    obtain ⟨S', -⟩ := sysExists (X.G g') (fun c x => if c = x then 1 else 0)
      (by intro c x; split_ifs; exacts [VF.Ge.one, VF.Ge.zero 0])
      (by
        intro c x hx
        rw [if_neg]
        rintro rfl
        exact hx rfl)
      (by
        have : (Matrix.of fun c x : I g' => if c = x then (1 : C) else 0) = 1 := by
          ext c x; simp [Matrix.one_apply]
        rw [this, Matrix.det_one, V.v.map_one])
    exact ⟨S'⟩
  obtain ⟨SS, rfl⟩ : ∃ SS : ∀ g', Sys (X.G g'), SS g = S :=
    ⟨Function.update (fun g' => (hS0 g').some) g S, by simp⟩
  choose t ht using fun g' => (tExistsUnique (X.G g') (SS g')).exists
  have hζ := GlobalTheory.T.zetaSeries_leaf_mainTerm_curveSystem C V d (I g) (J g) (X.G g) (SS g) _ D a i h hid (t g) (ht g) n0 em hem
  refine ⟨n0, fun δ => (SS g).tan (em δ), v',
    fun b c => ∑ κ : J g, ∑ k : I (1 - g), mainVec (SS g) D (em c) κ * X.pair g κ k * v' b k,
    ⟨⟨?_, hn0n⟩, isSat_tan _ em, ⟨fun c => A (c1 (c2 c)), fun c b => hAint _ b, fun c x => ?_⟩,
      ⟨Y, hYint, hYdet, fun b x => rfl⟩, fun b c => hΨint _ _ (hv'int b), fun b c hb => ?_, ?_,
      fun μ hμ => GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis C V d I J X g a i _ _ _ _ _ μ hμ⟩,
    ⟨SS g, t g, em, fun c => mainVec (SS g) D (em c), ht g, fun c => rfl, hemal,
      fun c κ => h.mainVec_int _ _, fun b c => rfl, hζ⟩, ?_⟩
  · have h1 := two_mul_chainStartIndex_add_one_of_odd hi
    rw [Kn_eq hi] at hN1
    have h2 : (i + 1) * X.j' = (s0 i + 1 + 1) * X.j' + s0 i * X.j' := by
      rw [← Nat.add_mul]; congr 1; omega
    omega
  · exact ((SS g).cur_zero_inl _ x).symm.trans (hAeq _ x)
  · rw [← hYΦ b c hb]
    simp only [v', Finset.mul_sum]
    rw [Finset.sum_comm (s := Finset.univ (α := Fin X.n))]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · exact GlobalTheory.T.weight_gauge_sub_mainTerm_leaf C V d I J X hA h5 g a i hi hid SS t ht n0 X.n _ v'
      (fun c => mainVec (SS g) D (em c)) hety hv'int hv'ty
      (GlobalTheory.T.leafCoordinate_weight_nonneg_of_adaptedChainData C V d (I g) (J g) (X.G g) (SS g) _ D a i h (t g) (ht g) n0 em hem) hζ
  · rintro rfl
    simp only [fun c => funext (h.mainVec_level_one (hem c))]
    exact GlobalTheory.T.gauge_sub_mainTerm_integral_lowBidegree C V d I J X hA hid g a SS t ht n0 em v' hemty hemal hv'int hv'ty

theorem main : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.LemmaM ∧ X.LemmaMPlus := by
  intro C _ V d _ I J _ _ X
  constructor
  · intro hA h5 g a hb i hi hid U U' hU hU'
    obtain ⟨n0, e, v', Φ, h1, h2, -⟩ := both X hA h5 g a hb i hi hid U U' hU hU'
    exact ⟨n0, e, v', Φ, h1, h2⟩
  · intro hA h5 hd g a hb U U' hU hU'
    obtain ⟨n0, e, v', Φ, h1, h2, h3⟩ := both X hA h5 g a hb 1 odd_one hd U U' hU hU'
    exact ⟨n0, e, v', Φ, h1, h2, h3 rfl⟩

end GlobalTheory.MainTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowDataMainTermNormalFormAndLevelOneStatement
open Formalism.L2.FormalSeriesBounds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowData_mainTerm_normalForm_and_levelOne : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.LemmaM ∧ X.LemmaMPlus := by
  first | exact @GlobalTheory.MainTerm.main | exact GlobalTheory.MainTerm.main | (intros; apply GlobalTheory.MainTerm.main <;> assumption)
end
