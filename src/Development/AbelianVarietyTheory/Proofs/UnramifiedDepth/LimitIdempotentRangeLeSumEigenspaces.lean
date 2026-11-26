module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RingHomEqOfCongruentIntegralUnramified
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RingHomEqOfCongruentIntegralUnramified
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.CongruentCharacters

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM; rw [V.v.map_neg]; exact ha

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  unfold VF.MM at *
  have ha' : (0 : WithTop ℝ) ≤ V.v a := by simpa [VF.Ge] using ha
  rw [V.v.map_mul]
  exact lt_of_lt_of_le hb (le_add_of_nonneg_left ha')

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem cancel_unit {u a : C} {w : ℝ} (hu : V.MM (u - 1)) (h : V.Ge w (u * a)) : V.Ge w a := by
  have h0 : V.v u = 0 := by
    have h1 : V.v (1 : C) < V.v (u - 1) := by rw [V.v.map_one]; exact hu
    have h2 := V.v.map_add_eq_of_lt_left h1
    rw [V.v.map_one] at h2
    simpa using h2
  unfold VF.Ge at *
  rwa [V.v.map_mul, h0, zero_add] at h

theorem pow_sub_pow_factor {a b : C} (ha : V.Ge 0 a) (hb : V.Ge 0 b) (hab : V.MM (a - b)) (n : ℕ) :
    ∃ S : C, a ^ (n + 1) - b ^ (n + 1) = (a - b) * S ∧
      V.MM (S - ((n + 1 : ℕ) : C) * b ^ n) := by
  induction n with
  | zero => exact ⟨1, by ring, by simp [VF.MM]⟩
  | succ n ih =>
    obtain ⟨S, h1, h2⟩ := ih
    refine ⟨a * S + b ^ (n + 1), by linear_combination a * h1, ?_⟩
    have h3 := mm_add (mm_int_mul ha h2)
      (mm_int_mul (VF.Ge.mul_int (VF.ge_natCast (n + 1)) (hb.pow n)) hab)
    convert h3 using 1
    push_cast; ring

theorem eq_zero_of_ge_all {a : C} (h : ∀ n : ℕ, V.Ge n a) : a = 0 := by
  apply (AddValuation.top_iff V.v).1
  induction hv : V.v a using WithTop.recTopCoe with
  | top => rfl
  | coe t =>
    exfalso
    obtain ⟨n, hn⟩ := exists_nat_gt t
    have := h n
    unfold VF.Ge at this
    rw [hv] at this
    have h' : (n : ℝ) ≤ t := WithTop.coe_le_coe.1 this
    linarith

theorem eq_of_congruent : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ), 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ ψ φ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, V.Ge 0 (φ x)) → V.MM (ψ ε - 1) → (∀ x, V.MM (ψ x - φ x)) → ψ = φ := by
  intro C _ V O _ d hd ε ⟨y, hy⟩ hx ψ φ hψ hφ hε hc
  have hl0 : 0 < V.l := V.l_prime.pos
  obtain ⟨m, hm⟩ : ∃ m, V.l ^ d = m + 1 := ⟨V.l ^ d - 1, by have := pow_pos hl0 d; omega⟩
  have hq : V.MM ((m + 1 : ℕ) : C) := by
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    rw [← hm, pow_succ, Nat.cast_mul]
    exact mm_int_mul (VF.ge_natCast _) mm_l
  have key : ∀ n : ℕ, ∀ x, V.Ge n (ψ x - φ x) := by
    intro n
    induction n with
    | zero => intro x; simpa using (hψ x).sub (hφ x)
    | succ n ih =>
      have hl : ∀ z, V.Ge ((n + 1 : ℕ) : ℝ) ((V.l : C) * (ψ z - φ z)) := fun z => by
        have := (ih z).l_mul
        convert this using 1
        push_cast; ring
      have hδε : V.Ge ((n + 1 : ℕ) : ℝ) (ψ ε - φ ε) := by
        have e1 := congrArg ψ hy
        have e2 := congrArg φ hy
        simp only [map_sub, map_mul, map_natCast] at e1 e2
        apply cancel_unit (u := ψ ε + φ ε - 1)
        · have := mm_add (mm_add hε hε) (mm_neg (hc ε))
          convert this using 1; ring
        · convert hl y using 1
          linear_combination e1 - e2
      intro x
      obtain ⟨z, hz⟩ := hx x
      have e1 := congrArg ψ hz
      have e2 := congrArg φ hz
      simp only [map_sub, map_mul, map_natCast, map_pow, hm] at e1 e2
      obtain ⟨S, hS1, hS2⟩ := pow_sub_pow_factor (hψ x) (hφ x) (hc x) m
      have hS : V.MM S := by
        have := mm_add hS2 (mm_int_mul ((hφ x).pow m) hq)
        convert this using 1; ring
      have ht : V.Ge 0 (φ x ^ (m + 1) - φ x) := ((hφ x).pow _).sub (hφ x)
      apply cancel_unit (u := 1 - S)
      · have := mm_neg hS
        convert this using 1; ring
      apply cancel_unit hε
      have := (VF.Ge.mul_int ht hδε).sub (hl z)
      convert this using 1
      linear_combination ψ ε * hS1 - e1 + e2
  ext x
  exact sub_eq_zero.1 (eq_zero_of_ge_all fun n => key n x)

end GlobalTheory.CongruentCharacters
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RingHomEqOfCongruentIntegralUnramifiedStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_eq_of_congruent_integral_unramified : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (d : ℕ), 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ ψ φ : O →+* C, (∀ x, V.Ge 0 (ψ x)) → (∀ x, V.Ge 0 (φ x)) → V.MM (ψ ε - 1) → (∀ x, V.MM (ψ x - φ x)) → ψ = φ := by
  first | exact @GlobalTheory.CongruentCharacters.eq_of_congruent | exact GlobalTheory.CongruentCharacters.eq_of_congruent | (intros; apply GlobalTheory.CongruentCharacters.eq_of_congruent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorOfGeneralizedEigenUnramifiedStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorOfGeneralizedEigenUnramified
open scoped BigOperators TensorProduct
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.GenEigen

theorem mem_of_add_nil {B : Type*} [CommRing B] (J : Ideal B) (u N y : B)
    (hu : ∀ b, u * b ∈ J → b ∈ J) (k : ℕ) (hN : N ^ k ∈ J) (h : (u + N) * y ∈ J) : y ∈ J := by
  have hpow : ∀ (j : ℕ) b, u ^ j * b ∈ J → b ∈ J := by
    intro j
    induction j with
    | zero => intro b hb; simpa using hb
    | succ j ih =>
      intro b hb
      apply hu
      apply ih
      rwa [← mul_assoc, ← pow_succ]
  obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow u (-N) k
  apply hpow k
  have e : u ^ k * y = c * ((u + N) * y) + ((-1) ^ k * y) * N ^ k := by
    have : u ^ k = (u - -N) * c + (-N) ^ k := by rw [← hc]; ring
    rw [this, neg_pow N]; ring
  rw [e]
  exact J.add_mem (J.mul_mem_left _ h) (J.mul_mem_left _ hN)

theorem step {O B : Type*} [CommRing O] [CommRing B] (a p : O →+* B) (J : Ideal B)
    (l d : ℕ) (hl : 0 < l) (hd : 0 < d) (ε : O)
    (h1 : ∃ y, ε * ε - ε = (l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (l ^ d) - x) = (l : O) * y)
    (hS : ∀ y, (l : B) * (a y - p y) ∈ J)
    (hreg : ∀ (e : O) b, p (1 + l * e) * b ∈ J → b ∈ J)
    (hnil : ∀ x, ∃ k : ℕ, (a x - p x) ^ k ∈ J)
    (hlim : ∃ n : ℕ, 1 - a (ε ^ (l ^ n)) ∈ J) (x : O) : a x - p x ∈ J := by
  have hε : a ε - p ε ∈ J := by
    obtain ⟨y, hy⟩ := h1
    obtain ⟨k, hk⟩ := hnil ε
    have ha : a ε * a ε - a ε = l * a y := by simpa using congrArg a hy
    have hp : p ε * p ε - p ε = l * p y := by simpa using congrArg p hy
    refine mem_of_add_nil J (2 * p ε - 1) (a ε - p ε) _ ?_ k hk ?_
    · intro b hb
      apply hreg (4 * y)
      have : p (1 + l * (4 * y)) * b = (2 * p ε - 1) * ((2 * p ε - 1) * b) := by
        simp only [map_add (f := _), map_mul, map_one, map_natCast, map_ofNat]
        linear_combination (-4 * b) * hp
      rw [this]
      exact J.mul_mem_left _ hb
    · have : (2 * p ε - 1 + (a ε - p ε)) * (a ε - p ε) = l * (a y - p y) := by
        linear_combination ha - hp
      rw [this]
      exact hS y
  have ht : (a x ^ (l ^ d) - a x) - (p x ^ (l ^ d) - p x) ∈ J := by
    obtain ⟨y, hy⟩ := h2 x
    obtain ⟨n, hn⟩ := hlim
    have ha : a ε * (a x ^ (l ^ d) - a x) = l * a y := by simpa using congrArg a hy
    have hp : p ε * (p x ^ (l ^ d) - p x) = l * p y := by simpa using congrArg p hy
    set s := a x ^ (l ^ d) - a x
    set t := p x ^ (l ^ d) - p x
    have h3 : a ε * (s - t) ∈ J := by
      have : a ε * (s - t) = l * (a y - p y) - t * (a ε - p ε) := by
        linear_combination ha - hp
      rw [this]
      exact J.sub_mem (hS y) (J.mul_mem_left _ hε)
    obtain ⟨j, hj⟩ : ∃ j, l ^ n = j + 1 := ⟨l ^ n - 1, by have := pow_pos hl n; omega⟩
    rw [hj, map_pow] at hn
    have : s - t = (s - t) * (1 - a ε ^ (j + 1)) + a ε ^ j * (a ε * (s - t)) := by ring
    rw [this]
    exact J.add_mem (J.mul_mem_left _ hn) (J.mul_mem_left _ h3)
  obtain ⟨H, hH⟩ := Polynomial.powAddExpansion (p x) (a x - p x) (l ^ d)
  obtain ⟨k, hk⟩ := hnil x
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  refine mem_of_add_nil J (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1)
    (H * (a x - p x)) _ ?_ k ?_ ?_
  · intro b hb
    apply hreg (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))
    have : p (1 + l * (-((l : O) ^ d' * x ^ (l ^ (d' + 1) - 1)))) * b =
        -((((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1) * b) := by
      simp only [map_add (f := _), map_mul, map_one, map_natCast, map_neg, map_pow, Nat.cast_pow]
      ring
    rw [this]
    exact J.neg_mem hb
  · rw [mul_pow]; exact J.mul_mem_left _ hk
  · have e : p x + (a x - p x) = a x := by ring
    rw [e] at hH
    have : (((l ^ (d' + 1) : ℕ) : B) * p x ^ (l ^ (d' + 1) - 1) - 1 + H * (a x - p x)) * (a x - p x)
        = (a x ^ (l ^ (d' + 1)) - a x) - (p x ^ (l ^ (d' + 1)) - p x) := by
      rw [hH]; ring
    rw [this]
    exact ht

variable {C : Type} [Field C] {V : VF C}

theorem ge_of_one_add_mul {e z : C} {m : ℝ} (he : V.Ge 1 e) (h : V.Ge m ((1 + e) * z)) :
    V.Ge m z := by
  have h0 : V.v (1 + e) = 0 := by
    have : V.v 1 < V.v e := by
      rw [V.v.map_one]
      exact lt_of_lt_of_le (by exact_mod_cast (zero_lt_one : (0 : ℝ) < 1)) he
    rw [V.v.map_add_eq_of_lt_left this, V.v.map_one]
  unfold VF.Ge at h ⊢
  rwa [V.v.map_mul, h0, zero_add] at h

theorem exists_ge (z : C) : ∃ m : ℝ, V.Ge m z := by
  unfold VF.Ge
  induction V.v z using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t => exact ⟨t, le_rfl⟩

theorem eq_zero_of_forall_ge {z : C} (m : ℝ) (h : ∀ k : ℕ, V.Ge (m + k) z) : z = 0 := by
  by_contra hz
  have hne : V.v z ≠ ⊤ := by
    intro ht
    have h1 : V.v (z * z⁻¹) = ⊤ := by rw [V.v.map_mul, ht, top_add]
    rw [mul_inv_cancel₀ hz, V.v.map_one] at h1
    exact WithTop.zero_ne_top h1
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨k, hk⟩ := exists_nat_gt (t - m)
  have := h k
  unfold VF.Ge at this
  rw [← ht] at this
  have : m + k ≤ t := by exact_mod_cast this
  linarith

theorem ge_mulVec {κ : Type} [Fintype κ] {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j))
    {z : κ → C} {m : ℝ} (hz : ∀ i, V.Ge m (z i)) (i : κ) : V.Ge m (M.mulVec z i) :=
  VF.Ge.sum fun j _ => (hM i j).mul_int (hz j)

def levelIdeal {κ : Type} [Fintype κ] [DecidableEq κ] {B : Type} [CommRing B]
    (Φ : B →+* Matrix κ κ C) (hΦ : ∀ b i j, V.Ge 0 (Φ b i j)) (w : κ → C) (m : ℝ) : Ideal B where
  carrier := {b | ∀ i, V.Ge m ((Φ b).mulVec w i)}
  add_mem' := by
    intro a b ha hb i
    rw [map_add (f := _), Matrix.add_mulVec]
    exact (ha i).add (hb i)
  zero_mem' := by
    intro i
    rw [map_zero, Matrix.zero_mulVec]
    exact VF.Ge.zero m
  smul_mem' := by
    intro c b hb i
    rw [smul_eq_mul, map_mul, ← Matrix.mulVec_mulVec]
    exact ge_mulVec (hΦ c) hb i

theorem eigen_of_gen_eigen (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type)
    [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C) (hL : ∀ x i j, V.Ge 0 (L x i j))
    (d : ℕ) (hd : 0 < d) (ε : O) (h1 : ∃ y, ε * ε - ε = (V.l : O) * y)
    (h2 : ∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) (ψ : O →+* C) (w : κ → C)
    (hψ : ∀ x, V.Ge 0 (ψ x))
    (hnil : ∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0)
    (hlim : ∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i))
    (x : O) : (L x).mulVec w = ψ x • w := by
  let P : O →+* Matrix κ κ C := (algebraMap C (Matrix κ κ C)).comp ψ
  have hP : ∀ x, P x = ψ x • (1 : Matrix κ κ C) := fun x => Algebra.algebraMap_eq_smul_one (ψ x)
  let Φ : O ⊗[ℤ] O →+* Matrix κ κ C :=
    (Algebra.TensorProduct.lift L.toIntAlgHom P.toIntAlgHom
      (fun x y => (Algebra.commutes (ψ y) (L x)).symm)).toRingHom
  have hΦt : ∀ x y, Φ (x ⊗ₜ y) = ψ y • L x := by
    intro x y
    change L x * P y = _
    rw [hP, Matrix.mul_smul, mul_one]
  have hΦ : ∀ b i j, V.Ge 0 (Φ b i j) := by
    intro b
    induction b using TensorProduct.induction_on with
    | zero => intro i j; rw [map_zero]; exact VF.Ge.zero 0
    | tmul x y => intro i j; rw [hΦt]; exact (hψ y).mul_int (hL x i j)
    | add a b ha hb => intro i j; rw [map_add (f := _)]; exact (ha i j).add (hb i j)
  let a : O →+* O ⊗[ℤ] O := Algebra.TensorProduct.includeLeftRingHom
  let p : O →+* O ⊗[ℤ] O := (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] O ⊗[ℤ] O).toRingHom
  have ha : ∀ x, Φ (a x) = L x := fun x => by
    change Φ (x ⊗ₜ 1) = _
    rw [hΦt, map_one, one_smul]
  have hp : ∀ x, Φ (p x) = ψ x • (1 : Matrix κ κ C) := fun x => by
    change Φ (1 ⊗ₜ x) = _
    rw [hΦt, map_one]
  have mem : ∀ m b, b ∈ levelIdeal Φ hΦ w m ↔ ∀ i, V.Ge m ((Φ b).mulVec w i) :=
    fun _ _ => Iff.rfl
  obtain ⟨m0, hm0⟩ : ∃ m0 : ℝ, ∀ i, V.Ge m0 (w i) := by
    choose f hf using fun i => exists_ge (V := V) (w i)
    obtain ⟨m0, hm0⟩ := (Set.finite_range f).bddBelow
    exact ⟨m0, fun i => (hf i).mono (hm0 ⟨i, rfl⟩)⟩
  have key : ∀ (k : ℕ) y, a y - p y ∈ levelIdeal Φ hΦ w (m0 + k) := by
    intro k
    induction k with
    | zero =>
      intro y
      rw [mem]
      rw [Nat.cast_zero, add_zero]
      exact ge_mulVec (hΦ _) hm0
    | succ k ih =>
      refine step a p _ V.l d V.l_prime.pos hd ε h1 h2 ?_ ?_ ?_ ?_
      · intro y
        rw [mem]
        intro i
        have := ((mem _ _).1 (ih y) i).l_mul
        rw [map_mul, map_natCast, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul C, Matrix.smul_mulVec]
        exact this.mono (by push_cast; linarith)
      · intro e b hb
        rw [mem] at hb ⊢
        intro i
        have := hb i
        rw [map_mul, hp, Matrix.smul_mul, one_mul, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul,
          map_add, map_one, map_mul, map_natCast] at this
        exact ge_of_one_add_mul (by simpa using (hψ e).l_mul) this
      · intro y
        obtain ⟨j, hj⟩ := hnil y
        refine ⟨j, (mem _ _).2 fun i => ?_⟩
        rw [map_pow, map_sub, ha, hp, hj]
        exact VF.Ge.zero _
      · obtain ⟨N, hN⟩ := exists_nat_ge (m0 + (k + 1 : ℕ))
        choose f hf using hlim N
        obtain ⟨n, hn⟩ := (Set.finite_range f).bddAbove
        refine ⟨n, (mem _ _).2 fun i => ?_⟩
        rw [map_sub, map_one, ha, Matrix.sub_mulVec, Matrix.one_mulVec]
        exact (hf i n (hn ⟨i, rfl⟩)).mono hN
  funext i
  have := eq_zero_of_forall_ge (V := V) m0 fun k => (mem _ _).1 (key k x) i
  rw [map_sub, ha, hp, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.sub_apply] at this
  exact sub_eq_zero.mp this

end GlobalTheory.GenEigen
end

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_of_generalized_eigen_unramified : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ d : ℕ, 0 < d → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y) → ∀ (ψ : O →+* C) (w : κ → C), (∀ x, V.Ge 0 (ψ x)) → (∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → (∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i)) → ∀ x, (L x).mulVec w = ψ x • w := by
  first | exact @GlobalTheory.GenEigen.eigen_of_gen_eigen | exact GlobalTheory.GenEigen.eigen_of_gen_eigen | (intros; apply GlobalTheory.GenEigen.eigen_of_gen_eigen <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCharacterGeneralizedEigen
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCharacterGeneralizedEigen
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.GenChar

theorem step {C : Type} [Field C] {O κ : Type} [Fintype κ] [DecidableEq κ]
    (n : O → Matrix κ κ C) (hc : ∀ x y, Commute (n x) (n y)) (w : κ → C) (hw : w ≠ 0)
    (hn : ∀ x, ∃ k : ℕ, ((n x) ^ k).mulVec w = 0) (x₀ : O) :
    ∃ u : κ → C, u ≠ 0 ∧ (∀ x, ∃ k : ℕ, ((n x) ^ k).mulVec u = 0) ∧ (n x₀).mulVec u = 0 ∧
      ∀ y, (n y).mulVec w = 0 → (n y).mulVec u = 0 := by
  classical
  have hk := Nat.find_spec (hn x₀)
  have hk0 : Nat.find (hn x₀) ≠ 0 := by
    intro h
    rw [h, pow_zero, Matrix.one_mulVec] at hk
    exact hw hk
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hlt : ¬ ((n x₀) ^ j).mulVec w = 0 := Nat.find_min (hn x₀) (by omega)
  have key : ∀ (y : O) (k : ℕ), ((n y) ^ k).mulVec w = 0 →
      ((n y) ^ k).mulVec (((n x₀) ^ j).mulVec w) = 0 := by
    intro y k h
    rw [Matrix.mulVec_mulVec, ((hc y x₀).pow_pow k j).eq, ← Matrix.mulVec_mulVec, h,
      Matrix.mulVec_zero]
  refine ⟨((n x₀) ^ j).mulVec w, hlt, fun x => ?_, ?_, fun y hy => ?_⟩
  · obtain ⟨k, h⟩ := hn x
    exact ⟨k, key x k h⟩
  · rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hj] at hk
    exact hk
  · have := key y 1 (by rwa [pow_one])
    rwa [pow_one] at this

theorem ge_of_eigen {C : Type} [Field C] (V : VF C) {κ : Type} [Fintype κ]
    (A : Matrix κ κ C) (hA : ∀ i j, V.Ge 0 (A i j)) (c : C) (u : κ → C) (hu : u ≠ 0)
    (h : A.mulVec u = c • u) : V.Ge 0 c := by
  classical
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hu
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => V.v (u i))
    ⟨i₀, Finset.mem_univ _⟩
  have h0 : V.v (u i₀) ≠ ⊤ := by
    intro h
    exact hi₀ (by simpa using h)
  have h1 : V.v (u i) ≠ ⊤ := ne_top_of_le_ne_top h0 (hi i₀ (Finset.mem_univ _))
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp h1
  have h2 : V.Ge t (c * u i) := by
    have : c * u i = ∑ j, A i j * u j := by
      have := congrFun h i
      simpa [Matrix.mulVec, dotProduct] using this.symm
    rw [this]
    refine VF.Ge.sum fun j _ => (hA i j).mul_int ?_
    unfold VF.Ge
    rw [ht]
    exact hi j (Finset.mem_univ _)
  unfold VF.Ge at h2 ⊢
  rw [V.v.map_mul, ← ht] at h2
  induction hv : V.v c using WithTop.recTopCoe with
  | top => exact le_top
  | coe s =>
    rw [hv] at h2
    have h' : ((t : ℝ) : WithTop ℝ) ≤ ((s + t : ℝ) : WithTop ℝ) := by
      simpa [WithTop.coe_add] using h2
    have h'' : t ≤ s + t := by exact_mod_cast h'
    have : (0 : ℝ) ≤ s := by linarith
    exact_mod_cast this

theorem exists_character : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (χ : O → C) (w : κ → C), w ≠ 0 → (∀ x, ∃ k : ℕ, ((L x - χ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → ∃ ψ : O →+* C, (∀ x, ψ x = χ x) ∧ ∀ x, V.Ge 0 (ψ x) := by
  intro C _ V O _ κ _ _ L hL χ w hw hn
  set n : O → Matrix κ κ C := fun x => L x - χ x • (1 : Matrix κ κ C) with hndef
  have hLc : ∀ x y, Commute (L x) (L y) := fun x y => (Commute.all x y).map L
  have hc : ∀ x y, Commute (n x) (n y) := fun x y =>
    ((hLc x y).sub_right ((Commute.one_right _).smul_right _)).sub_left
      ((Commute.one_left _).smul_left _)
  have heig : ∀ (x : O) (u : κ → C), (n x).mulVec u = 0 → (L x).mulVec u = χ x • u := by
    intro x u h
    simp only [hndef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at h
    exact sub_eq_zero.mp h
  have three : ∀ x y z : O, ∃ u : κ → C, u ≠ 0 ∧ (L x).mulVec u = χ x • u ∧
      (L y).mulVec u = χ y • u ∧ (L z).mulVec u = χ z • u := by
    intro x y z
    obtain ⟨u₁, h1, h1n, h1x, -⟩ := step n hc w hw hn x
    obtain ⟨u₂, h2, h2n, h2y, h2p⟩ := step n hc u₁ h1 h1n y
    obtain ⟨u₃, h3, -, h3z, h3p⟩ := step n hc u₂ h2 h2n z
    exact ⟨u₃, h3, heig _ _ (h3p _ (h2p _ h1x)), heig _ _ (h3p _ h2y), heig _ _ h3z⟩
  have h1 : χ 1 = 1 := by
    obtain ⟨u, hu, h, -, -⟩ := three 1 1 1
    rw [map_one, Matrix.one_mulVec] at h
    apply smul_left_injective C hu
    simpa using h.symm
  have h0 : χ 0 = 0 := by
    obtain ⟨u, hu, h, -, -⟩ := three 0 0 0
    rw [map_zero, Matrix.zero_mulVec] at h
    apply smul_left_injective C hu
    simpa using h.symm
  have hadd : ∀ x y, χ (x + y) = χ x + χ y := by
    intro x y
    obtain ⟨u, hu, hx, hy, h⟩ := three x y (x + y)
    rw [map_add (f := _), Matrix.add_mulVec, hx, hy, ← add_smul] at h
    exact smul_left_injective C hu h.symm
  have hmul : ∀ x y, χ (x * y) = χ x * χ y := by
    intro x y
    obtain ⟨u, hu, hx, hy, h⟩ := three x y (x * y)
    rw [map_mul, ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_smul, hx, smul_smul, mul_comm (χ y)] at h
    exact smul_left_injective C hu h.symm
  refine ⟨⟨⟨⟨χ, h1⟩, hmul⟩, h0, hadd⟩, fun _ => rfl, fun x => ?_⟩
  obtain ⟨u, hu, h, -, -⟩ := three x x x
  exact ge_of_eigen V (L x) (hL x) (χ x) u hu h

end GlobalTheory.GenChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIntegralCharacterGeneralizedEigenStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_character_generalizedEigen : ∀ (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (χ : O → C) (w : κ → C), w ≠ 0 → (∀ x, ∃ k : ℕ, ((L x - χ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0) → ∃ ψ : O →+* C, (∀ x, ψ x = χ x) ∧ ∀ x, V.Ge 0 (ψ x) := by
  first | exact @GlobalTheory.GenChar.exists_character | exact GlobalTheory.GenChar.exists_character | (intros; apply GlobalTheory.GenChar.exists_character <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LimitIdempotentRangeLeSumEigenspaces
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.IdemRange

section Val

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  V.v.map_lt_add ha hb

theorem mm_neg {a : C} (ha : V.MM a) : V.MM (-a) := by
  unfold VF.MM; rw [V.v.map_neg]; exact ha

theorem mm_mul {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM; rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa [VF.Ge] using hb
  exact lt_of_lt_of_le ha (le_add_of_nonneg_right hb')

theorem mm_or {a b : C} (h : V.MM (a * b)) : V.MM a ∨ V.MM b := by
  unfold VF.MM at *
  rw [V.v.map_mul] at h
  by_contra hc
  rw [not_or, not_lt, not_lt] at hc
  exact absurd h (not_lt.mpr (add_nonpos hc.1 hc.2))

theorem not_mm_one : ¬ V.MM (1 : C) := by
  unfold VF.MM; rw [V.v.map_one]; exact lt_irrefl _

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem mm_pow_sub {a b : C} (h : V.MM (a - b)) (ha : V.Ge 0 a) (hb : V.Ge 0 b) (n : ℕ) :
    V.MM (a ^ n - b ^ n) := by
  induction n with
  | zero => simp [VF.MM]
  | succ n ih =>
    have : a ^ (n + 1) - b ^ (n + 1) = (a ^ n - b ^ n) * a + (a - b) * b ^ n := by ring
    rw [this]
    exact mm_add (mm_mul ih ha) (mm_mul h (hb.pow n))

theorem eq_zero_of_ge_all {a : C} (h : ∀ N : ℕ, V.Ge N a) : a = 0 := by
  rw [← V.v.top_iff]
  unfold VF.Ge at h
  induction hv : V.v a using WithTop.recTopCoe with
  | top => rfl
  | coe t =>
    exfalso
    obtain ⟨N, hN⟩ := exists_nat_gt t
    have h1 := h N
    rw [hv] at h1
    have : (N : ℝ) ≤ t := by exact_mod_cast h1
    linarith

theorem exists_lower (a : C) : ∃ b : ℕ, V.Ge (-(b : ℝ)) a := by
  unfold VF.Ge
  induction hv : V.v a using WithTop.recTopCoe with
  | top => exact ⟨0, le_top⟩
  | coe t =>
    obtain ⟨N, hN⟩ := exists_nat_gt (-t)
    refine ⟨N, ?_⟩
    have : -(N : ℝ) ≤ t := by linarith
    exact_mod_cast this

theorem ge_l_pow (n : ℕ) : V.Ge n ((V.l : C) ^ n) := by
  induction n with
  | zero => simpa using VF.Ge.one (V := V)
  | succ n ih => rw [pow_succ]; push_cast; exact ih.mul VF.ge_l

theorem ge_of_unit_mul {c a : C} {w : ℝ} (hc : V.MM c) (h : V.Ge w ((1 - c) * a)) : V.Ge w a := by
  have h1 : V.v (1 - c) ≤ 0 := by
    by_contra hh
    have : V.MM (1 - c + c) := mm_add (not_le.mp hh) hc
    rw [sub_add_cancel] at this
    exact not_mm_one this
  unfold VF.Ge at *
  rw [V.v.map_mul] at h
  exact h.trans (add_le_of_nonpos_left h1)

variable {κ : Type} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem exists_lower_vec (v : κ → C) : ∃ b : ℕ, ∀ i, V.Ge (-(b : ℝ)) (v i) := by
  choose b hb using fun i => exists_lower (V := V) (v i)
  refine ⟨∑ i, b i, fun i => (hb i).mono ?_⟩
  have : b i ≤ ∑ j, b j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : (b i : ℝ) ≤ ((∑ j, b j : ℕ) : ℝ) := by exact_mod_cast this
  linarith

omit [DecidableEq κ] in
theorem ge_mulVec {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j)) {v : κ → C} {w : ℝ}
    (hv : ∀ i, V.Ge w (v i)) (i : κ) : V.Ge w (M.mulVec v i) :=
  VF.Ge.sum fun j _ => (hM i j).mul_int (hv j)

theorem ge_pow_mulVec {M : Matrix κ κ C} (hM : ∀ i j, V.Ge 0 (M i j)) {v : κ → C} {w : ℝ}
    (hv : ∀ i, V.Ge w (v i)) (k : ℕ) : ∀ i, V.Ge w ((M ^ k).mulVec v i) := by
  induction k with
  | zero => simpa using hv
  | succ k ih => rw [pow_succ', ← Matrix.mulVec_mulVec]; exact ge_mulVec hM ih

omit [DecidableEq κ] in
theorem uniform {P : κ → ℕ → Prop} (h : ∀ i, ∃ n0 : ℕ, ∀ n ≥ n0, P i n) :
    ∃ n0 : ℕ, ∀ n ≥ n0, ∀ i, P i n := by
  choose b hb using h
  refine ⟨∑ i, b i, fun n hn i => hb i n (le_trans ?_ hn)⟩
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

end Val

theorem frob_iter {C : Type} [Field C] {V : VF C} {O : Type} [CommRing O] {d : ℕ}
    (em : ZMod d → (O →+* C)) (h0 : ∀ a x, V.Ge 0 (em a x))
    (h1 : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) (a : ZMod d) (x : O) (n : ℕ) :
    V.MM (em (a + n) x - em a x ^ (V.l ^ n)) := by
  induction n with
  | zero => simp [VF.MM]
  | succ n ih =>
    have h2 := mm_pow_sub ih (h0 _ _) ((h0 _ _).pow _) V.l
    have h3 := mm_add (h1 (a + n) x) h2
    rw [← pow_mul, ← pow_succ, sub_add_sub_cancel] at h3
    push_cast
    rwa [← add_assoc]

theorem limit_idempotent_range : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∀ E : Matrix κ κ C, (∀ (N : ℕ) (v : κ → C) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (E.mulVec v i - (L (ε ^ (V.l ^ n))).mulVec v i)) → ∀ v : κ → C, ∃ w : ZMod d → κ → C, (∀ a x, (L x).mulVec (w a) = em a x • w a) ∧ E.mulVec v = ∑ a, w a := by
  intro C _ _ V O _ κ _ _ L hL d _ em h0 h1 ε hε hP E hE v
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hF : ∀ x : O, ∃ y, ε * (x ^ (V.l ^ d) - x) = (V.l : O) * y := by
    intro x
    apply hP
    intro a
    have := mm_neg (frob_iter em h0 h1 a x d)
    simpa using this
  have hzero : ∃ w : ZMod d → κ → C, (∀ a x, (L x).mulVec (w a) = em a x • w a) ∧
      (0 : κ → C) = ∑ a, w a := ⟨0, by simp, by simp⟩
  have htop := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun x : O => Matrix.toLin' (L x))
    (fun x y _ => by
      show Matrix.toLin' (L x) * Matrix.toLin' (L y) = Matrix.toLin' (L y) * Matrix.toLin' (L x)
      rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul,
        ← Matrix.toLin'_mul, ← map_mul, ← map_mul, mul_comm])
    (fun x => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hv : v ∈ ⨆ χ : O → C, ⨅ x, Module.End.maxGenEigenspace (Matrix.toLin' (L x)) (χ x) := by
    rw [htop]; trivial
  induction hv using Submodule.iSup_induction' with
  | zero => simpa using hzero
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, hw'⟩ := hx
    obtain ⟨u, hu, hu'⟩ := hy
    refine ⟨w + u, fun a x => ?_, ?_⟩
    · simp [Matrix.mulVec_add, hw, hu]
    · simp [Matrix.mulVec_add, hw', hu', Finset.sum_add_distrib]
  | mem χ v hv =>
    have hgen : ∀ x, ∃ k : ℕ, ((L x - χ x • (1 : Matrix κ κ C)) ^ k).mulVec v = 0 := by
      intro x
      have := (Submodule.mem_iInf _).mp hv x
      rw [Module.End.mem_maxGenEigenspace] at this
      obtain ⟨k, hk⟩ := this
      refine ⟨k, ?_⟩
      rw [← Matrix.toLin'_apply, Matrix.toLin'_pow, map_sub, map_smul, Matrix.toLin'_one]
      exact hk
    by_cases hv0 : v = 0
    · subst hv0; simpa using hzero
    obtain ⟨ψ, hψχ, hψ⟩ := GlobalTheory.T.exists_integral_character_generalizedEigen C V O κ L hL χ v hv0 hgen
    by_cases hw0 : E.mulVec v = 0
    · rw [hw0]; exact hzero
    set w := E.mulVec v with hwdef
    have hEu : ∀ N : ℕ, ∃ n0 : ℕ, ∀ n ≥ n0, ∀ i,
        V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec v i) := fun N => uniform (hE N v)
    have hgenw : ∀ x, ∃ k : ℕ, ((L x - ψ x • (1 : Matrix κ κ C)) ^ k).mulVec w = 0 := by
      intro x
      obtain ⟨k, hk⟩ := hgen x
      rw [← hψχ] at hk
      refine ⟨k, funext fun i => eq_zero_of_ge_all (V := V) fun N => ?_⟩
      obtain ⟨n, hn⟩ := hEu N
      have hint : ∀ i j, V.Ge 0 ((L x - ψ x • (1 : Matrix κ κ C)) i j) := by
        intro i j
        rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        refine (hL x i j).sub ((hψ x).mul_int ?_)
        rw [← map_one L]; exact hL 1 i j
      have hc : Commute (L x - ψ x • (1 : Matrix κ κ C)) (L (ε ^ (V.l ^ n))) := by
        refine Commute.sub_left ((Commute.all _ _).map L) ?_
        exact (Commute.one_left _).smul_left _
      have h2 := ge_pow_mulVec hint (v := w - (L (ε ^ (V.l ^ n))).mulVec v) (hn n le_rfl) k i
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec v _ (L _), (hc.pow_left k).eq, ← Matrix.mulVec_mulVec, hk,
        Matrix.mulVec_zero, sub_zero] at h2
      exact h2
    have hfix : ∀ (N : ℕ) i, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (w i - (L (ε ^ (V.l ^ n))).mulVec w i) := by
      intro N i
      obtain ⟨n0, hn0⟩ := hEu N
      obtain ⟨b, hb⟩ := exists_lower_vec (V := V) v
      refine ⟨max n0 (N + b), fun n hn => ?_⟩
      have hn1 : n0 ≤ n := le_trans (le_max_left _ _) hn
      have hn2 : N + b ≤ n := le_trans (le_max_right _ _) hn
      obtain ⟨y, hy⟩ := hε
      obtain ⟨z, hz⟩ := dvd_sub_pow_of_dvd_sub (p := V.l) (a := ε * ε) (b := ε) ⟨y, hy⟩ n
      rw [mul_pow] at hz
      set e := ε ^ (V.l ^ n) with he
      have hA := hn0 n hn1 i
      have hB := ge_mulVec (hL e) (v := w - (L e).mulVec v) (hn0 n hn1) i
      have hC : V.Ge N ((L (e * e - e)).mulVec v i) := by
        rw [hz, map_mul, map_pow, map_natCast, ← Nat.cast_pow, ← nsmul_eq_mul,
          ← Nat.cast_smul_eq_nsmul C, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, Nat.cast_pow]
        refine ((ge_l_pow (n + 1)).mul (ge_mulVec (hL z) hb i)).mono ?_
        have : (N : ℝ) + b ≤ n := by exact_mod_cast hn2
        push_cast; linarith
      have h3 := (hA.sub hB).sub hC
      convert h3 using 1
      simp only [map_sub, map_mul, Matrix.mulVec_sub, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
        Pi.sub_apply]
      ring
    have heig := GlobalTheory.T.eigenvector_of_generalized_eigen_unramified C V O κ L hL d hd ε hε hF ψ w hψ hgenw hfix
    have hnot : ¬ V.MM (ψ ε) := by
      intro hm
      apply hw0
      funext i
      refine eq_zero_of_ge_all (V := V) fun N => ?_
      obtain ⟨n, hn⟩ := hfix N i
      have h2 := hn n le_rfl
      rw [heig, Pi.smul_apply, smul_eq_mul, ← one_sub_mul] at h2
      refine ge_of_unit_mul ?_ h2
      obtain ⟨m, hm'⟩ := Nat.exists_eq_succ_of_ne_zero (pow_ne_zero n V.l_prime.ne_zero)
      rw [hm', map_pow, pow_succ']
      exact mm_mul hm ((hψ ε).pow _)
    have hl : ∀ x y : O, ε * x = (V.l : O) * y → V.MM (ψ x) := by
      intro x y hxy
      have h2 : V.MM (ψ ε * ψ x) := by
        rw [← map_mul, hxy, map_mul, map_natCast]
        exact mm_mul mm_l (hψ y)
      exact (mm_or h2).resolve_left hnot
    have hone : V.MM (ψ ε - 1) := by
      obtain ⟨y, hy⟩ := hε
      have := hl (ε - 1) y (by rw [← hy]; ring)
      simpa using this
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_embedding_congr_integral_character C V O d em h0 h1 ψ hψ fun x hx => by
      obtain ⟨y, hy⟩ := hP x hx
      exact hl x y hy
    have hψa := GlobalTheory.T.ringHom_eq_of_congruent_integral_unramified C V O d hd ε hε hF ψ (em a) hψ (h0 a) hone ha
    refine ⟨Pi.single a w, fun b x => ?_, by simp⟩
    by_cases hb : b = a
    · subst hb; rw [Pi.single_eq_same, heig, hψa]
    · simp [Pi.single_eq_of_ne hb]

end GlobalTheory.IdemRange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LimitIdempotentRangeLeSumEigenspacesStatement
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitIdempotent_range_le_sum_eigenspaces : ∀ (C : Type) [Field C] [IsAlgClosed C] (V : VF C) (O : Type) [CommRing O] (κ : Type) [Fintype κ] [DecidableEq κ] (L : O →+* Matrix κ κ C), (∀ x i j, V.Ge 0 (L x i j)) → ∀ (d : ℕ) [NeZero d] (em : ZMod d → (O →+* C)), (∀ a x, V.Ge 0 (em a x)) → (∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)) → ∀ ε : O, (∃ y, ε * ε - ε = (V.l : O) * y) → (∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y) → ∀ E : Matrix κ κ C, (∀ (N : ℕ) (v : κ → C) i, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (E.mulVec v i - (L (ε ^ (V.l ^ n))).mulVec v i)) → ∀ v : κ → C, ∃ w : ZMod d → κ → C, (∀ a x, (L x).mulVec (w a) = em a x • w a) ∧ E.mulVec v = ∑ a, w a := by
  first | exact @GlobalTheory.IdemRange.limit_idempotent_range | exact GlobalTheory.IdemRange.limit_idempotent_range | (intros; apply GlobalTheory.IdemRange.limit_idempotent_range <;> assumption)
end
