module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArithmeticCMKnownTheoremsProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulPow
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MatNthRoot

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}

def Bnd (r : WithZero (Multiplicative ℤ)) (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) : Prop :=
  ∀ i j, Valued.v (X i j) ≤ r

theorem v_natCast_le_one (m : ℕ) : Valued.v ((m : P.adicCompletion E)) ≤ 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ]
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

variable {r s : WithZero (Multiplicative ℤ)} {X Y : Matrix (Fin N) (Fin N) (P.adicCompletion E)}

theorem bnd_add (hX : Bnd r X) (hY : Bnd r Y) : Bnd r (X + Y) := fun i j =>
  (Valuation.map_add _ _ _).trans (max_le (hX i j) (hY i j))

theorem bnd_neg (hX : Bnd r X) : Bnd r (-X) := fun i j => by
  rw [Matrix.neg_apply, Valuation.map_neg]; exact hX i j

theorem bnd_sub (hX : Bnd r X) (hY : Bnd r Y) : Bnd r (X - Y) := by
  rw [sub_eq_add_neg]; exact bnd_add hX (bnd_neg hY)

theorem bnd_smul (a : P.adicCompletion E) (hX : Bnd r X) : Bnd (Valued.v a * r) (a • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]; exact mul_le_mul' le_rfl (hX i j)

theorem bnd_mul (hX : Bnd r X) (hY : Bnd s Y) : Bnd (r * s) (X * Y) := fun i j => by
  rw [Matrix.mul_apply]
  exact Valuation.map_sum_le _ fun k _ => by rw [Valuation.map_mul]; exact mul_le_mul' (hX i k) (hY k j)

theorem bnd_mono (h : r ≤ s) (hX : Bnd r X) : Bnd s X := fun i j => (hX i j).trans h

theorem bnd_zero : Bnd r (0 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) := fun i j => by simp

theorem bnd_one : Bnd 1 (1 : Matrix (Fin N) (Fin N) (P.adicCompletion E)) := fun i j => by
  rw [Matrix.one_apply]; split_ifs <;> simp

theorem bnd_sum {ι : Type} (t : Finset ι) (f : ι → Matrix (Fin N) (Fin N) (P.adicCompletion E))
    (h : ∀ k ∈ t, Bnd r (f k)) : Bnd r (∑ k ∈ t, f k) := fun i j => by
  rw [Matrix.sum_apply]; exact Valuation.map_sum_le _ fun k hk => h k hk i j

theorem bnd_pow (hX : Bnd 1 X) : ∀ k : ℕ, Bnd 1 (X ^ k)
  | 0 => by rw [pow_zero]; exact bnd_one
  | k + 1 => by rw [pow_succ]; simpa only [one_mul] using bnd_mul (bnd_pow hX k) hX

theorem bnd_pow_sub (hX : Bnd 1 X) (hY : Bnd 1 Y) (hXY : Bnd r (X - Y)) :
    ∀ k : ℕ, Bnd r (X ^ k - Y ^ k)
  | 0 => by rw [pow_zero, pow_zero, sub_self]; exact bnd_zero
  | k + 1 => by
    have e : X ^ (k + 1) - Y ^ (k + 1) = X ^ k * (X - Y) + (X ^ k - Y ^ k) * Y := by
      rw [pow_succ, pow_succ]; noncomm_ring
    rw [e]
    exact bnd_add (by simpa only [one_mul] using bnd_mul (bnd_pow hX k) hXY)
      (by simpa only [mul_one] using bnd_mul (bnd_pow_sub hX hY hXY k) hY)

noncomputable def tail (n : ℕ) (c : P.adicCompletion E) (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) :
    Matrix (Fin N) (Fin N) (P.adicCompletion E) :=
  ∑ k ∈ Finset.range (n - 1), ((n.choose (k + 2) : P.adicCompletion E) * ((n : P.adicCompletion E) * c) ^ k) • X ^ (k + 2)

theorem v_coef_le_one (n k : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) :
    Valued.v ((n.choose (k + 2) : P.adicCompletion E) * ((n : P.adicCompletion E) * c) ^ k) ≤ 1 := by
  rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_mul]
  exact mul_le_one' (v_natCast_le_one _) (pow_le_one' (mul_le_one' (v_natCast_le_one _) hc) _)

theorem bnd_tail (n : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) (hX : Bnd 1 X) :
    Bnd 1 (tail n c X) :=
  bnd_sum _ _ fun k _ => bnd_mono (by simpa only [mul_one] using v_coef_le_one n k hc)
    (bnd_smul _ (bnd_pow hX _))

theorem bnd_tail_sub (n : ℕ) {c : P.adicCompletion E} (hc : Valued.v c ≤ 1) (hX : Bnd 1 X) (hY : Bnd 1 Y)
    (hXY : Bnd r (X - Y)) : Bnd r (tail n c X - tail n c Y) := by
  unfold tail
  rw [← Finset.sum_sub_distrib]
  refine bnd_sum _ _ fun k _ => ?_
  rw [← smul_sub]
  exact bnd_mono (by simpa only [one_mul] using mul_le_mul' (v_coef_le_one n k hc) (le_refl r))
    (bnd_smul _ (bnd_pow_sub hX hY hXY _))

theorem one_add_smul_pow (n : ℕ) (hn : 0 < n) (c : P.adicCompletion E)
    (X : Matrix (Fin N) (Fin N) (P.adicCompletion E)) :
    (1 + ((n : P.adicCompletion E) * c) • X) ^ n =
      1 + ((n : P.adicCompletion E) ^ 2 * c) • (X + c • tail n c X) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [add_comm (1 : Matrix _ _ _), (Commute.one_right _).add_pow]
  simp only [one_pow, mul_one]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [tail, Nat.add_sub_cancel, smul_add, Finset.smul_sum, smul_smul, smul_pow]
  have hc : ∀ (j : ℕ) (Z : Matrix (Fin N) (Fin N) (P.adicCompletion E)),
      Z * ((j : ℕ) : Matrix (Fin N) (Fin N) (P.adicCompletion E)) = (j : P.adicCompletion E) • Z := by
    intro j Z
    rw [← Nat.cast_comm, ← nsmul_eq_mul, Nat.cast_smul_eq_nsmul]
  simp only [hc, smul_smul]
  have hs : ∀ x ∈ Finset.range m,
      (((m + 1).choose (x + 1 + 1) : P.adicCompletion E) * (((m + 1 : ℕ) : P.adicCompletion E) * c) ^ (x + 1 + 1)) •
        X ^ (x + 1 + 1) =
      (((m + 1 : ℕ) : P.adicCompletion E) ^ 2 * c * (c * (((m + 1).choose (x + 2) : P.adicCompletion E) *
        (((m + 1 : ℕ) : P.adicCompletion E) * c) ^ x))) • X ^ (x + 2) := by
    intro x _
    rw [show x + 1 + 1 = x + 2 by omega]
    congr 1
    ring
  rw [Finset.sum_congr rfl hs]
  simp only [zero_add, Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one, Nat.cast_one,
    one_mul, one_smul]
  have e : ((m + 1 : ℕ) : P.adicCompletion E) * (((m + 1 : ℕ) : P.adicCompletion E) * c) =
      ((m + 1 : ℕ) : P.adicCompletion E) ^ 2 * c := by ring
  rw [e]
  abel

end GlobalTheory.MatNthRoot

namespace GlobalTheory.MatNthRoot

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}

theorem exists_nthRoot : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (N n : ℕ)
    (c : P.adicCompletion E) (A : Matrix (Fin N) (Fin N) (P.adicCompletion E)), 0 < n → Valued.v c < 1 →
    (∀ i j, Valued.v ((A - 1) i j) ≤ Valued.v ((n : P.adicCompletion E) ^ 2 * c)) →
    ∃ M : Matrix (Fin N) (Fin N) (P.adicCompletion E),
      (∀ i j, Valued.v ((M - 1) i j) ≤ Valued.v ((n : P.adicCompletion E) * c)) ∧ M ^ n = A := by
  intro E _ _ P N n c A hn hc hA
  have hc1 : Valued.v c ≤ 1 := hc.le
  rcases eq_or_ne c 0 with rfl | hc0
  · refine ⟨1, fun i j => by simp, ?_⟩
    rw [one_pow]
    have hA1 : A - 1 = 0 := Matrix.ext fun i j => by
      have h := hA i j
      rwa [mul_zero, Valuation.map_zero, le_zero_iff, Valuation.zero_iff] at h
    exact (sub_eq_zero.1 hA1).symm
  have hn0 : (n : P.adicCompletion E) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  set s : P.adicCompletion E := (n : P.adicCompletion E) ^ 2 * c with hs
  have hs0 : s ≠ 0 := mul_ne_zero (pow_ne_zero _ hn0) hc0
  set Y : Matrix (Fin N) (Fin N) (P.adicCompletion E) := s⁻¹ • (A - 1) with hYdef
  have hY : Bnd 1 Y := fun i j => by
    rw [hYdef, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
    calc Valued.v s⁻¹ * Valued.v ((A - 1) i j) ≤ Valued.v s⁻¹ * Valued.v s := mul_le_mul' le_rfl (hA i j)
      _ = 1 := by rw [← Valuation.map_mul, inv_mul_cancel₀ hs0, Valuation.map_one]
  let f : Matrix (Fin N) (Fin N) (P.adicCompletion E) → Matrix (Fin N) (Fin N) (P.adicCompletion E) :=
    fun X => Y - c • tail n c X
  have hf1 : ∀ X, Bnd 1 X → Bnd 1 (f X) := fun X hX =>
    bnd_sub hY (bnd_mono (by simpa only [mul_one] using hc1) (bnd_smul c (bnd_tail n hc1 hX)))
  have hfl : ∀ X Z r, Bnd 1 X → Bnd 1 Z → Bnd r (X - Z) → Bnd (Valued.v c * r) (f X - f Z) := by
    intro X Z r hX hZ hXZ
    have e : f X - f Z = -(c • (tail n c X - tail n c Z)) := by
      simp only [f, smul_sub]; abel
    rw [e]
    exact bnd_neg (bnd_smul c (bnd_tail_sub n hc1 hX hZ hXZ))
  have hb : ∀ k : ℕ, Bnd 1 (f^[k] 0) := by
    intro k
    induction k with
    | zero => exact bnd_zero
    | succ k ih => rw [Function.iterate_succ_apply']; exact hf1 _ ih
  have hd : ∀ k : ℕ, Bnd (Valued.v c ^ k) (f^[k + 1] 0 - f^[k] 0) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact bnd_sub (hb 1) (hb 0)
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have := hfl _ _ _ (hb (k + 1)) (hb k) ih
      rwa [← Function.iterate_succ_apply' f k 0, ← pow_succ'] at this
  have hcau : ∀ i j, CauchySeq fun k => (f^[k] 0) i j := by
    intro i j
    refine cauchySeq_of_le_geometric ‖c‖ 1 (Valued.toNormedField.norm_lt_one_iff.2 hc) fun k => ?_
    rw [dist_eq_norm', one_mul, ← norm_pow]
    refine Valued.toNormedField.norm_le_iff.2 ?_
    rw [Valuation.map_pow]
    have := hd k i j
    rwa [Matrix.sub_apply] at this
  choose L hL using fun i j => cauchySeq_tendsto_of_complete (hcau i j)
  set L' : Matrix (Fin N) (Fin N) (P.adicCompletion E) := Matrix.of L with hL'
  have hT : Filter.Tendsto (fun k => f^[k] 0) Filter.atTop (nhds L') :=
    tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hL i j
  have hfc : Continuous f := by
    simp only [f, tail]
    fun_prop
  have hfix : f L' = L' := by
    have h1 : Filter.Tendsto (fun k => f^[k + 1] 0) Filter.atTop (nhds L') :=
      hT.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun k => f^[k + 1] 0) Filter.atTop (nhds (f L')) := by
      simp only [Function.iterate_succ_apply']
      exact (hfc.tendsto L').comp hT
    exact tendsto_nhds_unique h2 h1
  have hLb : Bnd 1 L' := by
    intro i j
    have hm := (Valued.isClosed_valuationSubring (P.adicCompletion E)).mem_of_tendsto (hL i j)
      (Filter.Eventually.of_forall fun k => (Valuation.mem_valuationSubring_iff _ _).2 (hb k i j))
    exact (Valuation.mem_valuationSubring_iff _ _).1 hm
  refine ⟨1 + ((n : P.adicCompletion E) * c) • L', fun i j => ?_, ?_⟩
  · rw [add_sub_cancel_left, Matrix.smul_apply, smul_eq_mul, Valuation.map_mul]
    simpa only [mul_one] using mul_le_mul' (le_refl (Valued.v ((n : P.adicCompletion E) * c))) (hLb i j)
  · rw [one_add_smul_pow n hn c L']
    have e : L' + c • tail n c L' = Y := by
      nth_rewrite 1 [← hfix]
      simp only [f]
      abel
    rw [e, hYdef, smul_smul, ← hs, mul_inv_cancel₀ hs0, one_smul, add_sub_cancel]

end GlobalTheory.MatNthRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesShapeAtBadPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesShapeAtBadPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT.CosShape

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem pow_smul_mem (S : Submodule (𝓞 E) (Sp E n)) (r : 𝓞 E) (k : ℕ) {x : Sp E n} (hx : x ∈ S) :
    ((r : E) ^ k) • x ∈ S := by

  have h : ((r : E) ^ k) • x = (r ^ k) • x := by
    rw [← algebraMap_smul E (r ^ k) x]
    simp
  rw [h]
  exact S.smul_mem _ hx

theorem core (S₀ L : Submodule (𝓞 E) (Sp E n)) (F : Sp E n ≃ₗ[E] Sp E n) (hF : ∀ w ∈ L, F.symm w ∈ S₀)
    (c : E) (hc : c ≠ 0) (hpow : ∀ (S : Submodule (𝓞 E) (Sp E n)) (k : ℕ) (x : Sp E n), x ∈ S → c ^ k • x ∈ S)
    (Y : Set (Sp E n)) (y₀ : Sp E n) (e e' : ℕ) (hY0 : y₀ ∈ Y) (hY : ∀ y ∈ Y, (c ^ e)⁻¹ • (y - y₀) ∈ L)
    (hy₀ : c ^ e' • y₀ ∈ L) (C : Set (Sp E n)) (hC : ∀ z, z ∈ C ↔ ∃ y ∈ Y, (c ^ e)⁻¹ • (z - F.symm y) ∈ S₀) :
    C.Nonempty ∧ (∀ y ∈ Y, F.symm y ∈ C) ∧ ∀ z ∈ C, (∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀) ∧
      ∀ (g g' : Sp E n ≃ₗ[E] Sp E n) (D : ℕ), (∀ x, g' x ∈ S₀ ↔ x ∈ S₀) →
        (∀ x ∈ S₀, (c ^ D)⁻¹ • (g x - g' x) ∈ S₀) → e + e' ≤ D →
        (c ^ e)⁻¹ • (g z - z) ∈ S₀ → ∀ z', g' z' ∈ C ↔ z' ∈ C := by

  have hYY : ∀ y ∈ Y, ∀ y' ∈ Y, (c ^ e)⁻¹ • (F.symm y - F.symm y') ∈ S₀ := by
    intro y hy y' hy'
    have h1 := hF _ (hY y hy)
    have h2 := hF _ (hY y' hy')
    have h3 : (c ^ e)⁻¹ • (F.symm y - F.symm y') =
        F.symm ((c ^ e)⁻¹ • (y - y₀)) - F.symm ((c ^ e)⁻¹ • (y' - y₀)) := by
      simp only [LinearEquiv.map_smul, map_sub]
      rw [← smul_sub]
      congr 1
      abel
    rw [h3]
    exact S₀.sub_mem h1 h2
  have hself : ∀ y ∈ Y, F.symm y ∈ C := by
    intro y hy
    exact (hC _).2 ⟨y, hy, by simp⟩

  have hmem : ∀ z ∈ C, ∀ z', z' ∈ C ↔ (c ^ e)⁻¹ • (z' - z) ∈ S₀ := by
    intro z hz z'
    obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
    constructor
    · intro hz'
      obtain ⟨y₂, hy₂, hz2⟩ := (hC z').1 hz'
      have key := S₀.add_mem (S₀.sub_mem hz2 hz1) (hYY y₂ hy₂ y₁ hy₁)
      convert key using 1
      rw [← smul_sub, ← smul_add]
      congr 1
      abel
    · intro h
      refine (hC z').2 ⟨y₁, hy₁, ?_⟩
      have key := S₀.add_mem h hz1
      convert key using 1
      rw [← smul_add]
      congr 1
      abel
  refine ⟨⟨F.symm y₀, hself y₀ hY0⟩, hself, fun z hz => ⟨hmem z hz, ?_⟩⟩
  intro g g' D hg' hD hle hgz z'
  obtain ⟨y₁, hy₁, hz1⟩ := (hC z).1 hz
  have hce : c ^ e ≠ 0 := pow_ne_zero _ hc

  have hx₀ : c ^ e' • z ∈ S₀ := by
    have a1 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (z - F.symm y₁))) ∈ S₀ := hpow _ _ _ (hpow _ _ _ hz1)
    have a2 : c ^ e' • (c ^ e • ((c ^ e)⁻¹ • (F.symm y₁ - F.symm y₀))) ∈ S₀ :=
      hpow _ _ _ (hpow _ _ _ (hYY y₁ hy₁ y₀ hY0))
    have a3 : F.symm (c ^ e' • y₀) ∈ S₀ := hF _ hy₀
    rw [smul_inv_smul₀ hce] at a1 a2
    rw [LinearEquiv.map_smul] at a3
    have a4 := S₀.add_mem (S₀.add_mem a1 a2) a3
    convert a4 using 1
    rw [← smul_add, ← smul_add]
    congr 1
    abel

  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hdiff : (c ^ e)⁻¹ • (g z - g' z) ∈ S₀ := by
    have b1 := hpow S₀ k _ (hD _ hx₀)
    convert b1 using 1
    rw [LinearEquiv.map_smul, LinearEquiv.map_smul, ← smul_sub, smul_smul, smul_smul]
    congr 1
    rw [pow_add, pow_add]
    field_simp
  have ht : (c ^ e)⁻¹ • (g' z - z) ∈ S₀ := by
    have b2 := S₀.sub_mem hgz hdiff
    convert b2 using 1
    rw [← smul_sub]
    congr 1
    abel
  rw [hmem z hz (g' z'), hmem z hz z']
  have hsplit : (c ^ e)⁻¹ • (g' z' - z) = g' ((c ^ e)⁻¹ • (z' - z)) + (c ^ e)⁻¹ • (g' z - z) := by
    rw [LinearEquiv.map_smul, ← smul_add, map_sub]
    congr 1
    abel
  rw [hsplit, add_mem_cancel_right ht]
  exact hg' _

end Gen

end GlobalTheory.Mem.Col2.AdT.CosShape

namespace GlobalTheory.Mem.Col2.AdT.CosShape


set_option maxHeartbeats 1600000 in
open Classical in
theorem cosShape : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (P : SBof I a), (i + 1 ≠ B.R.m → cosetIn p P = ∅) ∧ (i + 1 = B.R.m → (cosetIn p P).Nonempty ∧ (∀ y ∈ p.1.2, (frsF I.sel (I.tup a) p.1.1 P).symm y ∈ cosetIn p P) ∧ ∀ z ∈ cosetIn p P, (∀ z', z' ∈ cosetIn p P ↔ GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P z' z) ∧ ∀ g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → CongE P.1 ((I.cst a).D P) g g' → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g z) z → ∀ z', g' z' ∈ cosetIn p P ↔ z' ∈ cosetIn p P) := by
  intro B X I hI u a i p P
  refine ⟨fun hi => ?_, fun hi => ?_⟩
  ·
    have h0 : p.1.2 = ∅ := by
      have h := p.2
      rw [ysAt_ys_of_ne (h := hi)] at h
      exact Set.mem_singleton_iff.mp h
    ext z
    simp [cosetIn, h0]
  · have hY := PtAt.mem_ybSet p hi
    unfold ybSet at hY
    obtain ⟨y₀, hy₀, hYeq⟩ := hY

    have hfr : ∀ x, (frsF I.sel (I.tup a) p.1.1 P) x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N ↔
        x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro x
      simp only [frsF]
      split_ifs with h
      · exact (GlobalTheory.TopStep.liftFr_spec p.1.1.deco.2 ⟨P.1, h⟩).1 x
      · exact p.1.1.2 ⟨P.1, (Finset.mem_union.mp P.2).resolve_left h⟩ x
    have hF : ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N,
        (frsF I.sel (I.tup a) p.1.1 P).symm w ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro w hw
      rw [← hfr, LinearEquiv.apply_symm_apply]
      exact hw
    have hc : ((qOf P.1 : ℕ) : B.fields.E) ≠ 0 := by
      exact_mod_cast (GlobalTheory.GO.ChRoot.qOf_pos P.1).ne'
    have hpow : ∀ (S : Submodule (𝓞 B.fields.E) (Sp B.fields.E (B.R.N i))) (k : ℕ) (x : Sp B.fields.E (B.R.N i)),
        x ∈ S → ((qOf P.1 : ℕ) : B.fields.E) ^ k • x ∈ S := by
      intro S k x hx
      have h := pow_smul_mem S ((qOf P.1 : ℕ) : 𝓞 B.fields.E) k hx
      simpa using h
    have hY0 : y₀ ∈ p.1.2 := by
      rw [hYeq, Set.mem_setOf_eq, sub_self]
      exact zero_mem _
    have hY1 := (mem_locLat _ _ _ _).1 hy₀ P
    have hGL : ∀ g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i),
        g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 →
          ∀ x, g' x ∈ stdAt B.fields.E (B.R.N i) P.1 ↔ x ∈ stdAt B.fields.E (B.R.N i) P.1 := by
      intro g' hg'
      exact hg'
    by_cases hP : P.1 ∈ (B.primes X).vGs
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (y - y₀) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ 1 • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_pos hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ 0)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_pos hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ 0 1 hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD1 := (hI.idx_ok a).depthG P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'
    ·
      have hYl : ∀ y ∈ p.1.2, (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (y - y₀) ∈
          Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        intro y hy
        rw [hYeq, Set.mem_setOf_eq] at hy
        have h := (mem_locLat _ _ _ _).1 hy P
        simpa [hP] using h
      have hy₀' : ((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N := by
        simpa [hP] using hY1
      have hC : ∀ z, z ∈ cosetIn p P ↔ ∃ y ∈ p.1.2,
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (z - (frsF I.sel (I.tup a) p.1.1 P).symm y) ∈
            stdAt B.fields.E (B.R.N i) P.1 := by
        intro z
        simp only [cosetIn, Set.mem_setOf_eq, if_neg hP]
      have hSC : ∀ x y : Sp B.fields.E (B.R.N i), GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P x y ↔
          (((qOf P.1 : ℕ) : B.fields.E) ^ (I.cst a).M)⁻¹ • (x - y) ∈ stdAt B.fields.E (B.R.N i) P.1 := by
        intro x y
        rw [GlobalTheory.GO.ChRoot.mem_stdAt']
        simp only [GlobalTheory.TwU.SameCoset, if_neg hP, Pi.smul_apply, smul_eq_mul]
      obtain ⟨k1, k2, k3⟩ := core (stdAt B.fields.E (B.R.N i) P.1) (Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N)
        (frsF I.sel (I.tup a) p.1.1 P) hF _ hc hpow p.1.2 y₀ (I.cst a).M (I.cst a).M hY0 hYl hy₀' (cosetIn p P) hC
      refine ⟨k1, k2, fun z hz => ⟨fun z' => ((k3 z hz).1 z').trans (hSC z' z).symm, ?_⟩⟩
      intro g g' hg' hcong hgz z'
      have hD2 := (hI.idx_ok a).depthQ P hP
      exact (k3 z hz).2 g g' _ (hGL g' hg') hcong (by omega) ((hSC _ _).1 hgz) z'

end GlobalTheory.Mem.Col2.AdT.CosShape
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesShapeAtBadPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetInFrames_shape_at_bad_prime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (i : ℕ) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (P : SBof I a), (i + 1 ≠ B.R.m → cosetIn p P = ∅) ∧ (i + 1 = B.R.m → (cosetIn p P).Nonempty ∧ (∀ y ∈ p.1.2, (frsF I.sel (I.tup a) p.1.1 P).symm y ∈ cosetIn p P) ∧ ∀ z ∈ cosetIn p P, (∀ z', z' ∈ cosetIn p P ↔ GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P z' z) ∧ ∀ g g' : Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i), g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1 → CongE P.1 ((I.cst a).D P) g g' → GlobalTheory.TwU.SameCoset I.sel (I.tup a) (I.cst a) P (g z) z → ∀ z', g' z' ∈ cosetIn p P ↔ z' ∈ cosetIn p P) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.CosShape.cosShape | exact GlobalTheory.Mem.Col2.AdT.CosShape.cosShape | (intros; apply GlobalTheory.Mem.Col2.AdT.CosShape.cosShape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalCMTripleExponentialOfPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalCMTripleExponentialOfPeriod
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries

noncomputable section

namespace GlobalTheory.CuspFrom.PeriodTriple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {D : Datum H}
  {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}

theorem exists_isExp_of_sabMap {S : Scheme.{0}} {t : SAB H S} {y : Sp ℂ ⟶ S} (B : GlobalTheory.CM.PAT H (Sp ℂ))
    (m : SABMap B.t t y) (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) (hP : IsPeriod D ty P)
    (hol : IsHolTo Set.univ fun z => (e z).left) (add : ∀ z w, e (z + w) = e z * e w) (onto : Function.Surjective e)
    (ker : ∀ z, e z = 1 ↔ z ∈ P.range) (lin : ∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a)
    (weil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) :
    ∃ ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G), GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hy : y = spMap (RingHom.id ℂ) ≫ y := by rw [hid, Category.id_comp]
  obtain ⟨p, hp⟩ := LiePull.exists_pushEquiv m.cart (Over.mk (spMap (RingHom.id ℂ))) y hy
  have hp' : ∀ z, (p.symm (e z)).left ≫ m.φ = (e z).left := fun z => by
    rw [← hp, p.apply_symm_apply]
  refine ⟨fun z => p.symm (e z), hP, ?_, fun z w => ?_, p.symm.surjective.comp onto, fun z => ?_, fun a z => ?_,
    fun k a b c hk hc => ?_⟩
  · refine ThetaPoint.isHolTo_fibre m.cart.1 _ (fun z => (Over.w (p.symm (e z))).trans hid) ?_
    have h : (fun z => (p.symm (e z)).left ≫ m.cm.F) = fun z => (e z).left := funext hp'
    exact h ▸ hol
  · beta_reduce
    rw [add, map_mul]
  · exact (map_eq_one_iff _ p.symm.injective).trans (ker z)
  · beta_reduce
    rw [lin, p.symm_apply_eq]
    apply Over.OverMorphism.ext
    rw [hp, Over.comp_left, Over.comp_left, Category.assoc, m.act, ← Category.assoc]
    exact congrArg (· ≫ _) (hp' z).symm
  · exact (GlobalTheory.CM.ExCompare.weilIs_iff m _ _ hy k _ _ _ _ c (hp' _).symm (hp' _).symm).2 (weil k a b c hk hc)

theorem exists_isExp_of_rank_zero (l : Level H) (hD : D.p + D.q = 0) (hP : IsPeriod D ty P) :
    ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)),
      GlobalTheory.CM.IsExp B (RingHom.id ℂ) D ty P ex := by
  obtain ⟨B, hB, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H D l _ _ _ _
    (Models.RankZero.zeroObj hD l (spMap (algebraMap (KA l) ℂ)))
  have hz : IsIso B.t.G.hom := by
    rw [hB]
    exact Models.RankZero.isIso_zeroTriple _
  have := Models.RankZero.subsingleton_La hD
  have h0 : ∀ z : Fin g → ℂ, z = 0 := fun z => by
    have hz : z ∈ Submodule.span ℝ (Set.range P) := hP.2.2.2.1 ▸ Submodule.mem_top
    refine (Submodule.span_le (p := ⊥)).2 ?_ hz
    rintro _ ⟨a, rfl⟩
    rw [Subsingleton.elim a 0, map_zero]
    exact Submodule.zero_mem _
  refine ⟨B, fun _ => 1, hP, fun U f => ⟨?_, differentiableOn_const _⟩, fun _ _ => (_root_.mul_one _).symm,
    fun x => ⟨0, Models.RankZero.hom_unique hz _ _⟩, fun z => ⟨fun _ => ⟨0, by rw [map_zero, h0 z]⟩, fun _ => rfl⟩,
    fun _ _ => Models.RankZero.hom_unique hz _ _, fun k a b c hk hc => ?_⟩
  · simp only [Set.mem_univ, true_and]
    exact isOpen_const
  · have e : c = 1 := Units.ext (by rw [hc, Subsingleton.elim b 0, map_zero]; simp)
    rw [e, unitOn, map_one]
    exact Models.RankZero.weilIs_zero hz B.t.PP.isLB (Models.RankZero.triv_rig hz _) _ _ _

end GlobalTheory.CuspFrom.PeriodTriple

namespace GlobalTheory.CuspFrom

theorem exists_pat_isExp_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)), IsTypeFn H DB.p DB.q ty → IsPeriod DB ty PB → ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB ty PB ex := by
  intro E _ _ _ H l₀ DB g ty PB hty hP
  rcases Nat.eq_zero_or_pos (DB.p + DB.q) with h0 | hpq
  · exact PeriodTriple.exists_isExp_of_rank_zero l₀ h0 hP
  have kn := known_holds
  obtain ⟨l, hA⟩ : ∃ l : Level H, l.A = 1 := ⟨{ l₀ with A := 1, A_pos := one_pos }, rfl⟩
  obtain ⟨Xo⟩ := kn.n1ab E H DB l hpq
  have hζ : algebraMap (KA l) ℂ (baseKA l).ζ =
      Complex.exp (-(2 * Real.pi * Complex.I) * (((1 : ℤ) : ℂ)) / l.A) := by
    show zeta l.A = _
    rw [hA, zeta]
    simp [Complex.exp_neg]
  obtain ⟨y, e, -, -, ⟨add, onto, hol, -⟩, ker, lin, weil, -⟩ := GlobalTheory.Moduli.exists_point_of_isPeriod kn.theta kn.laws
    E H DB l Xo (algebraMap (KA l) ℂ) g ty hpq rfl hty DB LinearMap.id PB
    ⟨rfl, rfl, fun _ => LinearMap.id, fun _ => 1, fun n m _ _ a => ⟨0, by simp⟩,
      fun n _ => ⟨fun a => Iff.rfl, fun a => ⟨a, 0, by simp⟩⟩, fun n _ a a' => by simp, hζ, rfl⟩ hP
  obtain ⟨U, hU, -⟩ := GlobalTheory.CM.exists_pat_of_obj E H DB l _ _ _ _ Xo.univ
  obtain ⟨B, m, -⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ y U
  exact ⟨B, PeriodTriple.exists_isExp_of_sabMap B (hU ▸ m) e hP hol add onto ker lin weil⟩

end GlobalTheory.CuspFrom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalCMTripleExponentialOfPeriodStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory GlobalTheory.ArcQ GlobalTheory.ArcCM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.CuspFrom
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalCMTriple_exponential_of_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (l : Level H) (DB : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (PB : DB.La →+ (Fin g → ℂ)), IsTypeFn H DB.p DB.q ty → IsPeriod DB ty PB → ∃ (B : GlobalTheory.CM.PAT H (Sp ℂ)) (ex : (Fin g → ℂ) → (Over.mk (spMap (RingHom.id ℂ)) ⟶ B.t.G)), GlobalTheory.CM.IsExp B (RingHom.id ℂ) DB ty PB ex := by
  first | exact @GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod | exact GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod | (intros; apply GlobalTheory.CuspFrom.exists_pat_isExp_of_isPeriod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcOffBoundaryDescendsToModuliLocalization
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcOffBoundaryDescendsToModuliLocalization
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

noncomputable section

namespace GlobalTheory.ShFam.BdArc

theorem exists_basicOpen_subset_of_pt {A : Type} [CommRing A] (f : A →+* ℂ) (U : Set (Sp A)) (hU : IsOpen U)
    (h : ∀ s, spMap f s ∈ U) :
    ∃ a : A, f a ≠ 0 ∧ Set.range (spMap (algebraMap A (Localization.Away a))) ⊆ U := by
  let s₀ : PrimeSpectrum ℂ := ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨_, ⟨a, rfl⟩, h1, h2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := A)).exists_subset_of_mem_open (h s₀) hU
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply h1
    show f a ∈ (⊥ : Ideal ℂ)
    simp [h0]
  · have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
    rintro _ ⟨s, rfl⟩
    apply h2
    show _ ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))
    rw [← this]
    exact ⟨s, rfl⟩

theorem exists_hol_away {A : Type} [CommRing A] (ψ : ℂ → (A →+* ℂ)) (V : Set ℂ)
    (hψ : ∀ b, DifferentiableOn ℂ (fun u => ψ u b) V) (a : A) (ha : ∀ u ∈ V, ψ u a ≠ 0) (u₀ : ℂ) (h₀ : u₀ ∈ V) :
    ∃ ev : ℂ → (Localization.Away a →+* ℂ), (∀ u ∈ V, (ev u).comp (algebraMap A _) = ψ u) ∧
      ∀ t, DifferentiableOn ℂ (fun u => ev u t) V := by
  classical
  let ev : ℂ → (Localization.Away a →+* ℂ) := fun u =>
    if h : u ∈ V then IsLocalization.Away.lift a (g := ψ u) (Ne.isUnit (ha u h))
    else IsLocalization.Away.lift a (g := ψ u₀) (Ne.isUnit (ha u₀ h₀))
  have hev : ∀ u ∈ V, (ev u).comp (algebraMap A _) = ψ u := fun u hu => by
    simp only [ev, dif_pos hu]
    exact IsLocalization.Away.lift_comp a _
  refine ⟨ev, hev, fun t => ?_⟩
  obtain ⟨n, b, hb⟩ := IsLocalization.Away.surj a t
  refine (((hψ b).div ((hψ a).pow n) fun u hu => pow_ne_zero n (ha u hu))).congr fun u hu => ?_
  have h1 := congrArg (ev u) hb
  have h2 : ∀ z, ev u (algebraMap A _ z) = ψ u z := fun z => RingHom.congr_fun (hev u hu) z
  rw [map_mul, map_pow, h2, h2] at h1
  show _ = ψ u b / ψ u a ^ n
  rw [eq_div_iff (pow_ne_zero n (ha u hu)), h1]

theorem spMap_comp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem dualMap_comp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) :=
  by
    ext z <;> simp [dualMap]

theorem spMap_dualMap_sq {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    spMap (dualMap f) ≫ spMap (algebraMap A (DualNumber A)) = spMap (algebraMap B (DualNumber B)) ≫ spMap f := by
  rw [spMap_comp_comp, spMap_comp_comp]
  congr 1
  exact RingHom.ext fun z => by ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem arc_descends_to_moduli : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)), IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → ∀ u₀ ∈ Metric.ball (0 : ℂ) r, u₀ ≠ 0 → ∃ (R : Type) (_ : CommRing R) (xR : Sp R ⟶ Xo.X) (vR : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (ev : ℂ → (R →+* ℂ)) (V : Set ℂ), IsOpen V ∧ u₀ ∈ V ∧ (∀ t, DifferentiableOn ℂ (fun u => ev u t) V) ∧ ∀ u ∈ V, (y u).x = spMap (show R →+* CAt σ from ev u) ≫ xR ∧ ∀ τ i, (y u).u τ i = spMap (dualMap (show R →+* CAt σ from ev u)) ≫ vR τ i := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ A _ φ x fr ψ r y harc hm u₀ hu₀ hne
  haveI := Z.jQ_open
  obtain ⟨a, ha, hsub⟩ := exists_basicOpen_subset_of_pt (ψ u₀) (x ⁻¹' Set.range Z.jQ)
    ((IsOpenImmersion.isOpen_range Z.jQ).preimage x.continuous) (fun s => by
      have h := (hm u₀ hu₀ hne).1
      refine ⟨GlobalTheory.AllWt.ptF (y u₀) s, ?_⟩
      exact (congrArg (fun g => g s) h :))
  have hopen : IsOpen {u | u ∈ Metric.ball (0 : ℂ) r ∧ ψ u a ≠ 0} :=
    ((harc.1.2 a).continuousOn).isOpen_inter_preimage Metric.isOpen_ball (isOpen_ne (x := (0 : ℂ)))
  let V : Set ℂ := {u | u ∈ Metric.ball (0 : ℂ) r ∧ ψ u a ≠ 0} ∩ {u | u ≠ 0}
  obtain ⟨ev, hev, hd⟩ := exists_hol_away ψ V (fun b => (harc.1.2 b).mono fun u hu => hu.1.1) a
    (fun u hu => hu.1.2) u₀ ⟨⟨hu₀, ha⟩, hne⟩
  let R := Localization.Away a
  let ι : A →+* R := algebraMap A R
  have hr : Set.range (spMap ι ≫ x) ⊆ Set.range Z.jQ := by
    rintro _ ⟨s, rfl⟩
    exact hsub ⟨s, rfl⟩
  let x' : Sp R ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (spMap ι ≫ x) hr
  have hx' : x' ≫ Z.jQ = spMap ι ≫ x := IsOpenImmersion.lift_fac _ _ _
  have P : IsPullback Z.m.φ Z.oF.t.G.hom Z.t.G.hom (Z.jQ ≫ genι Z) := Z.m.cart.1
  have hw : ∀ τ i, (spMap (dualMap ι) ≫ fr.v τ i) ≫ Z.t.G.hom =
      (spMap (algebraMap R (DualNumber R)) ≫ x') ≫ Z.jQ ≫ genι Z := fun τ i => by
    rw [Category.assoc, (fr.tan τ i).1, ← Category.assoc, spMap_dualMap_sq, Category.assoc, Category.assoc,
      ← Category.assoc x', hx', Category.assoc]
  refine ⟨R, inferInstance, x' ≫ pullback.fst _ _, fun τ i => P.lift _ _ (hw τ i) ≫ Z.m0.toSABMap.φ, ev, V,
    hopen.inter isOpen_ne, ⟨⟨hu₀, ha⟩, hne⟩, hd, fun u hu => ?_⟩
  obtain ⟨h1, h2⟩ := hm u hu.1.1 hu.2
  let e : R →+* CAt σ := ev u
  have he : e.comp ι = (show A →+* CAt σ from ψ u) := hev u hu
  have hp : GlobalTheory.AllWt.ptF (y u) = spMap e ≫ x' := by
    rw [← cancel_mono Z.jQ, h1, Category.assoc, hx', ← Category.assoc, spMap_comp_comp, he]
  refine ⟨?_, fun τ i => ?_⟩
  · show _ = spMap e ≫ x' ≫ _
    rw [← Category.assoc, ← hp]
    exact (pullback.lift_fst _ _ _).symm
  · obtain ⟨w, hw1, hw2, hw3⟩ := h2 τ i
    show _ = spMap (dualMap e) ≫ P.lift _ _ (hw τ i) ≫ _
    rw [← hw2, ← Category.assoc]
    congr 1
    apply P.hom_ext
    · rw [hw3, Category.assoc, P.lift_fst, ← Category.assoc, spMap_comp_comp, dualMap_comp_comp, he]
    · rw [hw1, Category.assoc, P.lift_snd, ← Category.assoc, spMap_dualMap_sq, Category.assoc, hp]

end GlobalTheory.ShFam.BdArc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArcOffBoundaryDescendsToModuliLocalizationStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arc_off_boundary_descends_to_moduli_localization : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (A : Type) [CommRing A] (φ : c.F →+* A) (x : Sp A ⟶ gen Z) (fr : EigFrame Z φ (x ≫ genι Z)) (ψ : ℂ → (A →+* ℂ)) (r : ℝ) (y : ℂ → FrPt Xo c (CAt σ)), IsArc Z σ φ x ψ r → (∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) → ∀ u₀ ∈ Metric.ball (0 : ℂ) r, u₀ ≠ 0 → ∃ (R : Type) (_ : CommRing R) (xR : Sp R ⟶ Xo.X) (vR : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Xo.univ.t.G.left)) (ev : ℂ → (R →+* ℂ)) (V : Set ℂ), IsOpen V ∧ u₀ ∈ V ∧ (∀ t, DifferentiableOn ℂ (fun u => ev u t) V) ∧ ∀ u ∈ V, (y u).x = spMap (show R →+* CAt σ from ev u) ≫ xR ∧ ∀ τ i, (y u).u τ i = spMap (dualMap (show R →+* CAt σ from ev u)) ≫ vR τ i := by
  first | exact @GlobalTheory.ShFam.BdArc.arc_descends_to_moduli | exact GlobalTheory.ShFam.BdArc.arc_descends_to_moduli | (intros; apply GlobalTheory.ShFam.BdArc.arc_descends_to_moduli <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicFlowMajorantCauchySchwarz
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicFlowMajorantCauchySchwarz
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
open scoped ComplexConjugate

namespace GlobalTheory.CuspFrom.FlowMaj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma majForm_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    X.Hf x τ w u = conj (X.Hf x τ u w) := by
  rw [X.Hf_eq_jp, X.Hf_eq_jp, hermC_conj τ.1 X.Gm_herm, X.hermC_jp_left hx]

lemma majForm_sub_smul (x : Frame X.Ψ r) (τ : X.Ψ) (a : ℂ) (v e w : Fin r → ℂ) :
    X.Hf x τ (v - a • e) w = X.Hf x τ v w - a * X.Hf x τ e w := by
  simp only [X.Hf_eq_jp, X.jp_sub, X.jp_smul, hermC_sub_left, hermC_smul_left]

lemma maj_zero {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  have h := X.Hf_self hx τ 0
  rw [X.Hf_eq_jp, hermC_zero_right] at h
  exact_mod_cast h.symm

lemma maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) : 0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero X hx]
  · exact (X.maj_pos hx τ hv).le

lemma maj_split {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (a : ℂ) (e u : Fin r → ℂ)
    (h : X.Hf x τ u e = 0) : X.maj x τ (u + a • e) = X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e := by
  have h' : X.Hf x τ e u = 0 := by rw [majForm_conj X hx, h, map_zero]
  have h1 := X.Hf_self hx τ (u + a • e)
  have h2 := X.Hf_self hx τ u
  have h3 := X.Hf_self hx τ e
  simp only [X.Hf_eq_jp] at h h' h1 h2 h3
  simp only [X.jp_add, X.jp_smul, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right,
    h, h', h2, h3] at h1
  have h4 : a * conj a = ((‖a‖ : ℝ) : ℂ) ^ 2 := Complex.mul_conj' a
  have h5 : ((X.maj x τ (u + a • e) : ℝ) : ℂ) = ((X.maj x τ u + ‖a‖ ^ 2 * X.maj x τ e : ℝ) : ℂ) := by
    rw [← h1]
    push_cast
    linear_combination (X.maj x τ e : ℂ) * h4
  exact_mod_cast h5

lemma majForm_perp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) {e : Fin r → ℂ} (he : e ≠ 0) :
    X.Hf x τ (v - (X.Hf x τ v e / X.Hf x τ e e) • e) e = 0 := by
  have h0 : X.Hf x τ e e ≠ 0 := by
    rw [X.Hf_self hx]
    exact_mod_cast (X.maj_pos hx τ he).ne'
  rw [majForm_sub_smul, div_mul_cancel₀ _ h0, sub_self]

lemma majForm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  by_cases hw : w = 0
  · rw [hw, maj_zero X hx, X.Hf_eq_jp, hermC_zero_right]
    simp
  have hp := X.maj_pos hx τ hw
  have h1 := maj_split X hx τ (X.Hf x τ v w / X.Hf x τ w w) w _ (majForm_perp X hx τ v hw)
  rw [sub_add_cancel] at h1
  have h2 := maj_nonneg X hx τ (v - (X.Hf x τ v w / X.Hf x τ w w) • w)
  have h3 : ‖X.Hf x τ v w / X.Hf x τ w w‖ ^ 2 * X.maj x τ w * X.maj x τ w = ‖X.Hf x τ v w‖ ^ 2 := by
    rw [norm_div, X.Hf_self hx τ w, Complex.norm_real, Real.norm_of_nonneg hp.le]
    field_simp
  rw [← h3]
  exact mul_le_mul_of_nonneg_right (by linarith) hp.le

lemma maj_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.maj x τ (X.jp x τ v) = X.maj x τ v := by
  have h1 := X.Hf_self hx τ (X.jp x τ v)
  have h2 := X.Hf_self hx τ v
  rw [X.Hf_eq_jp, X.hermC_jp_jp hx, ← X.Hf_eq_jp, h2] at h1
  exact_mod_cast h1.symm

lemma herm_cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v w : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w := by
  have h := majForm_cs X hx τ (X.jp x τ v) w
  rwa [X.Hf_eq_jp, X.jp_jp hx, maj_jp X hx] at h

lemma maj_flow {ξ : Fin r → E} (hξ : X.IsIso ξ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ)
    (hxs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) (hv : hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0) :
    X.maj (X.flow ξ s x) τ v = X.maj x τ v +
      ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
        (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ)) := by
  have hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := by
    rw [← emb_herm, hξ.2.1, map_zero]
  have he : Data.emb τ.1 ξ ≠ 0 := emb_ne_zero τ.1 hξ.2.2
  have hH := majForm_perp X hx τ v he
  set a := X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) with ha
  set u := v - a • Data.emb τ.1 ξ with hu
  have hu0 : hermC τ.1 X.Gm u (Data.emb τ.1 ξ) = 0 := by
    rw [hu, hermC_sub_left, hermC_smul_left, hv, hiso, mul_zero, sub_zero]
  have hp : hermC τ.1 X.Gm (X.ppos x τ u) (Data.emb τ.1 ξ) = 0 := by
    have h := hH
    rw [X.Hf_eq_two_ppos, hu0, sub_zero] at h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  have hpp := Data.ppos_flow X ξ τ hx s hxs u hu0 hp
  have hHy : ∀ w, X.Hf (X.flow ξ s x) τ u w = X.Hf x τ u w := fun w => by
    rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hpp]
  have hm : X.maj (X.flow ξ s x) τ u = X.maj x τ u := by
    have h := hHy u
    rw [X.Hf_self hxs, X.Hf_self hx] at h
    exact_mod_cast h
  have h1 := maj_split X hx τ a _ u hH
  have h2 := maj_split X hxs τ a _ u ((hHy _).trans hH)
  rw [hu, sub_add_cancel, ← hu] at h1 h2
  rw [h1, h2, hm]
  ring

end GlobalTheory.CuspFrom.FlowMaj

namespace GlobalTheory.CuspFrom

theorem flowMajSt_holds : FlowMajSt := fun _ _ _ _ _ X =>
  ⟨fun _ hξ _ hx s hxs τ v hv => FlowMaj.maj_flow X hξ hx s hxs τ v hv,
    fun _ hx τ v w => ⟨FlowMaj.herm_cs X hx τ v w, FlowMaj.majForm_cs X hx τ v w⟩⟩

end GlobalTheory.CuspFrom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicFlowMajorantCauchySchwarzStatement
open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CuspFrom
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlow_majorant_cauchySchwarz : FlowMajSt := by
  first | exact @GlobalTheory.CuspFrom.flowMajSt_holds | exact GlobalTheory.CuspFrom.flowMajSt_holds | (intros; apply GlobalTheory.CuspFrom.flowMajSt_holds <;> assumption)
end
end
