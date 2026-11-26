module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentRadicalMemAdelic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionPhiPlusInductionFromBlockUni
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionPhiPlusInductionFromBlockUni
noncomputable section

namespace GlobalTheory.GLm.Stages

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem sum_fibres {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (f : G →* G')
    (hf : Function.Surjective f) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ h : G' → ℂ, ∑ p, h (f p) = (N : ℂ) * ∑ y, h y := by
  refine ⟨(Finset.univ.filter fun p => f p = 1).card, ?_, fun h => ?_⟩
  · exact Finset.card_ne_zero.2 ⟨1, by simp⟩
  · rw [Finset.sum_comp h f, Finset.image_univ_of_surjective hf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [nsmul_eq_mul]
    congr 2
    exact MonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf 1)

theorem sum_fibres' {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (P : Subgroup G) (π : G → G')
    (hmul : ∀ a ∈ P, ∀ b ∈ P, π (a * b) = π a * π b) (hs : ∀ y, ∃ p ∈ P, π p = y) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ h : G' → ℂ, (∑ p, if p ∈ P then h (π p) else 0) = (N : ℂ) * ∑ y, h y := by
  let f : P →* G' := MonoidHom.mk' (fun p => π p) fun a b => hmul a a.2 b b.2
  obtain ⟨N, hN, h⟩ := sum_fibres f fun y => by
    obtain ⟨p, hp, e⟩ := hs y
    exact ⟨⟨p, hp⟩, e⟩
  refine ⟨N, hN, fun k => ?_⟩
  rw [← h k, ← Finset.sum_filter]
  exact Finset.sum_subtype _ (by simp) fun p => k (π p)

theorem stages {G G' : Type} [Group G] [Group G'] [Fintype G] [Fintype G'] (P : Subgroup G) (P' : Subgroup G')
    (π : G → G') (hmul : ∀ a ∈ P, ∀ b ∈ P, π (a * b) = π a * π b) (N : ℕ)
    (fib : ∀ h : G' → ℂ, (∑ p, if p ∈ P then h (π p) else 0) = (N : ℂ) * ∑ y, h y)
    (θ : G → ℂ) (hθ : ∀ q ∈ P, π q ∈ P' → ∀ z ∈ P, π z ∈ P' → θ (q⁻¹ * z * q) = θ z)
    (F : G → ℂ) (F' : G' → ℂ) (hF : ∀ w ∈ P, F w = if π w ∈ P' then F' (π w) * θ w else 0)
    (x : G) (hx : x ∈ P) :
    ((Finset.univ.filter fun p => p ∈ P ∧ π p ∈ P').card : ℂ) * (∑ y, if y ∈ P then F (y⁻¹ * x * y) else 0) =
      N * ∑ y, if y ∈ P ∧ π (y⁻¹ * x * y) ∈ P' then
        (∑ y', if y' ∈ P' then F' (y'⁻¹ * π (y⁻¹ * x * y) * y') else 0) * θ (y⁻¹ * x * y) else 0 := by
  have h1 : π 1 = 1 := by
    have := hmul 1 P.one_mem 1 P.one_mem
    simpa using this
  have hinv : ∀ q ∈ P, π q⁻¹ = (π q)⁻¹ := fun q hq => by
    rw [eq_inv_iff_mul_eq_one, ← hmul _ (P.inv_mem hq) _ hq, inv_mul_cancel, h1]
  have hconj : ∀ q ∈ P, ∀ z ∈ P, π (q⁻¹ * z * q) = (π q)⁻¹ * π z * π q := fun q hq z hz => by
    rw [hmul _ (P.mul_mem (P.inv_mem hq) hz) _ hq, hmul _ (P.inv_mem hq) _ hz, hinv q hq]
  have shift : ∀ q ∈ P, (∑ y, if y ∈ P then F (y⁻¹ * x * y) else 0) =
      ∑ y, if y ∈ P then F (q⁻¹ * (y⁻¹ * x * y) * q) else 0 := fun q hq => by
    rw [← Equiv.sum_comp (Equiv.mulRight q)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Equiv.coe_mulRight, P.mul_mem_cancel_right hq, mul_inv_rev, mul_assoc]
  rw [← nsmul_eq_mul, ← Finset.sum_const,
    Finset.sum_congr rfl fun q hq => shift q (Finset.mem_filter.1 hq).2.1, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ P
  · have hz : y⁻¹ * x * y ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hy) hx) hy
    generalize y⁻¹ * x * y = z at hz
    simp only [hy, if_true, true_and]
    have hw : ∀ q ∈ P, q⁻¹ * z * q ∈ P := fun q hq => P.mul_mem (P.mul_mem (P.inv_mem hq) hz) hq
    by_cases hz' : π z ∈ P'
    · rw [if_pos hz', ← mul_assoc, ← fib, Finset.sum_filter, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      by_cases hq : q ∈ P
      · by_cases hq' : π q ∈ P'
        · simp only [hq, hq', if_true, and_self]
          rw [hF _ (hw q hq), hconj q hq z hz, if_pos (P'.mul_mem (P'.mul_mem (P'.inv_mem hq') hz') hq'),
            hθ q hq hq' z hz hz']
        · simp [hq, hq']
      · simp [hq]
    · rw [if_neg hz', mul_zero]
      refine Finset.sum_eq_zero fun q hq => ?_
      obtain ⟨hq, hq'⟩ := (Finset.mem_filter.1 hq).2
      rw [hF _ (hw q hq), hconj q hq z hz, if_neg]
      rw [P'.mul_mem_cancel_right hq', P'.mul_mem_cancel_left (P'.inv_mem hq')]
      exact hz'
  · simp [hy]

variable {g : ℕ} [Fact g.Prime]

theorem mir_mul_apply {n : ℕ} {A : Mt g n} (hA : InMir A) (B : Mt g n) (i j : Fin n) (hi : (i : ℕ) + 1 = n) :
    (A * B) i j = B i j := by
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => by rw [hA i k hi], ← Matrix.mul_apply, one_mul]

def mir (g n : ℕ) [Fact g.Prime] : Subgroup (Gn g n) where
  carrier := {p | InMir (p : Mt g n)}
  one_mem' := inMir_one n
  mul_mem' := fun {a b} ha hb i j hi => by
    rw [Units.val_mul, mir_mul_apply ha _ i j hi]; exact hb i j hi
  inv_mem' := fun {a} ha i j hi => by
    rw [← mir_mul_apply ha ((a⁻¹ : Gn g n) : Mt g n) i j hi, Units.mul_inv]

theorem mem_mir {n : ℕ} (p : Gn g n) : p ∈ mir g n ↔ InMir (p : Mt g n) := Iff.rfl

theorem tl_apply {m : ℕ} (A : Mt g (m + 1)) (i j : Fin m) : tl m A i j = A i.castSucc j.castSucc := by
  have h1 : (i : ℕ) < m + 1 := by omega
  have h2 : (j : ℕ) < m + 1 := by omega
  simp only [tl, entN, h1, h2, and_self, dif_pos]
  rfl

theorem tl_mul {m : ℕ} (A : Mt g (m + 1)) {B : Mt g (m + 1)} (hB : InMir B) : tl m (A * B) = tl m A * tl m B := by
  ext i j
  rw [tl_apply, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_castSucc, hB (Fin.last m) _ rfl,
    Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  simp [tl_apply]

theorem tl_one {m : ℕ} : tl m (1 : Mt g (m + 1)) = 1 := by
  ext i j
  simp [tl_apply, Matrix.one_apply]

theorem coe_toG {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG; rw [dif_pos h]; rfl

theorem coe_toG_tl {m : ℕ} {w : Gn g (m + 1)} (hw : w ∈ mir g (m + 1)) :
    ((toG (tl m (w : Mt g (m + 1))) : Gn g m) : Mt g m) = tl m (w : Mt g (m + 1)) := by
  refine coe_toG (IsUnit.of_mul_eq_one (tl m ((w⁻¹ : Gn g (m + 1)) : Mt g (m + 1))) ?_)
  rw [← tl_mul _ ((mir g (m + 1)).inv_mem hw), Units.mul_inv, tl_one]

theorem toG_tl_mul {m : ℕ} (a : Gn g (m + 1)) (ha : a ∈ mir g (m + 1)) (b : Gn g (m + 1))
    (hb : b ∈ mir g (m + 1)) :
    toG (tl m ((a * b : Gn g (m + 1)) : Mt g (m + 1))) =
      toG (tl m (a : Mt g (m + 1))) * toG (tl m (b : Mt g (m + 1))) := by
  apply Units.ext
  rw [coe_toG_tl ((mir g (m + 1)).mul_mem ha hb), Units.val_mul (toG _), coe_toG_tl ha, coe_toG_tl hb, Units.val_mul,
    tl_mul _ hb]

def ext1 {m : ℕ} (M : Mt g m) : Mt g (m + 1) := fun i j =>
  Fin.lastCases (Fin.lastCases 1 (fun _ => 0) j) (fun i' => Fin.lastCases 0 (fun j' => M i' j') j) i

theorem extendMatrixByIdentityAlongIndices_mul {m : ℕ} (M N : Mt g m) : ext1 M * ext1 N = ext1 (M * N) := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> simp [ext1, Matrix.mul_apply]

theorem blockDiagonalExtendByOnePrimeField_one {m : ℕ} : ext1 (1 : Mt g m) = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [ext1, Matrix.one_apply, (Fin.castSucc_lt_last _).ne, (Fin.castSucc_lt_last _).ne']

theorem toG_tl_surj {m : ℕ} (y : Gn g m) : ∃ p ∈ mir g (m + 1), toG (tl m (p : Mt g (m + 1))) = y := by
  let p : Gn g (m + 1) := ⟨ext1 (y : Mt g m), ext1 ((y⁻¹ : Gn g m) : Mt g m),
    by rw [extendMatrixByIdentityAlongIndices_mul, Units.mul_inv, blockDiagonalExtendByOnePrimeField_one], by rw [extendMatrixByIdentityAlongIndices_mul, Units.inv_mul, blockDiagonalExtendByOnePrimeField_one]⟩
  have hp : p ∈ mir g (m + 1) := by
    intro i j hi
    obtain rfl : i = Fin.last m := Fin.ext (by simpa using hi)
    induction j using Fin.lastCases <;> simp [p, ext1, Matrix.one_apply, (Fin.castSucc_lt_last _).ne']
  refine ⟨p, hp, Units.ext ?_⟩
  rw [coe_toG_tl hp]
  ext i j
  simp [tl_apply, p, ext1]

theorem corner_mul {m : ℕ} (hm : 0 < m) {A B : Mt g (m + 1)} (hA : InMir (tl m A)) (hB : InMir B) :
    entN (A * B) (m - 1) m = entN A (m - 1) m + entN B (m - 1) m := by
  have e : ∀ C : Mt g (m + 1), entN C (m - 1) m = C (Fin.castSucc ⟨m - 1, by omega⟩) (Fin.last m) := fun C => by
    have h1 : m - 1 < m + 1 := by omega
    simp only [entN, h1, Nat.lt_succ_self, and_self, dif_pos]
    rfl
  rw [e, e, e, Matrix.mul_apply, Fin.sum_univ_castSucc, hB (Fin.last m) _ rfl, Matrix.one_apply_eq, mul_one,
    add_comm]
  congr 1
  rw [Finset.sum_congr rfl fun k _ => by rw [← tl_apply A _ k, hA _ k (by simp; omega)]]
  simp [Matrix.one_apply]

theorem entN_tl {m n : ℕ} (A : Mt g n) {a b : ℕ} (ha : a < m) (hb : b < m) : entN (tl m A) a b = entN A a b := by
  simp [entN, ha, hb, tl]

theorem tl_tl {i m n : ℕ} (h : i ≤ m) (A : Mt g n) : tl i (tl m A) = tl i A := by
  ext a b
  exact entN_tl A (by omega) (by omega)

theorem supFrom_succ {i m : ℕ} (h : i < m) (A : Mt g (m + 1)) :
    supFrom i A = supFrom i (tl m A) + entN A (m - 1) m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [supFrom, Nat.add_sub_cancel]
  rw [Finset.sum_Ico_succ_top (by omega)]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have := (Finset.mem_Ico.1 hj).2
  rw [entN_tl A (by omega) (by omega)]

theorem inR_iff {i n : ℕ} (A : Mt g n) :
    InR i A ↔ ∀ a b : Fin n, i ≤ (a : ℕ) → (b : ℕ) ≤ a → A a b = (1 : Mt g n) a b := by
  constructor
  · intro hM a b ha hb
    by_cases hb' : (b : ℕ) < i
    · rw [hM.1 a b hb' ha, Matrix.one_apply_ne]
      intro e; subst e; omega
    · have h2 := hM.2 ⟨a - i, by omega⟩ ⟨b - i, by omega⟩
      have e : br i (n - i) A ⟨a - i, by omega⟩ ⟨b - i, by omega⟩ = A a b := by
        have h1 : i + (a - i) = a := by omega
        have h3 : i + (b - i) = b := by omega
        simp [br, entN, h1, h3]
      rw [e] at h2
      by_cases hab : a = b
      · subst hab; rw [h2.2 rfl]; simp
      · rw [Matrix.one_apply_ne hab]
        apply h2.1
        have : (a : ℕ) ≠ b := fun e => hab (Fin.ext e)
        simp only [Fin.lt_def]; omega
  · intro h
    refine ⟨fun a b hb ha => ?_, fun a b => ?_⟩
    · rw [h a b ha (by omega), Matrix.one_apply_ne]
      intro e; subst e; omega
    · have h1 : i + a < n := by omega
      have h2 : i + b < n := by omega
      have e : br i (n - i) A a b = A ⟨i + a, h1⟩ ⟨i + b, h2⟩ := by simp [br, entN, h1, h2]
      rw [e]
      constructor
      · intro hab
        rw [Fin.lt_def] at hab
        rw [h _ _ (by simp) (by simp; omega), Matrix.one_apply_ne]
        simp; omega
      · rintro rfl
        rw [h _ _ (by simp) (by simp), Matrix.one_apply_eq]

theorem inR_succ {i m : ℕ} {A : Mt g (m + 1)} (hA : InMir A) : InR i A ↔ InR i (tl m A) := by
  rw [inR_iff, inR_iff]
  constructor
  · intro h a b ha hb
    rw [tl_apply, h _ _ (by simpa) (by simpa)]
    simp [Matrix.one_apply]
  · intro h a b ha hb
    induction a using Fin.lastCases with
    | last => exact hA _ _ rfl
    | cast a =>
      induction b using Fin.lastCases with
      | last => simp at hb; omega
      | cast b =>
        rw [← tl_apply A a b, h _ _ (by simpa using ha) (by simpa using hb)]
        simp [Matrix.one_apply]

theorem inMir_of_inR {i n : ℕ} (h : i < n) {M : Mt g n} (hM : InR i M) : InMir M := fun a b ha =>
  (inR_iff M).1 hM a b (by omega) (by omega)

theorem corner_conj {m : ℕ} (hm : 0 < m) (q : Gn g (m + 1)) (hq : q ∈ mir g (m + 1))
    (hq' : toG (tl m (q : Mt g (m + 1))) ∈ mir g m) (z : Gn g (m + 1)) (hz : z ∈ mir g (m + 1))
    (hz' : toG (tl m (z : Mt g (m + 1))) ∈ mir g m) :
    entN ((q⁻¹ * z * q : Gn g (m + 1)) : Mt g (m + 1)) (m - 1) m = entN (z : Mt g (m + 1)) (m - 1) m := by
  have hw : q⁻¹ * z * q ∈ mir g (m + 1) := (mir g _).mul_mem ((mir g _).mul_mem ((mir g _).inv_mem hq) hz) hq
  rw [mem_mir, coe_toG_tl hq] at hq'
  rw [mem_mir, coe_toG_tl hz] at hz'
  have h1 := corner_mul hm hq' hw
  have h2 := corner_mul hm hz' hq
  have e : q * (q⁻¹ * z * q) = z * q := by group
  rw [← Units.val_mul, e, Units.val_mul, h2, add_comm] at h1
  exact (add_left_cancel h1).symm

end GlobalTheory.GLm.Stages

namespace GlobalTheory.GLm

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm.Stages
open scoped Classical

theorem indV_indR (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m : ℕ) (ρ : Gn g i → ℂ) (him : i < m)
    (x : Gn g (m + 1)) (hx : InMir (x : Mt g (m + 1))) :
    indV ψ m (indR ψ i m ρ) x = indR ψ i (m + 1) ρ x := by
  obtain ⟨N, hN, fib⟩ := sum_fibres' (mir g (m + 1)) (fun p => toG (tl m (p : Mt g (m + 1)))) toG_tl_mul
    toG_tl_surj
  have key := stages (mir g (m + 1)) (mir g m) (fun p => toG (tl m (p : Mt g (m + 1)))) toG_tl_mul N fib
    (fun w => ψ (entN (w : Mt g (m + 1)) (m - 1) m))
    (fun q hq hq' z hz hz' => congrArg ψ (corner_conj (by omega) q hq hq' z hz hz'))
    (fun w => if InR i (w : Mt g (m + 1)) then ρ (toG (tl i (w : Mt g (m + 1)))) * ψ (supFrom i (w : Mt g (m + 1)))
      else 0)
    (fun w => if InR i (w : Mt g m) then ρ (toG (tl i (w : Mt g m))) * ψ (supFrom i (w : Mt g m)) else 0)
    (fun w hw => by
      simp only [mem_mir (toG _), coe_toG_tl hw, ← inR_succ hw, tl_tl him.le]
      by_cases h : InR i (w : Mt g (m + 1))
      · rw [if_pos h, if_pos h, if_pos (inMir_of_inR him ((inR_succ hw).1 h)), supFrom_succ him,
          AddChar.map_add_eq_mul, mul_assoc]
      · simp [h]) x hx
  have hR := fib fun y => if InR i (y : Mt g m) then 1 else 0
  have hR' : ((Finset.univ.filter fun p : Gn g (m + 1) => InR i (p : Mt g (m + 1))).card : ℂ) =
      N * ((Finset.univ.filter fun p : Gn g m => InR i (p : Mt g m)).card : ℂ) := by
    rw [Finset.card_filter, Finset.card_filter]
    push_cast
    rw [← hR]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hp : p ∈ mir g (m + 1)
    · simp only [hp, if_true, coe_toG_tl hp, ← inR_succ hp]
    · rw [if_neg hp, if_neg fun h => hp (inMir_of_inR (by omega) h)]
  have hQ : (Finset.univ.filter fun p : Gn g (m + 1) =>
      p ∈ mir g (m + 1) ∧ toG (tl m (p : Mt g (m + 1))) ∈ mir g m) = Finset.univ.filter fun p : Gn g (m + 1) =>
      InMir (p : Mt g (m + 1)) ∧ InMir (tl m (p : Mt g (m + 1))) := by
    refine Finset.filter_congr fun p _ => and_congr_right fun hp => ?_
    rw [mem_mir, coe_toG_tl hp]
  have hQ0 : ((Finset.univ.filter fun p : Gn g (m + 1) =>
      InMir (p : Mt g (m + 1)) ∧ InMir (tl m (p : Mt g (m + 1)))).card : ℂ) ≠ 0 := by
    refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, inMir_one _, ?_⟩⟩)
    rw [Units.val_one, tl_one]; exact inMir_one _
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  rw [hQ] at key
  have e1 : indR ψ i (m + 1) ρ x =
      ((Finset.univ.filter fun p : Gn g (m + 1) => InR i (p : Mt g (m + 1))).card : ℂ)⁻¹ *
      ∑ y : Gn g (m + 1), if y ∈ mir g (m + 1) then
        (if InR i ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)) then
          ρ (toG (tl i ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1)))) *
            ψ (supFrom i ((y⁻¹ * x * y : Gn g (m + 1)) : Mt g (m + 1))) else 0) else 0 := by
    simp only [indR, ite_and, mem_mir]
  rw [e1, hR', (eq_inv_mul_iff_mul_eq₀ hQ0).2 key, mul_inv, mul_left_comm, mul_mul_mul_comm,
    inv_mul_cancel₀ hN', one_mul, Finset.mul_sum]
  unfold indV
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ mir g (m + 1)
  · have hz : y⁻¹ * x * y ∈ mir g (m + 1) := (mir g _).mul_mem ((mir g _).mul_mem ((mir g _).inv_mem hy) hx) hy
    generalize y⁻¹ * x * y = z at hz
    simp only [mem_mir (toG _), coe_toG_tl hz, hy, (mem_mir _).1 hy, (mem_mir _).1 hz, true_and]
    split_ifs
    · simp only [indR, ite_and, mem_mir, mul_assoc]
    · simp
  · have hy' : ¬ InMir (y : Mt g (m + 1)) := hy
    simp [hy, hy']

end GlobalTheory.GLm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionPhiPlusInductionFromBlockUniStatement
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicInductionPhiPlus_inductionFromBlockUni : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m : ℕ) (ρ : Gn g i → ℂ), i < m → ∀ x : Gn g (m + 1), InMir (x : Mt g (m + 1)) → indV ψ m (indR ψ i m ρ) x = indR ψ i (m + 1) ρ x := by
  first | exact @GlobalTheory.GLm.indV_indR | exact GlobalTheory.GLm.indV_indR | (intros; apply GlobalTheory.GLm.indV_indR <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicFunctionEqInducedDerivativeAddTail
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicFunctionEqInducedDerivativeAddTail
noncomputable section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm Matrix
open scoped Classical

namespace GlobalTheory.GLm.MirStep

variable {g : ℕ} [Fact g.Prime] {m : ℕ}

def Em (h : Mt g m) (v : Fin m → ZMod g) : Mt g (m + 1) := Matrix.of fun i j =>
  Fin.lastCases (motive := fun _ => ZMod g) (Fin.lastCases (motive := fun _ => ZMod g) 1 (fun _ => 0) j)
    (fun i' => Fin.lastCases (motive := fun _ => ZMod g) (v i') (h i') j) i

@[simp] theorem Em_cc (h : Mt g m) (v) (i j : Fin m) : Em h v i.castSucc j.castSucc = h i j := by simp [Em]
@[simp] theorem Em_cl (h : Mt g m) (v) (i : Fin m) : Em h v i.castSucc (Fin.last m) = v i := by simp [Em]
@[simp] theorem Em_lc (h : Mt g m) (v) (j : Fin m) : Em h v (Fin.last m) j.castSucc = 0 := by simp [Em]
@[simp] theorem Em_ll (h : Mt g m) (v) : Em h v (Fin.last m) (Fin.last m) = 1 := by simp [Em]

theorem Em_mul (h k : Mt g m) (v w) : Em h v * Em k w = Em (h * k) (h *ᵥ w + v) := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct]

theorem Em_one : Em (1 : Mt g m) 0 = 1 := by
  ext i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm]

theorem tl_apply (M : Mt g (m + 1)) (i j : Fin m) : tl m M i j = M i.castSucc j.castSucc := by
  have hi := i.2
  have hj := j.2
  simp only [tl, entN]
  rw [dite_eq_left ⟨by omega, by omega⟩]
  rfl

@[simp] theorem tl_Em (h : Mt g m) (v) : tl m (Em h v) = h := by
  ext i j
  simp [tl_apply]

theorem inMir_iff_row {n : ℕ} (l : Fin n) (hl : (l : ℕ) + 1 = n) (M : Mt g n) :
    InMir M ↔ Pi.single l 1 ᵥ* M = Pi.single l 1 := by
  rw [Matrix.single_one_vecMul]
  constructor
  · intro h
    ext j
    rw [Matrix.row_apply, h l j hl, Matrix.one_apply, Pi.single_apply]
    simp [eq_comm]
  · intro h i j hi
    have : i = l := Fin.ext (by omega)
    subst this
    have := congrFun h j
    rw [Matrix.row_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]
    simp [eq_comm]

theorem inMir_Em (h : Mt g m) (v) : InMir (Em h v) := by
  intro i j hi
  have : i = Fin.last m := Fin.ext (by simp; omega)
  subst this
  induction j using Fin.lastCases <;> simp [Matrix.one_apply, (Fin.castSucc_ne_last _).symm]

theorem eq_Em {M : Mt g (m + 1)} (hM : InMir M) : M = Em (tl m M) fun i => M i.castSucc (Fin.last m) := by
  ext i j
  induction i using Fin.lastCases
  · rw [hM _ j (by simp), inMir_Em _ _ _ j (by simp)]
  · induction j using Fin.lastCases <;> simp [tl_apply]

def E (h : Gn g m) (v : Fin m → ZMod g) : Gn g (m + 1) where
  val := Em (h : Mt g m) v
  inv := Em ((h⁻¹ : Gn g m) : Mt g m) (-(((h⁻¹ : Gn g m) : Mt g m) *ᵥ v))
  val_inv := by
    rw [Em_mul, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Units.mul_inv]
    simp [Em_one]
  inv_val := by
    rw [Em_mul, Units.inv_mul]
    simp [Em_one]

@[simp] theorem E_coe (h : Gn g m) (v) : ((E h v : Gn g (m + 1)) : Mt g (m + 1)) = Em (h : Mt g m) v := rfl

theorem E_mul (h k : Gn g m) (v w) : E h v * E k w = E (h * k) ((h : Mt g m) *ᵥ w + v) := by
  ext1
  simp [Em_mul]

theorem E_inv (h : Gn g m) (v) : (E h v)⁻¹ = E h⁻¹ (-(((h⁻¹ : Gn g m) : Mt g m) *ᵥ v)) := by
  ext1
  rfl

theorem E_conj (h k : Gn g m) (v w) : (E k w)⁻¹ * E h v * E k w =
    E (k⁻¹ * h * k) (((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w)) := by
  rw [E_inv, E_mul, E_mul]
  congr 1
  rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_mulVec, Units.val_mul]
  abel

theorem exists_E {x : Gn g (m + 1)} (hx : InMir (x : Mt g (m + 1))) : ∃ h v, x = E h v := by
  have hx' : InMir ((x⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) := by
    rw [inMir_iff_row (Fin.last m) (by simp)] at hx ⊢
    conv_lhs => rw [← hx]
    rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  have h1 : tl m (x : Mt g (m + 1)) * tl m ((x⁻¹ : Gn g (m + 1)) : Mt g (m + 1)) = 1 := by
    have := x.mul_inv
    rw [eq_Em hx, eq_Em hx', Em_mul, ← Em_one] at this
    simpa using congrArg (tl m) this
  have hu : IsUnit (tl m (x : Mt g (m + 1))) := IsUnit.of_mul_eq_one _ h1
  refine ⟨hu.unit, fun i => (x : Mt g (m + 1)) i.castSucc (Fin.last m), ?_⟩
  ext1
  rw [E_coe, hu.unit_spec]
  exact eq_Em hx

theorem sum_mir (Φ : Gn g (m + 1) → ℂ) (hΦ : ∀ y : Gn g (m + 1), ¬ InMir (y : Mt g (m + 1)) → Φ y = 0) :
    ∑ y, Φ y = ∑ h : Gn g m, ∑ v, Φ (E h v) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Finset.sum_of_injOn (fun p : Gn g m × (Fin m → ZMod g) => E p.1 p.2) ?_ (fun _ _ => by simp) ?_
    (fun _ _ => rfl)
  · rintro ⟨h, v⟩ - ⟨k, w⟩ - hh
    have h0 : Em (h : Mt g m) v = Em (k : Mt g m) w := congrArg Units.val hh
    refine Prod.ext (Units.ext ?_) ?_
    · simpa using congrArg (tl m) h0
    · ext i
      simpa using congrFun (congrFun h0 i.castSucc) (Fin.last m)
  · intro y _ hy
    apply hΦ
    intro hy'
    obtain ⟨h, v, rfl⟩ := exists_E hy'
    exact hy ⟨(h, v), by simp, rfl⟩

theorem toG_coe {n : ℕ} (h : Gn g n) : toG (h : Mt g n) = h := by
  simp [toG]

theorem uni_iff {b : ℕ} (hb : b = 1) (M : Mt g b) : IsUniUp M ↔ M = 1 := by
  subst hb
  constructor
  · intro h
    ext i j
    rw [(h i j).2 (Subsingleton.elim _ _), Matrix.one_apply, if_pos (Subsingleton.elim _ _)]
  · rintro rfl a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp

theorem wh_one (ψ : AddChar (ZMod g) ℂ) {b : ℕ} (hb : b = 1) (χ : Gn g b → ℂ) : wh ψ χ = χ 1 := by
  have hf : (Finset.univ.filter fun u : Gn g b => IsUniUp (u : Mt g b)) = {1} := by
    ext u
    simp [uni_iff hb]
  subst hb
  simp only [wh, tr, eU, eDat]
  have hf' : ∀ inst : DecidablePred fun u : Gn g 1 => IsUniUp (u : Mt g 1), @Finset.filter _ (fun u : Gn g 1 => IsUniUp (u : Mt g 1)) inst Finset.univ = {1} := by
    intro inst
    convert hf
  rw [hf']
  simp [MonoidAlgebra.coeff_single, Finsupp.single_apply]

theorem inR_iff (M : Mt g (m + 1)) : InR m M ↔ InMir M := by
  rw [InR, uni_iff (by omega)]
  have hb : br m (m + 1 - m) M = 1 ↔ M (Fin.last m) (Fin.last m) = 1 := by
    have : ∀ i j : Fin (m + 1 - m), br m (m + 1 - m) M i j = M (Fin.last m) (Fin.last m) := by
      intro i j
      have hi := i.2
      have hj := j.2
      simp only [br, entN]
      rw [dite_eq_left ⟨by omega, by omega⟩]
      congr 1 <;> exact Fin.ext (by simp; omega)
    constructor
    · intro h
      rw [← this ⟨0, by omega⟩ ⟨0, by omega⟩, h, Matrix.one_apply_eq]
    · intro h
      ext i j
      have hi := i.2
      have hj := j.2
      rw [this, h, Matrix.one_apply, if_pos (Fin.ext (by omega))]
  rw [hb]
  constructor
  · rintro ⟨h1, h2⟩ i j hi
    have : i = Fin.last m := Fin.ext (by simp; omega)
    subst this
    induction j using Fin.lastCases with
    | last => simpa using h2
    | cast j => rw [h1 _ _ (by simp) (by simp), Matrix.one_apply_ne (Fin.castSucc_ne_last _).symm]
  · intro h
    refine ⟨fun i j hj hi => ?_, by rw [h _ _ (by simp), Matrix.one_apply_eq]⟩
    have := i.2
    rw [h i j (by omega), Matrix.one_apply_ne (by intro e; subst e; omega)]

theorem exists_row (l : Fin m) (r : Fin m → ZMod g) (hr : r ≠ 0) :
    ∃ k : Gn g m, Pi.single l 1 ᵥ* (k : Mt g m) = r := by
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := by
    by_contra h
    push Not at h
    exact hr (funext h)
  have hd : (((1 : Mt g m).updateRow i r).submatrix (Equiv.swap i l) id).det ≠ 0 := by
    rw [Matrix.det_permute, ← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
    refine mul_ne_zero ?_ hi
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap i l)) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, ?_⟩
  rw [Matrix.single_one_vecMul]
  ext j
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.row_apply]

theorem exists_psi_ne {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) {u : Fin m → ZMod g} (hu : u ≠ 0) :
    ∃ r, ψ (u ⬝ᵥ r) ≠ 1 := by
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (funext h)
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.1 hψ
  refine ⟨Pi.single i (a / u i), ?_⟩
  rwa [dotProduct_single, mul_div_cancel₀ _ hi]

theorem q_ne_zero : ((g : ℂ) ^ m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : g.Prime).ne_zero)

theorem orth {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) (u : Fin m → ZMod g) :
    ∑ r, ψ (r ⬝ᵥ u) = if u = 0 then (g : ℂ) ^ m else 0 := by
  split_ifs with hu
  · subst hu
    simp [ZMod.card]
  · obtain ⟨r₀, h₀⟩ := exists_psi_ne hψ hu
    have h1 : ∑ r, ψ (r ⬝ᵥ u) = (∑ r, ψ (r ⬝ᵥ u)) * ψ (u ⬝ᵥ r₀) := by
      rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight r₀)]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [Equiv.coe_addRight]
      rw [add_dotProduct, ψ.map_add_eq_mul, dotProduct_comm r₀]
    have h2 : (∑ r, ψ (r ⬝ᵥ u)) * (1 - ψ (u ⬝ᵥ r₀)) = 0 := by linear_combination h1
    exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 h₀.symm)

def fc (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ) (h : Gn g m) (r : Fin m → ZMod g) : ℂ :=
  ((g : ℂ) ^ m)⁻¹ * ∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹

theorem inversion {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) (F : Gn g (m + 1) → ℂ) (h : Gn g m) (v) :
    ∑ r, fc ψ F h r * ψ (r ⬝ᵥ v) = F (E h v) := by
  have : ∀ r, fc ψ F h r * ψ (r ⬝ᵥ v) = ((g : ℂ) ^ m)⁻¹ * ∑ u, F (E h u) * ψ (r ⬝ᵥ (v - u)) := by
    intro r
    rw [fc, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [dotProduct_sub, AddChar.map_sub_eq_div]
    ring
  simp_rw [this]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum, orth hψ, sub_eq_zero]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have := q_ne_zero (g := g) (m := m)
  field_simp

theorem F_conj {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h k : Gn g m) (v w) :
    F (E (k⁻¹ * h * k) (((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w))) = F (E h v) := by
  rw [← E_conj]
  have := hF (E k w)⁻¹ (E h v) (by rw [E_inv]; exact inMir_Em _ _) (inMir_Em _ _)
  rwa [inv_inv] at this

theorem fc_conj (ψ : AddChar (ZMod g) ℂ) {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h k : Gn g m) (r) :
    fc ψ F (k⁻¹ * h * k) r = fc ψ F h (r ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) := by
  unfold fc
  congr 1
  symm
  refine Fintype.sum_bijective (fun v => ((k⁻¹ : Gn g m) : Mt g m) *ᵥ v) ?_ _ _ fun v => ?_
  · refine Finite.injective_iff_bijective.1 fun a b hab => ?_
    have := congrArg (fun v => (k : Mt g m) *ᵥ v) hab
    simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] using this
  · rw [← F_conj hF h k v 0, dotProduct_mulVec]
    simp

theorem fc_eq_zero {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1) {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F)
    (h : Gn g m) (r) (hr : r ᵥ* (h : Mt g m) ≠ r) : fc ψ F h r = 0 := by
  obtain ⟨w, hw⟩ := exists_psi_ne hψ (sub_ne_zero.2 hr)
  have h1 : ∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹ =
      (∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹) * (ψ ((r ᵥ* (h : Mt g m) - r) ⬝ᵥ w))⁻¹ := by
    rw [Finset.sum_mul, ← Equiv.sum_comp (Equiv.addRight ((h : Mt g m) *ᵥ w - w))]
    refine Finset.sum_congr rfl fun v _ => ?_
    have := F_conj hF h 1 v w
    simp only [inv_one, one_mul, mul_one, Units.val_one, Matrix.one_mulVec] at this
    simp only [Equiv.coe_addRight]
    rw [show v + ((h : Mt g m) *ᵥ w - w) = (h : Mt g m) *ᵥ w + v - w by abel, this,
      show (h : Mt g m) *ᵥ w + v - w = v + ((h : Mt g m) *ᵥ w - w) by abel, dotProduct_add, ψ.map_add_eq_mul,
      dotProduct_sub, dotProduct_mulVec, sub_dotProduct]
    ring
  have h2 : (∑ v, F (E h v) * (ψ (r ⬝ᵥ v))⁻¹) * (1 - (ψ ((r ᵥ* (h : Mt g m) - r) ⬝ᵥ w))⁻¹) = 0 := by
    linear_combination h1
  rw [fc, (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 (by simpa [eq_comm] using hw)), mul_zero]

theorem sum_fib (Φ : Gn g (m + 1) → ℂ) (h : Gn g m) :
    (∑ x : Gn g (m + 1), if InR m (x : Mt g (m + 1)) ∧ tl m (x : Mt g (m + 1)) = (h : Mt g m) then Φ x else 0) =
      ∑ v, Φ (E h v) := by
  rw [sum_mir _ fun y hy => if_neg fun hh => hy ((inR_iff _).1 hh.1)]
  simp only [E_coe, inR_iff, inMir_Em, tl_Em, true_and, Units.val_inj]
  rw [Finset.sum_comm]
  simp

theorem der_eq (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ) (h : Gn g m) : der ψ m F h = fc ψ F h 0 := by
  rw [der, wh_one ψ (by omega), res, fc]
  have e : m * (m + 1 - m) = m := by simp
  rw [e]
  congr 1
  simp only [zero_dotProduct, AddChar.map_zero_eq_one, inv_one, mul_one]
  rw [← sum_fib]
  refine Finset.sum_congr rfl fun x _ => if_congr ?_ rfl rfl
  rw [InR, uni_iff (by omega), Units.val_one]
  tauto

theorem entN_Em (l : Fin m) (hl : (l : ℕ) + 1 = m) (h : Mt g m) (v) :
    entN (Em h v) (m - 1) m = Pi.single l 1 ⬝ᵥ v := by
  rw [single_dotProduct, one_mul, ← Em_cl h v l, entN, dite_eq_left ⟨by omega, by omega⟩]
  congr 1
  exact Fin.ext (by simp; omega)

theorem tail_eq (l : Fin m) (hl : (l : ℕ) + 1 = m) (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ) (h : Gn g m) :
    tail ψ m F h = fc ψ F h (Pi.single l 1) := by
  rw [tail, fc, sum_fib (fun x => F x * (ψ (supFrom (m - 1) (x : Mt g (m + 1))))⁻¹)]
  have e : m * (m + 1 - m) + (m + 1 - m) * (m + 1 - m - 1) / 2 = m := by simp
  rw [e]
  congr 1
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← entN_Em l hl (h : Mt g m) v, supFrom]
  have : Finset.Ico (m - 1) (m + 1 - 1) = {m - 1} := by
    ext j
    simp
    omega
  rw [this, Finset.sum_singleton, show m - 1 + 1 = m by omega, E_coe]

theorem indR_eq (ψ : AddChar (ZMod g) ℂ) {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h : Gn g m) (v) :
    indR ψ m (m + 1) (der ψ m F) (E h v) = fc ψ F h 0 := by
  unfold indR
  rw [Finset.natCast_card_filter, sum_mir _ fun y hy => if_neg fun hh => hy ((inR_iff _).1 hh),
    sum_mir _ fun y hy => if_neg fun hh => hy hh.1]
  simp only [E_conj]
  simp only [E_coe, inR_iff, inMir_Em, tl_Em, true_and, if_true, toG_coe, der_eq, fc_conj ψ hF,
    supFrom, Nat.add_sub_cancel, Finset.Ico_self, Finset.sum_empty, AddChar.map_zero_eq_one, mul_one,
    Matrix.zero_vecMul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : (Fintype.card (Gn g m) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h2 : (Fintype.card (Fin m → ZMod g) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

theorem sum_rows (l : Fin m) (hl : (l : ℕ) + 1 = m) (φ : (Fin m → ZMod g) → ℂ) :
    ∑ k : Gn g m, φ (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) =
      (∑ k : Gn g m, if InMir (k : Mt g m) then (1 : ℂ) else 0) * ∑ r, if r = 0 then 0 else φ r := by
  refine (Equiv.sum_comp (Equiv.inv (Gn g m)) fun k : Gn g m => φ (Pi.single l 1 ᵥ* (k : Mt g m))).trans ?_
  rw [Finset.mul_sum,
    ← Finset.sum_fiberwise Finset.univ fun k : Gn g m => Pi.single l 1 ᵥ* (k : Mt g m)]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs with hr
  · subst hr
    rw [mul_zero]
    refine Finset.sum_eq_zero fun k hk => ?_
    have := congrArg (fun v => v ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) (Finset.mem_filter.1 hk).2
    simp only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] at this
    simpa using congrFun this l
  · obtain ⟨k₀, rfl⟩ := exists_row l r hr
    rw [Finset.sum_filter, Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight k₀)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : Pi.single l 1 ᵥ* ((k * k₀ : Gn g m) : Mt g m) = Pi.single l 1 ᵥ* (k₀ : Mt g m) ↔ InMir (k : Mt g m) := by
      rw [inMir_iff_row l hl, Units.val_mul, ← Matrix.vecMul_vecMul]
      refine ⟨fun e => ?_, fun e => by rw [e]⟩
      have := congrArg (fun v => v ᵥ* ((k₀⁻¹ : Gn g m) : Mt g m)) e
      simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, mul_assoc, mul_one] using this
    by_cases hk : InMir (k : Mt g m)
    · refine (if_pos (this.2 hk)).trans ?_
      rw [if_pos hk, one_mul]
      exact congrArg φ (this.2 hk)
    · refine (if_neg (fun e => hk (this.1 e))).trans ?_
      rw [if_neg hk, zero_mul]

theorem indV_eq (l : Fin m) (hl : (l : ℕ) + 1 = m) {ψ : AddChar (ZMod g) ℂ} (hψ : ψ ≠ 1)
    {F : Gn g (m + 1) → ℂ} (hF : IsMirClass F) (h : Gn g m) (v) :
    indV ψ m (tail ψ m F) (E h v) = ∑ r, if r = 0 then 0 else fc ψ F h r * ψ (r ⬝ᵥ v) := by
  unfold indV
  rw [Finset.natCast_card_filter, sum_mir _ fun y hy => if_neg fun hh => hy hh.1,
    sum_mir _ fun y hy => if_neg fun hh => hy hh.1]
  simp only [E_conj]
  simp only [E_coe, inMir_Em, tl_Em, true_and, toG_coe, tail_eq l hl, fc_conj ψ hF, entN_Em l hl]
  have key : ∀ (k : Gn g m) (w : Fin m → ZMod g),
      (if InMir ((k⁻¹ * h * k : Gn g m) : Mt g m) then fc ψ F h (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) *
        ψ (Pi.single l 1 ⬝ᵥ ((k⁻¹ : Gn g m) : Mt g m) *ᵥ ((h : Mt g m) *ᵥ w + v - w)) else 0) =
      fc ψ F h (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) *
        ψ ((Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) ⬝ᵥ v) := by
    intro k w
    have hiff : InMir ((k⁻¹ * h * k : Gn g m) : Mt g m) ↔
        (Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) ᵥ* (h : Mt g m) =
          Pi.single l 1 ᵥ* ((k⁻¹ : Gn g m) : Mt g m) := by
      rw [inMir_iff_row l hl, Units.val_mul, Units.val_mul]
      constructor
      · intro e
        have := congrArg (fun v => v ᵥ* ((k⁻¹ : Gn g m) : Mt g m)) e
        simpa only [Matrix.vecMul_vecMul, Units.mul_inv, mul_assoc, mul_one] using this
      · intro e
        have := congrArg (fun v => v ᵥ* (k : Mt g m)) e
        simpa only [Matrix.vecMul_vecMul, Units.inv_mul, Matrix.vecMul_one] using this
    split_ifs with hk
    · rw [dotProduct_mulVec, dotProduct_sub, dotProduct_add, dotProduct_mulVec, hiff.1 hk, add_sub_cancel_left]
    · rw [fc_eq_zero hψ hF h _ (fun e => hk (hiff.2 e)), zero_mul]
  simp only [key, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, sum_rows l hl fun r => fc ψ F h r * ψ (r ⬝ᵥ v)]
  have h2 : (Fintype.card (Fin m → ZMod g) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h1 : (∑ k : Gn g m, if InMir (k : Mt g m) then (1 : ℂ) else 0) ≠ 0 := by
    rw [← Finset.natCast_card_filter, Nat.cast_ne_zero, Finset.card_ne_zero]
    exact ⟨1, by simp [inMir_one]⟩
  field_simp

theorem mir_step : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (m : ℕ) (F : Gn g (m + 1) → ℂ),
    1 ≤ m → IsMirClass F → ∀ p : Gn g (m + 1), InMir (p : Mt g (m + 1)) →
      F p = indR ψ m (m + 1) (der ψ m F) p + indV ψ m (tail ψ m F) p := by
  intro g _ ψ hψ m F hm hF p hp
  obtain ⟨h, v, rfl⟩ := exists_E hp
  rw [indR_eq ψ hF, indV_eq ⟨m - 1, by omega⟩ (by simp; omega) hψ hF, ← inversion hψ F h v]
  have : fc ψ F h 0 = ∑ r, if r = 0 then fc ψ F h r * ψ (r ⬝ᵥ v) else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  split_ifs <;> simp

end GlobalTheory.GLm.MirStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicFunctionEqInducedDerivativeAddTailStatement
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_function_eq_induced_derivative_add_tail : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (m : ℕ) (F : Gn g (m + 1) → ℂ), 1 ≤ m → IsMirClass F → ∀ p : Gn g (m + 1), InMir (p : Mt g (m + 1)) → F p = indR ψ m (m + 1) (der ψ m F) p + indV ψ m (tail ψ m F) p := by
  first | exact @GlobalTheory.GLm.MirStep.mir_step | exact GlobalTheory.GLm.MirStep.mir_step | (intros; apply GlobalTheory.GLm.MirStep.mir_step <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicConjInvariantEqSumInducedDerivatives
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.MirSum

variable {g : ℕ} [Fact g.Prime]

theorem inMir_toG {m : ℕ} {M : Mt g m} (h : InMir M) : InMir ((toG M : Gn g m) : Mt g m) := by
  unfold toG
  split_ifs with hu
  · rw [hu.unit_spec]
    exact h
  · exact inMir_one m

theorem indV_sum (ψ : AddChar (ZMod g) ℂ) (m : ℕ) (f : Gn g m → ℂ) (s : Finset ℕ) (fs : ℕ → Gn g m → ℂ)
    (h : ∀ p : Gn g m, InMir (p : Mt g m) → f p = ∑ i ∈ s, fs i p) (x : Gn g (m + 1)) :
    indV ψ m f x = ∑ i ∈ s, indV ψ m (fs i) x := by
  simp only [indV]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hc
  · rw [h _ (inMir_toG hc.2.2), Finset.sum_mul]
  · simp

theorem inMir_one_iff (p : Gn g 1) : InMir (p : Mt g 1) ↔ p = 1 := by
  constructor
  · intro h
    ext i j
    fin_cases i
    fin_cases j
    simpa using h 0 0 rfl
  · rintro rfl i j _
    rfl

theorem isUniUp_one_iff (p : Gn g 1) : IsUniUp (p : Mt g 1) ↔ p = 1 := by
  constructor
  · intro h
    ext i j
    fin_cases i
    fin_cases j
    simpa using (h 0 0).2 rfl
  · rintro rfl a b
    fin_cases a
    fin_cases b
    simp

theorem br_one (M : Mt g 1) : br 0 1 M = M := by
  ext i j
  obtain rfl := Subsingleton.elim i 0
  obtain rfl := Subsingleton.elim j 0
  simp [br, entN]

theorem inPar_zero {n : ℕ} (M : Mt g n) : InPar 0 M := by
  intro i j hj _
  exact absurd hj (Nat.not_lt_zero _)

theorem inR_one_iff (p : Gn g 1) : InR 0 (p : Mt g 1) ↔ p = 1 := by
  show InPar 0 (p : Mt g 1) ∧ IsUniUp (br 0 1 (p : Mt g 1)) ↔ p = 1
  rw [br_one, isUniUp_one_iff]
  exact ⟨fun h => h.2, fun h => ⟨inPar_zero _, h⟩⟩

theorem res_one (F : Gn g 1 → ℂ) (h : Gn g 0) (u : Gn g 1) : res 0 1 F h u = F u := by
  have key : ∀ x : Gn g 1, (InPar 0 (x : Mt g 1) ∧ tl 0 (x : Mt g 1) = (h : Mt g 0) ∧
      br 0 1 (x : Mt g 1) = (u : Mt g 1)) ↔ x = u := by
    intro x
    rw [br_one]
    exact ⟨fun hx => Units.ext hx.2.2, fun hx => ⟨inPar_zero _, by ext i j; exact i.elim0, by rw [hx]⟩⟩
  unfold res
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_mul, pow_zero, inv_one, one_mul]

theorem eU_one (ψ : AddChar (ZMod g) ℂ) : eU g 1 ψ = MonoidAlgebra.single 1 1 := by
  have hf : (Finset.univ.filter fun u : Gn g 1 => IsUniUp (u : Mt g 1)) = {1} := by
    ext u
    simp [isUniUp_one_iff]
  simp only [eU, eDat, hf]
  simp

theorem der_one (ψ : AddChar (ZMod g) ℂ) (F : Gn g 1 → ℂ) (h : Gn g 0) : der ψ 0 F h = F 1 := by
  show wh ψ (res 0 1 F h) = F 1
  unfold wh tr
  rw [eU_one, Finset.sum_eq_single (1 : Gn g 1)]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_mul, res_one]
  · intro b _ hb
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hb]
  · intro h1
    exact absurd (Finset.mem_univ _) h1

theorem base (ψ : AddChar (ZMod g) ℂ) (F : Gn g 1 → ℂ) : F 1 = indR ψ 0 1 (der ψ 0 F) 1 := by
  have hc : (Finset.univ.filter fun p : Gn g 1 => InR 0 (p : Mt g 1)) = {1} := by
    ext p
    simp [inR_one_iff]
  have hs : ∀ y : Gn g 1, (InMir (y : Mt g 1) ∧ InR 0 ((y⁻¹ * 1 * y : Gn g 1) : Mt g 1)) ↔ y = 1 := by
    intro y
    rw [inMir_one_iff, inR_one_iff]
    simp
  unfold indR
  simp only [hc, hs, Finset.card_singleton, Nat.cast_one, inv_one, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, der_one, supFrom]
  simp

theorem eq_sum_indR_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (n : ℕ) (F : Gn g n → ℂ), 1 ≤ n → IsMirClass F → ∀ p : Gn g n, InMir (p : Mt g n) → F p = ∑ i ∈ Finset.range n, indR ψ i n (der ψ i F) p := by
  intro g _ ψ hψ n
  induction n with
  | zero =>
    intro F h
    omega
  | succ m ih =>
    intro F _ hF p hp
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hp1 := (inMir_one_iff p).mp hp
      subst hp1
      show F 1 = ∑ i ∈ Finset.range 1, indR ψ i 1 (der ψ i F) 1
      rw [Finset.sum_range_one]
      exact base ψ F
    · have hT := GlobalTheory.T.isMirabolicConjInvariant_twistedTailMeanFun g ψ m (m + 1) F hm (Nat.le_succ m) hF
      rw [GlobalTheory.T.mirabolic_function_eq_induced_derivative_add_tail g ψ hψ m F hm hF p hp, Finset.sum_range_succ,
        add_comm (indR ψ m (m + 1) (der ψ m F) p)]
      congr 1
      refine (indV_sum ψ m (tail ψ m F) (Finset.range m)
        (fun i => indR ψ i m (der ψ i (tail ψ m F))) (fun q hq => ih (tail ψ m F) hm hT q hq) p).trans ?_
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      show indV ψ m (indR ψ i m (der ψ i (tail ψ m F))) p = _
      rw [GlobalTheory.T.mirabolicInductionPhiPlus_inductionFromBlockUni g ψ i m _ hi p hp, GlobalTheory.T.der_tail_of_lt_of_le g ψ i m (m + 1) F hi (Nat.le_succ m)]

end GlobalTheory.GLm.MirSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicConjInvariantEqSumInducedDerivativesStatement
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicConjInvariant_eq_sum_induced_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (n : ℕ) (F : Gn g n → ℂ), 1 ≤ n → IsMirClass F → ∀ p : Gn g n, InMir (p : Mt g n) → F p = ∑ i ∈ Finset.range n, indR ψ i n (der ψ i F) p := by
  first | exact @GlobalTheory.GLm.MirSum.eq_sum_indR_der | exact GlobalTheory.GLm.MirSum.eq_sum_indR_der | (intros; apply GlobalTheory.GLm.MirSum.eq_sum_indR_der <;> assumption)
end
