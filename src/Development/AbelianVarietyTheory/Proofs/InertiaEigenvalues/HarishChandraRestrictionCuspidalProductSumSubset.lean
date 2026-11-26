module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IteratedDerivLine
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MackeyCellTermOfBlockSizes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastNeZeroPs

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.Reciprocity
noncomputable section

namespace GlobalTheory.GLm.Recip

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem toG_coe {g : ℕ} [Fact g.Prime] {n : ℕ} (h : Gn g n) : toG (h : Mt g n) = h := by
  unfold toG
  rw [dite_eq_left h.isUnit]
  exact Units.ext (IsUnit.unit_spec _)

theorem coe_toG {g : ℕ} [Fact g.Prime] {n : ℕ} {M : Mt g n} (h : IsUnit M) : ((toG M : Gn g n) : Mt g n) = M := by
  unfold toG
  rw [dite_eq_left h]
  exact IsUnit.unit_spec _

theorem mean_conj {G : Type} [Group G] [Fintype G] (χ F : G → ℂ) (hχ : IsClass χ) (c : ℂ) :
    mean (fun x => χ x * (c * ∑ y, F (y⁻¹ * x * y))) = c * ∑ x, F x * χ x := by
  unfold mean
  have h1 : ∀ y : G, ∑ x, χ x * F (y⁻¹ * x * y) = ∑ x, F x * χ x := by
    intro y
    symm
    refine Fintype.sum_equiv (MulAut.conj y).toEquiv _ _ ?_
    intro x
    have : y⁻¹ * (y * x * y⁻¹) * y = x := by group
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    rw [hχ, this, mul_comm]
  have h2 : ∑ x, χ x * (c * ∑ y, F (y⁻¹ * x * y)) = c * ∑ y : G, ∑ x, χ x * F (y⁻¹ * x * y) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum]; ring
  have h3 : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [h2]
  simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem mean_res (g : ℕ) [Fact g.Prime] (c d n : ℕ) (hn : n = c + d) (χ : Gn g n → ℂ)
    (Λ : Gn g c → Gn g d → ℂ) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) =
      ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n,
        if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
  obtain ⟨-, -, hu, -, -, hcard⟩ := GlobalTheory.T.blockParabolic_unitriangular_subgroups_GLnPrimeField g c d n hn
  have key : ∀ x : Gn g n, (∑ p : Gn g c × Gn g d, Λ p.1 p.2 *
      (if InPar c (x : Mt g n) ∧ tl c (x : Mt g n) = (p.1 : Mt g c) ∧ br c d (x : Mt g n) = (p.2 : Mt g d)
        then χ x else 0)) =
      if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0 := by
    intro x
    by_cases hx : InPar c (x : Mt g n)
    · obtain ⟨h1, h2⟩ := hu x hx
      rw [if_pos hx, Finset.sum_eq_single (toG (tl c (x : Mt g n)), toG (br c d (x : Mt g n)))]
      · rw [if_pos ⟨hx, (coe_toG h1).symm, (coe_toG h2).symm⟩]
      · intro p _ hp
        rw [if_neg, mul_zero]
        rintro ⟨-, e1, e2⟩
        apply hp
        rw [e1, e2, toG_coe, toG_coe]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp [hx]
  unfold mean res
  rw [hcard]
  simp only [← key]
  rw [Finset.sum_comm (γ := Gn g n), Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.mul_sum, Fintype.card_prod]
  push_cast
  rw [mul_inv (_ * _)]
  ring

theorem eq_of_mean (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ)
    (hA1 : ∀ y, IsClass fun x => A x y) (hA2 : ∀ x, IsClass (A x)) (hB1 : ∀ y, IsClass fun x => B x y)
    (hB2 : ∀ x, IsClass (B x))
    (h : ∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) →
      mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) :
    A = B := by
  have h0 := h (fun x y => (starRingEnd ℂ) (A x y - B x y))
    (fun y x z => by
      have e1 := hA1 y x z
      have e2 := hB1 y x z
      simp only at e1 e2 ⊢
      rw [e1, e2])
    (fun x y z => by
      simp only
      rw [hA2 x y z, hB2 x y z])
  unfold mean at h0
  have h3 : (Fintype.card (G₁ × G₂) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  have h1 := sub_eq_zero.mpr (mul_left_cancel₀ h3 h0)
  rw [← Finset.sum_sub_distrib] at h1
  have h2 : ∑ p : G₁ × G₂, Complex.normSq (A p.1 p.2 - B p.1 p.2) = 0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_sum, Complex.ofReal_zero, ← h1]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]; ring
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at h2
  funext x y
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp (h2 (x, y) (Finset.mem_univ _)))

theorem reciprocity : ∀ (g : ℕ) [Fact g.Prime] , (∀ (a b n : ℕ), n = a + b → ∀ (χ : Gn g n → ℂ) (Φ : Gn g a → Gn g b → ℂ), IsClass χ → mean (fun x => χ x * hcT a b Φ n x) = mean (fun p : Gn g a × Gn g b => res a b χ p.1 p.2 * Φ p.1 p.2)) ∧ (∀ (c d n : ℕ), n = c + d → ∀ (χ : Gn g n → ℂ) (Λ : Gn g c → Gn g d → ℂ), mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d χ p.1 p.2) = ((Finset.univ.filter fun x : Gn g n => InPar c (x : Mt g n)).card : ℂ)⁻¹ * ∑ x : Gn g n, if InPar c (x : Mt g n) then Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))) * χ x else 0) ∧ ∀ (G₁ G₂ : Type) [Group G₁] [Group G₂] [Fintype G₁] [Fintype G₂] (A B : G₁ → G₂ → ℂ), (∀ y, IsClass fun x => A x y) → (∀ x, IsClass (A x)) → (∀ y, IsClass fun x => B x y) → (∀ x, IsClass (B x)) → (∀ Λ : G₁ → G₂ → ℂ, (∀ y, IsClass fun x => Λ x y) → (∀ x, IsClass (Λ x)) → mean (fun p : G₁ × G₂ => Λ p.1 p.2 * A p.1 p.2) = mean (fun p : G₁ × G₂ => Λ p.1 p.2 * B p.1 p.2)) → A = B := by
  intro g _
  refine ⟨?_, mean_res g, eq_of_mean⟩
  intro a b n hn χ Φ hχ
  have h1 := mean_res g a b n hn χ Φ
  have h2 := mean_conj χ (fun x : Gn g n => if InPar a (x : Mt g n) then
    Φ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) else 0) hχ
    ((Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card : ℂ)⁻¹
  simp only [ite_mul, zero_mul] at h2
  rw [← h1] at h2
  simp only [mul_comm (res a b χ _ _)]
  exact h2

end GlobalTheory.GLm.Recip
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MackeyFormulaHarishChandraRestrictionInduction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MackeyFormulaHarishChandraRestrictionInduction
noncomputable section

namespace GlobalTheory.GLq.Mackey

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem blocks_conj (a b n : ℕ) (hn : n = a + b) (P : Subgroup (Gn g n))
    (hP : ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) (Λ : Gn g a → Gn g b → ℂ)
    (h1 : ∀ y, IsClass fun x => Λ x y) (h2 : ∀ x, IsClass (Λ x)) :
    ∀ h ∈ P, ∀ x ∈ P, Λ (toG (tl a ((h * x * h⁻¹ : Gn g n) : Mt g n))) (toG (br a b ((h * x * h⁻¹ : Gn g n) : Mt g n)))
      = Λ (toG (tl a (x : Mt g n))) (toG (br a b (x : Mt g n))) := by
  obtain ⟨-, -, hu, hmul, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn
  let f₁ : P →* Gn g a := MonoidHom.mk' (fun p => toG (tl a ((p : Gn g n) : Mt g n))) (by
    intro p q
    have hp : InPar a ((p : Gn g n) : Mt g n) := (hP p).1 p.2
    have hq : InPar a ((q : Gn g n) : Mt g n) := (hP q).1 q.2
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (hmul _ _ hp hq).1, Units.val_mul,
      Recip.coe_toG ((hu _ hp).1.mul (hu _ hq).1), Recip.coe_toG (hu _ hp).1, Recip.coe_toG (hu _ hq).1])
  let f₂ : P →* Gn g b := MonoidHom.mk' (fun p => toG (br a b ((p : Gn g n) : Mt g n))) (by
    intro p q
    have hp : InPar a ((p : Gn g n) : Mt g n) := (hP p).1 p.2
    have hq : InPar a ((q : Gn g n) : Mt g n) := (hP q).1 q.2
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (hmul _ _ hp hq).2, Units.val_mul,
      Recip.coe_toG ((hu _ hp).2.mul (hu _ hq).2), Recip.coe_toG (hu _ hp).2, Recip.coe_toG (hu _ hq).2])
  intro h hh x hx
  have E1 : toG (tl a ((h * x * h⁻¹ : Gn g n) : Mt g n)) = f₁ ⟨h, hh⟩ * f₁ ⟨x, hx⟩ * (f₁ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  have E2 : toG (br a b ((h * x * h⁻¹ : Gn g n) : Mt g n)) = f₂ ⟨h, hh⟩ * f₂ ⟨x, hx⟩ * (f₂ ⟨h, hh⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  rw [E1, E2]
  exact (h2 _ _ _).trans (h1 _ _ _)

theorem mean_prod_right {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun p : A × B => F p.1 p.2) = mean (fun b => mean (fun a => F a b)) := by
  unfold mean
  rw [Fintype.sum_prod_type_right, Fintype.card_prod]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  push_cast; rw [mul_inv]; ring

theorem mean_prod_left {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun p : A × B => F p.1 p.2) = mean (fun a => mean (fun b => F a b)) := by
  unfold mean
  rw [Fintype.sum_prod_type, Fintype.card_prod]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  push_cast; rw [mul_inv]; ring

theorem mean_swap {A B : Type} [Fintype A] [Fintype B] (F : A → B → ℂ) :
    mean (fun b => mean (fun a => F a b)) = mean (fun a => mean (fun b => F a b)) := by
  rw [← mean_prod_right, mean_prod_left]

theorem mean_equiv {A B : Type} [Fintype A] [Fintype B] (e : A ≃ B) (F : B → ℂ) :
    mean (fun x => F (e x)) = mean F := by
  unfold mean
  rw [Fintype.card_congr e, Equiv.sum_comp e F]

theorem mean_sum {A ι : Type} [Fintype A] (R : Finset ι) (Λ : A → ℂ) (T : ι → A → ℂ) :
    mean (fun p => Λ p * ∑ i ∈ R, T i p) = ∑ i ∈ R, mean (fun p => Λ p * T i p) := by
  unfold mean
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem res_comm {p q r s m k : ℕ} (Λ : Gn g m → Gn g k → ℂ) (y₁ : Gn g p) (y₃ : Gn g q) (y₂ : Gn g r)
    (y₄ : Gn g s) :
    res r s (fun h₂ => res p q (fun x => Λ x h₂) y₁ y₃) y₂ y₄ =
      res p q (fun z => res r s (Λ z) y₂ y₄) y₁ y₃ := by
  unfold res
  simp only [← Finset.sum_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  ring

theorem left_side (a b c d n : ℕ) (hn1 : n = a + b) (hn2 : n = c + d) (Φ : Gn g a → Gn g b → ℂ)
    (hΦ1 : ∀ y, IsClass fun x => Φ x y) (hΦ2 : ∀ x, IsClass (Φ x))
    (Λ : Gn g c → Gn g d → ℂ) (hΛ1 : ∀ y, IsClass fun x => Λ x y) (hΛ2 : ∀ x, IsClass (Λ x)) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * res c d (hcT a b Φ n) p.1 p.2) =
      ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        mean (fun y : (Gn g i × Gn g (a - i)) × (Gn g (c - i) × Gn g (b - (c - i))) =>
          res i (c - i) (fun z => res (a - i) (b - (c - i)) (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  obtain ⟨-, R2, -⟩ := Recip.reciprocity g
  obtain ⟨⟨Pc, hPc⟩, -, -, -, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g c d n hn2
  obtain ⟨⟨Pa, hPa⟩, -, -, -, -, -⟩ := GlobalTheory.GLm.ParBasic.par_basic g a b n hn1
  have hR : ∀ x : Gn g n, ∃! i, i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b) ∧
      ∃ h ∈ Pc, ∃ k ∈ Pa, x = h * wI g a c i n * k := by
    intro x
    obtain ⟨i, ⟨hi, p, q, hp, hq, e⟩, hu⟩ := GlobalTheory.GLm.ParCoset.doubleCoset g a b c d n hn1 hn2 x
    refine ⟨i, ⟨hi, p, (hPc p).2 hp, q, (hPa q).2 hq, e⟩, ?_⟩
    rintro j ⟨hj, h, hh, k, hk, e'⟩
    exact hu j ⟨hj, h, k, (hPc h).1 hh, (hPa k).1 hk, e'⟩
  have hm := mackey_doubleCoset_pairing (Gn g n) Pc Pa ℕ
    ((Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b)) (fun i => wI g a c i n) hR
    (fun x => Λ (toG (tl c (x : Mt g n))) (toG (br c d (x : Mt g n))))
    (fun z => Φ (toG (tl a (z : Mt g n))) (toG (br a b (z : Mt g n))))
    (blocks_conj c d n hn2 Pc hPc Λ hΛ1 hΛ2) (blocks_conj a b n hn1 Pa hPa Φ hΦ1 hΦ2)
  have cc : ∀ (P : Subgroup (Gn g n)) (Q : Gn g n → Prop), (∀ x, x ∈ P ↔ Q x) →
      Nat.card P = (Finset.univ.filter Q).card := by
    intro P Q hP
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext x
    simp [hP]
  rw [cc Pc _ hPc, cc Pa _ hPa] at hm
  simp only [hPc, hPa] at hm
  rw [R2 c d n hn2]
  unfold hcT
  rw [hm]
  refine Finset.sum_congr rfl fun i hi => ?_
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  exact mackey_cell_term g a b c d n i hn1 hn2 (by omega) hi.2.1 hi.2.2 Λ Φ

theorem right_term (a b c d n i : ℕ) (hn1 : n = a + b) (hn2 : n = c + d) (hia : i ≤ a) (hic : i ≤ c)
    (hcb : c - i ≤ b) (Φ : Gn g a → Gn g b → ℂ) (Λ : Gn g c → Gn g d → ℂ)
    (hΛ1 : ∀ y, IsClass fun x => Λ x y) (hΛ2 : ∀ x, IsClass (Λ x)) :
    mean (fun p : Gn g c × Gn g d => Λ p.1 p.2 * hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i))
      (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d p.2) c p.1) =
    mean (fun y : (Gn g i × Gn g (a - i)) × (Gn g (c - i) × Gn g (b - (c - i))) =>
      res i (c - i) (fun z => res (a - i) (b - (c - i)) (Λ z) y.1.2 y.2.2) y.1.1 y.2.1 *
        res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y.2.1 y.2.2) y.1.1 y.1.2) := by
  have hc : c = i + (c - i) := by omega
  have hd : d = (a - i) + (b - (c - i)) := by omega
  obtain ⟨R1, -, -⟩ := Recip.reciprocity g
  rw [mean_prod_right (fun (h₁ : Gn g c) (h₂ : Gn g d) => Λ h₁ h₂ * hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i))
      (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁)]
  calc _ = mean (fun h₂ : Gn g d => mean (fun q : Gn g i × Gn g (c - i) =>
          res i (c - i) (fun x => Λ x h₂) q.1 q.2 * hcT (a - i) (b - (c - i))
            (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 y₄) q.1 y₂) d h₂)) := by
        congr 1; funext h₂
        exact R1 i (c - i) c hc (fun x => Λ x h₂) _ (hΛ1 h₂)
    _ = mean (fun q : Gn g i × Gn g (c - i) => mean (fun h₂ : Gn g d =>
          res i (c - i) (fun x => Λ x h₂) q.1 q.2 * hcT (a - i) (b - (c - i))
            (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 y₄) q.1 y₂) d h₂)) :=
        mean_swap _
    _ = mean (fun q : Gn g i × Gn g (c - i) => mean (fun r : Gn g (a - i) × Gn g (b - (c - i)) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) q.1 q.2) r.1 r.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 r.2) q.1 r.1)) := by
        congr 1; funext q
        refine R1 (a - i) (b - (c - i)) d hd _ _ ?_
        intro x y
        show res i (c - i) (fun z => Λ z (y * x * y⁻¹)) q.1 q.2 = res i (c - i) (fun z => Λ z x) q.1 q.2
        rw [show (fun z => Λ z (y * x * y⁻¹)) = (fun z => Λ z x) from funext fun z => hΛ2 z x y]
    _ = mean (fun w : (Gn g i × Gn g (c - i)) × (Gn g (a - i) × Gn g (b - (c - i))) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) w.1.1 w.1.2) w.2.1 w.2.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) w.1.2 w.2.2) w.1.1 w.2.1) :=
        (mean_prod_left (fun (q : Gn g i × Gn g (c - i)) (r : Gn g (a - i) × Gn g (b - (c - i))) =>
          res (a - i) (b - (c - i)) (fun h₂ => res i (c - i) (fun x => Λ x h₂) q.1 q.2) r.1 r.2 *
            res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) q.2 r.2) q.1 r.1)).symm
    _ = _ := by
        rw [← mean_equiv (Equiv.prodProdProdComm (Gn g i) (Gn g (a - i)) (Gn g (c - i)) (Gn g (b - (c - i))))]
        congr 1; funext y
        simp only [Equiv.prodProdProdComm_apply]
        rw [res_comm]

theorem mackey_formula : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d →
    ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → ∀ h₁ h₂,
      res c d (hcT a b Φ n) h₁ h₂ = ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ =>
          res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁ := by
  intro g _ a b c d n hn1 hn2 Φ hΦ1 hΦ2 h₁ h₂
  obtain ⟨-, -, R3⟩ := Recip.reciprocity g
  have hcl : IsClass (hcT a b Φ n) := (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g a b n hn1).1 Φ
  have hres := (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g c d n hn2).2 _ hcl
  suffices H : (fun (h₁ : Gn g c) (h₂ : Gn g d) => res c d (hcT a b Φ n) h₁ h₂) =
      (fun (h₁ : Gn g c) (h₂ : Gn g d) => ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b),
        hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ =>
          res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁) from
    congrFun (congrFun H h₁) h₂
  refine R3 (Gn g c) (Gn g d) _ _ hres.2 hres.1 ?_ ?_ ?_
  · intro y x z
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g i (c - i) c (by omega)).1 _ x z
  · intro x y z
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have hd' : ∀ Ψ, hcT (a - i) (b - (c - i)) Ψ d (z * y * z⁻¹) = hcT (a - i) (b - (c - i)) Ψ d y :=
      fun Ψ => (GlobalTheory.T.harishChandra_induction_restriction_isClassFunction g (a - i) (b - (c - i)) d (by omega)).1 Ψ y z
    simp only [hd']
  · intro Λ hΛ1 hΛ2
    rw [left_side a b c d n hn1 hn2 Φ hΦ1 hΦ2 Λ hΛ1 hΛ2, mean_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    exact (right_term a b c d n i hn1 hn2 (by omega) hi.2.1 hi.2.2 Φ Λ hΛ1 hΛ2).symm

end GlobalTheory.GLq.Mackey
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MackeyFormulaHarishChandraRestrictionInductionStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mackey_formula_harishChandra_restriction_induction : ∀ (g : ℕ) [Fact g.Prime] (a b c d n : ℕ), n = a + b → n = c + d → ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) → ∀ h₁ h₂, res c d (hcT a b Φ n) h₁ h₂ = ∑ i ∈ (Finset.range (a + 1)).filter (fun i => i ≤ c ∧ c - i ≤ b), hcT i (c - i) (fun y₁ y₃ => hcT (a - i) (b - (c - i)) (fun y₂ y₄ => res i (a - i) (fun x => res (c - i) (b - (c - i)) (Φ x) y₃ y₄) y₁ y₂) d h₂) c h₁ := by
  first | exact @GlobalTheory.GLq.Mackey.mackey_formula | exact GlobalTheory.GLq.Mackey.mackey_formula | (intros; apply GlobalTheory.GLq.Mackey.mackey_formula <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionCuspidalProductSumSubset
noncomputable section

namespace GlobalTheory.GLq.ResCuspProd

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

variable {g : ℕ} [Fact g.Prime]

theorem toG_coe {n : ℕ} (x : Gn g n) : toG (x : Mt g n) = x := by
  unfold toG
  rw [dif_pos x.isUnit]
  exact Units.ext rfl

theorem br_zero_eq {a : ℕ} (M : Mt g a) : br 0 a M = M := by
  funext i j
  simp only [br, entN, zero_add, i.isLt, j.isLt, and_self, dif_pos]

theorem tl_self_eq {a : ℕ} (M : Mt g a) : tl a M = M := by
  funext i j
  simp only [tl, entN, i.isLt, j.isLt, and_self, dif_pos]

theorem inPar_zero' {n : ℕ} (M : Mt g n) : InPar 0 M := fun _ _ hj _ => absurd hj (Nat.not_lt_zero _)

theorem inPar_self' {a : ℕ} (M : Mt g a) : InPar a M := fun i _ _ hi => absurd i.isLt (not_lt.2 hi)

theorem isClass_conj {G : Type} [Group G] {χ : G → ℂ} (h : IsClass χ) (x y : G) : χ (y⁻¹ * x * y) = χ x := by
  have := h x y⁻¹
  rwa [inv_inv] at this

theorem mean_of_isClass {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsClass χ) (x : G) :
    (Fintype.card G : ℂ)⁻¹ * ∑ y : G, χ (y⁻¹ * x * y) = χ x := by
  simp only [isClass_conj h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

theorem isClass_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsClass χ := by
  obtain ⟨V, _, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

theorem isClass_hcT (a b : ℕ) (Φ : Gn g a → Gn g b → ℂ) (n : ℕ) : IsClass (hcT a b Φ n) := by
  intro x z
  unfold hcT
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft z⁻¹) _ _ (fun y => ?_)
  have : (z⁻¹ * y)⁻¹ * x * (z⁻¹ * y) = y⁻¹ * (z * x * z⁻¹) * y := by group
  simp only [Equiv.coe_mulLeft, this]

theorem isClass_hcL (L : List (Pc g)) (n : ℕ) : IsClass (hcL L n) := by
  cases L with
  | nil => intro x y; rfl
  | cons p L =>
    rw [hcL_cons]
    unfold hc
    exact isClass_hcT _ _ _ _

theorem res_left_zero (i n : ℕ) (hi : i = 0) (χ : Gn g n → ℂ) (y₁ : Gn g i) (y₂ : Gn g n) :
    res i n χ y₁ y₂ = χ y₂ := by
  subst hi
  unfold res
  have hy : ∀ x : Gn g n, (InPar 0 (x : Mt g n) ∧ tl 0 (x : Mt g n) = (y₁ : Mt g 0) ∧
      br 0 n (x : Mt g n) = (y₂ : Mt g n)) ↔ x = y₂ := by
    intro x
    rw [br_zero_eq, Units.val_inj]
    exact ⟨fun h => h.2.2, fun h => ⟨inPar_zero' _, Subsingleton.elim _ _, h⟩⟩
  simp only [hy, zero_mul, pow_zero, inv_one, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem res_right_zero (n b : ℕ) (hb : b = 0) (χ : Gn g n → ℂ) (y₁ : Gn g n) (y₂ : Gn g b) :
    res n b χ y₁ y₂ = χ y₁ := by
  subst hb
  unfold res
  have hy : ∀ x : Gn g n, (InPar n (x : Mt g n) ∧ tl n (x : Mt g n) = (y₁ : Mt g n) ∧
      br n 0 (x : Mt g n) = (y₂ : Mt g 0)) ↔ x = y₁ := by
    intro x
    rw [tl_self_eq, Units.val_inj]
    exact ⟨fun h => h.2.1, fun h => ⟨inPar_self' _, h, Subsingleton.elim _ _⟩⟩
  simp only [hy, mul_zero, pow_zero, inv_one, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem res_mul_const (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) (c : ℂ) (y₁ : Gn g a) (y₂ : Gn g b) :
    res a b (fun x => χ x * c) y₁ y₂ = res a b χ y₁ y₂ * c := by
  unfold res
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

theorem res_const_mul (a b : ℕ) {n : ℕ} (χ : Gn g n → ℂ) (c : ℂ) (y₁ : Gn g a) (y₂ : Gn g b) :
    res a b (fun x => c * χ x) y₁ y₂ = c * res a b χ y₁ y₂ := by
  simp_rw [mul_comm c]
  exact res_mul_const a b χ c y₁ y₂

theorem hcT_sum {ι : Type} (s : Finset ι) (a b : ℕ) (Φ : ι → Gn g a → Gn g b → ℂ) (n : ℕ) (x : Gn g n) :
    hcT a b (fun u v => ∑ j ∈ s, Φ j u v) n x = ∑ j ∈ s, hcT a b (Φ j) n x := by
  unfold hcT
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem hcT_mul_const (a b : ℕ) (Φ : Gn g a → Gn g b → ℂ) (c : ℂ) (n : ℕ) (x : Gn g n) :
    hcT a b (fun u v => Φ u v * c) n x = hcT a b Φ n x * c := by
  unfold hcT
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> simp

theorem hcT_zero (a b : ℕ) (n : ℕ) (x : Gn g n) : hcT a b (fun (_ : Gn g a) (_ : Gn g b) => (0 : ℂ)) n x = 0 := by
  unfold hcT
  simp

theorem hcT_left_zero (i a : ℕ) (hi : i = 0) (ψ : Gn g a → ℂ) (hψ : IsClass ψ) (x : Gn g a) :
    hcT i a (fun (_ : Gn g i) v => ψ v) a x = ψ x := by
  subst hi
  unfold hcT
  simp only [inPar_zero', if_true, br_zero_eq, toG_coe]
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.card_univ]
  exact mean_of_isClass hψ x

theorem sum_subsets_fin_succ {β : Type} [AddCommMonoid β] {n : ℕ} (f : Finset (Fin (n + 1)) → β) :
    ∑ S, f S = ∑ S : Finset (Fin n),
      (f (S.map (Fin.succEmb n)) + f (insert 0 (S.map (Fin.succEmb n)))) := by
  have hu : (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 (Finset.univ.map (Fin.succEmb n)) := by
    ext x; cases x using Fin.cases <;> simp
  have h0 : (0 : Fin (n + 1)) ∉ Finset.univ.map (Fin.succEmb n) := by
    simp [Fin.succ_ne_zero]
  have hp : (Finset.univ.map (Fin.succEmb n)).powerset =
      (Finset.univ : Finset (Finset (Fin n))).map (Finset.mapEmbedding (Fin.succEmb n)).toEmbedding := by
    ext t; simp [Finset.subset_map_iff, eq_comm]
  rw [← Finset.powerset_univ, hu, Finset.sum_powerset_insert h0, hp,
    Finset.sum_map, Finset.sum_map, ← Finset.sum_add_distrib]
  rfl

theorem degL_sort_map (L : List (Pc g)) (J : Finset (Fin L.length)) :
    degL ((J.sort (· ≤ ·)).map L.get) = ∑ j ∈ J, (L.get j).1 := by
  unfold degL
  rw [List.map_map, ← List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rfl

theorem degL_eq_sum (L : List (Pc g)) : degL L = ∑ j : Fin L.length, (L.get j).1 := by
  unfold degL
  rw [← Fin.sum_univ_fun_getElem]
  simp

theorem sort_map_succ (p : Pc g) (L : List (Pc g)) (J : Finset (Fin L.length)) :
    ((J.map (Fin.succEmb L.length) : Finset (Fin (p :: L).length)).sort (· ≤ ·)).map (p :: L).get =
      (J.sort (· ≤ ·)).map L.get := by
  have h : (J.sort (· ≤ ·)).map (Fin.succEmb L.length) =
      ((J.map (Fin.succEmb L.length)).sort (· ≤ ·) : List (Fin (L.length + 1))) :=
    Finset.map_sort (Fin.succEmb L.length) J (· ≤ ·) (· ≤ ·) (fun a _ b _ => by simp)
  erw [← h]
  rw [List.map_map]
  congr 1

theorem sort_insert_map_succ (p : Pc g) (L : List (Pc g)) (J : Finset (Fin L.length)) :
    ((insert 0 (J.map (Fin.succEmb L.length)) : Finset (Fin (p :: L).length)).sort (· ≤ ·)).map (p :: L).get =
      p :: (J.sort (· ≤ ·)).map L.get := by
  rw [Finset.sort_insert (· ≤ ·) (fun b _ => Fin.zero_le b) (by simp [Fin.succ_ne_zero]), List.map_cons,
    sort_map_succ]
  rfl

theorem compl_map_succ {n : ℕ} (J : Finset (Fin n)) :
    (J.map (Fin.succEmb n))ᶜ = insert 0 (Jᶜ.map (Fin.succEmb n)) := by
  ext x; cases x using Fin.cases <;> simp [Fin.succ_ne_zero]

theorem compl_insert_map_succ {n : ℕ} (J : Finset (Fin n)) :
    (insert 0 (J.map (Fin.succEmb n)))ᶜ = Jᶜ.map (Fin.succEmb n) := by
  ext x; cases x using Fin.cases <;> simp [Fin.succ_ne_zero]

theorem collapse_mid {e a b : ℕ} (ρ : Gn g e → ℂ) (hρ : IsCusp ρ) (i c d : ℕ) (h0 : 0 < i) (he : i < e)
    (R : Gn g c → Gn g d → ℂ) (x : Gn g a) (y : Gn g b) :
    hcT i c (fun y₁ y₃ => hcT (e - i) d (fun y₂ y₄ => res i (e - i) ρ y₁ y₂ * R y₃ y₄) b y) a x = 0 := by
  simp only [GlobalTheory.T.harishChandraRestrictionTwoBlock_cuspidal_eq_zero g e i ρ hρ h0 he, zero_mul, hcT_zero]

theorem collapse_left {e a b : ℕ} (i c ei d : ℕ) (hi : i = 0) (hca : c = a) (hei : ei = e) (ρ : Gn g e → ℂ)
    {ι : Type} (s : Finset ι) (F G : ι → (n : ℕ) → Gn g n → ℂ) (hF : ∀ j n, IsClass (F j n))
    (x : Gn g a) (y : Gn g b) :
    hcT i c (fun y₁ y₃ => hcT ei d (fun y₂ y₄ => res i ei ρ y₁ y₂ * ∑ j ∈ s, F j c y₃ * G j d y₄) b y) a x =
      ∑ j ∈ s, F j a x * hc e d ρ (G j d) b y := by
  subst i; subst c; subst ei
  simp only [res_left_zero 0 e rfl]
  have key : ∀ y₃ : Gn g a, hcT e d (fun y₂ y₄ => ρ y₂ * ∑ j ∈ s, F j a y₃ * G j d y₄) b y =
      ∑ j ∈ s, hc e d ρ (G j d) b y * F j a y₃ := by
    intro y₃
    have : (fun (y₂ : Gn g e) (y₄ : Gn g d) => ρ y₂ * ∑ j ∈ s, F j a y₃ * G j d y₄) =
        fun y₂ y₄ => ∑ j ∈ s, (ρ y₂ * G j d y₄) * F j a y₃ := by
      funext y₂ y₄
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, hcT_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hcT_mul_const]; rfl
  simp only [key]
  refine (hcT_left_zero 0 a rfl (fun y₃ => ∑ j ∈ s, hc e d ρ (G j d) b y * F j a y₃) ?_ x).trans ?_
  · intro u v
    simp only [hF _ _ u v]
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem collapse_right {e a b : ℕ} (c ei d : ℕ) (hei : ei = 0) (hd : d = b) (ρ : Gn g e → ℂ)
    {ι : Type} (s : Finset ι) (F G : ι → (n : ℕ) → Gn g n → ℂ) (hG : ∀ j n, IsClass (G j n))
    (x : Gn g a) (y : Gn g b) :
    hcT e c (fun y₁ y₃ => hcT ei d (fun y₂ y₄ => res e ei ρ y₁ y₂ * ∑ j ∈ s, F j c y₃ * G j d y₄) b y) a x =
      ∑ j ∈ s, hc e c ρ (F j c) a x * G j b y := by
  subst ei; subst d
  simp only [res_right_zero e 0 rfl]
  have key : ∀ (y₁ : Gn g e) (y₃ : Gn g c),
      hcT 0 b (fun (_ : Gn g 0) y₄ => ρ y₁ * ∑ j ∈ s, F j c y₃ * G j b y₄) b y =
        ∑ j ∈ s, (ρ y₁ * F j c y₃) * G j b y := by
    intro y₁ y₃
    refine (hcT_left_zero 0 b rfl (fun y₄ => ρ y₁ * ∑ j ∈ s, F j c y₃ * G j b y₄) ?_ y).trans ?_
    · intro u v
      simp only [hG _ _ u v]
    · simp only [Finset.mul_sum, mul_assoc]
  simp only [key]
  rw [hcT_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [hcT_mul_const]; rfl

theorem main : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (a b : ℕ), degL L = a + b → (∀ p ∈ L, IsCusp p.2) →
    ∀ x y, res a b (hcL L (a + b)) x y =
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ i ∈ I, (L.get i).1 = a),
        hcL ((I.sort (· ≤ ·)).map L.get) a x * hcL ((Iᶜ.sort (· ≤ ·)).map L.get) b y := by
  intro g _ L
  induction L with
  | nil =>
    intro a b hdeg _ x y
    have hab : a + b = 0 := by simpa [degL] using hdeg.symm
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    rw [hcL_nil, res_left_zero 0 (0 + 0) rfl (fun _ => (1 : ℂ)) x y]
    have h0 : ∀ l : List (Fin 0), l.map ([] : List (Pc g)).get = [] := by
      intro l
      cases l with
      | nil => rfl
      | cons i _ => exact i.elim0
    simp [h0, hcL_nil]
  | cons p L ih =>
    intro a b hdeg hcusp x y
    obtain ⟨e, ρ⟩ := p
    have hdeg' : e + degL L = a + b := by simpa [degL] using hdeg
    have hρ : IsCusp ρ := hcusp ⟨e, ρ⟩ List.mem_cons_self
    have hL : ∀ p ∈ L, IsCusp p.2 := fun p hp => hcusp p (List.mem_cons_of_mem _ hp)
    have hρc : IsClass ρ := isClass_of_isIrr hρ.2.1
    have he0 : 0 < e := hρ.1
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.T.mackey_formula_harishChandra_restriction_induction g e (degL L) a b (a + b) hdeg'.symm rfl (fun u v => ρ u * hcL L (degL L) v)
      (fun v u w => by simp only [hρc u w]) (fun u v w => by simp only [isClass_hcL L (degL L) v w]) x y]
    simp only [res_const_mul, res_mul_const]
    set S := (Finset.range (e + 1)).filter (fun i => i ≤ a ∧ a - i ≤ degL L) with hS
    rw [← Finset.sum_filter_add_sum_filter_not S (fun i => i = 0),
      ← Finset.sum_filter_add_sum_filter_not (S.filter fun i => ¬ i = 0) (fun i => i = e)]
    rw [Finset.sum_eq_zero (s := (S.filter fun i => ¬ i = 0).filter fun i => ¬ i = e), add_zero]
    swap
    · intro i hi
      simp only [hS, Finset.mem_filter, Finset.mem_range] at hi
      exact collapse_mid ρ hρ i (a - i) (degL L - (a - i)) (by omega) (by omega) _ x y
    rw [Finset.filter_eq', Finset.filter_eq']
    rw [Finset.sum_filter]
    erw [sum_subsets_fin_succ]
    rw [Finset.sum_add_distrib]
    have hget : ∀ j : Fin L.length, (⟨e, ρ⟩ :: L).get (Fin.succEmb L.length j) = L.get j := fun j => rfl
    have hsum : ∀ J : Finset (Fin L.length), ∑ j ∈ J, (L.get j).1 ≤ degL L := fun J => by
      rw [degL_eq_sum L]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ J)
    have hcompl : ∀ J : Finset (Fin L.length), ∑ j ∈ Jᶜ, (L.get j).1 = degL L - ∑ j ∈ J, (L.get j).1 := fun J => by
      rw [degL_eq_sum L, ← Finset.sum_compl_add_sum J]
      omega
    congr 1
    · by_cases h0 : a ≤ degL L
      · rw [if_pos (by simp only [hS, Finset.mem_filter, Finset.mem_range]; omega), Finset.sum_singleton]
        have ih' := ih (a - 0) (degL L - (a - 0)) (by omega) hL
        rw [show a - 0 + (degL L - (a - 0)) = degL L by omega] at ih'
        simp only [ih']
        refine (collapse_left 0 (a - 0) (e - 0) (degL L - (a - 0)) rfl rfl rfl ρ
          (Finset.univ.filter fun I : Finset (Fin L.length) => ∑ i ∈ I, (L.get i).1 = a - 0)
          (fun (J : Finset (Fin L.length)) (n : ℕ) => hcL (List.map L.get (J.sort (· ≤ ·))) n)
          (fun (J : Finset (Fin L.length)) (n : ℕ) => hcL (List.map L.get (Jᶜ.sort (· ≤ ·))) n)
          (fun J n => isClass_hcL _ _) x y).trans ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [Finset.sum_map, hget]
        by_cases hJ : ∑ j ∈ J, (L.get j).1 = a
        · rw [if_pos (by omega), if_pos hJ]
          erw [sort_map_succ, compl_map_succ, sort_insert_map_succ]
          rw [hcL_cons, degL_sort_map, hcompl, hJ]
          rfl
        · rw [if_neg (by omega), if_neg hJ]
      · rw [if_neg (by simp only [hS, Finset.mem_filter, Finset.mem_range]; omega), Finset.sum_empty]
        refine (Finset.sum_eq_zero fun J _ => ?_).symm
        simp only [Finset.sum_map, hget]
        rw [if_neg]
        have := hsum J
        omega
    · by_cases he : e ≤ a
      · rw [if_pos (by simp only [hS, Finset.mem_filter, Finset.mem_range]; omega), Finset.sum_singleton]
        have ih' := ih (a - e) (degL L - (a - e)) (by omega) hL
        rw [show a - e + (degL L - (a - e)) = degL L by omega] at ih'
        simp only [ih']
        refine (collapse_right (a - e) (e - e) (degL L - (a - e)) (Nat.sub_self e) (by omega) ρ
          (Finset.univ.filter fun I : Finset (Fin L.length) => ∑ i ∈ I, (L.get i).1 = a - e)
          (fun (J : Finset (Fin L.length)) (n : ℕ) => hcL (List.map L.get (J.sort (· ≤ ·))) n)
          (fun (J : Finset (Fin L.length)) (n : ℕ) => hcL (List.map L.get (Jᶜ.sort (· ≤ ·))) n)
          (fun J n => isClass_hcL _ _) x y).trans ?_
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_insert (by simp [Fin.succ_ne_zero])]
        simp only [Finset.sum_map, hget]
        by_cases hJ : ∑ j ∈ J, (L.get j).1 = a - e
        · rw [if_pos hJ, if_pos (by
            show e + ∑ j ∈ J, (L.get j).1 = a
            omega)]
          erw [sort_insert_map_succ, compl_insert_map_succ, sort_map_succ]
          rw [hcL_cons, degL_sort_map, hJ]
        · rw [if_neg hJ, if_neg (by
            show ¬ e + ∑ j ∈ J, (L.get j).1 = a
            omega)]
      · rw [if_neg (by simp only [hS, Finset.mem_filter, Finset.mem_range]; omega), Finset.sum_empty]
        refine (Finset.sum_eq_zero fun J _ => ?_).symm
        rw [Finset.sum_insert (by simp [Fin.succ_ne_zero])]
        rw [if_neg]
        show ¬ e + _ = a
        omega

end GlobalTheory.GLq.ResCuspProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionCuspidalProductSumSubsetStatement
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraRestriction_cuspidal_product_sum_subsets : ∀ (g : ℕ) [Fact g.Prime] (L : List (Pc g)) (a b : ℕ), degL L = a + b → (∀ p ∈ L, IsCusp p.2) → ∀ x y, res a b (hcL L (a + b)) x y = ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ i ∈ I, (L.get i).1 = a), hcL ((I.sort (· ≤ ·)).map L.get) a x * hcL ((Iᶜ.sort (· ≤ ·)).map L.get) b y := by
  first | exact @GlobalTheory.GLq.ResCuspProd.main | exact GlobalTheory.GLq.ResCuspProd.main | (intros; apply GlobalTheory.GLq.ResCuspProd.main <;> assumption)
end
