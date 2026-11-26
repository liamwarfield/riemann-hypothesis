module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CvRhoOfParts

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.DetRowsZero
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL

variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}

def rel (E : Fin n → Fin n → A) (a b c d : Fin n) : A :=
  E a b * E c d - E c d * E a b - ((if b = c then E a d else 0) - (if d = a then E c b else 0))

theorem two_formal (E : Fin n → Fin n → A) (x y : ℂ) (hxy : x - y = 1) (p q c d : Fin n) :
    Tm E x p c * Tm E y q d - Tm E x q c * Tm E y p d + Tm E x p d * Tm E y q c
      - Tm E x q d * Tm E y p c = rel E p c q d + rel E p d q c := by
  obtain rfl : y = x - 1 := by linear_combination -hxy
  unfold rel
  simp only [eq_comm (a := c) (b := q), eq_comm (a := d) (b := p), eq_comm (a := d) (b := q),
    eq_comm (a := c) (b := p)]
  rw [ite_zero_eq_ite_smul (q = c) (E p d), ite_zero_eq_ite_smul (p = d) (E q c), ite_zero_eq_ite_smul (q = d) (E p c), ite_zero_eq_ite_smul (p = c) (E q d)]
  simp only [shiftedGenerator_eq_ite_smul_add, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  rw [ite_zero_eq_mul_ite (p = c) x, ite_zero_eq_mul_ite (q = d) (x - 1), ite_zero_eq_mul_ite (q = c) x, ite_zero_eq_mul_ite (p = d) (x - 1),
    ite_zero_eq_mul_ite (p = d) x, ite_zero_eq_mul_ite (q = c) (x - 1), ite_zero_eq_mul_ite (q = d) x, ite_zero_eq_mul_ite (p = c) (x - 1)]
  module

theorem four_formal {t : ℕ} (f₁ f₂ f₃ f₄ : Fin t → A) (i : ℕ) (hi : i + 1 < t)
    (h₂ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₂ k = f₁ k)
    (h₃ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₃ k = f₁ k)
    (h₄ : ∀ k : Fin t, (k : ℕ) ≠ i → (k : ℕ) ≠ i + 1 → f₄ k = f₁ k) :
    (List.ofFn f₁).prod - (List.ofFn f₂).prod + (List.ofFn f₃).prod - (List.ofFn f₄).prod =
      ((List.ofFn f₁).take i).prod * (f₁ ⟨i, by omega⟩ * f₁ ⟨i + 1, hi⟩ - f₂ ⟨i, by omega⟩ * f₂ ⟨i + 1, hi⟩
        + f₃ ⟨i, by omega⟩ * f₃ ⟨i + 1, hi⟩ - f₄ ⟨i, by omega⟩ * f₄ ⟨i + 1, hi⟩) *
        ((List.ofFn f₁).drop (i + 2)).prod := by
  rw [prod_ofFn_split_pair f₁ i hi, prod_ofFn_split_pair f₂ i hi, prod_ofFn_split_pair f₃ i hi, prod_ofFn_split_pair f₄ i hi,
    take_ofFn_congr f₂ f₁ i (fun k hk => h₂ k (by omega) (by omega)),
    take_ofFn_congr f₃ f₁ i (fun k hk => h₃ k (by omega) (by omega)),
    take_ofFn_congr f₄ f₁ i (fun k hk => h₄ k (by omega) (by omega)),
    drop_ofFn_congr f₂ f₁ (i + 2) (fun k hk => h₂ k (by omega) (by omega)),
    drop_ofFn_congr f₃ f₁ (i + 2) (fun k hk => h₃ k (by omega) (by omega)),
    drop_ofFn_congr f₄ f₁ (i + 2) (fun k hk => h₄ k (by omega) (by omega)), sandwich_alternating_sum]

def fac (E : Fin n → Fin n → A) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin t)) : Fin t → A :=
  fun k => Tm E (u - (k : ℂ)) (a (σ k)) (b k)

def Lt (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (i : Fin m) : A :=
  ((List.ofFn (fac E a b u σ)).take (i : ℕ)).prod

def Rt (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (u : ℂ) (σ : Equiv.Perm (Fin (m + 1)))
    (i : Fin m) : A :=
  ((List.ofFn (fac E a b u σ)).drop ((i : ℕ) + 2)).prod

def Md (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (σ : Equiv.Perm (Fin (m + 1))) (i : Fin m) : A :=
  rel E (a (σ i.castSucc)) (b i.castSucc) (a (σ i.succ)) (b i.succ) +
    rel E (a (σ i.castSucc)) (b i.succ) (a (σ i.succ)) (b i.castSucc)

theorem key_formal (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ)
    (σ : Equiv.Perm (Fin (m + 1))) :
    exchangeTwo_self_eq_one E a b u σ - exchangeTwo_self_eq_one E a b u (σ * Equiv.swap i.castSucc i.succ)
      + exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u σ
      - exchangeTwo_self_eq_one E a (b ∘ Equiv.swap i.castSucc i.succ) u (σ * Equiv.swap i.castSucc i.succ) =
      Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i := by
  have hs : ∀ k : Fin (m + 1), (k : ℕ) ≠ (i : ℕ) → (k : ℕ) ≠ (i : ℕ) + 1 →
      Equiv.swap i.castSucc i.succ k = k := by
    intro k h1 h2
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; apply h1; rw [h]; simp
    · intro h; apply h2; rw [h]; simp
  unfold exchangeTwo_self_eq_one Lt Rt
  rw [four_formal _ _ _ _ (i : ℕ) (by omega)]
  · congr 2
    have e1 : (⟨(i : ℕ), by omega⟩ : Fin (m + 1)) = i.castSucc := rfl
    have e2 : (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 1)) = i.succ := rfl
    simp only [e1, e2, Equiv.Perm.mul_apply, Function.comp_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Md]
    exact two_formal E _ _ (by simp) _ _ _ _
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]
  · intro k h1 h2; simp [hs k h1 h2]
  · intro k h1 h2; simp [Equiv.Perm.mul_apply, hs k h1 h2]

theorem adj_formal (E : Fin n → Fin n → A) {m : ℕ} (a b : Fin (m + 1) → Fin n) (i : Fin m) (u : ℂ) :
    (2 : ℂ) • (qminor E a (b ∘ Equiv.swap i.castSucc i.succ) u + qminor E a b u) =
      ∑ σ : Equiv.Perm (Fin (m + 1)),
        ((Equiv.Perm.sign σ : ℤ) : A) * (Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i) := by
  set s := Equiv.swap i.castSucc i.succ with hs_def
  have hsgn : Equiv.Perm.sign s = -1 := Equiv.Perm.sign_swap (by simp [Fin.ext_iff])
  set G : Equiv.Perm (Fin (m + 1)) → A := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : A) * (exchangeTwo_self_eq_one E a (b ∘ s) u σ + exchangeTwo_self_eq_one E a b u σ) with hG
  have hsum : qminor E a (b ∘ s) u + qminor E a b u = ∑ σ, G σ := by
    rw [quantumMinor_eq_sum_term, quantumMinor_eq_sum_term, ← Finset.sum_add_distrib]
    simp only [hG, mul_add]
  have hre : ∑ σ, G (σ * s) = ∑ σ, G σ := Fintype.sum_equiv (Equiv.mulRight s) _ _ (fun σ => rfl)
  have hpair : ∀ σ, G σ + G (σ * s) =
      ((Equiv.Perm.sign σ : ℤ) : A) * (Lt E a b u σ i * Md E a b σ i * Rt E a b u σ i) := by
    intro σ
    simp only [hG, Equiv.Perm.sign_mul, hsgn, mul_neg, mul_one, Units.val_neg, Int.cast_neg]
    have k := key_formal E a b i u σ
    rw [← hs_def] at k
    rw [← k]
    noncomm_ring
  rw [hsum, two_smul, ← Finset.sum_congr rfl (fun σ _ => hpair σ), Finset.sum_add_distrib, hre]

def Ead (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : A :=
  ∑ a, ∑ b, (P a c * Q d b) • E a b

theorem Tm_Ead (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) (v : ℂ) (c d : Fin n) :
    Tm (Ead E P Q) v c d = ∑ a, ∑ b, (P a c * Q d b) • Tm E v a b := by
  have h1 : ∀ a, ∑ b, (P a c * Q d b) • (if a = b then algebraMap ℂ A v else 0) =
      (P a c * Q d a) • algebraMap ℂ A v := by
    intro a; simp [smul_ite]
  have h2 : ∑ a, P a c * Q d a = if c = d then 1 else 0 := by
    have := congrFun (congrFun hQP d) c
    simp only [Matrix.mul_apply, Matrix.one_apply] at this
    rw [show (∑ a, P a c * Q d a) = ∑ a, Q d a * P a c from Finset.sum_congr rfl fun a _ => mul_comm _ _, this]
    simp [eq_comm]
  unfold Tm Ead
  simp only [smul_add, Finset.sum_add_distrib, h1]
  rw [← Finset.sum_smul, h2]
  split_ifs <;> simp

theorem prod_expand {X : Type*} [Fintype X] :
    ∀ (t : ℕ) (c : Fin t → X → ℂ) (B : Fin t → X → A),
      (List.ofFn fun j => ∑ x, c j x • B j x).prod =
        ∑ φ : Fin t → X, (∏ j, c j (φ j)) • (List.ofFn fun j => B j (φ j)).prod := by
  intro t
  induction t with
  | zero => intro c B; simp
  | succ t ih =>
    intro c B
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => c j.succ) (fun j => B j.succ), Finset.sum_mul]
    rw [← (Fin.consEquiv fun _ : Fin (t + 1) => X).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ,
      List.prod_cons, smul_mul_smul_comm]

theorem rowsum_det {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (α : Fin t → Fin n) :
    ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, P (α j) (e (σ j)) =
      (Matrix.of fun i j : Fin t => P (α i) (e j)).det := by
  rw [Matrix.det_apply]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin t))) _ _ (fun σ => ?_)
  simp only [Equiv.inv_apply, Equiv.Perm.sign_inv, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  congr 1
  exact Fintype.prod_equiv σ _ _ (fun j => by simp)

theorem det_rows_perm {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (γ : Equiv.Perm (Fin t)) :
    (Matrix.of fun i j : Fin t => P (e (γ i)) (e j)).det = ((Equiv.Perm.sign γ : ℤ) : ℂ) * P.det := by
  have : (Matrix.of fun i j : Fin t => P (e (γ i)) (e j)) = (P.submatrix e e).submatrix γ id := by
    ext i j; simp
  rw [this, Matrix.det_permute, Matrix.det_submatrix_equiv_self]

theorem det_rows_zero {t : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (e : Fin t ≃ Fin n) (α : Fin t → Fin n)
    (hα : ¬ Function.Injective α) : (Matrix.of fun i j : Fin t => P (α i) (e j)).det = 0 := by
  simp only [Function.Injective, not_forall] at hα
  obtain ⟨i, i', h, hne⟩ := hα
  exact Matrix.det_zero_of_row_eq hne (by funext j; simp [h])

theorem sum_inj {M : Type*} [AddCommMonoid M] {t : ℕ} (e : Fin t ≃ Fin n) (F : (Fin t → Fin n) → M)
    (hF : ∀ α, ¬ Function.Injective α → F α = 0) :
    ∑ α, F α = ∑ γ : Equiv.Perm (Fin t), F (e ∘ γ) := by
  classical
  have himg : ∑ α ∈ (Finset.univ.image fun γ : Equiv.Perm (Fin t) => (e ∘ γ : Fin t → Fin n)), F α = ∑ α, F α := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro α _ hα
    apply hF
    intro hinj
    apply hα
    have hi : Function.Injective (e.symm ∘ α) := e.symm.injective.comp hinj
    have hs : Function.Surjective (e.symm ∘ α) := Finite.injective_iff_surjective.mp hi
    refine Finset.mem_image.mpr ⟨Equiv.ofBijective _ ⟨hi, hs⟩, Finset.mem_univ _, ?_⟩
    funext j
    show e ((e.symm ∘ α) j) = α j
    simp
  rw [← himg, Finset.sum_image]
  intro γ₁ _ γ₂ _ h
  exact Equiv.ext fun j => by have := congrFun h j; simpa using this

theorem qminor_Ead (E : Fin n → Fin n → A) {P Q : Matrix (Fin n) (Fin n) ℂ} (hQP : Q * P = 1) {t : ℕ}
    (e : Fin t ≃ Fin n) (u : ℂ) :
    qminor (Ead E P Q) e e u = P.det • ∑ β : Fin t → Fin n, (∏ j, Q (e j) (β j)) • qminor E e β u := by
  have step1 : ∀ σ : Equiv.Perm (Fin t),
      (List.ofFn fun k : Fin t => Tm (Ead E P Q) (u - (k : ℂ)) (e (σ k)) (e k)).prod =
        ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
    intro σ
    calc (List.ofFn fun k : Fin t => Tm (Ead E P Q) (u - (k : ℂ)) (e (σ k)) (e k)).prod
        = (List.ofFn fun j : Fin t => ∑ x : Fin n × Fin n,
            (P x.1 (e (σ j)) * Q (e j) x.2) • Tm E (u - (j : ℂ)) x.1 x.2).prod := by
          simp only [Tm_Ead E hQP, ← Finset.sum_product', Finset.univ_product_univ]
      _ = ∑ φ : Fin t → Fin n × Fin n, (∏ j, (P (φ j).1 (e (σ j)) * Q (e j) (φ j).2)) •
            (List.ofFn fun j => Tm E (u - (j : ℂ)) (φ j).1 (φ j).2).prod :=
          by exact prod_expand (X := Fin n × Fin n) t _ _
      _ = _ := by
          rw [← (Equiv.arrowProdEquivProdArrow (Fin t) (fun _ => Fin n) (fun _ => Fin n)).symm.sum_comp, Fintype.sum_prod_type,
            Finset.sum_comm]
          refine Finset.sum_congr rfl fun β _ => Finset.sum_congr rfl fun α _ => ?_
          simp [Equiv.arrowProdEquivProdArrow, Finset.prod_mul_distrib]
  have inner : ∀ β α : Fin t → Fin n,
      ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
        (((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod) =
      ((Matrix.of fun i j : Fin t => P (α i) (e j)).det * ∏ j, Q (e j) (β j)) •
          (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
    intro β α
    rw [← rowsum_det P e α, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [show ((Equiv.Perm.sign σ : ℤ) : A) = algebraMap ℂ A ((Equiv.Perm.sign σ : ℤ) : ℂ) by simp,
      ← Algebra.smul_def, smul_smul, mul_assoc]
  calc qminor (Ead E P Q) e e u
      = ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) * ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
        unfold qminor; simp only [step1]
    _ = ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n, ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : A) *
          (((∏ j, P (α j) (e (σ j))) * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun β _ => Finset.sum_comm
    _ = ∑ β : Fin t → Fin n, ∑ α : Fin t → Fin n,
          ((Matrix.of fun i j : Fin t => P (α i) (e j)).det * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (α k) (β k)).prod := by
        simp only [inner]
    _ = ∑ β : Fin t → Fin n, ∑ γ : Equiv.Perm (Fin t),
          ((Matrix.of fun i j : Fin t => P (e (γ i)) (e j)).det * ∏ j, Q (e j) (β j)) •
            (List.ofFn fun k : Fin t => Tm E (u - (k : ℂ)) (e (γ k)) (β k)).prod := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [sum_inj e _ (fun α hα => by rw [det_rows_zero P e α hα, zero_mul, zero_smul])]
        rfl
    _ = ∑ β : Fin t → Fin n, P.det • ((∏ j, Q (e j) (β j)) • qminor E e β u) := by
        refine Finset.sum_congr rfl fun β _ => ?_
        unfold qminor
        rw [Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [det_rows_perm P e γ,
          show ((Equiv.Perm.sign γ : ℤ) : A) = algebraMap ℂ A ((Equiv.Perm.sign γ : ℤ) : ℂ) by simp,
          ← Algebra.smul_def, smul_smul, smul_smul]
        congr 1
        ring
    _ = _ := by rw [Finset.smul_sum]

end Formalism.FourierDecayAlt.P.JFxE
end
end

open Matrix Finset
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.JFxE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

abbrev Ix (k r : ℕ) := Fin (2 * r + k + 1) × Fin (2 * r + k + 1)

abbrev VV (k r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] := List (Ix k r) → (Mat k r → E)

abbrev AA (k r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] := Module.End ℂ (VV k r E)

def ell (x : Ix k r) : AA k r E := LinearMap.funLeft ℂ (Mat k r → E) (fun w : List (Ix k r) => w ++ [x])

theorem ell_apply (x : Ix k r) (Φ : VV k r E) (w : List (Ix k r)) : ell x Φ w = Φ (w ++ [x]) := rfl

def Lf (k r : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : Fin (2 * r + k + 1)) : AA k r E :=
  ell (a, b)

def Rep (d : ℕ) (a : AA k r E) : Prop :=
  ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d) ∧
    ∀ Φ w, a Φ w = (L.map fun p => p.1 • Φ (w ++ p.2)).sum

section RepLemmas

theorem Rep.mono {d d' : ℕ} (h : d ≤ d') {a : AA k r E} (ha : Rep d a) : Rep d' a := by
  obtain ⟨L, hL, h'⟩ := ha
  exact ⟨L, fun p hp => (hL p hp).trans h, h'⟩

theorem rep_ell (x : Ix k r) : Rep 1 (ell x : AA k r E) := by
  exact ⟨[(1, [x])], by simp, fun Φ w => by simp [ell_apply]⟩

theorem rep_add {d : ℕ} {a b : AA k r E} (ha : Rep d a) (hb : Rep d b) : Rep d (a + b) := by
  obtain ⟨La, hLa, ha'⟩ := ha
  obtain ⟨Lb, hLb, hb'⟩ := hb
  refine ⟨La ++ Lb, fun p hp => ?_, fun Φ w => ?_⟩
  · rcases List.mem_append.mp hp with h | h
    exacts [hLa p h, hLb p h]
  · rw [LinearMap.add_apply, Pi.add_apply, ha', hb', List.map_append, List.sum_append]

theorem rep_smul {d : ℕ} (c : ℂ) {a : AA k r E} (ha : Rep d a) : Rep d (c • a) := by
  obtain ⟨L, hL, h⟩ := ha
  refine ⟨L.map fun p => (c * p.1, p.2), ?_, fun Φ w => ?_⟩
  · intro p hp
    simp only [List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact hL q hq
  · rw [LinearMap.smul_apply, Pi.smul_apply, h, List.smul_sum]
    simp only [List.map_map, Function.comp_def, mul_smul]

theorem rep_sub {d : ℕ} {a b : AA k r E} (ha : Rep d a) (hb : Rep d b) : Rep d (a - b) := by
  have h1 := rep_add ha (rep_smul (-1) hb)
  first
    | (simpa [neg_one_smul] using h1)
    | (simpa [sub_eq_add_neg, neg_one_smul] using h1)

private theorem exists_word_expansion_length_le_add {d e : ℕ} {b : AA k r E} (Lb : List (ℂ × List (Ix k r)))
    (hLb : ∀ q ∈ Lb, q.2.length ≤ e) (hb : ∀ Φ w, b Φ w = (Lb.map fun q => q.1 • Φ (w ++ q.2)).sum) :
    ∀ La : List (ℂ × List (Ix k r)), (∀ p ∈ La, p.2.length ≤ d) →
      ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d + e) ∧
        ∀ Φ w, (La.map fun p => p.1 • (b Φ) (w ++ p.2)).sum = (L.map fun p => p.1 • Φ (w ++ p.2)).sum := by
  intro La
  induction La with
  | nil => intro _; exact ⟨[], by simp, fun _ _ => by simp⟩
  | cons p La ih =>
    intro hLa
    obtain ⟨L, hL, hL'⟩ := ih (fun q hq => hLa q (by simp [hq]))
    refine ⟨(Lb.map fun q => (p.1 * q.1, p.2 ++ q.2)) ++ L, ?_, ?_⟩
    · intro q hq
      simp only [List.mem_append, List.mem_map] at hq
      rcases hq with ⟨q', hq', rfl⟩ | hq
      · have h1 := hLa p (by simp)
        have h2 := hLb q' hq'
        simp only [List.length_append]
        omega
      · exact hL q hq
    · intro Φ w
      rw [List.map_cons, List.sum_cons, hL' Φ w, List.map_append, List.sum_append, hb, List.smul_sum]
      congr 1
      simp only [List.map_map, Function.comp_def, mul_smul, List.append_assoc]

theorem rep_mul {d e : ℕ} {a b : AA k r E} (ha : Rep d a) (hb : Rep e b) : Rep (d + e) (a * b) := by
  obtain ⟨La, hLa, ha'⟩ := ha
  obtain ⟨Lb, hLb, hb'⟩ := hb
  obtain ⟨L, hL, hL'⟩ := exists_word_expansion_length_le_add Lb hLb hb' La hLa
  refine ⟨L, hL, fun Φ w => ?_⟩
  show a (b Φ) w = _
  rw [ha', hL']

end RepLemmas

def HC (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (m : ℕ) (f : Mat k r → E), CkOn ((m + 1 : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Eop a b f)

def HL (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (f f₂ : Mat k r → E), (∀ g ∈ GV k r, f g = f₂ g) → ∀ g ∈ GV k r, Eop a b f g = Eop a b f₂ g

def HA (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (f f₂ : Mat k r → E), CkOn 1 (GV k r) f → CkOn 1 (GV k r) f₂ → ∀ g ∈ GV k r,
    Eop a b (fun x => f x + f₂ x) g = Eop a b f g + Eop a b f₂ g

def HS (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b (c : ℂ) (f : Mat k r → E), CkOn 1 (GV k r) f → ∀ g ∈ GV k r, Eop a b (fun x => c • f x) g = c • Eop a b f g

def HGl (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) : Prop :=
  ∀ a b c d (f : Mat k r → E), CkOn 2 (GV k r) f → ∀ g ∈ GV k r,
    Eop a b (Eop c d f) g - Eop c d (Eop a b f) g =
      (if b = c then Eop a d f g else 0) - (if d = a then Eop c b f g else 0)

def Fw (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (w : List (Ix k r))
    (f : Mat k r → E) : Mat k r → E :=
  w.foldr (fun x φ => Eop x.1 x.2 φ) f

def Phi (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (f : Mat k r → E) :
    VV k r E := fun w => Fw Eop w f

def ev (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E)) (a : AA k r E)
    (f : Mat k r → E) : Mat k r → E := a (Phi Eop f) []

section Words

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem Fw_append (w q : List (Ix k r)) (f : Mat k r → E) : Fw Eop (w ++ q) f = Fw Eop w (Fw Eop q f) := by
  simp [Fw, List.foldr_append]

theorem Fw_ck (hC : HC Eop) : ∀ (w : List (Ix k r)) (m : ℕ) (f : Mat k r → E),
    CkOn ((m + w.length : ℕ) : ℕ∞) (GV k r) f → CkOn (m : ℕ∞) (GV k r) (Fw Eop w f) := by
  intro w
  induction w with
  | nil => intro m f hf; simpa [Fw] using hf
  | cons x w ih =>
    intro m f hf
    have h1 : CkOn (((m + 1) + w.length : ℕ) : ℕ∞) (GV k r) f := by
      have e : (m + 1) + w.length = m + (x :: w).length := by simp only [List.length_cons]; omega
      rw [e]; exact hf
    exact hC x.1 x.2 m _ (ih (m + 1) f h1)

theorem ck_mono' {m m' : ℕ} (h : m ≤ m') {f : Mat k r → E} (hf : CkOn ((m' : ℕ) : ℕ∞) (GV k r) f) :
    CkOn ((m : ℕ) : ℕ∞) (GV k r) f := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hcd, hfe⟩ := hf g₀ hg₀
  refine ⟨U, f', hU, hg, hcd.of_le ?_, hfe⟩
  first | exact_mod_cast h | exact WithTop.coe_le_coe.mpr (Nat.cast_le.mpr h) | (norm_cast)

theorem Fw_add (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) : ∀ (w : List (Ix k r)) (f f₂ : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂ →
    ∀ g ∈ GV k r, Fw Eop w (fun x => f x + f₂ x) g = Fw Eop w f g + Fw Eop w f₂ g := by
  intro w
  induction w with
  | nil => intro f f₂ _ _ g _; rfl
  | cons x w ih =>
    intro f f₂ hf hf₂ g hg
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f := ck_mono' (by simp) hf
    have hf₂' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f₂ := ck_mono' (by simp) hf₂
    have e : 1 + w.length = (x :: w).length := by simp only [List.length_cons]; omega
    have c1 : CkOn 1 (GV k r) (Fw Eop w f) := by
      have h' : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f := by rw [e]; exact hf
      simpa using Fw_ck Eop hC w 1 f h'
    have c2 : CkOn 1 (GV k r) (Fw Eop w f₂) := by
      have h' : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f₂ := by rw [e]; exact hf₂
      simpa using Fw_ck Eop hC w 1 f₂ h'
    show Eop x.1 x.2 (Fw Eop w (fun y => f y + f₂ y)) g =
      Eop x.1 x.2 (Fw Eop w f) g + Eop x.1 x.2 (Fw Eop w f₂) g
    rw [hL x.1 x.2 _ (fun y => Fw Eop w f y + Fw Eop w f₂ y) (ih f f₂ hf' hf₂') g hg]
    exact hA x.1 x.2 _ _ c1 c2 g hg

theorem Fw_smul (hC : HC Eop) (hL : HL Eop) (hS : HS Eop) : ∀ (w : List (Ix k r)) (c : ℂ) (f : Mat k r → E),
    CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f → ∀ g ∈ GV k r, Fw Eop w (fun x => c • f x) g = c • Fw Eop w f g := by
  intro w
  induction w with
  | nil => intro c f _ g _; rfl
  | cons x w ih =>
    intro c f hf g hg
    have hf' : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) f := ck_mono' (by simp) hf
    have e : 1 + w.length = (x :: w).length := by simp only [List.length_cons]; omega
    have c1 : CkOn 1 (GV k r) (Fw Eop w f) := by
      have h' : CkOn ((1 + w.length : ℕ) : ℕ∞) (GV k r) f := by rw [e]; exact hf
      simpa using Fw_ck Eop hC w 1 f h'
    show Eop x.1 x.2 (Fw Eop w (fun y => c • f y)) g = c • Eop x.1 x.2 (Fw Eop w f) g
    rw [hL x.1 x.2 _ (fun y => c • Fw Eop w f y) (ih c f hf') g hg]
    exact hS x.1 x.2 c _ c1 g hg

theorem Fw_zero (hC : HC Eop) (hL : HL Eop) (hS : HS Eop) (w : List (Ix k r)) :
    ∀ g ∈ GV k r, Fw Eop w (fun _ => (0 : E)) g = 0 := by
  intro g hg
  have h0 : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) (fun _ : Mat k r => (0 : E)) :=
    fun g₀ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
  have h1 := Fw_smul Eop hC hL hS w 0 (fun _ => (0 : E)) h0 g hg
  simpa using h1

theorem ck_lsum {m : ℕ∞} (L : List (ℂ × (Mat k r → E))) (h : ∀ p ∈ L, CkOn m (GV k r) p.2) :
    CkOn m (GV k r) (fun x => (L.map fun p => p.1 • p.2 x).sum) := by
  induction L with
  | nil =>
    intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => by simp⟩
  | cons p L ih =>
    intro g₀ hg₀
    obtain ⟨U1, f1, hU1, hg1, hc1, he1⟩ := h p (by simp) g₀ hg₀
    obtain ⟨U2, f2, hU2, hg2, hc2, he2⟩ := ih (fun q hq => h q (by simp [hq])) g₀ hg₀
    refine ⟨U1 ∩ U2, fun x => p.1 • f1 x + f2 x, hU1.inter hU2, ⟨hg1, hg2⟩,
      ((hc1.mono Set.inter_subset_left).const_smul p.1).add (hc2.mono Set.inter_subset_right), ?_⟩
    intro g hg hgG
    simp only [List.map_cons, List.sum_cons]
    rw [he1 g hg.1 hgG]
    congr 1
    exact he2 g hg.2 hgG

theorem Fw_lsum (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) (w : List (Ix k r)) :
    ∀ (L : List (ℂ × (Mat k r → E))), (∀ p ∈ L, CkOn ((w.length : ℕ) : ℕ∞) (GV k r) p.2) →
    ∀ g ∈ GV k r, Fw Eop w (fun x => (L.map fun p => p.1 • p.2 x).sum) g = (L.map fun p => p.1 • Fw Eop w p.2 g).sum := by
  intro L
  induction L with
  | nil =>
    intro _ g hg
    simp only [List.map_nil, List.sum_nil]
    exact Fw_zero Eop hC hL hS w g hg
  | cons p L ih =>
    intro h g hg
    have hL' : ∀ q ∈ L, CkOn ((w.length : ℕ) : ℕ∞) (GV k r) q.2 := fun q hq => h q (by simp [hq])
    have hs : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) (fun x => p.1 • p.2 x) := by
      intro g₀ hg₀
      obtain ⟨U, f', hU, hg', hc, he⟩ := h p (by simp) g₀ hg₀
      exact ⟨U, fun x => p.1 • f' x, hU, hg', hc.const_smul p.1, fun g hg hgG => by simp only [he g hg hgG]⟩
    have hr := ck_lsum L hL'
    simp only [List.map_cons, List.sum_cons]
    rw [Fw_add Eop hC hL hA w (fun x => p.1 • p.2 x) _ hs hr g hg,
      Fw_smul Eop hC hL hS w p.1 p.2 (h p (by simp)) g hg, ih hL' g hg]

end Words

section Values

variable (Eop : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Mat k r → E) → (Mat k r → E))

theorem lsum_apply {ι : Type*} (l : List ι) (F : ι → Mat k r → E) (x : Mat k r) :
    (l.map F).sum x = (l.map fun i => F i x).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih]

theorem ev_rep_ex {d : ℕ} {a : AA k r E} (ha : Rep d a) :
    ∃ L : List (ℂ × List (Ix k r)), (∀ p ∈ L, p.2.length ≤ d) ∧
      ∀ f x, ev Eop a f x = (L.map fun p => p.1 • Fw Eop p.2 f x).sum := by
  obtain ⟨L, hL, h⟩ := ha
  refine ⟨L, hL, fun f x => ?_⟩
  simp only [ev, h, lsum_apply, List.nil_append, Pi.smul_apply, Phi]

theorem ev_ck (hC : HC Eop) {d : ℕ} {a : AA k r E} (ha : Rep d a) (m : ℕ) (f : Mat k r → E)
    (hf : CkOn ((m + d : ℕ) : ℕ∞) (GV k r) f) : CkOn (m : ℕ∞) (GV k r) (ev Eop a f) := by
  obtain ⟨L, hL, h⟩ := ev_rep_ex Eop ha
  have e : ev Eop a f = fun x => ((L.map fun p => (p.1, Fw Eop p.2 f)).map fun q => q.1 • q.2 x).sum := by
    funext x
    rw [h]
    simp [List.map_map, Function.comp_def]
  rw [e]
  apply ck_lsum
  intro q hq
  simp only [List.mem_map] at hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact Fw_ck Eop hC p.2 m f (ck_mono' (by have := hL p hp; omega) hf)

theorem ev_smul (c : ℂ) (a : AA k r E) (f : Mat k r → E) (x : Mat k r) : ev Eop (c • a) f x = c • ev Eop a f x :=
  rfl

theorem ev_fsum {ι : Type*} (s : Finset ι) (F : ι → AA k r E) (f : Mat k r → E) (x : Mat k r) :
    ev Eop (∑ i ∈ s, F i) f x = ∑ i ∈ s, ev Eop (F i) f x := by
  first
    | (simp [ev, LinearMap.sum_apply, Finset.sum_apply]; done)
    | (simp only [ev, LinearMap.coeFn_sum, Finset.sum_apply])

theorem ev_intCast_mul (z : ℤ) (a : AA k r E) (f : Mat k r → E) (x : Mat k r) :
    ev Eop ((z : AA k r E) * a) f x = (z : ℂ) • ev Eop a f x := by
  rw [← map_intCast (algebraMap ℂ (AA k r E)) z]
  first
    | (simp only [ev, Module.End.mul_apply, Module.algebraMap_end_apply, Pi.smul_apply]; done)
    | (simp only [ev, LinearMap.mul_apply, Module.algebraMap_end_apply, Pi.smul_apply]; done)
    | rfl

theorem ev_mul (hC : HC Eop) (hL : HL Eop) (hA : HA Eop) (hS : HS Eop) {d e : ℕ} {a b : AA k r E}
    (ha : Rep d a) (hb : Rep e b) (f : Mat k r → E) (hf : CkOn ((d + e : ℕ) : ℕ∞) (GV k r) f) :
    ∀ g ∈ GV k r, ev Eop (a * b) f g = ev Eop a (ev Eop b f) g := by
  obtain ⟨La, hLa, ha'⟩ := ha
  obtain ⟨Lb, hLb, hb'⟩ := hb
  have hev : ev Eop b f = fun x => ((Lb.map fun q => (q.1, Fw Eop q.2 f)).map fun q => q.1 • q.2 x).sum := by
    funext x
    simp only [ev, hb', lsum_apply, List.nil_append, Pi.smul_apply, Phi, List.map_map, Function.comp_def]
  intro g hg
  show a (b (Phi Eop f)) [] g = a (Phi Eop (ev Eop b f)) [] g
  rw [ha', ha', lsum_apply, lsum_apply]
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [List.nil_append, Pi.smul_apply]
  congr 1
  have hck : ∀ q ∈ Lb.map (fun q => (q.1, Fw Eop q.2 f)), CkOn ((p.2.length : ℕ) : ℕ∞) (GV k r) q.2 := by
    intro q' hq'
    simp only [List.mem_map] at hq'
    obtain ⟨q, hq, rfl⟩ := hq'
    exact Fw_ck Eop hC q.2 p.2.length f (ck_mono' (by have := hLa p hp; have := hLb q hq; omega) hf)
  show b (Phi Eop f) p.2 g = Fw Eop p.2 (ev Eop b f) g
  rw [hev, Fw_lsum Eop hC hL hA hS p.2 _ hck g hg, hb', lsum_apply]
  simp only [List.map_map, Function.comp_def, Pi.smul_apply, Phi, Fw_append]

end Values

end Formalism.FourierDecayAlt.P.JFxE
