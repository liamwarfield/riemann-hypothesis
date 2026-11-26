module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.EntireEqZeroOrEqZeroOfMulEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KaFormHomogeneous
namespace GlobalTheory

open Finset GlobalTheory.KeyKa

private theorem kaForm_prod_zpow {G : Type} [CommGroup G] (a : G) (s : Finset ℕ) (f : ℕ → ℤ) :
    ∏ j ∈ s, a ^ f j = a ^ ∑ j ∈ s, f j := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [prod_insert hj, sum_insert hj, ih, zpow_add]

theorem tComb_rescale {R : Type} [CommRing R] (g n l Pr : ℕ) (t a : Rˣ) (lam be : ℕ → Rˣ)
    (hl : g * n < l) (hd : ∀ j ∈ range (g + 1), (l - j * n) ∣ Pr) :
    tComb g n l Pr (t * ∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ)))
      (fun j => lam j * be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ) *
        a ^ (8 * (l - j * n) ^ (4 * g + 2)))
      = tComb g n l Pr t lam *
        a ^ (8 * ((Pr ^ (3 * g + 2) : ℕ) : ℤ) * ((g.factorial * n ^ g : ℕ) : ℤ)) := by
  unfold tComb
  rw [mul_pow]
  simp only [mul_zpow, prod_mul_distrib]
  have hB : (∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) ^ (4 * Pr ^ (3 * g + 2)) *
      ∏ j ∈ range (g + 1), (be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ)) ^
        ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) = 1 := by
    rw [← prod_pow, ← prod_mul_distrib]
    refine prod_eq_one fun j hj => ?_
    rw [← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    convert zpow_zero (be j) using 2
    have key : Pr / (l - j * n) * (l - j * n) = Pr := Nat.div_mul_cancel (hd j hj)
    generalize Pr / (l - j * n) = q at key ⊢
    generalize l - j * n = d at key ⊢
    subst key
    push_cast
    ring
  have hA : ∏ j ∈ range (g + 1), (a ^ (8 * (l - j * n) ^ (4 * g + 2))) ^
        ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) =
      a ^ (8 * ((Pr ^ (3 * g + 2) : ℕ) : ℤ) * ((g.factorial * n ^ g : ℕ) : ℤ)) := by
    rw [prod_congr rfl fun j _ => by rw [← zpow_natCast, ← zpow_mul], kaForm_prod_zpow,
      ← alternating_sum_choose_mul_sub_pow g n l hl.le, mul_sum]
    congr 1
    refine sum_congr rfl fun j hj => ?_
    have key : Pr / (l - j * n) * (l - j * n) = Pr := Nat.div_mul_cancel (hd j hj)
    generalize Pr / (l - j * n) = q at key ⊢
    generalize l - j * n = d at key ⊢
    subst key
    push_cast
    ring
  calc _ = t ^ (4 * Pr ^ (3 * g + 2)) *
        (∏ j ∈ range (g + 1), lam j ^ ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ))) *
        ((∏ j ∈ range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) ^ (4 * Pr ^ (3 * g + 2)) *
          ∏ j ∈ range (g + 1), (be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ)) ^
            ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ))) *
        ∏ j ∈ range (g + 1), (a ^ (8 * (l - j * n) ^ (4 * g + 2))) ^
          ((-1 : ℤ) ^ j * (g.choose j : ℤ) * ((Pr / (l - j * n)) ^ (3 * g + 2) : ℕ)) := by ac_rfl
    _ = _ := by rw [hB, hA, mul_one]

theorem tComb_mul_left {R : Type} [CommRing R] (g n l Pr : ℕ) (t c : Rˣ) (lam : ℕ → Rˣ) :
    tComb g n l Pr (t * c) lam = tComb g n l Pr t lam * c ^ (4 * Pr ^ (3 * g + 2)) := by
  unfold tComb
  rw [mul_pow]
  exact mul_right_comm _ _ _

private theorem kaForm_monomial_eq_of_exponent_relations {G : Type} [CommGroup G] (X X' J u dl a : G) (N k : ℕ)
    (z1 z2 z3 α e1 e2 e3 : ℤ) (hu : z1 * N * e1 + z2 * N * e2 + z3 * e3 = 0)
    (hdl : 2 * N * e1 + 2 * N * e2 + 2 * e3 = 0) (ha : α * e1 + α * e2 + k = 0) :
    (X * (u ^ z1) ^ N * (dl ^ 2) ^ N * a ^ α) ^ e1 * (X' * (u ^ z2) ^ N * (dl ^ 2) ^ N * a ^ α) ^ e2 *
      (J * u ^ z3 * dl ^ 2) ^ e3 * a ^ k = X ^ e1 * X' ^ e2 * J ^ e3 := by
  have eU : u ^ (z1 * N * e1) * u ^ (z2 * N * e2) * u ^ (z3 * e3) = 1 := by
    rw [← zpow_add, ← zpow_add, hu, zpow_zero]
  have eD : dl ^ (2 * N * e1) * dl ^ (2 * N * e2) * dl ^ (2 * e3) = 1 := by
    rw [← zpow_add, ← zpow_add, hdl, zpow_zero]
  have eA : a ^ (α * e1) * a ^ (α * e2) * a ^ (k : ℤ) = 1 := by
    rw [← zpow_add, ← zpow_add, ha, zpow_zero]
  simp only [mul_zpow, ← zpow_natCast, ← zpow_mul, Nat.cast_ofNat]
  calc _ = X ^ e1 * X' ^ e2 * J ^ e3 * (u ^ (z1 * N * e1) * u ^ (z2 * N * e2) * u ^ (z3 * e3)) *
        (dl ^ (2 * N * e1) * dl ^ (2 * N * e2) * dl ^ (2 * e3)) *
        (a ^ (α * e1) * a ^ (α * e2) * a ^ (k : ℤ)) := by simp only [mul_comm, mul_assoc, mul_left_comm]
    _ = _ := by rw [eU, eD, eA, mul_one, mul_one, mul_one]

theorem kaForm_homogeneous :
    ∀ (R : Type) [CommRing R] (g n l l' : ℕ) (t t' J u a dl : Rˣ) (lam lam' be be' : ℕ → Rˣ), g * n < l → l < l' → kaForm g n l l' (t * u ^ (-2 * (l : ℤ)) * dl ^ 2 * ∏ j ∈ Finset.range (g + 1), be j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) (t' * u ^ (-2 * (l' : ℤ)) * dl ^ 2 * ∏ j ∈ Finset.range (g + 1), be' j ^ (2 * (-1 : ℤ) ^ j * (g.choose j : ℤ))) (fun j => lam j * be j ^ (-8 * ((l - j * n) ^ (3 * g + 2) : ℕ) : ℤ) * a ^ (8 * (l - j * n) ^ (4 * g + 2))) (fun j => lam' j * be' j ^ (-8 * ((l' - j * n) ^ (3 * g + 2) : ℕ) : ℤ) * a ^ (8 * (l' - j * n) ^ (4 * g + 2))) (J * u ^ (-((g * n : ℕ) : ℤ)) * dl ^ 2) * a ^ (8 * kaExp g n l l') = kaForm g n l l' t t' lam lam' J := by
  intro R _ g n l l' t t' J u a dl lam lam' be be' hl hl'
  have hd : ∀ j ∈ range (g + 1), (l - j * n) ∣ degProd g n l l' := fun j hj =>
    (dvd_mul_right _ _).trans (dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n)) hj)
  have hd' : ∀ j ∈ range (g + 1), (l' - j * n) ∣ degProd g n l l' := fun j hj =>
    (dvd_mul_left _ _).trans (dvd_prod_of_mem (fun j => (l - j * n) * (l' - j * n)) hj)
  unfold kaForm
  rw [tComb_rescale g n l _ _ a lam be hl hd, tComb_rescale g n l' _ _ a lam' be' (hl.trans hl') hd',
    tComb_mul_left, tComb_mul_left, tComb_mul_left, tComb_mul_left]
  refine kaForm_monomial_eq_of_exponent_relations _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
  all_goals
    try unfold kaExp
    push_cast [Nat.cast_sub hl'.le]
    ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsDifferentiableOnTorsSq
open GlobalTheory.KeyKa

namespace GlobalTheory.TorsionHolomorphic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod {ι : Type} (s : Finset ι) (f : ι → E → ℂ) (W : Set E)
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) :
    DifferentiableOn ℂ (fun e => ∏ i ∈ s, f i e) W := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.prod_empty]
    exact differentiableOn_const 1
  · intro a s ha ih
    simp only [Finset.prod_insert ha]
    exact (hf a).mul ih

theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_sum {ι : Type} (s : Finset ι) (f : ι → E → ℂ) (W : Set E)
    (hf : ∀ i, DifferentiableOn ℂ (f i) W) :
    DifferentiableOn ℂ (fun e => ∑ i ∈ s, f i e) W :=
  DifferentiableOn.fun_sum (fun i _ => hf i)

theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det {n : Type} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W) :
    DifferentiableOn ℂ (fun e => (A e).det) W := by
  have hdet : (fun e => (A e).det) =
      fun e => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A e (σ i) i := by
    funext e
    exact Matrix.det_apply' _
  rw [hdet]
  refine DifferentiableOn.fun_sum (fun σ _ => ?_)
  exact (differentiableOn_const _).mul
    (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_finset_prod Finset.univ (fun i e => A e (σ i) i) W
      (fun i => hA _ _))

theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul {n : Type} [Fintype n] (A B : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W)
    (hB : ∀ p q, DifferentiableOn ℂ (fun e => B e p q) W) (p q : n) :
    DifferentiableOn ℂ (fun e => (A e * B e) p q) W := by
  simp only [Matrix.mul_apply]
  exact DifferentiableOn.fun_sum (fun r _ => (hA p r).mul (hB r q))

theorem _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv {n : Type} [Fintype n] [DecidableEq n] (A : E → Matrix n n ℂ)
    (W : Set E) (hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W)
    (hdet : ∀ e ∈ W, (A e).det ≠ 0) (p q : n) :
    DifferentiableOn ℂ (fun e => (A e)⁻¹ p q) W := by
  have key : ∀ e, (A e)⁻¹ p q = ((A e).det)⁻¹ * (A e).adjugate p q := by
    intro e
    rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  simp only [key]
  refine (DifferentiableOn.inv (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA) hdet).mul ?_
  simp only [Matrix.adjugate_apply]
  have hentry : ∀ i j, DifferentiableOn ℂ
      (fun e => (A e).updateRow q (Pi.single p 1) i j) W := by
    intro i j
    by_cases hi : i = q
    · subst hi
      simp only [Matrix.updateRow_self]
      exact differentiableOn_const _
    · simp only [Matrix.updateRow_ne hi]
      exact hA i j
  exact _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (A e).updateRow q (Pi.single p 1))
    W hentry

private theorem degree_part_homotopy_of_anticommutator_eq_one {Ix : Type} [Fintype Ix] [DecidableEq Ix]
    (deg : Ix → ℕ) (D h : Matrix Ix Ix ℂ) (hD : ∀ p q, deg q ≠ deg p + 1 → D p q = 0)
    (hh : D * h + h * D = 1) :
    D * Matrix.of (fun p q => if deg p = deg q + 1 then h p q else 0) +
      Matrix.of (fun p q => if deg p = deg q + 1 then h p q else 0) * D = 1 := by
  ext p q
  have h1 : ∀ r, D p r * (if deg r = deg q + 1 then h r q else 0) =
      if deg p = deg q then D p r * h r q else 0 := by
    intro r
    by_cases hr : deg r = deg p + 1
    · by_cases hpq : deg p = deg q
      · rw [if_pos (by omega), if_pos hpq]
      · rw [if_neg (by omega), if_neg hpq, mul_zero]
    · rw [hD p r hr, zero_mul, zero_mul, ite_self]
  have h2 : ∀ r, (if deg p = deg r + 1 then h p r else 0) * D r q =
      if deg p = deg q then h p r * D r q else 0 := by
    intro r
    by_cases hr : deg q = deg r + 1
    · by_cases hpq : deg p = deg q
      · rw [if_pos (by omega), if_pos hpq]
      · rw [if_neg (by omega), if_neg hpq, zero_mul]
    · rw [hD r q hr, mul_zero, mul_zero, ite_self]
  have hpq' := congrFun (congrFun hh p) q
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply] at hpq' ⊢
  simp only [h1, h2]
  by_cases hpq : deg p = deg q
  · simp only [if_pos hpq]
    exact hpq'
  · simp only [if_neg hpq, Finset.sum_const_zero, add_zero]
    have hne : p ≠ q := fun h => hpq (h ▸ rfl)
    rw [Matrix.one_apply_ne hne]

private theorem contracting_homotopy_of_det_anticommutator_ne_zero {Ix : Type} [Fintype Ix]
    [DecidableEq Ix] (D h : Matrix Ix Ix ℂ) (hDD : D * D = 0)
    (hdet : (D * h + h * D).det ≠ 0) :
    D * (h * (D * h + h * D)⁻¹) + h * (D * h + h * D)⁻¹ * D = 1 := by
  set A := D * h + h * D with hA
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hdet
  have hcomm : D * A = A * D := by
    rw [hA, Matrix.mul_add, Matrix.add_mul, ← Matrix.mul_assoc, hDD, Matrix.zero_mul, zero_add,
      Matrix.mul_assoc h D D, hDD, Matrix.mul_zero, add_zero, Matrix.mul_assoc]
  have hinv : A⁻¹ * D = D * A⁻¹ := by
    calc A⁻¹ * D = A⁻¹ * D * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv A hu, Matrix.mul_one]
      _ = A⁻¹ * (D * A) * A⁻¹ := by simp only [Matrix.mul_assoc]
      _ = A⁻¹ * (A * D) * A⁻¹ := by rw [hcomm]
      _ = D * A⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul A hu, Matrix.one_mul]
  calc D * (h * A⁻¹) + h * A⁻¹ * D = D * h * A⁻¹ + h * D * A⁻¹ := by
        rw [Matrix.mul_assoc h, hinv, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    _ = A * A⁻¹ := by rw [hA, Matrix.add_mul]
    _ = 1 := Matrix.mul_nonsing_inv A hu

theorem _root_.GlobalTheory.TorsionHolomorphic.exists_differentiableOn_torsSq :
    ∀ (E Ix : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : E → Matrix Ix Ix ℂ) (W : Set E) (e₀ : E) (t₀ : ℂ), IsOpen W → e₀ ∈ W → (∀ p q, DifferentiableOn ℂ (fun e => D e p q) W) → (∀ e ∈ W, _root_.GlobalTheory.KeyKa.IsCx deg (D e)) → _root_.GlobalTheory.KeyKa.TorsSq deg (D e₀) t₀ → ∃ (W' : Set E) (t : E → ℂ), IsOpen W' ∧ e₀ ∈ W' ∧ W' ⊆ W ∧ DifferentiableOn ℂ t W' ∧ ∀ e ∈ W', _root_.GlobalTheory.KeyKa.TorsSq deg (D e) (t e) := by
  intro E Ix _ _ _ _ deg D W e₀ t₀ hW he₀ hD hcx htor
  obtain ⟨h₀, -, hcontr₀, σ, -⟩ := htor
  set A : E → Matrix Ix Ix ℂ := fun e => D e * h₀ + h₀ * D e with hAdef
  have hA : ∀ p q, DifferentiableOn ℂ (fun e => A e p q) W := by
    intro p q
    simp only [hAdef, Matrix.add_apply]
    exact (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul D (fun _ => h₀) W hD (fun _ _ => differentiableOn_const _)
      p q).add (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) D W
        (fun _ _ => differentiableOn_const _) hD p q)
  have hAdet := _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det A W hA
  set W' := W ∩ (fun e => (A e).det) ⁻¹' {(0 : ℂ)}ᶜ with hW'
  have hW'open : IsOpen W' := hAdet.continuousOn.isOpen_inter_preimage hW isOpen_compl_singleton
  have hsub : W' ⊆ W := Set.inter_subset_left
  have hdetW' : ∀ e ∈ W', (A e).det ≠ 0 := fun e he => he.2
  have hAe₀ : A e₀ = 1 := hcontr₀
  have he₀' : e₀ ∈ W' := ⟨he₀, by simp [hAe₀]⟩
  set hh : E → Matrix Ix Ix ℂ := fun e =>
    Matrix.of (fun p q => if deg p = deg q + 1 then (h₀ * (A e)⁻¹) p q else 0) with hhdef
  have hhdiff : ∀ p q, DifferentiableOn ℂ (fun e => hh e p q) W' := by
    intro p q
    simp only [hhdef, Matrix.of_apply]
    by_cases hpq : deg p = deg q + 1
    · simp only [if_pos hpq]
      exact _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_mul (fun _ => h₀) (fun e => (A e)⁻¹) W'
        (fun _ _ => differentiableOn_const _)
        (_root_.GlobalTheory.TorsionHolomorphic.differentiableOn_matrix_inv A W' (fun i j => (hA i j).mono hsub) hdetW') p q
    · simp only [if_neg hpq]
      exact differentiableOn_const _
  refine ⟨W', fun e => ((D e + hh e).submatrix (fun p : {p // Even (deg p)} => (p : Ix))
    (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))).det ^ 2,
    hW'open, he₀', hsub, ?_, ?_⟩
  · refine DifferentiableOn.pow ?_ 2
    refine _root_.GlobalTheory.TorsionHolomorphic.differentiableOn_det (fun e => (D e + hh e).submatrix
      (fun p : {p // Even (deg p)} => (p : Ix))
      (fun p : {p // Even (deg p)} => ((σ p : {p // ¬Even (deg p)}) : Ix))) W' (fun i j => ?_)
    simp only [Matrix.submatrix_apply, Matrix.add_apply]
    exact ((hD _ _).mono hsub).add (hhdiff _ _)
  · intro e he
    refine ⟨hh e, ?_, ?_, σ, rfl⟩
    · intro p q hpq
      simp only [hhdef, Matrix.of_apply, if_neg hpq]
    · exact degree_part_homotopy_of_anticommutator_eq_one deg (D e) (h₀ * (A e)⁻¹) (hcx e (hsub he)).1
        (contracting_homotopy_of_det_anticommutator_ne_zero (D e) h₀ (hcx e (hsub he)).2 (hdetW' e he))

end GlobalTheory.TorsionHolomorphic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubmatrixMulOfVanish
open GlobalTheory.KeyKa

namespace GlobalTheory.TorsionUnique

variable {R Ix : Type} [CommRing R] [Fintype Ix] [DecidableEq Ix]

def HasDeg (deg : Ix → ℕ) (k : ℤ) (X : Matrix Ix Ix R) : Prop :=
  ∀ p q, (deg p : ℤ) ≠ deg q + k → X p q = 0

private lemma submatrix_mul_eq_of_vanishing_off {ι κ : Type} (X Y : Matrix Ix Ix R) (Q : Ix → Prop)
    [DecidablePred Q] (f : ι → Ix) (g : κ → Ix) (hX : ∀ i r, ¬ Q r → X (f i) r = 0) :
    (X * Y).submatrix f g
      = X.submatrix f (Subtype.val : {r // Q r} → Ix) * Y.submatrix Subtype.val g := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype Q,
    Finset.sum_eq_zero (s := (Finset.univ : Finset {r // ¬ Q r}))
      (fun r _ => by rw [hX i r r.2, zero_mul]), add_zero]
  rfl

private lemma apply_eq_zero_of_hasDeg_odd_of_even_even {deg : Ix → ℕ} {k : ℤ} {X : Matrix Ix Ix R}
    (hX : _root_.GlobalTheory.TorsionUnique.HasDeg deg k X) (hk : k = 1 ∨ k = -1) {p q : Ix}
    (hp : Even (deg p)) (hq : Even (deg q)) : X p q = 0 := by
  rw [Nat.even_iff] at hp hq
  exact hX p q (by omega)

private lemma hasDeg_mul {deg : Ix → ℕ} {a b c : ℤ} {X Y : Matrix Ix Ix R}
    (hX : _root_.GlobalTheory.TorsionUnique.HasDeg deg a X) (hY : _root_.GlobalTheory.TorsionUnique.HasDeg deg b Y)
    (hc : a + b = c) : _root_.GlobalTheory.TorsionUnique.HasDeg deg c (X * Y) := by
  intro p q hpq
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun r _ => ?_
  by_cases hr : (deg p : ℤ) = deg r + a
  · rw [hY r q (by omega), mul_zero]
  · rw [hX p r hr, zero_mul]

private lemma hasDeg_sub {deg : Ix → ℕ} {a : ℤ} {X Y : Matrix Ix Ix R}
    (hX : _root_.GlobalTheory.TorsionUnique.HasDeg deg a X) (hY : _root_.GlobalTheory.TorsionUnique.HasDeg deg a Y) :
    _root_.GlobalTheory.TorsionUnique.HasDeg deg a (X - Y) := by
  intro p q hpq
  rw [Matrix.sub_apply, hX p q hpq, hY p q hpq, sub_zero]

private lemma det_one_add_sub_mul_degree_submatrix_eq_one (deg : Ix → ℕ) (D h₁ h₂ : Matrix Ix Ix R)
    (hD : _root_.GlobalTheory.TorsionUnique.HasDeg deg (-1) D) (hDD : D * D = 0)
    (h₁d : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h₁) (h₂d : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h₂)
    (h₁c : D * h₁ + h₁ * D = 1) (h₂c : D * h₂ + h₂ * D = 1) (d : ℕ) :
    (((1 : Matrix Ix Ix R) + (h₂ - h₁) * D).submatrix (Subtype.val : {p // deg p = d} → Ix)
      Subtype.val).det = 1 := by
  set k := h₂ - h₁ with hk_def
  have hkd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 k := hasDeg_sub h₂d h₁d
  have hψd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 0 (k * D) := hasDeg_mul hkd hD (by norm_num)
  have hkD : D * k + k * D = 0 := by
    have : D * k + k * D = (D * h₂ + h₂ * D) - (D * h₁ + h₁ * D) := by
      simp only [hk_def, mul_sub, sub_mul]; abel
    rw [this, h₁c, h₂c, sub_self]
  have hDk : D * k = -(k * D) := eq_neg_of_add_eq_zero_left hkD
  have hψψ : k * D * (k * D) = 0 := by
    calc k * D * (k * D) = k * (D * k) * D := by simp only [mul_assoc]
      _ = -(k * k * (D * D)) := by rw [hDk]; simp only [mul_neg, neg_mul, mul_assoc]
      _ = 0 := by rw [hDD]; simp
  have hblock : ∀ n : ℕ, ((1 : Matrix Ix Ix R) + k * D).submatrix
      (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
        = 1 + (k * D).submatrix (Subtype.val : {p // deg p = n} → Ix)
          (Subtype.val : {p // deg p = n} → Ix) := by
    intro n
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Subtype.val_injective.ne hij)]
  induction d with
  | zero =>
    rw [hblock]
    have : (k * D).submatrix (Subtype.val : {p // deg p = 0} → Ix) (Subtype.val : {p // deg p = 0} → Ix) = 0 := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [hD r j (by have := j.2; omega), mul_zero]
    rw [this, add_zero, Matrix.det_one]
  | succ n ih =>
    rw [hblock] at ih ⊢
    have hsplit : (k * D).submatrix (Subtype.val : {p // deg p = n + 1} → Ix) (Subtype.val : {p // deg p = n + 1} → Ix)
        = k.submatrix (Subtype.val : {p // deg p = n + 1} → Ix) (Subtype.val : {p // deg p = n} → Ix)
          * D.submatrix (Subtype.val : {p // deg p = n} → Ix)
            (Subtype.val : {p // deg p = n + 1} → Ix) :=
      submatrix_mul_eq_of_vanishing_off k D (fun r => deg r = n) (Subtype.val : {p // deg p = n + 1} → Ix) (Subtype.val : {p // deg p = n + 1} → Ix)
        (fun i r hr => hkd _ r (by have := i.2; omega))
    have hswap : D.submatrix (Subtype.val : {p // deg p = n} → Ix)
          (Subtype.val : {p // deg p = n + 1} → Ix)
          * k.submatrix (Subtype.val : {p // deg p = n + 1} → Ix) (Subtype.val : {p // deg p = n} → Ix)
        = -(k * D).submatrix (Subtype.val : {p // deg p = n} → Ix)
          (Subtype.val : {p // deg p = n} → Ix) := by
      exact (submatrix_mul_eq_of_vanishing_off D k (fun r => deg r = n + 1) (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
        (fun i r hr => hD _ r (by have := i.2; omega))).symm.trans (by rw [hDk, Matrix.submatrix_neg]; rfl)
    have hsq : (k * D).submatrix (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
          * (k * D).submatrix (Subtype.val : {p // deg p = n} → Ix)
            (Subtype.val : {p // deg p = n} → Ix) = 0 := by
      exact (submatrix_mul_eq_of_vanishing_off (k * D) (k * D) (fun r => deg r = n) (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
        (fun i r hr => hψd _ r (by have := i.2; omega))).symm.trans (by rw [hψψ, Matrix.submatrix_zero]; rfl)
    set ψ := (k * D).submatrix (Subtype.val : {p // deg p = n} → Ix) (Subtype.val : {p // deg p = n} → Ix)
    have hinv : (1 - ψ).det * (1 + ψ).det = 1 := by
      rw [← Matrix.det_mul, sub_mul, one_mul, mul_add, mul_one, hsq]; simp
    rw [hsplit, Matrix.det_one_add_mul_comm, hswap, ← sub_eq_add_neg]
    rw [ih, mul_one] at hinv
    exact hinv

private lemma det_even_submatrix_homotopy_product_eq_one (deg : Ix → ℕ) (D h₁ h₂ : Matrix Ix Ix R)
    (hD : _root_.GlobalTheory.TorsionUnique.HasDeg deg (-1) D) (hDD : D * D = 0)
    (h₁d : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h₁) (h₂d : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h₂)
    (h₁c : D * h₁ + h₁ * D = 1) (h₂c : D * h₂ + h₂ * D = 1) :
    (((D + h₂) * (D + h₁)).submatrix (Subtype.val : {p // Even (deg p)} → Ix)
      Subtype.val).det = 1 := by
  have hG : (D + h₂) * (D + h₁) = 1 + (h₂ - h₁) * D + h₂ * h₁ := by
    have e₁ : D * h₁ = 1 - h₁ * D := eq_sub_of_add_eq h₁c
    rw [add_mul, mul_add, mul_add, hDD, e₁, sub_mul]; abel
  have hψd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 0 ((h₂ - h₁) * D) :=
    hasDeg_mul (hasDeg_sub h₂d h₁d) hD (by norm_num)
  have hhd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 2 (h₂ * h₁) := hasDeg_mul h₂d h₁d (by norm_num)
  have hlow : ∀ p q, deg p < deg q → ((D + h₂) * (D + h₁)) p q = 0 := by
    intro p q hpq
    rw [hG, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply_ne (by rintro rfl; omega),
      hψd p q (by omega), hhd p q (by omega)]
    simp
  have hdiag : ∀ p q, deg p = deg q →
      ((D + h₂) * (D + h₁)) p q = ((1 : Matrix Ix Ix R) + (h₂ - h₁) * D) p q := by
    intro p q hpq
    rw [hG, Matrix.add_apply (1 + _), hhd p q (by omega), add_zero]
  set M := ((D + h₂) * (D + h₁)).submatrix (Subtype.val : {p // Even (deg p)} → Ix)
    Subtype.val
  have htri : Matrix.BlockTriangular M.transpose (fun i => deg i.1) := by
    intro i j hij
    exact hlow _ _ hij
  rw [← Matrix.det_transpose, htri.det]
  refine Finset.prod_eq_one fun d _ => ?_
  by_cases hd : Even d
  · let E : {i : {p // Even (deg p)} // deg i.1 = d} ≃ {p : Ix // deg p = d} :=
      { toFun := fun i => ⟨i.1.1, i.2⟩
        invFun := fun p => ⟨⟨p.1, by rw [p.2]; exact hd⟩, p.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have : M.transpose.toSquareBlock (fun i => deg i.1) d
        = (((1 : Matrix Ix Ix R) + (h₂ - h₁) * D).submatrix
            (Subtype.val : {p // deg p = d} → Ix) Subtype.val).transpose.submatrix E E := by
      ext i j
      simp only [Matrix.toSquareBlock, Matrix.submatrix_apply, Matrix.transpose_apply, M, E,
        Equiv.coe_fn_mk]
      exact hdiag _ _ (by rw [i.2, j.2])
    rw [this, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact det_one_add_sub_mul_degree_submatrix_eq_one deg D h₁ h₂ hD hDD h₁d h₂d h₁c h₂c d
  · haveI : IsEmpty {i : {p // Even (deg p)} // deg i.1 = d} :=
      ⟨fun i => hd (by rw [← i.2]; exact i.1.2)⟩
    exact Matrix.det_isEmpty

theorem _root_.GlobalTheory.TorsionUnique.torsSq_unique : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix]
    (deg : Ix → ℕ) (D : Matrix Ix Ix R) (t t' : R),
    _root_.GlobalTheory.KeyKa.IsCx deg D → _root_.GlobalTheory.KeyKa.TorsSq deg D t →
      _root_.GlobalTheory.KeyKa.TorsSq deg D t' → t = t' ∧ IsUnit t := by
  intro R Ix _ _ _ deg D t t' hDiff H H'
  obtain ⟨h, hh, hc, e, rfl⟩ := H
  obtain ⟨h', hh', hc', e', rfl⟩ := H'
  have hDiff' := hDiff
  unfold _root_.GlobalTheory.KeyKa.IsCx at hDiff'
  obtain ⟨hD0, hDD⟩ := hDiff'
  have hD : _root_.GlobalTheory.TorsionUnique.HasDeg deg (-1) D := fun p q hpq => hD0 p q (by omega)
  have hd : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h := fun p q hpq => hh p q (by omega)
  have hd' : _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 h' := fun p q hpq => hh' p q (by omega)
  have hprod : ∀ g : Matrix Ix Ix R, _root_.GlobalTheory.TorsionUnique.HasDeg deg 1 g →
      ((D + g).submatrix (Subtype.val : {p // Even (deg p)} → Ix) (fun p => (e' p : Ix))
        * (D + h).submatrix (fun p => (e' p : Ix)) Subtype.val)
        = ((D + g) * (D + h)).submatrix (Subtype.val : {p // Even (deg p)} → Ix)
          (Subtype.val : {p // Even (deg p)} → Ix) := by
    intro g hg
    rw [submatrix_mul_eq_of_vanishing_off (D + g) (D + h) (fun r => ¬ Even (deg r)) _ _
      (fun i r hr => by
        rw [not_not] at hr
        rw [Matrix.add_apply, apply_eq_zero_of_hasDeg_odd_of_even_even hD (Or.inr rfl) i.2 hr,
          apply_eq_zero_of_hasDeg_odd_of_even_even hg (Or.inl rfl) i.2 hr, add_zero])]
    ext i j
    simp only [Matrix.mul_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e' (fun r => (D + g) i.1 r.1 * (D + h) r.1 j.1)
  set c := ((D + h).submatrix (fun p => (e' p : Ix))
    (Subtype.val : {p // Even (deg p)} → Ix)).det
  set a := ((D + h).submatrix (Subtype.val : {p // Even (deg p)} → Ix)
    (fun p => (e' p : Ix))).det
  set b := ((D + h').submatrix (Subtype.val : {p // Even (deg p)} → Ix)
    (fun p => (e' p : Ix))).det
  have hac : a * c = 1 := by
    rw [← Matrix.det_mul, hprod h hd]
    exact det_even_submatrix_homotopy_product_eq_one deg D h h hD hDD hd hd hc hc
  have hbc : b * c = 1 := by
    rw [← Matrix.det_mul, hprod h' hd']
    exact det_even_submatrix_homotopy_product_eq_one deg D h h' hD hDD hd hd' hc hc'
  have hba : b = a := by
    calc b = b * (a * c) := by rw [hac, mul_one]
      _ = a * (b * c) := by ring
      _ = a := by rw [hbc, mul_one]
  have hsq : ∀ (g : Matrix Ix Ix R) (f : {p // Even (deg p)} ≃ {p // ¬ Even (deg p)}),
      ((g.submatrix (fun p : {p // Even (deg p)} => (p : Ix)) fun p => (f p : Ix)).det) ^ 2
        = ((g.submatrix (fun p : {p // Even (deg p)} => (p : Ix)) fun p => (e' p : Ix)).det) ^ 2 := by
    intro g f
    have : g.submatrix (fun p : {p // Even (deg p)} => (p : Ix)) (fun p => (f p : Ix))
        = (g.submatrix (fun p : {p // Even (deg p)} => (p : Ix)) fun p => (e' p : Ix)).submatrix id
          (f.trans e'.symm) := by
      ext i j
      simp
    rw [this, Matrix.det_permute', mul_pow]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (f.trans e'.symm)) with hs | hs <;> simp [hs]
  refine ⟨?_, ?_⟩
  · rw [hsq (D + h) e, hsq (D + h') e']
    change a ^ 2 = b ^ 2
    rw [hba]
  · rw [hsq (D + h) e]
    have ha : IsUnit a := ⟨⟨a, c, hac, by rw [mul_comm]; exact hac⟩, rfl⟩
    exact ha.pow 2

end GlobalTheory.TorsionUnique
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TorsSqMap
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem torsSq_map : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) (R' : Type) [CommRing R'] (f : R →+* R') (t : R), TorsSq deg D t → TorsSq deg (D.map f) (f t) := by
  intro R Ix _ _ _ deg D R' _ f t H
  obtain ⟨h, h1, h2, e, h3⟩ := H
  refine ⟨h.map f, ?_, ?_, e, ?_⟩
  · intro p q hpq
    simp [Matrix.map_apply, h1 p q hpq]
  · have := congrArg (f.mapMatrix : Matrix Ix Ix R →+* Matrix Ix Ix R') h2
    rw [map_add (f := _), map_mul, map_mul, map_one] at this
    exact this
  · rw [h3, map_pow, RingHom.map_det]
    congr 2
    ext p q
    simp [Matrix.map_apply]

end GlobalTheory.KeyKa
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsUnitField
open GlobalTheory.KeyKa

namespace GlobalTheory.TorsExists

variable {Ix : Type} [Fintype Ix] [DecidableEq Ix]

theorem exists_mul_mul_eq {K : Type} [Field K] (D : Matrix Ix Ix K) : ∃ G : Matrix Ix Ix K, D * G * D = D := by
  set f := Matrix.toLin' D with hf
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  obtain ⟨g, hg⟩ := LinearMap.exists_extend s
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', ← hf]
  refine LinearMap.ext fun v => ?_
  have h1 : g (f v) = s (f.rangeRestrict v) := by rw [← hg]; rfl
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict v))
  simp only [LinearMap.comp_apply, h1]
  exact h2

theorem exists_isUnit_field {K : Type} [Field K] (D : Matrix Ix Ix K) (hD : D * D = 0)
    (hex : ∀ v : Ix → K, D.mulVec v = 0 → ∃ w, D.mulVec w = v) :
    ∃ G : Matrix Ix Ix K, IsUnit (D * G + G * D).det := by
  obtain ⟨G, hG⟩ := exists_mul_mul_eq D
  refine ⟨G, ?_⟩
  set N := 1 - (D * G + G * D) with hN
  have h1 : D * N = 0 := by
    rw [hN, mul_sub, mul_add, ← mul_assoc, ← mul_assoc, hD, hG]; simp
  have h2 : N * D = 0 := by
    rw [hN, sub_mul, add_mul, mul_assoc G, hD, hG]; simp
  have h3 : N * N = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    obtain ⟨w, hw⟩ := hex (N.mulVec v) (by rw [Matrix.mulVec_mulVec, h1, Matrix.zero_mulVec])
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← hw, Matrix.mulVec_mulVec, h2,
      Matrix.zero_mulVec, Matrix.zero_mulVec]
  have h4 : (D * G + G * D) * (1 + N) = 1 := by
    have : D * G + G * D = 1 - N := by rw [hN]; abel
    rw [this, sub_mul, mul_add, mul_add, h3]; simp
  exact Matrix.isUnit_det_of_right_inverse h4

theorem exists_contraction {R : Type} [CommRing R] [IsLocalRing R] (D : Matrix Ix Ix R) (hD : D * D = 0)
    (hex : ∀ v : Ix → IsLocalRing.ResidueField R, (D.map (IsLocalRing.residue R)).mulVec v = 0 →
      ∃ w, (D.map (IsLocalRing.residue R)).mulVec w = v) :
    ∃ h : Matrix Ix Ix R, D * h + h * D = 1 := by
  obtain ⟨G, hG⟩ := exists_isUnit_field (D.map (IsLocalRing.residue R))
    (by rw [← Matrix.map_mul, hD]; simp) hex
  choose H hH using fun p q => IsLocalRing.residue_surjective (R := R) (G p q)
  have hHG : (Matrix.of H).map (IsLocalRing.residue R) = G := by ext p q; exact hH p q
  set A := D * Matrix.of H + Matrix.of H * D with hA
  have hu : IsUnit A.det := by
    have : IsLocalRing.residue R A.det = (D.map (IsLocalRing.residue R) * G + G * D.map (IsLocalRing.residue R)).det := by
      rw [RingHom.map_det, ← hHG, hA]
      simp [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_add (f := _)]
    rw [← this] at hG
    exact (isUnit_map_iff _ _).1 hG
  have hc : A * D = D * A := by
    rw [hA, add_mul, mul_add, mul_assoc (Matrix.of H), hD, ← mul_assoc D D, hD]; simp [mul_assoc]
  have hc' : A⁻¹ * D = D * A⁻¹ := by
    calc A⁻¹ * D = A⁻¹ * D * (A * A⁻¹) := by rw [Matrix.mul_nonsing_inv _ hu, mul_one]
      _ = A⁻¹ * (A * D) * A⁻¹ := by rw [hc]; simp only [mul_assoc]
      _ = D * A⁻¹ := by rw [← mul_assoc, Matrix.nonsing_inv_mul _ hu, one_mul]
  refine ⟨Matrix.of H * A⁻¹, ?_⟩
  rw [mul_assoc, hc', ← mul_assoc, ← mul_assoc, ← add_mul, ← hA, Matrix.mul_nonsing_inv _ hu]

theorem exists_homogeneous {R : Type} [CommRing R] (deg : Ix → ℕ) (D h : Matrix Ix Ix R)
    (hD : ∀ p q, deg q ≠ deg p + 1 → D p q = 0) (hh : D * h + h * D = 1) :
    ∃ h' : Matrix Ix Ix R, (∀ p q, deg p ≠ deg q + 1 → h' p q = 0) ∧ D * h' + h' * D = 1 := by
  refine ⟨Matrix.of fun p q => if deg p = deg q + 1 then h p q else 0, fun p q hpq => by simp [hpq], ?_⟩
  ext a b
  by_cases hab : deg a = deg b
  · rw [← hh]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    congr 1 <;> refine Finset.sum_congr rfl fun p _ => ?_
    · split_ifs with hp
      · rfl
      · rw [hD a p (by omega)]; simp
    · split_ifs with hp
      · rfl
      · rw [hD p b (by omega)]; simp
  · rw [Matrix.one_apply_ne (fun e => hab (by rw [e]))]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro p _
      split_ifs with hp
      · rw [hD p b (by omega)]; simp
      · simp
    · intro p _
      split_ifs with hp
      · rw [hD a p (by omega)]; simp
      · simp

theorem block_mul_block {R : Type} [CommRing R] (P Q : Ix → Prop) [DecidablePred P] [DecidablePred Q]
    (M : Matrix Ix Ix R) (hM : M * M = 1) (h0 : ∀ p r, P p → ¬ Q r → M p r = 0) :
    M.submatrix (fun p : {p // P p} => p.1) (fun r : {r // Q r} => r.1) *
      M.submatrix (fun r : {r // Q r} => r.1) (fun p : {p // P p} => p.1) = 1 := by
  ext a b
  have h1 : (M * M) a.1 b.1 = (1 : Matrix {p // P p} {p // P p} R) a b := by
    rw [hM]; simp [Matrix.one_apply, Subtype.ext_iff]
  rw [← h1]
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  rw [← Fintype.sum_subtype_add_sum_subtype Q (fun r => M a.1 r * M r b.1)]
  rw [Finset.sum_eq_zero (s := (Finset.univ : Finset {r // ¬ Q r})), add_zero]
  intro r _
  rw [h0 _ _ a.2 r.2, zero_mul]

theorem nonempty_equiv {R : Type} [CommRing R] [Nontrivial R] (deg : Ix → ℕ) (D h : Matrix Ix Ix R)
    (hD : IsCx deg D) (hdeg : ∀ p q, deg p ≠ deg q + 1 → h p q = 0) (hh : D * h + h * D = 1) :
    Nonempty ({p // Even (deg p)} ≃ {p // ¬ Even (deg p)}) := by
  obtain ⟨hD1, hD2⟩ := hD
  have e1 : D * h = 1 - h * D := eq_sub_of_add_eq hh
  have e2 : D * h * D = D := by rw [e1, sub_mul, mul_assoc, hD2]; simp
  have e3 : D * h * (h * D) = 0 := by
    have : D * h = 1 - h * D := e1
    have e4 : h * D * (h * D) = h * D := by
      rw [mul_assoc, ← mul_assoc D, e2]
    rw [e1, sub_mul, e4]; simp
  set M := D + h * D * h with hM
  have hMM : M * M = 1 := by
    have : M * M = D * D + (D * h * D) * h + h * (D * h * D) + h * (D * h * (h * D)) * h := by
      rw [hM]; noncomm_ring
    rw [this, hD2, e2, e3, ← hh]; simp
  have hpar : ∀ p q, (Even (deg p) ↔ Even (deg q)) → M p q = 0 := by
    intro p q hpq
    have n1 : deg q ≠ deg p + 1 := fun e => by
      rw [e, Nat.even_add_one] at hpq; tauto
    have n2 : deg p ≠ deg q + 1 := fun e => by
      rw [e, Nat.even_add_one] at hpq; tauto
    rw [hM, Matrix.add_apply, hD1 p q n1, zero_add, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases c1 : deg p = deg s + 1
    · by_cases c2 : deg r = deg s + 1
      · rw [hdeg r q (by omega)]; simp
      · rw [hD1 s r c2]; simp
    · rw [hdeg p s c1]; simp
  exact ⟨Matrix.indexEquivOfInv
    (block_mul_block (fun p => Even (deg p)) (fun p => ¬ Even (deg p)) M hMM
      (fun p r hp hr => hpar p r (by tauto)))
    (block_mul_block (fun p => ¬ Even (deg p)) (fun p => Even (deg p)) M hMM
      (fun p r hp hr => hpar p r (by tauto)))⟩

theorem exists_torsSq : ∀ (R Ix : Type) [CommRing R] [Fintype Ix] [DecidableEq Ix] (deg : Ix → ℕ) (D : Matrix Ix Ix R) [IsLocalRing R], IsCx deg D → (∀ v : Ix → IsLocalRing.ResidueField R, (D.map (IsLocalRing.residue R)).mulVec v = 0 → ∃ w, (D.map (IsLocalRing.residue R)).mulVec w = v) → ∃ t, TorsSq deg D t := by
  intro R Ix _ _ _ deg D _ hD hex
  obtain ⟨h0, hh0⟩ := exists_contraction D hD.2 hex
  obtain ⟨h, hdeg, hh⟩ := exists_homogeneous deg D h0 hD.1 hh0
  obtain ⟨e⟩ := nonempty_equiv deg D h hD hdeg hh
  exact ⟨_, h, hdeg, hh, e, rfl⟩

end GlobalTheory.TorsExists
end
