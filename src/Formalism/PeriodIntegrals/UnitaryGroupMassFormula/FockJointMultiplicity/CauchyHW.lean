module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.JointMultOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistGen

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJM

def bRow {σ : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) : Module.End ℂ (MvPolynomial σ ℂ) :=
  ∑ k : Fin n, LinearMap.mulLeft ℂ (X (ι (a, k))) * (pderiv (ι (b, k))).toLinearMap

def bCol {σ : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) : Module.End ℂ (MvPolynomial σ ℂ) :=
  ∑ i : Fin m, LinearMap.mulLeft ℂ (X (ι (i, c))) * (pderiv (ι (i, d))).toLinearMap

def CauchyHW : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (β : Fin n → ℕ) (P : MvPolynomial σ ℂ), P ≠ 0 →
  (∀ a b : Fin m, a < b → bRow ι a b P = 0) → (∀ c d : Fin n, c < d → bCol ι c d P = 0) →
  (∀ e ∈ P.support, (∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) ∧ (∀ k, ∑ i : Fin m, e (ι (i, k)) = β k)) →
  (∀ i, 0 < α i) → (∀ k, 0 < β k) →
  m = n ∧ Antitone α ∧ (∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → α i = β k) ∧
    ∃ Q : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) ∧
      P = shapeProd (Matrix.of fun (i : Fin m) (k : Fin n) => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α) * Q

def MinDegJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  ∀ P ∈ JH p q r s μ μ', P ≠ 0 →
    (∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
    (∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ' ∧ P ∈ homog (Ix p q × Ix r s) d)

abbrev nu1 (p q r s : ℕ) (μ : Ix p q → ℚ) : Ix p q → ℚ := shiftNu (cPair r s) μ
abbrev nu2 (p q r s : ℕ) (μ' : Ix r s → ℚ) : Ix r s → ℚ := shiftNu (cPair p q) μ'

def MinHyp (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s) : Prop :=
  P ∈ JH p q r s μ μ' ∧ P ≠ 0 ∧ ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ (d : ℚ) = degW (cPair p q) μ' ∧
    P ∈ homog (Ix p q × Ix r s) d

def PureJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  ∀ e ∈ P.support, ∀ l : Ln p q r s, e l ≠ 0 →
    nu1 p q r s μ l.1 ≠ 0 ∧ nu2 p q r s μ' l.2 ≠ 0 ∧
    (linePos l = true ↔ 0 < nu1 p q r s μ l.1) ∧ (linePos l = true ↔ 0 < nu2 p q r s μ' l.2)

def SegJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  (∀ i i' : Fin p, i < i' → 0 < nu1 p q r s μ (.inl i') → 0 < nu1 p q r s μ (.inl i)) ∧
  (∀ i i' : Fin p, i < i' → nu1 p q r s μ (.inl i) < 0 → nu1 p q r s μ (.inl i') < 0) ∧
  (∀ j j' : Fin q, j < j' → 0 < nu1 p q r s μ (.inr j') → 0 < nu1 p q r s μ (.inr j)) ∧
  (∀ j j' : Fin q, j < j' → nu1 p q r s μ (.inr j) < 0 → nu1 p q r s μ (.inr j') < 0) ∧
  (∀ k k' : Fin r, k < k' → 0 < nu2 p q r s μ' (.inl k') → 0 < nu2 p q r s μ' (.inl k)) ∧
  (∀ k k' : Fin r, k < k' → nu2 p q r s μ' (.inl k) < 0 → nu2 p q r s μ' (.inl k') < 0) ∧
  (∀ l l' : Fin s, l < l' → 0 < nu2 p q r s μ' (.inr l') → 0 < nu2 p q r s μ' (.inr l)) ∧
  (∀ l l' : Fin s, l < l' → nu2 p q r s μ' (.inr l) < 0 → nu2 p q r s μ' (.inr l') < 0)

end PI.FJM
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistWt
open MvPolynomial FockH1Action PI.FJM

noncomputable section

namespace PI.FJMX

theorem tele (g : ℕ → ℕ) (hg : ∀ t, g (t + 1) ≤ g t) (i₀ : ℕ) (n : ℕ) :
    ∑ t ∈ Finset.range n, (if i₀ ≤ t then (g t - g (t + 1)) else 0) =
      if i₀ < n then g i₀ - g n else 0 := by
  have anti : Antitone g := antitone_nat_of_succ_le hg
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 := hg n
    by_cases h : i₀ < n
    · have h2 : g n ≤ g i₀ := anti h.le
      rw [if_pos h, if_pos (by omega : i₀ ≤ n), if_pos (by omega : i₀ < n + 1)]
      omega
    · by_cases h' : i₀ = n
      · subst h'
        simp
      · rw [if_neg h, if_neg (by omega : ¬ i₀ ≤ n), if_neg (by omega : ¬ i₀ < n + 1)]

theorem getD_succ_le (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) (t : ℕ) :
    α.getD (t + 1) 0 ≤ α.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : t + 1 < α.length
  · rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    exact (List.pairwise_iff_getElem.1 hα) t (t + 1) (by omega) h (by omega)
  · rw [List.getElem?_eq_none (by omega)]
    simp

theorem getD_length (α : List ℕ) : α.getD α.length 0 = 0 := by
  simp

theorem shape_sum (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) (i₀ : ℕ) :
    ∑ t ∈ Finset.range α.length, (α.getD t 0 - α.getD (t + 1) 0) • (if i₀ < t + 1 then 1 else 0) =
      α.getD i₀ 0 := by
  have e : ∀ t, (α.getD t 0 - α.getD (t + 1) 0) • (if i₀ < t + 1 then 1 else 0) =
      if i₀ ≤ t then (α.getD t 0 - α.getD (t + 1) 0) else 0 := by
    intro t
    by_cases h : i₀ ≤ t
    · rw [if_pos (by omega), if_pos h]; simp
    · rw [if_neg (by omega), if_neg h]; simp
  simp only [e]
  rw [tele (fun t => α.getD t 0) (getD_succ_le α hα), getD_length]
  split_ifs with h
  · simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

variable {p q r s m k : ℕ}

theorem leadT_hom_row (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (i₀ : Fin m)
    (hw : ∀ i j, w (ρ i, κ j) = if i = i₀ then 1 else 0) (t : ℕ) :
    IsWeightedHomogeneous w (leadT (varMat ρ κ) t) (if i₀.val < t then 1 else 0) := by
  classical
  unfold leadT
  split_ifs with hh hlt
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun i => if Fin.castLE hh.1 i = i₀ then 1 else 0) (fun _ => 0) (fun i j => by simp [hw])
    have hs : ∑ i : Fin t, (if Fin.castLE hh.1 i = i₀ then 1 else 0) + ∑ _j : Fin t, 0 = 1 := by
      simp only [Finset.sum_const_zero, add_zero]
      rw [Finset.sum_eq_single ⟨i₀.val, hlt⟩]
      · simp [Fin.ext_iff]
      · intro i _ hi
        rw [if_neg]
        intro e
        apply hi
        ext
        simp [← e]
      · simp
    rw [hs] at this
    exact this
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun i => if Fin.castLE hh.1 i = i₀ then 1 else 0) (fun _ => 0) (fun i j => by simp [hw])
    have hs : ∑ i : Fin t, (if Fin.castLE hh.1 i = i₀ then 1 else 0) + ∑ _j : Fin t, 0 = 0 := by
      simp only [Finset.sum_const_zero, add_zero]
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      intro e
      apply hlt
      rw [← e]
      simp
    rw [hs] at this
    exact this
  · exact isWeightedHomogeneous_zero _ _ _
  · exact isWeightedHomogeneous_zero _ _ _

theorem leadT_hom_col (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (j₀ : Fin k)
    (hw : ∀ i j, w (ρ i, κ j) = if j = j₀ then 1 else 0) (t : ℕ) :
    IsWeightedHomogeneous w (leadT (varMat ρ κ) t) (if j₀.val < t then 1 else 0) := by
  classical
  unfold leadT
  split_ifs with hh hlt
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun _ => 0) (fun j => if Fin.castLE hh.2 j = j₀ then 1 else 0) (fun i j => by simp [hw])
    have hs : ∑ _i : Fin t, 0 + ∑ j : Fin t, (if Fin.castLE hh.2 j = j₀ then 1 else 0) = 1 := by
      simp only [Finset.sum_const_zero, zero_add]
      rw [Finset.sum_eq_single ⟨j₀.val, hlt⟩]
      · simp [Fin.ext_iff]
      · intro j _ hj
        rw [if_neg]
        intro e
        apply hj
        ext
        simp [← e]
      · simp
    rw [hs] at this
    exact this
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun _ => 0) (fun j => if Fin.castLE hh.2 j = j₀ then 1 else 0) (fun i j => by simp [hw])
    have hs : ∑ _i : Fin t, 0 + ∑ j : Fin t, (if Fin.castLE hh.2 j = j₀ then 1 else 0) = 0 := by
      simp only [Finset.sum_const_zero, zero_add]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro e
      apply hlt
      rw [← e]
      simp
    rw [hs] at this
    exact this
  · exact isWeightedHomogeneous_zero _ _ _
  · exact isWeightedHomogeneous_zero _ _ _

theorem leadT_hom_zero (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ)
    (hw : ∀ i j, w (ρ i, κ j) = 0) (t : ℕ) :
    IsWeightedHomogeneous w (leadT (varMat ρ κ) t) 0 := by
  unfold leadT
  split_ifs with hh
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun _ => 0) (fun _ => 0) (fun i j => by simp [hw])
    simp only [Finset.sum_const_zero, add_zero] at this
    exact this
  · exact isWeightedHomogeneous_zero _ _ _

theorem shapeProd_hom_of (M : Matrix (Fin m) (Fin k) (Pol p q r s)) (w : Ln p q r s → ℕ) (α : List ℕ)
    (deg : ℕ → ℕ) (h : ∀ t, IsWeightedHomogeneous w (leadT M t) (deg t)) :
    IsWeightedHomogeneous w (shapeProd M α)
      (∑ t ∈ Finset.range α.length, (α.getD t 0 - α.getD (t + 1) 0) • deg (t + 1)) := by
  unfold shapeProd
  exact IsWeightedHomogeneous.prod _ _ _ fun t _ => (h (t + 1)).pow _

theorem shapeProd_hom_row (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (i₀ : Fin m)
    (hw : ∀ i j, w (ρ i, κ j) = if i = i₀ then 1 else 0) (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) :
    IsWeightedHomogeneous w (shapeProd (varMat ρ κ) α) (α.getD i₀.val 0) := by
  have := shapeProd_hom_of (varMat ρ κ) w α _ (leadT_hom_row ρ κ w i₀ hw)
  rwa [shape_sum α hα] at this

theorem shapeProd_hom_col (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (j₀ : Fin k)
    (hw : ∀ i j, w (ρ i, κ j) = if j = j₀ then 1 else 0) (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) :
    IsWeightedHomogeneous w (shapeProd (varMat ρ κ) α) (α.getD j₀.val 0) := by
  have := shapeProd_hom_of (varMat ρ κ) w α _ (leadT_hom_col ρ κ w j₀ hw)
  rwa [shape_sum α hα] at this

theorem shapeProd_hom_zero (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ)
    (hw : ∀ i j, w (ρ i, κ j) = 0) (α : List ℕ) :
    IsWeightedHomogeneous w (shapeProd (varMat ρ κ) α) 0 := by
  have := shapeProd_hom_of (varMat ρ κ) w α _ (leadT_hom_zero ρ κ w hw)
  simpa using this

end PI.FJMX
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ShapeProdVarMatNeZero
noncomputable section

open Matrix FockH1Action

namespace PI.FJMD

open PI.FJM

theorem det_mem_subalgebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine sum_mem fun τ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

theorem shapeProd_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
    {m k : ℕ} (M : Matrix (Fin m) (Fin k) A) (α : List ℕ)
    (h : ∀ (i : Fin m) (j : Fin k), i.val < α.length → j.val < α.length → M i j ∈ S) :
    shapeProd M α ∈ S := by
  unfold PI.FJM.shapeProd
  refine prod_mem fun t ht => pow_mem ?_ _
  have ht' : t < α.length := Finset.mem_range.mp ht
  unfold PI.FJM.leadT
  split_ifs with hc
  · apply det_mem_subalgebra S
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    rw [Matrix.submatrix_apply]
    exact h _ _ (show i.val < α.length by omega) (show j.val < α.length by omega)
  · exact zero_mem _

theorem det_vars_ne_zero {σ : Type*} {n : ℕ} (f : Fin n × Fin n → σ) (hf : Function.Injective f) :
    (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ)).det ≠ 0 := by
  classical
  intro h0
  have hg : ∀ i j, (if ∃ i', f (i', i') = f (i, j) then (1 : ℂ) else 0) =
      if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos ⟨i, rfl⟩, if_pos rfl]
    · rw [if_neg hij, if_neg]
      rintro ⟨i', hi'⟩
      have hpair := hf hi'
      simp only [Prod.mk.injEq] at hpair
      exact hij (hpair.1.symm.trans hpair.2)
  have hmap : (MvPolynomial.eval (fun x : σ => if ∃ i', f (i', i') = x then (1 : ℂ) else 0)).mapMatrix
      (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ)) = 1 := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.one_apply]
    exact hg i j
  have hdet := RingHom.map_det (MvPolynomial.eval (fun x : σ => if ∃ i', f (i', i') = x then (1 : ℂ) else 0))
    (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ))
  rw [h0, map_zero, hmap, Matrix.det_one] at hdet
  exact zero_ne_one hdet

theorem shapeProd_varMat_ne_zero {p q r s m k : ℕ} (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (hρ : Function.Injective ρ) (hκ : Function.Injective κ) (α : List ℕ)
    (hm : α.length ≤ m) (hk : α.length ≤ k) : shapeProd (varMat (r := r) (s := s) ρ κ) α ≠ 0 := by
  unfold PI.FJM.shapeProd
  rw [Finset.prod_ne_zero_iff]
  intro t ht
  have ht' : t < α.length := Finset.mem_range.mp ht
  apply pow_ne_zero
  have hc : t + 1 ≤ m ∧ t + 1 ≤ k := ⟨by omega, by omega⟩
  unfold PI.FJM.leadT
  rw [dite_eq_left hc]
  have hinj : Function.Injective
      (fun x : Fin (t + 1) × Fin (t + 1) => (ρ (Fin.castLE hc.1 x.1), κ (Fin.castLE hc.2 x.2))) := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hxy
    simp only [Prod.mk.injEq] at hxy ⊢
    exact ⟨Fin.castLE_injective _ (hρ hxy.1), Fin.castLE_injective _ (hκ hxy.2)⟩
  exact det_vars_ne_zero
    (fun x : Fin (t + 1) × Fin (t + 1) => (ρ (Fin.castLE hc.1 x.1), κ (Fin.castLE hc.2 x.2))) hinj

private theorem pderiv_pderiv_comm_of_complex {σ : Type*} (i j : σ) (P : MvPolynomial σ ℂ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j P) = MvPolynomial.pderiv j (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.pderiv_C, map_zero]
  next P Q hP hQ =>
    simp only [map_add (f := _), hP, hQ]
  next P n hP =>
    simp only [Derivation.leibniz, map_add (f := _), smul_eq_mul, MvPolynomial.pderiv_X, Pi.single_apply]
    split_ifs <;>
      simp only [Derivation.map_one_eq_zero, map_zero, mul_zero, zero_mul, add_zero, zero_add,
        mul_one, one_mul, hP] <;> ring

private theorem pderiv_eq_zero_of_mem_supported_of_not_mem {σ : Type*} {S : Set σ} {P : MvPolynomial σ ℂ}
    (hP : P ∈ MvPolynomial.supported ℂ S) {i : σ} (hi : i ∉ S) : MvPolynomial.pderiv i P = 0 := by
  have hv : i ∉ P.vars := fun hmem => hi ((MvPolynomial.mem_supported.mp hP) (Finset.mem_coe.mpr hmem))
  first
  | exact MvPolynomial.pderiv_eq_zero_of_notMem_vars hv
  | exact MvPolynomial.pderiv_eq_zero_of_not_mem_vars hv

theorem dd_eq_zero {p q r s : ℕ} {S : Set (Ln p q r s)} {P : Pol p q r s}
    (hP : P ∈ MvPolynomial.supported ℂ S) {l l' : Ln p q r s} (h : l ∉ S ∨ l' ∉ S) : dd l l' P = 0 := by
  have key : PI.FJM.dd l l' P = MvPolynomial.pderiv l (MvPolynomial.pderiv l' P) := by
    first
    | rfl
    | simp [PI.FJM.dd]
  rw [key]
  rcases h with h | h
  · rw [pderiv_pderiv_comm_of_complex, pderiv_eq_zero_of_mem_supported_of_not_mem hP h, map_zero]
  · rw [pderiv_eq_zero_of_mem_supported_of_not_mem hP h, map_zero]

def inS {p q r s : ℕ} (la lb lc ld : ℕ) : Ln p q r s → Prop
  | (Sum.inl i, Sum.inl k) => i.val < la ∧ k.val < la
  | (Sum.inl i, Sum.inr l) => p ≤ i.val + lb ∧ s ≤ l.val + lb
  | (Sum.inr j, Sum.inr l) => j.val < lc ∧ l.val < lc
  | (Sum.inr j, Sum.inl k) => q ≤ j.val + ld ∧ r ≤ k.val + ld

theorem posPart_length (a : List ℤ) : (PI.FJM.posPart a).length = a.length := by
  simp [PI.FJM.posPart]

theorem negPart_length (b : List ℤ) : (PI.FJM.negPart b).length = b.length := by
  simp [PI.FJM.negPart]

private theorem fin_rev_val {n : ℕ} (i : Fin n) : (Fin.rev i).val = n - (i.val + 1) := rfl

private theorem varMat_apply_mem_supported {p q r s m k : ℕ} (ρ : Fin m → FockH1Action.Ix p q)
    (κ : Fin k → FockH1Action.Ix r s) (T : Set (FockH1Action.Ln p q r s)) (i : Fin m) (j : Fin k)
    (h : (ρ i, κ j) ∈ T) : PI.FJM.varMat ρ κ i j ∈ MvPolynomial.supported ℂ T := by
  rw [show PI.FJM.varMat ρ κ i j = MvPolynomial.X (ρ i, κ j) from rfl]
  first
  | exact MvPolynomial.X_mem_supported.mpr h
  | exact MvPolynomial.mem_supported.mpr (by rw [MvPolynomial.vars_X]; simpa using h)

theorem hwVec_mem_supported (p q r s : ℕ) (a b c d : List ℤ) :
    hwVec p q r s a b c d ∈ MvPolynomial.supported ℂ
      {l : Ln p q r s | inS a.length b.length c.length d.length l} := by
  unfold PI.FJM.hwVec
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_
  · apply shapeProd_mem
    intro i j hi hj
    rw [posPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS]
    exact ⟨hi, hj⟩
  · apply shapeProd_mem
    intro i j hi hj
    rw [negPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS, fin_rev_val]
    have := i.isLt
    have := j.isLt
    constructor <;> omega
  · apply shapeProd_mem
    intro i j hi hj
    rw [posPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS]
    exact ⟨hi, hj⟩
  · apply shapeProd_mem
    intro i j hi hj
    rw [negPart_length] at hi hj
    apply varMat_apply_mem_supported
    simp only [Set.mem_setOf_eq, inS, fin_rev_val]
    have := i.isLt
    have := j.isLt
    constructor <;> omega

theorem shapeVector_ne_zero : VecNe := by
  intro p q r s a b c d h
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := h
  unfold PI.FJM.hwVec
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Sum.inl_injective hxy) (by intro x y hxy; exact Sum.inl_injective hxy) _
      (by rw [posPart_length]; omega) (by rw [posPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Fin.rev_injective (Sum.inl_injective hxy))
      (by intro x y hxy; exact Fin.rev_injective (Sum.inr_injective hxy)) _
      (by rw [negPart_length]; omega) (by rw [negPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Sum.inr_injective hxy) (by intro x y hxy; exact Sum.inr_injective hxy) _
      (by rw [posPart_length]; omega) (by rw [posPart_length]; omega)
  · exact shapeProd_varMat_ne_zero _ _
      (by intro x y hxy; exact Fin.rev_injective (Sum.inr_injective hxy))
      (by intro x y hxy; exact Fin.rev_injective (Sum.inl_injective hxy)) _
      (by rw [negPart_length]; omega) (by rw [negPart_length]; omega)

private theorem moduleEnd_finset_sum_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    (t : Finset ι) (f : ι → Module.End ℂ V) (v : V) : (∑ x ∈ t, f x) v = ∑ x ∈ t, f x v := by
  first
  | exact LinearMap.sum_apply t f v
  | simp

theorem vecJ_of (hF : FormJ) : VecJ := by
  intro p q r s a b c d h
  have hsupp := hwVec_mem_supported p q r s a b c d
  obtain ⟨-, -, -, -, -, -, -, -, h1, h2, h3, h4⟩ := h
  refine (hF p q r s (PI.FJM.hwVec p q r s a b c d)).mpr ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    unfold PI.FJM.lapA
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun l _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro i j
    unfold PI.FJM.lapB
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun k _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro k l
    unfold PI.FJM.lapC
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun i _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega
  · intro k l
    unfold PI.FJM.lapD
    rw [moduleEnd_finset_sum_apply]
    refine Finset.sum_eq_zero fun j _ => dd_eq_zero hsupp ?_
    refine not_and_or.mp ?_
    rintro ⟨hx, hy⟩
    simp only [Set.mem_setOf_eq, inS] at hx hy
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨hy1, hy2⟩ := hy
    omega

end PI.FJMD
end
end
