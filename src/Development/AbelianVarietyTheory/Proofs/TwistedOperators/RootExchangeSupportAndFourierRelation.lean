module

public import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.WithZeroEqOfLeExpIff
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SemilinearExtensionBases

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelation
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology

noncomputable section
namespace GlobalTheory.RootEx.ExchangeSupport

section Algebra
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

def rowM (c p : ℕ) (u : n → k) : Matrix (Fin c) n k :=
  Matrix.of fun l s => if l.val + 1 = p then u s else 0

def colM (c p : ℕ) (β : n → k) : Matrix n (Fin c) k :=
  Matrix.of fun r i => if i.val + 1 = p then β r else 0

theorem rowE_val (u : n → k) : (rowE c p u).val = fromBlocks 1 0 (rowM c p u) 1 := rfl
theorem colE_val (u : n → k) : (colE c p u).val = fromBlocks 1 (colM c p u) 0 1 := rfl
theorem rowE_inv_val (u : n → k) : ((rowE c p u)⁻¹).val = fromBlocks 1 0 (-rowM c p u) 1 := rfl
theorem colE_inv_val (u : n → k) : ((colE c p u)⁻¹).val = fromBlocks 1 (-colM c p u) 0 1 := rfl

omit [DecidableEq n] [Fintype n] in
theorem colM_mul_rowM (u β : n → k) : colM c (p + 1) β * rowM c p u = 0 := by
  ext r s
  simp only [colM, rowM, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with h1 h2
  · omega
  all_goals simp

omit [DecidableEq n] in
theorem rowM_mul_colM (u β : n → k) (i j : Fin c) :
    (rowM c p u * colM c (p + 1) β) i j = if i.val + 1 = p ∧ j.val = p then u ⬝ᵥ β else 0 := by
  simp only [colM, rowM, Matrix.mul_apply, Matrix.of_apply, dotProduct]
  by_cases h1 : i.val + 1 = p <;> by_cases h2 : j.val = p <;> simp [h1, h2]

theorem rowE_add (u w : n → k) : rowE c p (u + w) = rowE c p u * rowE c p w := by
  apply Units.ext
  rw [Units.val_mul, rowE_val, rowE_val, rowE_val]
  have : rowM c p (u + w) = rowM c p u + rowM c p w := by
    ext i j; simp only [rowM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]; split_ifs <;> simp
  simp [fromBlocks_multiply, this]

theorem colE_add (u w : n → k) : colE c p (u + w) = colE c p u * colE c p w := by
  apply Units.ext
  rw [Units.val_mul, colE_val, colE_val, colE_val]
  have : colM c p (u + w) = colM c p w + colM c p u := by
    ext i j; simp only [colM, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp [add_comm]
  simp [fromBlocks_multiply, this]

theorem rowE_zero : rowE c p (0 : n → k) = 1 := by
  have := rowE_add (c := c) (p := p) (0 : n → k) 0
  rw [add_zero] at this
  exact left_eq_mul.mp this

theorem colE_zero : colE c p (0 : n → k) = 1 := by
  have := colE_add (c := c) (p := p) (0 : n → k) 0
  rw [add_zero] at this
  exact left_eq_mul.mp this

theorem simpleSum_eq (hp : 1 ≤ p) (hc : p < c) (g : GL (n ⊕ Fin c) k) (t : k)
    (h : ∀ i j : Fin c, g.val (Sum.inr i) (Sum.inr j) =
      (1 : Matrix (Fin c) (Fin c) k) i j + if i.val + 1 = p ∧ j.val = p then t else 0) :
    simpleSum g = t := by
  unfold simpleSum
  rw [Finset.sum_eq_single (⟨p - 1, by omega⟩ : Fin c), Finset.sum_eq_single (⟨p, hc⟩ : Fin c)]
  · have h1 : p - 1 + 1 = p := by omega
    have h2 : (⟨p - 1, by omega⟩ : Fin c) ≠ ⟨p, hc⟩ := by
      simp only [ne_eq, Fin.mk.injEq]; omega
    simp [h, h1, Matrix.one_apply_ne h2]
  · intro j _ hj
    have : j.val ≠ p - 1 + 1 := fun e => hj (Fin.ext (by simp only; omega))
    simp [this]
  · simp
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hj
    · have h1 : i.val + 1 ≠ p := fun e => hi (Fin.ext (by simp only; omega))
      have h2 : i ≠ j := fun e => by subst e; omega
      simp [h, h1, Matrix.one_apply_ne h2]
    · rfl
  · simp

theorem conj_col (hp : 1 ≤ p) (hc : p < c) (u β : n → k) :
    rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹ ∈ N k n c p ∧
      simpleSum (rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹) = u ⬝ᵥ β := by
  have hv : (rowE c p u * colE c (p + 1) β * (rowE c p u)⁻¹).val =
      fromBlocks 1 (colM c (p + 1) β) 0 (1 + rowM c p u * colM c (p + 1) β) := by
    rw [Units.val_mul, Units.val_mul, rowE_val, colE_val, rowE_inv_val]
    simp [fromBlocks_multiply, Matrix.add_mul, Matrix.mul_assoc, colM_mul_rowM, add_comm]
  refine ⟨Subgroup.subset_closure ?_, simpleSum_eq hp hc _ _ ?_⟩
  · intro r s hrs
    rw [hv, ← fromBlocks_one]
    rcases r with r | r <;> rcases s with s | s
    · rfl
    · have : s.val ≠ p := by simp [lev] at hrs; omega
      simp [colM, this]
    · rfl
    · have : ¬ (r.val + 1 = p ∧ s.val = p) := by simp [lev] at hrs; omega
      simp [rowM_mul_colM, this]
  · intro i j
    rw [hv]; simp [rowM_mul_colM]

theorem conj_row (hp : 1 ≤ p) (hc : p < c) (u β : n → k) :
    colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹ ∈ N k n c (p + 1) ∧
      simpleSum (colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹) = -(u ⬝ᵥ β) := by
  have hv : (colE c (p + 1) β * rowE c p u * (colE c (p + 1) β)⁻¹).val =
      fromBlocks 1 0 (rowM c p u) (1 - rowM c p u * colM c (p + 1) β) := by
    rw [Units.val_mul, Units.val_mul, rowE_val, colE_val, colE_inv_val]
    simp [fromBlocks_multiply, colM_mul_rowM, sub_eq_add_neg, add_comm]
  refine ⟨Subgroup.subset_closure ?_, simpleSum_eq hp hc _ _ ?_⟩
  · intro r s hrs
    rw [hv, ← fromBlocks_one]
    rcases r with r | r <;> rcases s with s | s
    · rfl
    · rfl
    · have : r.val + 1 ≠ p := by simp [lev] at hrs; omega
      simp [rowM, this]
    · have : ¬ (r.val + 1 = p ∧ s.val = p) := by simp [lev] at hrs; omega
      simp [rowM_mul_colM, this]
  · intro i j
    rw [hv]; simp only [fromBlocks_apply₂₂, Matrix.sub_apply, rowM_mul_colM]
    split_ifs <;> simp [sub_eq_add_neg]

end Algebra

section Top
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}

omit [Fintype n] [DecidableEq n] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_rowM : Continuous fun u : n → k => rowM c p u := by
  refine continuous_matrix fun i j => ?_
  simp only [rowM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply j
  · exact continuous_const

omit [Fintype n] [DecidableEq n] [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem continuous_colM : Continuous fun u : n → k => colM c p u := by
  refine continuous_matrix fun i j => ?_
  simp only [colM, Matrix.of_apply]
  split_ifs
  · exact continuous_apply i
  · exact continuous_const

theorem continuous_rowE : Continuous fun u : n → k => rowE c p u := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_rowM continuous_const
  · exact Continuous.matrix_fromBlocks continuous_const continuous_const continuous_rowM.neg continuous_const

theorem continuous_colE : Continuous fun u : n → k => colE c p u := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Continuous.matrix_fromBlocks continuous_const continuous_colM continuous_const continuous_const
  · exact Continuous.matrix_fromBlocks continuous_const continuous_colM.neg continuous_const continuous_const

theorem mem_SB_of {ψ : AddChar k Circle} (hψ : ψ ≠ 1) (f : (n → k) → ℂ)
    (h1 : ∀ᶠ w in 𝓝 (0 : n → k), ∀ u, f (u + w) = f u)
    (h2 : ∀ᶠ β in 𝓝 (0 : n → k), ∀ u, f u = (ψ (u ⬝ᵥ β) : ℂ) * f u) : f ∈ SB (n → k) := by
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have ht : Tendsto (fun y : n → k => y - x) (𝓝 x) (𝓝 0) := by
      have : Continuous fun y : n → k => y - x := by fun_prop
      simpa using this.tendsto x
    filter_upwards [ht.eventually h1] with y hy
    simpa using hy x
  · obtain ⟨x₀, hx₀⟩ : ∃ x₀, ψ x₀ ≠ 1 := by
      by_contra h
      push Not at h
      exact hψ (by ext x; simp [h])
    have h3 : ∀ᶠ y in 𝓝 (0 : k), ∀ i : n, ∀ u, f u = (ψ (u ⬝ᵥ Pi.single i y) : ℂ) * f u := by
      rw [eventually_all]
      intro i
      have : Continuous fun y : k => (Pi.single i y : n → k) := continuous_single (A := fun _ : n => k) i
      have ht := this.tendsto 0
      rw [Pi.single_zero] at ht
      exact ht.eventually h2
    obtain ⟨γ, hγ, hs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' k).mem_iff.mp h3
    refine HasCompactSupport.intro
      (isCompact_univ_pi fun _ : n =>
        IsNonarchimedeanLocalField.isCompact_closedBall k (valuation k x₀ / γ)) ?_
    intro u hu
    simp only [Set.mem_pi, Set.mem_univ, true_imp_iff, not_forall, Set.mem_ofPred_eq, not_le] at hu
    obtain ⟨i, hi⟩ := hu
    have hu0 : u i ≠ 0 := by
      intro e; rw [e] at hi; simp at hi
    have hv0 : 0 < valuation k (u i) := lt_of_le_of_lt zero_le hi
    have hγ0 : 0 < γ := zero_lt_iff.2 hγ
    have hy : valuation k (x₀ / u i) < γ := by
      rw [map_div₀, div_lt_iff₀ hv0]
      rw [div_lt_iff₀ hγ0] at hi
      rwa [mul_comm]
    have := hs hy i u
    rw [dotProduct_single, mul_div_cancel₀ _ hu0] at this
    by_contra hf
    apply hx₀
    have h4 : (ψ x₀ : ℂ) = 1 := by
      have h5 : (ψ x₀ : ℂ) * f u = 1 * f u := by rw [one_mul]; exact this.symm
      exact mul_right_cancel₀ hf h5
    exact Circle.ext (by simpa using h4)

end Top

theorem exchange_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (IsNEquiv ψ p σ l → (fun u : n → k => l (σ (rowE c p u) v)) ∈ SB (n → k) ∧ (∀ u β : n → k, l (σ (rowE c p u) (σ (colE c (p + 1) β) v)) = (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v)) ∧ ∀ β : n → k, exUp ν p σ l (σ (colE c (p + 1) β) v) = ∫ u : n → k, (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)) ∧ (IsNEquiv ψ (p + 1) σ l → (fun β : n → k => l (σ (colE c (p + 1) β) v)) ∈ SB (n → k) ∧ ∀ u β : n → k, l (σ (colE c (p + 1) β) (σ (rowE c p u) v)) = (ψ (-(u ⬝ᵥ β)) : ℂ) * l (σ (colE c (p + 1) β) v)) := by
  intro k _ _ _ _ _ _ n _ _ c p hp hc ψ _ hψ ν _ A _ _ σ hσ l v
  have hrow : ∀ᶠ w in 𝓝 (0 : n → k), σ (rowE c p w) v = v :=
    continuous_rowE.continuousAt.eventually_mem ((hσ v).mem_nhds (by simp [rowE_zero]))
  have hcol : ∀ᶠ w in 𝓝 (0 : n → k), σ (colE c (p + 1) w) v = v :=
    continuous_colE.continuousAt.eventually_mem ((hσ v).mem_nhds (by simp [colE_zero]))
  have hmul : ∀ (a b : GL (n ⊕ Fin c) k), σ a (σ b v) = σ (a * b * a⁻¹) (σ a v) := by
    intro a b
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · have key : ∀ u β : n → k, l (σ (rowE c p u) (σ (colE c (p + 1) β) v)) =
        (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v) := by
      intro u β
      rw [hmul, hl _ (conj_col hp hc u β).1, (conj_col hp hc u β).2]
    refine ⟨mem_SB_of hψ _ ?_ ?_, key, fun β => ?_⟩
    · filter_upwards [hrow] with w hw u
      rw [rowE_add, map_mul, Module.End.mul_apply, hw]
    · filter_upwards [hcol] with w hw u
      rw [← key, hw]
    · simp only [exUp, key]
  · have key : ∀ u β : n → k, l (σ (colE c (p + 1) β) (σ (rowE c p u) v)) =
        (ψ (-(u ⬝ᵥ β)) : ℂ) * l (σ (colE c (p + 1) β) v) := by
      intro u β
      rw [hmul, hl _ (conj_row hp hc u β).1, (conj_row hp hc u β).2]
    refine ⟨mem_SB_of hψ _ ?_ ?_, key⟩
    · filter_upwards [hcol] with w hw u
      rw [colE_add, map_mul, Module.End.mul_apply, hw]
    · have hneg : Tendsto (fun w : n → k => -w) (𝓝 0) (𝓝 0) := by
        simpa using (continuous_neg (G := n → k)).tendsto 0
      filter_upwards [hneg.eventually hrow] with w hw u
      have := key (-w) u
      rwa [hw, neg_dotProduct, neg_neg, dotProduct_comm] at this

end GlobalTheory.RootEx.ExchangeSupport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeSupportAndFourierRelationStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchange_support_and_fourier_relation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1) (ν : Measure k) [ν.IsAddHaarMeasure] (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (l : A →ₗ[ℂ] ℂ) (v : A), (IsNEquiv ψ p σ l → (fun u : n → k => l (σ (rowE c p u) v)) ∈ SB (n → k) ∧ (∀ u β : n → k, l (σ (rowE c p u) (σ (colE c (p + 1) β) v)) = (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v)) ∧ ∀ β : n → k, exUp ν p σ l (σ (colE c (p + 1) β) v) = ∫ u : n → k, (ψ (u ⬝ᵥ β) : ℂ) * l (σ (rowE c p u) v) ∂(Measure.pi fun _ => ν)) ∧ (IsNEquiv ψ (p + 1) σ l → (fun β : n → k => l (σ (colE c (p + 1) β) v)) ∈ SB (n → k) ∧ ∀ u β : n → k, l (σ (colE c (p + 1) β) (σ (rowE c p u) v)) = (ψ (-(u ⬝ᵥ β)) : ℂ) * l (σ (colE c (p + 1) β) v)) := by
  first | exact @GlobalTheory.RootEx.ExchangeSupport.exchange_support | exact GlobalTheory.RootEx.ExchangeSupport.exchange_support | (intros; apply GlobalTheory.RootEx.ExchangeSupport.exchange_support <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd
open Module GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula

namespace GlobalTheory.GaussCount

private lemma cast_prod_pow_sub_pow_eq_prod_pow_mul_prod (q m a : ℕ) (hq : 0 < q) (h : a ≤ m) :
    ((∏ i ∈ Finset.range a, (q ^ m - q ^ i) : ℕ) : ℤ) =
      (∏ i ∈ Finset.range a, (q : ℤ) ^ i) * ∏ i ∈ Finset.range a, ((q : ℤ) ^ (m - i) - 1) := by
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ m := by have := Finset.mem_range.mp hi; omega
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq hi')]
  have e : (q : ℤ) ^ m = (q : ℤ) ^ i * (q : ℤ) ^ (m - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi']
  push_cast
  rw [e]
  ring

private lemma gaussBinom_self (q n : ℕ) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n n = 1 := by
  induction n with
  | zero => exact _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right q 0
  | succ n ih =>
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero q n (n + 1) (by omega),
      Nat.sub_self, pow_zero, ih]
    rfl

private lemma gaussBinom_mul_prod_pow_succ_sub_one (q n a : ℕ) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a : ℤ) * ∏ i ∈ Finset.range a, ((q : ℤ) ^ (i + 1) - 1) =
      ∏ i ∈ Finset.range a, ((q : ℤ) ^ (n - i) - 1) := by
  induction n generalizing a with
  | zero =>
    rcases a with _ | a
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right]
    · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_succ, Finset.prod_range_succ']
      simp
  | succ n ih =>
    rcases a with _ | a
    · simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right]
    · have h1 := ih (a + 1)
      have h2 := ih a
      rw [Finset.prod_range_succ, Finset.prod_range_succ] at h1
      have hB : (∏ i ∈ Finset.range a, ((q : ℤ) ^ (n - i) - 1)) *
          ((q : ℤ) ^ (n - a) * (q : ℤ) ^ (a + 1) - (q : ℤ) ^ (n + 1)) = 0 := by
        by_cases han : a ≤ n
        · rw [← pow_add, show n - a + (a + 1) = n + 1 by omega]
          ring
        · rw [Finset.prod_eq_zero (i := n) (Finset.mem_range.mpr (by omega)) (by simp)]
          ring
      rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ, Finset.prod_range_succ, Finset.prod_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      push_cast
      linear_combination h1 + (q : ℤ) ^ (n - a) * ((q : ℤ) ^ (a + 1) - 1) * h2 + hB

private lemma prod_pow_succ_sub_one_eq_prod_pow_sub (q n : ℕ) :
    ∏ i ∈ Finset.range n, ((q : ℤ) ^ (i + 1) - 1) = ∏ i ∈ Finset.range n, ((q : ℤ) ^ (n - i) - 1) := by
  simpa [gaussBinom_self] using gaussBinom_mul_prod_pow_succ_sub_one q n n

private lemma prod_pow_succ_sub_one_ne_zero {q : ℕ} (hq : 1 < q) (n : ℕ) :
    ∏ i ∈ Finset.range n, ((q : ℤ) ^ (i + 1) - 1) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have : (1 : ℤ) < (q : ℤ) ^ (i + 1) := one_lt_pow₀ (by exact_mod_cast hq) (by omega)
  linarith

private lemma card_submodule_finrank_eq_gaussBinom (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V]
    [Module k V] [FiniteDimensional k V] (j : ℕ) :
    Nat.card {L : Submodule k V // finrank k L = j} =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Nat.card k) (finrank k V) j := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  by_cases hj : j ≤ finrank k V
  · have h := _root_.GlobalTheory.SubspaceNumber.card_subspaces_mul k V j hj
    have hZ := congrArg (fun x : ℕ => (x : ℤ)) h
    simp only [Nat.cast_mul] at hZ
    rw [cast_prod_pow_sub_pow_eq_prod_pow_mul_prod (Nat.card k) j j (by omega) le_rfl,
      cast_prod_pow_sub_pow_eq_prod_pow_mul_prod (Nat.card k) _ j (by omega) hj,
      ← prod_pow_succ_sub_one_eq_prod_pow_sub (Nat.card k) j,
      ← gaussBinom_mul_prod_pow_succ_sub_one (Nat.card k) (finrank k V) j] at hZ
    have hQ : ∏ i ∈ Finset.range j, ((Nat.card k : ℕ) : ℤ) ^ i ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ =>
        pow_ne_zero _ (by exact_mod_cast (show Nat.card k ≠ 0 by omega))
    have hF := prod_pow_succ_sub_one_ne_zero hq j
    have key : (Nat.card {L : Submodule k V // finrank k L = j} : ℤ) =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Nat.card k) (finrank k V) j := by
      apply mul_right_cancel₀ (mul_ne_zero hQ hF)
      linear_combination hZ
    exact_mod_cast key
  · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero _ _ _ (by omega)]
    haveI : IsEmpty {L : Submodule k V // finrank k L = j} :=
      ⟨fun ⟨L, hL⟩ => by have := Submodule.finrank_le L; omega⟩
    exact Nat.card_of_isEmpty

theorem _root_.GlobalTheory.GaussCount.subspaceCount : _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.SubspaceCount := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.SubspaceCount
  intro k _ _ V _ _ _ j
  exact card_submodule_finrank_eq_gaussBinom k V j

private lemma gaussBinom_mul_prod_mul_prod_sub_eq_prod (q n a : ℕ) (h : a ≤ n) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a : ℤ) * (∏ i ∈ Finset.range a, ((q : ℤ) ^ (i + 1) - 1)) *
        (∏ i ∈ Finset.range (n - a), ((q : ℤ) ^ (i + 1) - 1)) =
      ∏ i ∈ Finset.range n, ((q : ℤ) ^ (i + 1) - 1) := by
  rw [mul_assoc, ← mul_assoc (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a : ℤ), gaussBinom_mul_prod_pow_succ_sub_one, prod_pow_succ_sub_one_eq_prod_pow_sub q (n - a), prod_pow_succ_sub_one_eq_prod_pow_sub q n]
  have hsplit := Finset.prod_range_add (fun i => (q : ℤ) ^ (n - i) - 1) a (n - a)
  rw [Nat.add_sub_cancel' h] at hsplit
  rw [hsplit]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.sub_sub]

private lemma gaussBinom_sub_eq_gaussBinom {q : ℕ} (hq : 1 < q) (n a : ℕ) (h : a ≤ n) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n (n - a) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a := by
  have h1 := gaussBinom_mul_prod_mul_prod_sub_eq_prod q n a h
  have h2 := gaussBinom_mul_prod_mul_prod_sub_eq_prod q n (n - a) (Nat.sub_le n a)
  rw [Nat.sub_sub_self h] at h2
  have hne := mul_ne_zero (prod_pow_succ_sub_one_ne_zero hq a) (prod_pow_succ_sub_one_ne_zero hq (n - a))
  have : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n (n - a) : ℤ) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q n a := by
    apply mul_right_cancel₀ hne
    linear_combination h2 - h1
  exact_mod_cast this

theorem _root_.GlobalTheory.GaussCount.card_codim (k : Type) [Field k] [Finite k] (V : Type) [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (j : ℕ) :
    Nat.card {L : Submodule k V // finrank k (V ⧸ L) = j} =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Nat.card k) (finrank k V) j := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  by_cases hj : j ≤ finrank k V
  · have e : {L : Submodule k V // finrank k (V ⧸ L) = j} ≃
        {L : Submodule k V // finrank k L = finrank k V - j} :=
      Equiv.subtypeEquivRight fun L => by
        have := L.finrank_quotient_add_finrank
        omega
    rw [Nat.card_congr e, card_submodule_finrank_eq_gaussBinom k V, gaussBinom_sub_eq_gaussBinom hq _ _ hj]
  · rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero _ _ _ (by omega)]
    haveI : IsEmpty {L : Submodule k V // finrank k (V ⧸ L) = j} :=
      ⟨fun ⟨L, hL⟩ => by have := L.finrank_quotient_add_finrank; omega⟩
    exact Nat.card_of_isEmpty

theorem _root_.GlobalTheory.GaussCount.gauss_formula (q : ℕ) (R : Type) [CommRing R] (Y : R) (m : ℕ) :
    ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j =
      ∏ i ∈ Finset.range m, (1 - (q : R) ^ i * Y) := by
  induction m with
  | zero => simp [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right]
  | succ m ih =>
    have h0 : ∑ j ∈ Finset.range (m + 1 + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j =
        ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j := by
      rw [Finset.sum_range_succ, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_eq_zero q m (m + 1) (by omega)]
      simp
    have h2 := Finset.sum_range_succ' (fun j => (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) *
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j) (m + 1)
    have h1 : ∑ j ∈ Finset.range (m + 1), (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
        ((q ^ (m - j) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : ℕ) : R) * Y ^ (j + 1) =
        -((q : R) ^ m * Y) * ∑ j ∈ Finset.range (m + 1),
        (-1 : R) ^ j * (q : R) ^ (j * (j - 1) / 2) * (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : R) * Y ^ j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjm : j ≤ m := by have := Finset.mem_range.mp hj; omega
      have e : (q : R) ^ m = (q : R) ^ j * (q : R) ^ (m - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hjm]
      rw [Nat.triangle_succ, e]
      push_cast
      ring
    have hterm : ∀ j, (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
        (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q (m + 1) (j + 1) : R) * Y ^ (j + 1) =
        (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
          (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m (j + 1) : R) * Y ^ (j + 1) +
        (-1 : R) ^ (j + 1) * (q : R) ^ ((j + 1) * (j + 1 - 1) / 2) *
          ((q ^ (m - j) * _root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom q m j : ℕ) : R) * Y ^ (j + 1) := by
      intro j
      rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_succ_succ]
      push_cast
      ring
    rw [Finset.prod_range_succ, ← ih, Finset.sum_range_succ',
      Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib, h1]
    simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom_zero_right] at h2 ⊢
    linear_combination h0 - h2

end GlobalTheory.GaussCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagPartMulDiagPart
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.BlockLevi

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagPart (f : ι → ℕ) (A : Matrix ι ι k) : Matrix ι ι k :=
  Matrix.of fun r s => if f r = f s then A r s else 0

theorem mul_diagPart_apply (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) {r s : ι} (h : f s ≤ f r) :
    (A * diagPart f B) r s = (A * B) r s := by
  simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with ht
  · rfl
  · rcases lt_or_gt_of_ne ht with h1 | h1
    · rw [hA (lt_of_lt_of_le h1 h)]; simp
    · rw [hB h1]

theorem diagPart_mul_diagPart (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) (hAB : A * B = 1) :
    diagPart f A * diagPart f B = 1 := by
  ext r s
  by_cases h : f r = f s
  · rw [← hAB, ← mul_diagPart_apply f hA hB h.ge]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_pos (h.trans ht.symm)]
    · simp [ht]
  · have hrs : r ≠ s := fun e => h (e ▸ rfl)
    rw [Matrix.one_apply_ne hrs]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_neg (fun e => h (e.trans ht))]; simp
    · simp [ht]

theorem blockTriangular_inv (f : ι → ℕ) (b : GL ι k) (hb : b.val.BlockTriangular f) :
    (b⁻¹).val.BlockTriangular f := by
  letI : Invertible b.val := b.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem exists_unip_mul_levi : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (b : GL (n ⊕ Fin c) k), b.val.BlockTriangular (lev p) → ∃ u ∈ N k n c p, ∃ m : GL (n ⊕ Fin c) k, (∀ r s, lev p r ≠ lev p s → m.val r s = 0) ∧ (∀ r s, lev p r = lev p s → m.val r s = b.val r s) ∧ b = u * m := by
  intro k _ n _ _ c p b hb
  have hi := blockTriangular_inv (lev p) b hb
  let m : GL (n ⊕ Fin c) k := ⟨diagPart (lev p) b.val, diagPart (lev p) (b⁻¹).val,
    diagPart_mul_diagPart _ hb hi b.mul_inv, diagPart_mul_diagPart _ hi hb b.inv_mul⟩
  refine ⟨b * m⁻¹, Subgroup.subset_closure ?_, m, ?_, ?_, by simp⟩
  · intro r s h
    have : (b * m⁻¹).val = b.val * diagPart (lev p) (b⁻¹).val := rfl
    rw [this, mul_diagPart_apply _ hb hi h, b.mul_inv]
  · intro r s h
    simp [m, diagPart, h]
  · intro r s h
    simp [m, diagPart, h]

end GlobalTheory.RootEx.BlockLevi
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeakIntegralOfIsLocallyConstantOfIsCompact
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory

theorem _root_.GlobalTheory.exists_weakIntegral_of_isLocallyConstant_of_isCompact :
    ∀ (U : Type) [TopologicalSpace U] [T2Space U] [MeasurableSpace U] [OpensMeasurableSpace U] (m : Measure U) [IsFiniteMeasureOnCompacts m] (V : Type) [AddCommGroup V] [Module ℂ V] (T : U → V) (_ : IsLocallyConstant T) (K : Set U) (_ : IsCompact K) (_ : ∀ u, u ∉ K → T u = 0), ∃ w : V, ∀ l : V →ₗ[ℂ] ℂ, l w = ∫ u, l (T u) ∂m := by
  intro U _ _ _ _ m _ V _ _ T hT K hK hzero
  classical
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun v : V => T ⁻¹' {v})
    (fun v => hT.isOpen_fiber v) (fun u _ => Set.mem_iUnion.2 ⟨T u, rfl⟩)
  have hS : ∀ u, T u ∈ insert 0 t := by
    intro u
    by_cases hu : u ∈ K
    · have h := ht hu
      simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff] at h
      obtain ⟨v, hv, huv⟩ := h
      rw [huv]
      exact Finset.mem_insert_of_mem hv
    · rw [hzero u hu]
      exact Finset.mem_insert_self 0 t
  have hmeas : ∀ v, MeasurableSet (T ⁻¹' {v}) := fun v => (hT.isOpen_fiber v).measurableSet
  refine ⟨∑ v ∈ insert 0 t, ((m.real (T ⁻¹' {v}) : ℂ)) • v, fun l => ?_⟩
  have hpt : ∀ u, l (T u) = ∑ v ∈ insert 0 t, (T ⁻¹' {v}).indicator (fun _ => l v) u := by
    intro u
    rw [Finset.sum_eq_single_of_mem (T u) (hS u)]
    · simp
    · intro v _ hv
      exact Set.indicator_of_notMem
        (show u ∉ T ⁻¹' {v} from fun h => hv (Set.mem_singleton_iff.1 h).symm) (fun _ => l v)
  have hint : ∀ v ∈ insert 0 t, Integrable ((T ⁻¹' {v}).indicator fun _ => l v) m := by
    intro v _
    by_cases hv : v = 0
    · subst hv
      simp
    · have hsub : T ⁻¹' {v} ⊆ K := by
        intro u hu
        by_contra hK'
        exact hv (by rw [← Set.mem_singleton_iff.1 hu, hzero u hK'])
      have hfin : m (T ⁻¹' {v}) ≠ ⊤ := ((measure_mono hsub).trans_lt hK.measure_lt_top).ne
      exact (integrable_indicator_iff (hmeas v)).2 (integrableOn_const (C := l v) hfin)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [integral_congr_ae (ae_of_all _ hpt), MeasureTheory.integral_finsetSum _ hint, map_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (hmeas v), map_smul, smul_eq_mul, Complex.real_smul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleOuterTprod
open scoped TensorProduct

namespace GlobalTheory.OuterTensor

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem isIrreducible_outer_tprod :
    ∀ (G H V W : Type) [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ V] [FiniteDimensional ℂ W] (ρ : Representation ℂ G V) (σ : Representation ℂ H W), ρ.IsIrreducible → σ.IsIrreducible → (Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H)) : Representation ℂ (G × H) (V ⊗[ℂ] W)).IsIrreducible := by
  intro G H V W _ _ _ _ _ _ _ _ ρ σ hρ hσ
  have hV := nontrivial_of_isIrreducible ρ hρ
  have hW := nontrivial_of_isIrreducible σ hσ
  have sρ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible G V ρ hρ
  have sσ := GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible H W σ hσ
  have hVW : Nontrivial (V ⊗[ℂ] W) := by
    apply Module.nontrivial_of_finrank_pos (R := ℂ)
    rw [Module.finrank_tensorProduct]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (congrArg Subrepresentation.toSubmodule h : (⊥ : Submodule ℂ (V ⊗[ℂ] W)) = ⊤)
  have h1 : ∀ (g : G) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map (ρ g) B x ∈ S.toSubmodule := by
    intro g B
    have hB : B ∈ Submodule.span ℂ (Set.range σ) := sσ ▸ Submodule.mem_top
    induction hB using Submodule.span_induction with
    | mem B hB =>
      obtain ⟨h, rfl⟩ := hB
      intro x hx
      exact S.apply_mem_toSubmodule (g, h) hx
    | zero => intro x _; simp
    | add B C _ _ hB hC =>
      intro x hx
      rw [TensorProduct.map_add_right, LinearMap.add_apply]
      exact add_mem (hB x hx) (hC x hx)
    | smul c B _ hB =>
      intro x hx
      rw [TensorProduct.map_smul_right, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hB x hx)
  have h2 : ∀ (A : V →ₗ[ℂ] V) (B : W →ₗ[ℂ] W), ∀ x ∈ S.toSubmodule,
      TensorProduct.map A B x ∈ S.toSubmodule := by
    intro A B
    have hA : A ∈ Submodule.span ℂ (Set.range ρ) := sρ ▸ Submodule.mem_top
    induction hA using Submodule.span_induction with
    | mem A hA =>
      obtain ⟨g, rfl⟩ := hA
      exact h1 g B
    | zero => intro x _; simp
    | add A C _ _ hA hC =>
      intro x hx
      rw [TensorProduct.map_add_left, LinearMap.add_apply]
      exact add_mem (hA x hx) (hC x hx)
    | smul c A _ hA =>
      intro x hx
      rw [TensorProduct.map_smul_left, LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (hA x hx)
  have h3 : ∀ (F : V ⊗[ℂ] W →ₗ[ℂ] V ⊗[ℂ] W), ∀ x ∈ S.toSubmodule, F x ∈ S.toSubmodule := by
    intro F
    obtain ⟨t, rfl⟩ := (homTensorHomEquiv ℂ V W V W).surjective F
    induction t using TensorProduct.induction_on with
    | zero => intro x _; simp
    | tmul A B =>
      intro x hx
      rw [homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
      exact h2 A B x hx
    | add s t hs ht =>
      intro x hx
      rw [map_add (f := _), LinearMap.add_apply]
      exact add_mem (hs x hx) (ht x hx)
  by_cases hS : S.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hS)
  · right
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
    apply Subrepresentation.toSubmodule_injective
    change S.toSubmodule = ⊤
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hx0
    have := h3 (f.smulRight y) x hx
    simpa [hf] using this

end GlobalTheory.OuterTensor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBasisTensor
noncomputable section

open scoped TensorProduct
open Module

namespace GlobalTheory.SemilinearExt

open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases

section

variable {O K K'' : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]

theorem algebraMap_tmul (c : K) (m : Fm) :
    algebraMap K K'' c ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (c • m) := by
  obtain ⟨⟨a, b⟩, hc⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
  dsimp only at hc
  subst hc
  have hb : algebraMap O K (b : O) ≠ 0 := (IsLocalization.map_units K b).ne_zero
  set m₀ : Fm := (algebraMap O K (b : O))⁻¹ • m with hm₀
  have h1 : (b : O) • m₀ = m := by
    rw [← algebraMap_smul K (b : O) m₀, hm₀, smul_smul, mul_inv_cancel₀ hb, one_smul]
  have h2 : IsLocalization.mk' K a b • m = (a : O) • m₀ := by
    rw [← algebraMap_smul K a m₀, hm₀, smul_smul, ← div_eq_mul_inv, IsFractionRing.mk'_eq_div]
  have h3 : (b : O) • algebraMap K K'' (IsLocalization.mk' K a b) = (a : O) • (1 : K'') := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply O K K'' (b : O),
      IsScalarTower.algebraMap_apply O K K'' a, ← map_mul, IsLocalization.mk'_spec']
  calc algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] m
      = algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] ((b : O) • m₀) := by rw [h1]
    _ = ((b : O) • algebraMap K K'' (IsLocalization.mk' K a b)) ⊗ₜ[O] m₀ :=
        (TensorProduct.smul_tmul _ _ _).symm
    _ = ((a : O) • (1 : K'')) ⊗ₜ[O] m₀ := by rw [h3]
    _ = (1 : K'') ⊗ₜ[O] ((a : O) • m₀) := TensorProduct.smul_tmul _ _ _
    _ = (1 : K'') ⊗ₜ[O] (IsLocalization.mk' K a b • m) := by rw [h2]

theorem exists_basis_tensor {ι : Type} (b : Basis ι K Fm) :
    ∃ c : Basis ι K'' (K'' ⊗[O] Fm), ∀ i, c i = (1 : K'') ⊗ₜ[O] b i := by
  have : TensorProduct.CompatibleSMul O K K'' Fm := ⟨fun c x m => by
    rw [Algebra.smul_def, mul_comm, ← smul_eq_mul x, ← TensorProduct.smul_tmul', algebraMap_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]⟩
  refine ⟨(Algebra.TensorProduct.basis K'' b).map (TensorProduct.equivOfCompatibleSMul O K K'' K'' Fm),
    fun i => ?_⟩
  rw [Basis.map_apply, Algebra.TensorProduct.basis_apply]
  rfl

end

def extOfBasis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V'] [Module L' V']
    (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') : V →ₛₗ[σ] V' where
  toFun x := ∑ k, σ (B.repr x k) • w k
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [mul_smul, Finset.smul_sum]

theorem extOfBasis_basis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') (k : Fin n) :
    extOfBasis σ B w (B k) = w k := by
  show ∑ j, σ (B.repr (B k) j) • w j = w k
  rw [B.repr_self, Finset.sum_eq_single k]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

theorem carries_of_basis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] {σ : L →+* L'} (e : V →ₛₗ[σ] V') {n : ℕ} (B : Basis (Fin n) L V) (C : Basis (Fin n) L' V')
    (h : ∀ k, e (B k) = C k) {ι : Type} (b : Basis ι L V) : ∃ c : Basis ι L' V', ∀ i, c i = e (b i) := by
  classical
  have : Module.Finite L V := Module.Finite.of_basis B
  have : Module.Finite L' V' := Module.Finite.of_basis C
  have : Finite ι := Module.Finite.finite_basis b
  haveI : Fintype ι := Fintype.ofFinite ι
  have hspan : ⊤ ≤ Submodule.span L' (Set.range fun i => e (b i)) := by
    rw [← C.span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h k, ← b.sum_repr (B k), map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card ι = finrank L' V' := by
    rw [finrank_eq_card_basis C, ← finrank_eq_card_basis B, finrank_eq_card_basis b]
  exact ⟨basisOfTopLeSpanOfCardEqFinrank _ hspan hcard, fun i => by simp⟩

theorem semilinearExtension : SemilinearExtension := by
  intro Ks LL WL _ _ _ _ _ _ _ WK hForm O K K'' _ _ _ _ _ _ _ _ _ _ emb hemb Fm _ _ _ _ eF
  obtain ⟨n, bv, -, hKs, hspanK, hLL, hspanL⟩ := hForm
  let B : Basis (Fin n) LL WL := Basis.mk hLL hspanL.ge
  have hB : ∀ k, B k = bv k := fun k => Basis.mk_apply _ _ _
  let BK : Basis (Fin n) Ks WK := (Basis.span hKs).map (LinearEquiv.ofEq _ _ hspanK)
  have hBK : ∀ k, (BK k : WL) = bv k := fun k => by simp [BK, Basis.span_apply]
  let bF : Basis (Fin n) K Fm := (Algebra.TensorProduct.basis K BK).map eF.symm
  obtain ⟨c, hc⟩ := exists_basis_tensor (O := O) (K'' := K'') bF
  have hck : ∀ k, c k = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [hc, Basis.map_apply, Algebra.TensorProduct.basis_apply]
  have hscal : ∀ (a : Ks) (m : Fm),
      emb (algebraMap Ks LL a) ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (algebraMap Ks K a • m) := by
    intro a m
    rw [← RingHom.comp_apply emb (algebraMap Ks LL) a, hemb, RingHom.comp_apply, algebraMap_tmul]
  have hf : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) →
      ∀ f : WK, e f = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] f) := by
    intro e he f
    have hterm : ∀ (r : Ks) (j : Fin n),
        e (r • bv j) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] (r • BK j)) := by
      intro r j
      rw [← algebraMap_smul LL r (bv j), map_smulₛₗ, he, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        hscal, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    have hsum : (f : WL) = ∑ j, BK.repr f j • bv j := by
      conv_lhs => rw [← BK.sum_repr f]
      simp only [Submodule.coe_sum, Submodule.coe_smul, hBK]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    simp_rw [hterm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← TensorProduct.tmul_sum, ← map_sum eF.symm, ← TensorProduct.tmul_sum, BK.sum_repr]
  have hext : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm,
      (∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)) → IsExt O emb eF e := by
    intro e he ι _ a f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hf e he, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hval : ∀ e : WL →ₛₗ[emb] K'' ⊗[O] Fm, IsExt O emb eF e →
      ∀ k, e (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := by
    intro e he k
    rw [← hBK]
    exact he.apply_coe (BK k)
  let e₀ : WL →ₛₗ[emb] K'' ⊗[O] Fm :=
    extOfBasis emb B fun k => (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k)
  have he₀ : ∀ k, e₀ (bv k) = (1 : K'') ⊗ₜ[O] eF.symm ((1 : K) ⊗ₜ[Ks] BK k) := fun k => by
    rw [← hB]
    exact extOfBasis_basis emb B _ k
  refine ⟨⟨e₀, hext e₀ he₀, fun e' he' => B.ext fun k => ?_⟩, fun e he => ?_, fun a m => ?_⟩
  · rw [hB, hval e' he' k, he₀ k]
  · exact fun ι b => carries_of_basis e B c (fun k => by rw [hB, hval e he k, hck k]) b
  · exact hscal a m

end GlobalTheory.SemilinearExt
end
end
