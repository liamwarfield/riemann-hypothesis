module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
public import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransportSymm

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionCoefficientSigns
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionCoefficientSigns
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeSign

theorem sign_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ x ∈ s, f x ≠ 0) :
    0 < (-1 : ℝ) ^ (s.filter fun x => f x < 0).card * ∏ x ∈ s, f x := by
  have e : (-1 : ℝ) ^ (s.filter fun x => f x < 0).card
      = ∏ x ∈ s, (if f x < 0 then (-1 : ℝ) else 1) := by
    rw [Finset.prod_ite]; simp
  rw [e, ← Finset.prod_mul_distrib]
  apply Finset.prod_pos
  intro x hx
  split_ifs with hneg
  · linarith
  · have : 0 < f x := lt_of_le_of_ne (not_lt.mp hneg) (Ne.symm (h x hx))
    linarith

theorem sign_div {a b P Q : ℝ} (hP : 0 < a * P) (hQ : 0 < b * Q) : 0 < a * b * (P / Q) := by
  have hQ0 : Q ≠ 0 := by
    rintro rfl
    simp at hQ
  have e : a * b * (P / Q) = (a * P) * (b * Q) / Q ^ 2 := by
    field_simp
  rw [e]
  exact div_pos (mul_pos hP hQ) (by positivity)

theorem above_eq {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ) (r : ℝ) :
    above d d' r = (univ.filter fun k => r < d k).card + (univ.filter fun j => r < d' j).card := by
  unfold above
  simp only [Finset.card_filter, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  congr!

theorem pfSign {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hinj : Function.Injective (Sum.elim d d')) :
    (∀ i, 0 < (-1 : ℝ) ^ above d d' (d i) * pfD d d' i) ∧
      ∀ j, 0 < (-1 : ℝ) ^ above d d' (d' j) * pfR d d' j := by
  have hd : ∀ {i k}, k ≠ i → d i - d k ≠ 0 := by
    intro i k hk h
    apply hk
    have := hinj (a₁ := Sum.inl k) (a₂ := Sum.inl i) (by simpa using (sub_eq_zero.mp h).symm)
    simpa using this
  have hd' : ∀ {j k}, k ≠ j → d' j - d' k ≠ 0 := by
    intro j k hk h
    apply hk
    have := hinj (a₁ := Sum.inr k) (a₂ := Sum.inr j) (by simpa using (sub_eq_zero.mp h).symm)
    simpa using this
  have hx : ∀ i j, d i - d' j ≠ 0 := by
    intro i j h
    have := hinj (a₁ := Sum.inl i) (a₂ := Sum.inr j) (by simpa using sub_eq_zero.mp h)
    simp at this
  have hy : ∀ j i, d' j - d i ≠ 0 := by
    intro j i h
    exact hx i j (by linarith)
  constructor
  · intro i
    have h1 := sign_prod (univ.erase i) (fun k => d i - d k)
      (fun k hk => hd (Finset.ne_of_mem_erase hk))
    have h2 := sign_prod (univ : Finset (Fin m)) (fun j => d i - d' j) (fun j _ => hx i j)
    have e1 : ((univ.erase i).filter fun k => d i - d k < 0) = univ.filter fun k => d i < d k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, sub_neg]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        exact lt_irrefl _ h
    have e2 : (univ.filter fun j => d i - d' j < 0) = univ.filter fun j => d i < d' j := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
    rw [e1] at h1
    rw [e2] at h2
    rw [above_eq, pow_add]
    exact sign_div h1 h2
  · intro j
    have h1 := sign_prod (univ : Finset (Fin (m + 1))) (fun i => d' j - d i) (fun i _ => hy j i)
    have h2 := sign_prod (univ.erase j) (fun k => d' j - d' k)
      (fun k hk => hd' (Finset.ne_of_mem_erase hk))
    have e1 : (univ.filter fun i => d' j - d i < 0) = univ.filter fun i => d' j < d i := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sub_neg]
    have e2 : ((univ.erase j).filter fun k => d' j - d' k < 0)
        = univ.filter fun k => d' j < d' k := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and, sub_neg]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rintro rfl
        exact lt_irrefl _ h
    rw [e1] at h1
    rw [e2] at h2
    rw [above_eq, pow_add]
    exact sign_div h1 h2

end GlobalTheory.CompanionTheory.RgHeSign
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionCoefficientSignsStatement
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_coefficient_signs : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → (∀ i, 0 < (-1 : ℝ) ^ above d d' (d i) * pfD d d' i) ∧ ∀ j, 0 < (-1 : ℝ) ^ above d d' (d' j) * pfR d d' j := by
  first | exact @GlobalTheory.CompanionTheory.RgHeSign.pfSign | exact GlobalTheory.CompanionTheory.RgHeSign.pfSign | (intros; apply GlobalTheory.CompanionTheory.RgHeSign.pfSign <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormula
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem trace_diagonal_block_conjugate (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ)
    (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hg : IsUnit g.det)
    (hX : X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)))
    (hb : ∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) :
    trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g))
      = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal (fun i => ((d i : ℝ) : ℂ)) with hD
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) with hB
  have h1 : g * D * g⁻¹ = X := by
    rw [← hX, Matrix.mul_assoc, Matrix.mul_nonsing_inv g hg, Matrix.mul_one]
  have h2 : trace (D * (g⁻¹ * B * g)) = trace (X * B) := by
    rw [← h1]
    have : D * (g⁻¹ * B * g) = (D * g⁻¹ * B) * g := by
      simp only [Matrix.mul_assoc]
    rw [this, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [h2]
  have h3 : trace (X * B) = ∑ u, ∑ w, X (e u) (e w) *
      (Matrix.fromBlocks Y 0 0 0 : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) ℂ) w u := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [hB, Matrix.reindex_apply]
  rw [h3]
  simp only [Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, add_zero, hb]
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.diagonal_apply]

end GlobalTheory.CompanionTheory.RgHeFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceDiagonalBlockConjugateFormulaStatement
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_diagonal_block_conjugate_formula : ∀ (n : ℕ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ), IsUnit g.det → X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) → (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) → ∀ Y : Matrix (Fin n) (Fin n) ℂ, trace (diagonal (fun i => ((d i : ℝ) : ℂ)) * (g⁻¹ * Matrix.reindex e e (Matrix.fromBlocks Y 0 0 0) * g)) = trace (diagonal (fun a => ((d' a : ℝ) : ℂ)) * Y) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | exact GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.trace_diagonal_block_conjugate <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryInterlacingRealization
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionDiagonalIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionDiagonalIdentity
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHe.Frame

open Polynomial

theorem degree_sub_lt_of_nextCoeff_eq {p q : ℝ[X]} {m : ℕ} (hp : p.Monic) (hq : q.Monic)
    (hpd : p.natDegree = m + 1) (hqd : q.natDegree = m + 1) (hn : p.nextCoeff = q.nextCoeff) :
    (p - q).degree < (m : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro k hk
  rw [coeff_sub]
  rcases hk.eq_or_lt with rfl | hk'
  · have h1 : p.nextCoeff = p.coeff m := by
      rw [nextCoeff_of_natDegree_pos (by omega), hpd]; rfl
    have h2 : q.nextCoeff = q.coeff m := by
      rw [nextCoeff_of_natDegree_pos (by omega), hqd]; rfl
    rw [← h1, ← h2, hn, sub_self]
  · rcases (Nat.succ_le_of_lt hk').eq_or_lt with rfl | hk''
    · have h1 := hp.coeff_natDegree
      have h2 := hq.coeff_natDegree
      rw [hpd] at h1
      rw [hqd] at h2
      rw [h1, h2, sub_self]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega),
        sub_zero]

theorem prod_eq_partial_fraction {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hd' : Function.Injective d') :
    (∏ i, (X - C (d i))) = (X - C (pfX d d')) * (∏ j, (X - C (d' j))) +
      ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) := by
  have hPm : (∏ i, (X - C (d i)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hQm : (∏ j, (X - C (d' j)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPd : (∏ i, (X - C (d i)) : ℝ[X]).natDegree = m + 1 := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hQd : (∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]; simp
  have hRm : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).Monic := (monic_X_sub_C _).mul hQm
  have hRd : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m + 1 := by
    rw [(monic_X_sub_C _).natDegree_mul hQm, hQd, natDegree_X_sub_C]; omega
  have hn : (∏ i, (X - C (d i)) : ℝ[X]).nextCoeff =
      ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).nextCoeff := by
    rw [(monic_X_sub_C _).nextCoeff_mul hQm, prod_X_sub_C_nextCoeff, prod_X_sub_C_nextCoeff,
      nextCoeff_X_sub_C, pfX]
    ring
  have hD := degree_sub_lt_of_nextCoeff_eq hPm hRm hPd hRd hn
  have hS : (∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < (m : WithBot ℕ) := by
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    rw [finsetSum_coeff]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [coeff_C_mul]
    have hL : (∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).natDegree < n := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
      have hj : (univ.erase j).card + 1 = m := by
        rw [Finset.card_erase_of_mem (mem_univ j)]
        have : 0 < m := j.pos
        simp only [card_univ, Fintype.card_fin]
        omega
      simp only [natDegree_X_sub_C, sum_const, smul_eq_mul, mul_one]
      omega
    rw [coeff_eq_zero_of_natDegree_lt hL, mul_zero]
  have hcard : (#(univ : Finset (Fin m)) : ℕ) = m := by simp
  have key := Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := (univ : Finset (Fin m)))
    (v := d') (f := (∏ i, (X - C (d i))) - (X - C (pfX d d')) * ∏ j, (X - C (d' j)))
    (g := ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)))
    hd'.injOn (by rw [hcard]; exact hD) (by rw [hcard]; exact hS) (by
      intro j _
      have hne : ∏ k ∈ univ.erase j, (d' j - d' k) ≠ 0 := by
        refine Finset.prod_ne_zero_iff.mpr fun k hk => sub_ne_zero.mpr fun h => ?_
        exact (Finset.mem_erase.mp hk).1 (hd' h).symm
      have hQ0 : (∏ l, (d' j - d' l)) = 0 :=
        Finset.prod_eq_zero (mem_univ j) (sub_self _)
      have hterm : ∀ l ∈ (univ : Finset (Fin m)), l ≠ j →
          pfR d d' l * ∏ k ∈ univ.erase l, (d' j - d' k) = 0 := by
        intro l _ hl
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hl.symm, mem_univ j⟩) (sub_self _), mul_zero]
      simp only [eval_sub, eval_mul, eval_prod, eval_X, eval_C, eval_finsetSum]
      rw [hQ0, mul_zero, sub_zero, Finset.sum_eq_single_of_mem j (mem_univ j) hterm, pfR,
        div_mul_cancel₀ _ hne])
  rw [← key]
  ring

theorem pfZero {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (hinj : Function.Injective (Sum.elim d d')) (i : Fin (m + 1)) :
    d i - pfX d d' + ∑ j, pfR d d' j / (d i - d' j) = 0 := by
  have hd' : Function.Injective d' := fun a b h =>
    Sum.inr_injective (hinj (by simpa using h))
  have hne : ∀ j, d i - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h => by
    simpa using hinj (a₁ := Sum.inl i) (a₂ := Sum.inr j) (by simpa using h)
  have hQ : ∏ j, (d i - d' j) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => hne j
  have h := congrArg (eval (d i)) (prod_eq_partial_fraction d d' hd')
  simp only [eval_add, eval_sub, eval_mul, eval_prod, eval_X, eval_C, eval_finsetSum] at h
  rw [Finset.prod_eq_zero (mem_univ i) (sub_self _)] at h
  have hsum : ∀ j, pfR d d' j * ∏ k ∈ univ.erase j, (d i - d' k) =
      (pfR d d' j / (d i - d' j)) * ∏ k, (d i - d' k) := by
    intro j
    rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
    field_simp [hne j]
  simp only [hsum, ← Finset.sum_mul] at h
  rw [← add_mul] at h
  exact (mul_eq_zero.mp h.symm).resolve_right hQ

end GlobalTheory.CompanionTheory.RgHe.Frame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionDiagonalIdentityStatement
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_diagonal_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i, d i - pfX d d' + ∑ j, pfR d d' j / (d i - d' j) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHe.Frame.pfZero | exact GlobalTheory.CompanionTheory.RgHe.Frame.pfZero | (intros; apply GlobalTheory.CompanionTheory.RgHe.Frame.pfZero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionOffDiagonalIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionOffDiagonalIdentity
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem pfOrth : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ),
    Function.Injective (Sum.elim d d') → ∀ i k, i ≠ k →
      1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) = 0 := by
  intro m d d' hinj i k hik
  have hi := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj i
  have hk := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj k
  have hne : d i - d k ≠ 0 := sub_ne_zero.mpr fun h => hik (Sum.inl.inj (@hinj (Sum.inl i) (Sum.inl k) h))
  have hij : ∀ j, d i - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h =>
    Sum.inl_ne_inr (@hinj (Sum.inl i) (Sum.inr j) h)
  have hkj : ∀ j, d k - d' j ≠ 0 := fun j => sub_ne_zero.mpr fun h =>
    Sum.inl_ne_inr (@hinj (Sum.inl k) (Sum.inr j) h)
  have hdiff : ∑ j, pfR d d' j / (d i - d' j) - ∑ j, pfR d d' j / (d k - d' j) =
      -(d i - d k) * ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp [hij j, hkj j]
    ring
  have key : (d i - d k) * (1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j))) = 0 := by
    linear_combination hi - hk - hdiff
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hne
  · exact h

end GlobalTheory.CompanionTheory.RgHeFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionOffDiagonalIdentityStatement
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_off_diagonal_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i k, i ≠ k → 1 - ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.pfOrth | exact GlobalTheory.CompanionTheory.RgHeFrame.pfOrth | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.pfOrth <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionSquareIdentity
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionSquareIdentity
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

open Polynomial

variable {m : ℕ}

noncomputable def pfPoly (x : ℝ) (r d' : Fin m → ℝ) : ℝ[X] :=
  (X - C x) * ∏ j, (X - C (d' j)) + ∑ j, C (r j) * ∏ k ∈ univ.erase j, (X - C (d' k))

lemma eval_pfPoly (x : ℝ) (r d' : Fin m → ℝ) (s : ℝ) (hs : ∀ j, s - d' j ≠ 0) :
    (pfPoly x r d').eval s =
      (∏ j, (s - d' j)) * (s - x + ∑ j, r j / (s - d' j)) := by
  have hj : ∀ j, (∏ k ∈ univ.erase j, (s - d' k)) = (∏ k, (s - d' k)) / (s - d' j) := by
    intro j
    rw [eq_div_iff (hs j), mul_comm, Finset.mul_prod_erase univ (fun k => s - d' k) (mem_univ j)]
  simp only [pfPoly, eval_add, eval_mul, eval_sub, eval_X, eval_C, eval_prod, eval_finsetSum]
  rw [mul_add, Finset.mul_sum, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hj j]
  ring

lemma prod_eq_pfPoly (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ)
    (h : Function.Injective (Sum.elim d d')) :
    (∏ i, (X - C (d i)) : ℝ[X]) = pfPoly (pfX d d') (pfR d d') d' := by
  have hdd' : ∀ i j, d i - d' j ≠ 0 := by
    intro i j hij
    have : Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j) := by
      simpa using sub_eq_zero.mp hij
    exact absurd (h this) (by simp)
  have hinj : Function.Injective d := fun a b hab => by
    have : Sum.elim d d' (Sum.inl a) = Sum.elim d d' (Sum.inl b) := by simpa using hab
    simpa using h this
  have hP : (∏ i, (X - C (d i)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hQ : (∏ j, (X - C (d' j)) : ℝ[X]).Monic := monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have hPd : (∏ i, (X - C (d i)) : ℝ[X]).degree = (m + 1 : ℕ) := by
    rw [degree_eq_natDegree hP.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  have hQd : (∏ j, (X - C (d' j)) : ℝ[X]).natDegree = m := by
    rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
  have hL : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).Monic := (monic_X_sub_C _).mul hQ
  have hLd : ((X - C (pfX d d')) * ∏ j, (X - C (d' j)) : ℝ[X]).degree = (m + 1 : ℕ) := by
    rw [degree_eq_natDegree hL.ne_zero, (monic_X_sub_C _).natDegree_mul hQ, hQd]
    simp [add_comm]
  have hsub : ((∏ i, (X - C (d i)) : ℝ[X]) -
      (X - C (pfX d d')) * ∏ j, (X - C (d' j))).degree < ((m + 1 : ℕ) : WithBot ℕ) := by
    have := degree_sub_lt (hPd.trans hLd.symm) hP.ne_zero (hP.leadingCoeff.trans hL.leadingCoeff.symm)
    rwa [hPd] at this
  have hterm : ∀ j : Fin m, (C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < ((m + 1 : ℕ) : WithBot ℕ) := by
    intro j
    rw [← smul_eq_C_mul]
    refine (degree_smul_le _ _).trans_lt ?_
    have hM : (∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).Monic :=
      monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
    rw [degree_eq_natDegree hM.ne_zero, natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
    simp
    exact_mod_cast (by omega : m - 1 < m + 1)
  have hsum : (∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) : ℝ[X]).degree
      < ((m + 1 : ℕ) : WithBot ℕ) := by
    refine (degree_sum_le _ _).trans_lt ?_
    exact (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ => hterm j
  have hdeg : ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d').degree
      < (univ : Finset (Fin (m + 1))).card := by
    have : ((∏ i, (X - C (d i)) : ℝ[X]) - pfPoly (pfX d d') (pfR d d') d') =
        ((∏ i, (X - C (d i)) : ℝ[X]) - (X - C (pfX d d')) * ∏ j, (X - C (d' j))) -
          ∑ j, C (pfR d d' j) * ∏ k ∈ univ.erase j, (X - C (d' k)) := by
      simp only [pfPoly]; ring
    rw [this]
    simpa using (degree_sub_le _ _).trans_lt (max_lt hsub hsum)
  refine sub_eq_zero.mp (eq_zero_of_degree_lt_of_eval_index_eq_zero univ hinj.injOn hdeg ?_)
  intro i _
  have hz := GlobalTheory.T.partial_fraction_diagonal_identity d d' h i
  rw [eval_sub, eval_pfPoly _ _ _ _ (hdd' i), hz, mul_zero, eval_prod]
  simp only [eval_sub, eval_X, eval_C, sub_zero]
  exact Finset.prod_eq_zero (mem_univ i) (sub_self _)

theorem pfDer : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ),
    Function.Injective (Sum.elim d d') →
      ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  intro m d d' h i
  have hdd' : ∀ j, d i - d' j ≠ 0 := by
    intro j hij
    have : Sum.elim d d' (Sum.inl i) = Sum.elim d d' (Sum.inr j) := by
      simpa using sub_eq_zero.mp hij
    exact absurd (h this) (by simp)
  set Q : ℝ[X] := ∏ j, (X - C (d' j)) with hQdef
  have hQe : ∀ s, Q.eval s = ∏ j, (s - d' j) := fun s => by simp [hQdef, eval_prod]
  have hQ0 : Q.eval (d i) ≠ 0 := by
    rw [hQe]; exact Finset.prod_ne_zero_iff.2 fun j _ => hdd' j

  let f : ℝ → ℝ := fun s => s - pfX d d' + ∑ j, pfR d d' j / (s - d' j)
  have hterm : ∀ j ∈ (univ : Finset (Fin m)), HasDerivAt (fun s => pfR d d' j / (s - d' j))
      (-(pfR d d' j / (d i - d' j) ^ 2)) (d i) := by
    intro j _
    have h1 : HasDerivAt (fun s : ℝ => s - d' j) 1 (d i) := (hasDerivAt_id _).sub_const _
    have h2 := (hasDerivAt_const (d i) (pfR d d' j)).fun_div h1 (hdd' j)
    exact h2.congr_deriv (by simp [neg_div])
  have hf : HasDerivAt f (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2) (d i) := by
    have h3 := HasDerivAt.fun_sum hterm
    have h4 := ((hasDerivAt_id (d i)).sub_const (pfX d d')).fun_add h3
    exact h4.congr_deriv (by simp [sub_eq_add_neg])
  have hf0 : f (d i) = 0 := GlobalTheory.T.partial_fraction_diagonal_identity d d' h i
  have hprod : HasDerivAt (fun s => Q.eval s * f s)
      (Q.eval (d i) * (1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2)) (d i) := by
    have := (Q.hasDerivAt (d i)).fun_mul hf
    exact this.congr_deriv (by simp [hf0])

  set P : ℝ[X] := ∏ k, (X - C (d k)) with hPdef
  have hPfac : P = (X - C (d i)) * ∏ k ∈ univ.erase i, (X - C (d k)) :=
    (Finset.mul_prod_erase univ (fun k => (X - C (d k) : ℝ[X])) (mem_univ i)).symm
  have hPder : P.derivative.eval (d i) = ∏ k ∈ univ.erase i, (d i - d k) := by
    rw [hPfac, derivative_mul]
    simp [eval_prod]
  have hev : (fun s => P.eval s) =ᶠ[nhds (d i)] fun s => Q.eval s * f s := by
    have hopen : ∀ᶠ s in nhds (d i), ∀ j, s - d' j ≠ 0 := by
      refine Filter.eventually_all.2 fun j => ?_
      have hc : ContinuousAt (fun s : ℝ => s - d' j) (d i) := by fun_prop
      exact hc.eventually_ne (hdd' j)
    filter_upwards [hopen] with s hs
    rw [hPdef, prod_eq_pfPoly d d' h, eval_pfPoly _ _ _ _ hs, hQe]
  have huniq := (P.hasDerivAt (d i)).unique (hprod.congr_of_eventuallyEq hev)
  rw [hPder] at huniq
  unfold pfD
  rw [← hQe (d i), huniq]
  field_simp

end GlobalTheory.CompanionTheory.RgHeFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialFractionSquareIdentityStatement
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partial_fraction_square_identity : ∀ {m : ℕ} (d : Fin (m + 1) → ℝ) (d' : Fin m → ℝ), Function.Injective (Sum.elim d d') → ∀ i, 1 - ∑ j, pfR d d' j / (d i - d' j) ^ 2 = pfD d d' i := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.pfDer | exact GlobalTheory.CompanionTheory.RgHeFrame.pfDer | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.pfDer <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryInterlacingRealization
open Finset Matrix PositivityTheory.RgHe.Frame

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeFrame

def sg (b : Bool) : ℝ := if b then 1 else -1

lemma sg_mul_self (b : Bool) : sg b * sg b = 1 := by cases b <;> simp [sg]

lemma sg_ne_zero (b : Bool) : sg b ≠ 0 := by cases b <;> simp [sg]

lemma sg_cast (b : Bool) : ((sg b : ℝ) : ℂ) = if b then 1 else -1 := by cases b <;> simp [sg]

variable {n : ℕ}

def cc (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (i : Fin (n + 1)) : ℝ := 1 / √|pfD d d' i|

def yy (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (j : Fin n) : ℝ :=
  √(-(sg (ε' j) * pfR d d' j))

def G0 (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (r : Fin n ⊕ Unit)
    (i : Fin (n + 1)) : ℝ :=
  Sum.elim (fun j => cc d d' i * yy ε' d d' j / (d i - d' j)) (fun _ => cc d d' i) r

def X0 (ε' : Fin n → Bool) (d : Fin (n + 1) → ℝ) (d' : Fin n → ℝ) (r t : Fin n ⊕ Unit) : ℝ :=
  Sum.elim
    (fun a => Sum.elim (fun b => if a = b then d' a else 0) (fun _ => yy ε' d d' a) t)
    (fun _ => Sum.elim (fun b => sg (ε' b) * yy ε' d d' b) (fun _ => pfX d d') t) r

lemma yy_sq {ε' : Fin n → Bool} {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {j : Fin n}
    (h : 0 < -(sg (ε' j) * pfR d d' j)) :
    sg (ε' j) * (yy ε' d d' j * yy ε' d d' j) = -pfR d d' j := by
  unfold yy
  rw [Real.mul_self_sqrt h.le]
  have := sg_mul_self (ε' j)
  linear_combination (-pfR d d' j) * this

lemma cc_sq {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {i : Fin (n + 1)} {b : Bool}
    (h : 0 < sg b * pfD d d' i) : cc d d' i * cc d d' i * pfD d d' i = sg b := by
  have hcc : cc d d' i * cc d d' i = 1 / |pfD d d' i| := by
    unfold cc
    rw [div_mul_div_comm, Real.mul_self_sqrt (abs_nonneg _), one_mul]
  rw [hcc]
  cases b with
  | true =>
    have hp : 0 < pfD d d' i := by simpa [sg] using h
    rw [abs_of_pos hp]
    simp only [sg]
    field_simp
    simp
  | false =>
    have hp : pfD d d' i < 0 := by simpa [sg] using h
    rw [abs_of_neg hp]
    simp only [sg]
    have := hp.ne
    field_simp
    simp

lemma cc_ne_zero {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ} {i : Fin (n + 1)} {b : Bool}
    (h : 0 < sg b * pfD d d' i) : cc d d' i ≠ 0 := by
  intro h0
  have := cc_sq h
  rw [h0] at this
  exact sg_ne_zero b (by simpa using this.symm)

lemma sum_terms {ε' : Fin n → Bool} {d : Fin (n + 1) → ℝ} {d' : Fin n → ℝ}
    (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j)) (i k : Fin (n + 1)) :
    ∑ j, (cc d d' i * yy ε' d d' j / (d i - d' j)) * sg (ε' j) *
        (cc d d' k * yy ε' d d' j / (d k - d' j)) =
      -(cc d d' i * cc d d' k * ∑ j, pfR d d' j / ((d i - d' j) * (d k - d' j))) := by
  rw [mul_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  have h := yy_sq (hR j)
  calc (cc d d' i * yy ε' d d' j / (d i - d' j)) * sg (ε' j) *
        (cc d d' k * yy ε' d d' j / (d k - d' j))
      = cc d d' i * cc d d' k * (sg (ε' j) * (yy ε' d d' j * yy ε' d d' j)) /
          ((d i - d' j) * (d k - d' j)) := by
          simp only [div_eq_mul_inv, mul_inv]; ring
    _ = _ := by rw [h]; ring

lemma gram {ε : Fin (n + 1) → Bool} {d : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {d' : Fin n → ℝ}
    (e : Fin n ⊕ Unit ≃ Fin (n + 1)) (hz : ε (e (Sum.inr ())) = true)
    (hs : ∀ a, ε (e (Sum.inl a)) = ε' a) (hinj : Function.Injective (Sum.elim d d'))
    (hD : ∀ i, 0 < sg (ε i) * pfD d d' i) (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j))
    (i k : Fin (n + 1)) :
    ∑ r, G0 ε' d d' (e.symm r) i * sg (ε r) * G0 ε' d d' (e.symm r) k =
      if i = k then sg (ε i) else 0 := by
  rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
  simp only [Equiv.symm_apply_apply, G0, Sum.elim_inl, Sum.elim_inr, hs, hz, univ_unique,
    sum_singleton]
  rw [sum_terms hR]
  have hz1 : sg true = 1 := by simp [sg]
  rw [hz1]
  by_cases hik : i = k
  · subst hik
    have h1 := GlobalTheory.T.partial_fraction_square_identity d d' hinj i
    have h2 := cc_sq (hD i)
    simp only [if_true]
    have h3 : ∑ j, pfR d d' j / ((d i - d' j) * (d i - d' j)) =
        ∑ j, pfR d d' j / (d i - d' j) ^ 2 := by
      refine sum_congr rfl fun j _ => ?_
      rw [sq]
    rw [h3]
    linear_combination (cc d d' i * cc d d' i) * h1 + h2
  · have h1 := GlobalTheory.T.partial_fraction_off_diagonal_identity d d' hinj i k hik
    simp only [hik, if_false]
    linear_combination (cc d d' i * cc d d' k) * h1

lemma inter {d : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {d' : Fin n → ℝ}
    (hinj : Function.Injective (Sum.elim d d'))
    (hR : ∀ j, 0 < -(sg (ε' j) * pfR d d' j)) (r : Fin n ⊕ Unit) (i : Fin (n + 1)) :
    ∑ t, X0 ε' d d' r t * G0 ε' d d' t i = G0 ε' d d' r i * d i := by
  have hne : ∀ j, d i - d' j ≠ 0 := by
    intro j h
    have : (Sum.inl i : Fin (n + 1) ⊕ Fin n) = Sum.inr j :=
      hinj (by simpa using sub_eq_zero.mp h)
    simp at this
  rw [Fintype.sum_sum_type]
  rcases r with a | u
  · simp only [X0, G0, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton, ite_mul, zero_mul,
      sum_ite_eq, mem_univ, if_true]
    have := hne a
    field_simp
    ring
  · simp only [X0, G0, Sum.elim_inl, Sum.elim_inr, univ_unique, sum_singleton]
    have h0 := GlobalTheory.T.partial_fraction_diagonal_identity d d' hinj i
    have h1 : ∑ j, sg (ε' j) * yy ε' d d' j * (cc d d' i * yy ε' d d' j / (d i - d' j)) =
        -(cc d d' i * ∑ j, pfR d d' j / (d i - d' j)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun j _ => ?_
      have h := yy_sq (hR j)
      calc sg (ε' j) * yy ε' d d' j * (cc d d' i * yy ε' d d' j / (d i - d' j))
          = cc d d' i * (sg (ε' j) * (yy ε' d d' j * yy ε' d d' j)) / (d i - d' j) := by ring
        _ = _ := by rw [h]; ring
    rw [h1]
    linear_combination (-cc d d' i) * h0

theorem build : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), ε (e (Sum.inr ())) = true → (∀ a, ε (e (Sum.inl a)) = ε' a) → Function.Injective (Sum.elim d d') → (∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i) → (∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j)) → ∃ g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Formalism.REAL.inUJ ε g ∧ X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) ∧ (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) ∧ ∀ i, ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ)) i ≠ 0 := by
  intro n ε d ε' d' e hz hs hinj hD hR
  have hD' : ∀ i, 0 < sg (ε i) * pfD d d' i := hD
  have hR' : ∀ j, 0 < -(sg (ε' j) * pfR d d' j) := hR
  obtain ⟨g, hg⟩ : ∃ g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ r i, g r i = ((G0 ε' d d' (e.symm r) i : ℝ) : ℂ) := ⟨Matrix.of _, fun _ _ => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      ∀ r t, X r t = ((X0 ε' d d' (e.symm r) (e.symm t) : ℝ) : ℂ) := ⟨Matrix.of _, fun _ _ => rfl⟩
  refine ⟨g, X, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.REAL.inUJ Formalism.REAL.Jm
    ext i k
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hg,
      RCLike.star_def, Complex.conj_ofReal]
    have h := gram e hz hs hinj hD' hR' i k
    have h2 := congrArg (fun x : ℝ => (x : ℂ)) h
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, sg_cast] at h2
    rw [h2]
    by_cases hik : i = k
    · simp [hik, sg_cast]
    · simp [hik]
  · ext r i
    rw [Matrix.mul_diagonal, Matrix.mul_apply, ← Equiv.sum_comp e]
    simp only [hg, hX, Equiv.symm_apply_apply]
    have h := inter (ε' := ε') hinj hR' (e.symm r) i
    exact_mod_cast h
  · intro a b
    simp only [hX, Equiv.symm_apply_apply, X0, Sum.elim_inl]
    split_ifs <;> simp
  · intro i
    rw [Matrix.mulVec_single_one]
    change (Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) i (e (Sum.inr ())) ≠ 0
    unfold Formalism.REAL.Jm
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, hg,
      Equiv.symm_apply_apply, G0, Sum.elim_inr, hz, RCLike.star_def, Complex.conj_ofReal]
    have hc := cc_ne_zero (hD' i)
    have : ((cc d d' i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
    cases h : ε i <;> simpa using this

end GlobalTheory.CompanionTheory.RgHeFrame
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnitaryInterlacingRealizationStatement
open Finset Matrix PositivityTheory.RgHe.Frame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_interlacing_realization : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), ε (e (Sum.inr ())) = true → (∀ a, ε (e (Sum.inl a)) = ε' a) → Function.Injective (Sum.elim d d') → (∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i) → (∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j)) → ∃ g X : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, Formalism.REAL.inUJ ε g ∧ X * g = g * diagonal (fun i => ((d i : ℝ) : ℂ)) ∧ (∀ a b, X (e (Sum.inl a)) (e (Sum.inl b)) = if a = b then ((d' a : ℝ) : ℂ) else 0) ∧ ∀ i, ((Formalism.REAL.Jm ε * gᴴ * Formalism.REAL.Jm ε) *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ)) i ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.build | exact GlobalTheory.CompanionTheory.RgHeFrame.build | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.build <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicative
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHe

theorem hs_mul_le_mul {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ) :
    Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  have key : ∀ i j, ‖(P * Q) i j‖ ^ 2 ≤ (∑ k, ‖P i k‖ ^ 2) * (∑ k, ‖Q k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(P * Q) i j‖ ≤ ∑ k, ‖P i k‖ * ‖Q k j‖ := by
      rw [Matrix.mul_apply]
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => norm_mul_le _ _)
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans
      (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
  have hQ : Formalism.REAL.hs Q = ∑ j, ∑ k, ‖Q k j‖ ^ 2 := by
    unfold Formalism.REAL.hs
    exact Finset.sum_comm
  rw [hQ]
  unfold Formalism.REAL.hs
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j

end GlobalTheory.CompanionTheory.RgHe
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HilbertSchmidtNormSubmultiplicativeStatement
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_schmidt_norm_submultiplicative : ∀ {m : ℕ} (P Q : Matrix (Fin m) (Fin m) ℂ), Formalism.REAL.hs (P * Q) ≤ Formalism.REAL.hs P * Formalism.REAL.hs Q := by
  first | exact @GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | exact GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul | (intros; apply GlobalTheory.CompanionTheory.RgHe.hs_mul_le_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantAnnihilatingVectorZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantAnnihilatingVectorZero
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

theorem commutant_cyclic_eq_zero : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (v : Fin m → ℂ),
    IsUnit g.det → Function.Injective d → (∀ i, (g⁻¹ *ᵥ v) i ≠ 0) →
    ∀ A : Matrix (Fin m) (Fin m) ℂ, A * (g * diagonal d * g⁻¹) = (g * diagonal d * g⁻¹) * A →
      A *ᵥ v = 0 → A = 0 := by
  intro m g d v hg hd hv A hc hAv
  have h1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g hg
  have h2 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv g hg
  obtain ⟨M, hM⟩ : ∃ M, M = g⁻¹ * A * g := ⟨_, rfl⟩
  have hcomm : M * diagonal d = diagonal d * M := by
    calc M * diagonal d = g⁻¹ * (A * (g * diagonal d * g⁻¹)) * g := by
          rw [hM]
          simp only [Matrix.mul_assoc]
          rw [h1, Matrix.mul_one]
      _ = g⁻¹ * ((g * diagonal d * g⁻¹) * A) * g := by rw [hc]
      _ = diagonal d * M := by
          rw [hM]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc g⁻¹ g, h1, Matrix.one_mul]
  have hdiag : ∀ i k, i ≠ k → M i k = 0 := by
    intro i k hik
    have h := congrFun (congrFun hcomm i) k
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    have h3 : M i k * (d k - d i) = 0 := by rw [mul_sub, h]; ring
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · exact absurd (hd (sub_eq_zero.mp h4)).symm hik
  have hMg : M * g⁻¹ = g⁻¹ * A := by
    rw [hM, Matrix.mul_assoc, h2, Matrix.mul_one]
  have hMv : M *ᵥ (g⁻¹ *ᵥ v) = 0 := by
    rw [Matrix.mulVec_mulVec, hMg, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero]
  have hM0 : M = 0 := by
    ext i k
    by_cases hik : i = k
    · subst hik
      have h := congrFun hMv i
      have h5 : M i i * (g⁻¹ *ᵥ v) i = 0 := by
        have h6 : (M *ᵥ (g⁻¹ *ᵥ v)) i = M i i * (g⁻¹ *ᵥ v) i := by
          rw [Matrix.mulVec, dotProduct]
          exact Finset.sum_eq_single i (fun j _ hj => by rw [hdiag i j (Ne.symm hj), zero_mul])
            (fun h => absurd (Finset.mem_univ i) h)
        rw [← h6, h]; rfl
      simpa using (mul_eq_zero.mp h5).resolve_right (hv i)
    · simpa using hdiag i k hik
  calc A = g * (g⁻¹ * A * g) * g⁻¹ := by
        simp only [Matrix.mul_assoc]
        rw [h2, Matrix.mul_one, ← Matrix.mul_assoc, h2, Matrix.one_mul]
    _ = 0 := by rw [← hM, hM0, Matrix.mul_zero, Matrix.zero_mul]

end GlobalTheory.CompanionTheory.RgHeFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutantAnnihilatingVectorZeroStatement
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutant_annihilating_vector_zero : ∀ {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (v : Fin m → ℂ), IsUnit g.det → Function.Injective d → (∀ i, (g⁻¹ *ᵥ v) i ≠ 0) → ∀ A : Matrix (Fin m) (Fin m) ℂ, A * (g * diagonal d * g⁻¹) = (g * diagonal d * g⁻¹) * A → A *ᵥ v = 0 → A = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero | exact GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.commutant_cyclic_eq_zero <;> assumption)
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.Assembly
noncomputable section

open Finset Matrix Formalism.REAL

namespace PositivityTheory.RgHe.FrameA

open PositivityTheory.RgHe.Frame PositivityTheory.UnitaryDecomposition

variable {n : ℕ} {e : Fin n ⊕ Unit ≃ Fin (n + 1)}

theorem hs_nonneg' {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : 0 ≤ hs A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem hs_emb_sub (a : Matrix (Fin n) (Fin n) ℂ) : hs (emb e a - 1) = hs (a - 1) := by
  have h1 : emb e a - 1 = Matrix.reindex e e (Matrix.fromBlocks (a - 1) 0 0 0) := by
    ext i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j <;> simp [emb, Matrix.one_apply, e.injective.eq_iff]
  rw [h1]
  unfold hs
  rw [← e.sum_comp, Fintype.sum_sum_type]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  simp [← e.sum_comp, Fintype.sum_sum_type]

theorem emb_mulVec_alt (a : Matrix (Fin n) (Fin n) ℂ) :
    emb e a *ᵥ (Pi.single (e (Sum.inr ())) (1 : ℂ) : Fin (n + 1) → ℂ) = Pi.single (e (Sum.inr ())) 1 := by
  ext i
  rw [Matrix.mulVec_single_one]
  obtain ⟨i, rfl⟩ := e.surjective i
  rcases i with i | i <;> simp [emb]

theorem frame : PositivityTheory.RgHe.Frame := by
  intro n ε d ε' d' e hF hinj hW
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.interlacing_signature_parity n ε d ε' d' e hF hinj hW
  obtain ⟨ps1, ps2⟩ := GlobalTheory.T.partial_fraction_coefficient_signs d d' hinj
  have hD : ∀ i, 0 < (if ε i then (1 : ℝ) else -1) * pfD d d' i := fun i => by
    have h := ps1 i
    by_cases hi : ε i = true
    · rw [if_pos hi, one_mul]
      rwa [((hs1 i).1 hi).neg_one_pow, one_mul] at h
    · rw [if_neg hi]
      have ho : ¬ Even (above d d' (d i)) := fun h' => hi ((hs1 i).2 h')
      rw [(Nat.not_even_iff_odd.1 ho).neg_one_pow] at h
      linarith
  have hR : ∀ j, 0 < -((if ε' j then (1 : ℝ) else -1) * pfR d d' j) := fun j => by
    have h := ps2 j
    by_cases hj : ε' j = true
    · rw [if_pos hj]
      rw [(Nat.not_even_iff_odd.1 ((hs2 j).1 hj)).neg_one_pow] at h
      linarith
    · rw [if_neg hj]
      have he : Even (above d d' (d' j)) := by
        by_contra h'
        exact hj ((hs2 j).2 h')
      rw [he.neg_one_pow, one_mul] at h
      linarith
  obtain ⟨g, X, hgU, hXg, hblk, hβ⟩ := GlobalTheory.T.exists_unitary_interlacing_realization n ε d ε' d' e hF.1 hF.2 hinj hD hR
  set J := Jm ε with hJ
  have hJJ : J * J = 1 := Jm_mul_self ε
  have h2 : (J * gᴴ * J) * g = 1 := by
    have : (J * gᴴ * J) * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
    rw [this, hgU, hJJ]
  have hinv : g⁻¹ = J * gᴴ * J := Matrix.inv_eq_left_inv h2
  have hdet : IsUnit g.det := Matrix.isUnit_det_of_left_inverse h2
  have h1 : g * (J * gᴴ * J) = 1 := by rw [← hinv]; exact Matrix.mul_nonsing_inv g hdet
  let gu : UJ ε := ⟨⟨g, J * gᴴ * J, h1, h2⟩, hgU⟩
  have hgu : um gu = g := rfl
  have hgu' : um gu⁻¹ = g⁻¹ := by
    rw [hinv]; rfl
  refine ⟨gu, fun Y => ?_, ?_⟩
  · rw [hgu, hgu']
    exact GlobalTheory.T.trace_diagonal_block_conjugate_formula n e d d' g X hdet hXg hblk Y
  · set D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ := diagonal fun i => ((d i : ℝ) : ℂ) with hDd
    have hX : X = g * D * g⁻¹ := by
      rw [hXg.symm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    set v : Fin (n + 1) → ℂ := Pi.single (e (Sum.inr ())) 1 with hv
    have hdi : Function.Injective fun i => ((d i : ℝ) : ℂ) := fun i j h =>
      Sum.inl_injective (hinj (by simpa using h))
    have hcyc : ∀ A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0 := by
      intro A hA hAv
      rw [hX] at hA
      exact GlobalTheory.T.commutant_annihilating_vector_zero g _ v hdet hdi (fun i => by rw [hinv]; exact hβ i) A hA hAv
    obtain ⟨c, hc, hAc⟩ := GlobalTheory.T.commutator_coercive_on_annihilator X v hcyc
    refine ⟨c * hs g * hs g⁻¹ + 1, by have := hs_nonneg' g; have := hs_nonneg' g⁻¹; positivity, fun h => ?_⟩
    set B := emb e (um h) with hB
    set B' := emb e (um h⁻¹) with hB'
    have hBB : B * B' = 1 := by
      rw [hB, hB', ← emb_mul, ← emb_one (e := e)]
      congr 1
      exact Units.mul_inv h.1
    have hBB' : B' * B = 1 := by
      rw [hB, hB', ← emb_mul, ← emb_one (e := e)]
      congr 1
      exact Units.inv_mul h.1
    set δ := dg d - (um gu⁻¹ * B' * um gu) * dg d * (um gu⁻¹ * B * um gu) with hδ
    have hdg : dg d = D := rfl
    have key : (B - 1) * X - X * (B - 1) = B * (g * δ * g⁻¹) := by
      rw [hδ, hgu, hgu', hdg, hX]
      have e1 : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul _ hdet
      have e2 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      have e3 : B * (g * (g⁻¹ * (B' * (g * (D * (g⁻¹ * (B * (g * g⁻¹)))))))) = g * (D * (g⁻¹ * B)) := by
        rw [e2, Matrix.mul_one, ← Matrix.mul_assoc g g⁻¹, e2, Matrix.one_mul, ← Matrix.mul_assoc B B', hBB, Matrix.one_mul]
      rw [e3]
      abel
    have hAv : (B - 1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hB, emb_mulVec_alt, sub_self]
    have i1 := hAc (B - 1) hAv
    rw [key] at i1
    have i2 : hs (B * (g * δ * g⁻¹)) ≤ hs B * (hs g * hs δ * hs g⁻¹) := by
      refine (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_left ?_ (hs_nonneg' _))
      refine (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _).trans (mul_le_mul_of_nonneg_right (GlobalTheory.T.hilbert_schmidt_norm_submultiplicative _ _) (hs_nonneg' _))
    have i3 : hs (um h - 1) = hs (B - 1) := (hs_emb_sub (e := e) (um h)).symm
    rw [i3]
    have := hs_nonneg' B; have := hs_nonneg' δ; have := hs_nonneg' g; have := hs_nonneg' g⁻¹
    calc hs (B - 1) ≤ c * (hs B * (hs g * hs δ * hs g⁻¹)) := i1.trans (mul_le_mul_of_nonneg_left i2 hc.le)
      _ = (c * hs g * hs g⁻¹) * hs B * hs δ := by ring
      _ ≤ (c * hs g * hs g⁻¹ + 1) * hs B * hs δ := by gcongr; linarith

end PositivityTheory.RgHe.FrameA
end
end

namespace PositivityTheory.RgHe.FrameF

theorem frame : PositivityTheory.RgHe.Frame := PositivityTheory.RgHe.FrameA.frame

end PositivityTheory.RgHe.FrameF
