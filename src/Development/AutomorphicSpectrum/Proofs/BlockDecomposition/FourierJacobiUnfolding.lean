module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeisenbergCosetsParamRational

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCentreCharacterCell
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCentreCharacterCell
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf.SmallZ
open GlobalTheory.CompanionTheory.SwUnf.SmallCell

variable {D : D7} {n ρ p : ℕ}

theorem zinc_inl {K : Type} [Field K] (hn : ρ + p = n) (u : Fin ρ → K) (a : Fin ρ) :
    zinc hn u ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl a)) = u a := by
  change Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm _) = u a
  rw [Equiv.symm_apply_apply, Sum.elim_inl]

theorem zinc_inr {K : Type} [Field K] (hn : ρ + p = n) (u : Fin ρ → K) (a : Fin p) :
    zinc hn u ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr a)) = 0 := by
  change Sum.elim u (fun _ : Fin p => (0 : K)) ((finSumFinEquiv.trans (finCongr hn)).symm _) = 0
  rw [Equiv.symm_apply_apply, Sum.elim_inr]

theorem blockMatrix_inl_inl {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i j : Fin ρ) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = a i j := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem blockMatrix_inl_inr {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i : Fin ρ) (j : Fin p) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

theorem blockMatrix_inr_inl {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i : Fin p) (j : Fin ρ) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

theorem blockMatrix_inr_inr {R : Type} [Zero R] (hn : ρ + p = n) (a : Matrix (Fin ρ) (Fin ρ) R) (i j : Fin p) :
    bl hn a 0 0 0 ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i))
      ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = 0 := by
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

def rk2 {m : ℕ} (τ : AE D) (v r : Fin m → D.host.E) : Mx D m m :=
  τ • ((rat (Matrix.replicateCol (Fin 1) v) : Mx D m 1) ⬝ (rat (Matrix.replicateRow (Fin 1) r) : Mx D 1 m) +
    adj (rat (Matrix.replicateRow (Fin 1) r) : Mx D 1 m) ⬝ adj (rat (Matrix.replicateCol (Fin 1) v) : Mx D m 1))

theorem rank_two_matrix_apply {m : ℕ} (τ : AE D) (v r : Fin m → D.host.E) (i j : Fin m) :
    rk2 τ v r i j = τ * (incA D (v i) * incA D (r j) + cA D (incA D (r i)) * cA D (incA D (v j))) := by
  simp only [rk2, Matrix.smul_apply, Matrix.add_apply, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul]
  rfl

theorem rk_term (τ : AE D) (a b c d : D.host.E) (h1 : a = 0 ∨ b = 0) (h2 : c = 0 ∨ d = 0) :
    τ * (incA D a * incA D b + cA D (incA D c) * cA D (incA D d)) = 0 := by
  have e1 : incA D a * incA D b = 0 := by
    rcases h1 with rfl | rfl
    · rw [map_zero (incA D), zero_mul]
    · rw [map_zero (incA D), mul_zero]
  have e2 : cA D (incA D c) * cA D (incA D d) = 0 := by
    rcases h2 with rfl | rfl
    · rw [map_zero (incA D), map_zero (cA D), zero_mul]
    · rw [map_zero (incA D), map_zero (cA D), mul_zero]
  rw [e1, e2, add_zero, mul_zero]

theorem rank_two_embedding_small (hn : ρ + p = n) (τ : AE D) (v r : Fin ρ → D.host.E) :
    rk2 τ (zinc hn v) (zinc hn r) = bl hn (rk2 τ v r) 0 0 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i <;> rcases j with j | j
  · rw [blockMatrix_inl_inl, rank_two_matrix_apply, rank_two_matrix_apply, zinc_inl, zinc_inl, zinc_inl, zinc_inl]
  · rw [blockMatrix_inl_inr, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inr (zinc_inr hn r j)) (Or.inr (zinc_inr hn v j))
  · rw [blockMatrix_inr_inl, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inl (zinc_inr hn v i)) (Or.inl (zinc_inr hn r i))
  · rw [blockMatrix_inr_inr, rank_two_matrix_apply]
    exact rk_term _ _ _ _ _ (Or.inl (zinc_inr hn v i)) (Or.inl (zinc_inr hn r i))

theorem small : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ), b₀.1.det ≠ 0 →
    ∀ (W : Submodule D.host.E (Fin ρ → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D ρ, chz ψ b₀ ν ≠ 1 ∧
    ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → zKer hn x = W →
      mat u = blk4 1 (bl hn ν.1 0 0 0) 0 1 →
      ∃ q ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat q) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = q * γ := by
  intro D n ρ p hn ψ hψ β hβ W hW
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hw : β.1 *ᵥ v ≠ 0 := fun h => hv0 (Matrix.eq_zero_of_mulVec_eq_zero hβ h)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw
  let r : Fin ρ → D.host.E := Pi.single i0 ((β.1 *ᵥ v) i0)⁻¹
  let V0 : Matrix (Fin ρ) (Fin 1) D.host.E := Matrix.replicateCol _ v
  let R0 : Matrix (Fin 1) (Fin ρ) D.host.E := Matrix.replicateRow _ r
  have hbV : β.1 ⬝ V0 = Matrix.replicateCol _ (β.1 *ᵥ v) := by
    ext i j
    simp [V0, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hS0 : R0 ⬝ β.1 ⬝ V0 = (1 : Matrix (Fin 1) (Fin 1) D.host.E) := by
    rw [Matrix.mul_assoc, hbV]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [R0, r, Matrix.mul_apply, Pi.single_apply, inv_mul_cancel₀ (show (β.1 *ᵥ v) i0 ≠ 0 from hi0)]
  have hS : (rat R0 : Mx D 1 ρ) ⬝ (rat β.1 : Mx D ρ ρ) ⬝ (rat V0 : Mx D ρ 1) = 1 := by
    rw [← rat_mul, ← rat_mul, hS0]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [rat]
  obtain ⟨x0, hx0⟩ := hψ.2.2.2
  obtain ⟨t, ht⟩ := exists_scalar (D := D) x0
  have hν : adj (rk2 (algebraMap (AF D.host.F) (AE D) t) v r) = rk2 (algebraMap (AF D.host.F) (AE D) t) v r := by
    unfold rk2
    rw [adj_smul, cA_algebraMap', adj_add, adj_mul, adj_mul, adj_adj, adj_adj, add_comm]
  refine ⟨⟨_, hν⟩, ?_, ?_⟩
  · have h := trace_val (rat β.1) (adj_rat_herm β) (rat V0) (rat R0) (algebraMap (AF D.host.F) (AE D) t) hS
    change ψ (halfTr (Matrix.trace ((rat β.1 : Mx D ρ ρ) ⬝ _))) ≠ 1
    change ψ (halfTr (Matrix.trace ((rat β.1 : Mx D ρ ρ) ⬝ (algebraMap (AF D.host.F) (AE D) t • _)))) ≠ 1
    rw [h, ht]
    exact hx0
  · intro γ u hγ x hx hW' hu
    refine cell_absorb (rat (Matrix.replicateCol (Fin 1) (zinc hn v))) (rat (Matrix.replicateRow (Fin 1) (zinc hn r)))
      (algebraMap (AF D.host.F) (AE D) t) ((rank_two_embedding_small hn _ v r).symm) γ u hu ?_
    have hv : lowerC x *ᵥ zinc hn v = 0 := by
      rw [← hW'] at hvW
      exact hvW
    have h0 : (HMul.hMul (lowerC x) (Matrix.replicateCol (Fin 1) (zinc hn v)) : Matrix (Fin n) (Fin 1) D.host.E) = 0 := by
      refine Matrix.ext fun i j => ?_
      have := congrFun hv i
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    rw [hx, lowerC_map]
    change (rat (lowerC x) : Mx D n n) ⬝ (rat (Matrix.replicateCol (Fin 1) (zinc hn v)) : Mx D n 1) = 0
    rw [← rat_mul, h0]
    ext i j
    simp [rat]

end GlobalTheory.CompanionTheory.ZUnf.SmallZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCentreCharacterCellStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nondegenerate_centre_character_cell : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ), b₀.1.det ≠ 0 →
    ∀ (W : Submodule D.host.E (Fin ρ → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D ρ, chz ψ b₀ ν ≠ 1 ∧
    ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → zKer hn x = W →
      mat u = blk4 1 (bl hn ν.1 0 0 0) 0 1 →
      ∃ q ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat q) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = q * γ := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.SmallZ.small | exact GlobalTheory.CompanionTheory.ZUnf.SmallZ.small | (intros; apply GlobalTheory.CompanionTheory.ZUnf.SmallZ.small <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainUnfoldingTwoSums
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainUnfoldingTwoSums
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.UnfoldFam

open GlobalTheory.CompanionTheory.UnfoldAbs

theorem unfold_fam : ∀ {A X Y U : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] [Countable U] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : U → A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1)
    (Um : X → ℝ) (_ : Summable Um) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (_ : ∀ b, ∃ l : Λ, ∀ q, ‖F q b‖ ≤ Um (τ l q))
    (e : Λ × U → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l l' : Λ) u, τ l' (e (l, u)) = e (l' + l, u))
    (_ : ∀ (l : Λ) u b, F (e (l, u)) b = F0 u ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    (∀ u, Integrable (F0 u) lam ∧ ∫ b, ‖F0 u b‖ ∂lam ≤ ∑' l : Λ, Um (e (l, u))) ∧
    HasSum (fun u => ∫ b, F0 u b * ch b ∂lam) (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) := by
  intro A X Y U _ _ _ lam _ Λ _ 𝓖 h𝓖 h1 _ _ c y0 F F0 ch hF hch hnorm hmul hΛ Um hUm τ hτ hcτ hbd
    e he hfib hτe hF0 hν
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by simp [h1]⟩

  have hUm0 : ∀ q, 0 ≤ Um q := by
    intro q
    obtain ⟨l, hl⟩ := hbd 0
    have := hl ((τ l).symm q)
    rw [Equiv.apply_symm_apply] at this
    exact (norm_nonneg _).trans this

  have hb : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ ∑' q, Um q := by
    intro b
    obtain ⟨l, hl⟩ := hbd b
    have hs : Summable (fun q => Um (τ l q)) := (τ l).summable_iff.mpr hUm
    have hs1 : Summable (fun q => ‖F q b‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hl hs
    refine ⟨hs1, ?_⟩
    calc ∑' q, ‖F q b‖ ≤ ∑' q, Um (τ l q) := hs1.tsum_le_tsum hl hs
      _ = ∑' q, Um q := (τ l).tsum_eq Um
  have hsub : ∀ {Z : Type} (j : Z → X), Function.Injective j → ∀ b,
      Summable (fun z => ‖F (j z) b‖) ∧ ∑' z, ‖F (j z) b‖ ≤ ∑' q, Um q := by
    intro Z j hj b
    refine ⟨(hb b).1.comp_injective hj, ?_⟩
    exact (tsum_comp_le_tsum_of_inj (hb b).1 (fun _ => norm_nonneg _) hj).trans (hb b).2
  have key : ∀ {Z : Type} [Countable Z] (j : Z → X), Function.Injective j →
      HasSum (fun z => ∫ b in 𝓖, F (j z) b * ch b ∂lam)
        (∫ b in 𝓖, (∑' z, F (j z) b) * ch b ∂lam) := by
    intro Z _ j hj
    have := hasSum_integral_of_norm_bound (lam.restrict 𝓖) (fun z b => F (j z) b * ch b)
      (fun z => ((hF (j z)).mul hch).restrict) (∑' q, Um q) (fun b => by
        simpa [hnorm] using hsub j hj b)
    simpa only [tsum_mul_right] using this

  have heu : ∀ u, Function.Injective (fun l : Λ => e (l, u)) := fun u a b h =>
    (Prod.mk.inj (he h)).1
  have hF0e : ∀ u, F0 u = F (e (0, u)) := by
    intro u
    funext b
    have := hF0 0 u b
    simpa using this.symm
  have hm0 : ∀ u, AEStronglyMeasurable (F0 u) lam := fun u => hF0e u ▸ hF (e (0, u))
  have hSs : ∀ u, Summable (fun l : Λ => Um (e (l, u))) := fun u => hUm.comp_injective (heu u)
  have hS0 : ∀ u, 0 ≤ ∑' l : Λ, Um (e (l, u)) := fun u => tsum_nonneg fun _ => hUm0 _
  have horb : ∀ u b, Summable (fun l : Λ => ‖F0 u ((l : A) + b)‖) ∧
      ∑' l : Λ, ‖F0 u ((l : A) + b)‖ ≤ ∑' l : Λ, Um (e (l, u)) := by
    intro u b
    obtain ⟨l0, hl0⟩ := hbd b
    have hle : ∀ l : Λ, ‖F0 u ((l : A) + b)‖ ≤ Um (e (l0 + l, u)) := by
      intro l
      rw [← hF0 l u b, ← hτe l l0 u]
      exact hl0 _
    have hs : Summable (fun l : Λ => Um (e (l0 + l, u))) :=
      (Equiv.addLeft l0).summable_iff.mpr (hSs u)
    have hs1 : Summable (fun l : Λ => ‖F0 u ((l : A) + b)‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hs
    refine ⟨hs1, ?_⟩
    calc ∑' l : Λ, ‖F0 u ((l : A) + b)‖ ≤ ∑' l : Λ, Um (e (l0 + l, u)) :=
          hs1.tsum_le_tsum hle hs
      _ = ∑' l : Λ, Um (e (l, u)) :=
          (Equiv.addLeft l0).tsum_eq (fun l : Λ => Um (e (l, u)))
  have hint0 : ∀ u, Integrable (F0 u) lam := fun u =>
    integrable_of_lattice_bound lam Λ 𝓖 h𝓖 h1 (F0 u) (hm0 u) _ (horb u)
  have hnb : ∀ u, ∫ b, ‖F0 u b‖ ∂lam ≤ ∑' l : Λ, Um (e (l, u)) := by
    intro u
    rw [integral_norm_eq_lintegral_enorm (hm0 u)]
    refine ENNReal.toReal_le_of_le_ofReal (hS0 u) ?_
    have ee : ∫⁻ b, ‖F0 u b‖ₑ ∂lam = ∑' l : Λ, ∫⁻ b in 𝓖, ‖F0 u ((l : A) + b)‖ₑ ∂lam :=
      h𝓖.lintegral_eq_tsum'' _
    have hmeas : ∀ l : Λ, AEMeasurable (fun b => ‖F0 u ((l : A) + b)‖ₑ) (lam.restrict 𝓖) :=
      fun l => (((hm0 u).comp_measurePreserving
        (measurePreserving_add_left lam (l : A))).enorm).restrict
    rw [ee, ← lintegral_tsum hmeas]
    calc ∫⁻ b in 𝓖, ∑' l : Λ, ‖F0 u ((l : A) + b)‖ₑ ∂lam
        ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal (∑' l : Λ, Um (e (l, u))) ∂lam := by
          refine lintegral_mono (fun b => ?_)
          simp_rw [← ofReal_norm_eq_enorm]
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (horb u b).1]
          exact ENNReal.ofReal_le_ofReal (horb u b).2
      _ = ENNReal.ofReal (∑' l : Λ, Um (e (l, u))) := by simp [h1]
  refine ⟨fun u => ⟨hint0 u, hnb u⟩, ?_⟩

  have hT := key (Z := X) id Function.injective_id
  simp only [id] at hT
  have hsig := (Equiv.sigmaFiberEquiv c).hasSum_iff.mpr hT
  have hg : HasSum (fun y => ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam)
      (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) :=
    hsig.sigma (fun y => key (Z := {x // c x = y}) Subtype.val Subtype.val_injective)

  have hzero : ∀ y, y ≠ y0 → ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam = 0 := by
    intro y hy
    obtain ⟨ν, hν1, hνq⟩ := hν y hy
    refine setIntegral_eq_zero_of_translate lam Λ 𝓖 h𝓖 _ ν (ch ν) hν1 (fun l b => ?_) (fun b => ?_)
    · have hs : ∑' z : {x // c x = y}, F z ((l : A) + b) = ∑' z : {x // c x = y}, F z b := by
        calc ∑' z : {x // c x = y}, F z ((l : A) + b)
            = ∑' z : {x // c x = y}, F (τ l z) b := tsum_congr fun z => hτ l z b
          _ = ∑' z : {x // c x = y}, F z b :=
            ((τ l).subtypeEquiv (p := fun x => c x = y) (q := fun x => c x = y)
              (fun a => by rw [hcτ])).tsum_eq (fun z : {x // c x = y} => F z b)
      rw [hs, hmul, hΛ, one_mul]
    · have hs : ∑' z : {x // c x = y}, F z (ν + b) = ∑' z : {x // c x = y}, F z b :=
        tsum_congr fun z => hνq z z.2 b
      rw [hs, hmul]
      ring
  have hT' := hg.unique (hasSum_single y0 (fun y hy => hzero y hy))
  rw [hT']

  let ee : Λ × U ≃ {x // c x = y0} := Equiv.ofBijective
    (fun p => ⟨e p, (hfib _).2 ⟨p, rfl⟩⟩)
    ⟨fun a b h => he (congrArg Subtype.val h), fun q => by
      obtain ⟨p, hp⟩ := (hfib q).1 q.2
      exact ⟨p, Subtype.ext hp⟩⟩
  have hsum : ∀ b, ∑' z : {x // c x = y0}, F z b = ∑' p : Λ × U, F (e p) b := fun b =>
    (ee.tsum_eq (fun z => F z b)).symm
  simp_rw [hsum]
  have hK := key e he
  have hK' : HasSum (fun p : U × Λ => ∫ b in 𝓖, F (e (p.2, p.1)) b * ch b ∂lam)
      (∫ b in 𝓖, (∑' p : Λ × U, F (e p) b) * ch b ∂lam) :=
    (Equiv.prodComm U Λ).hasSum_iff.mpr hK
  refine hK'.prod_fiberwise (fun u => ?_)
  have hs := hK'.summable.prod_factor u
  have hint1 : Integrable (fun b => F0 u b * ch b) lam :=
    (hint0 u).mono ((hint0 u).aestronglyMeasurable.mul hch) (ae_of_all _ fun b => by simp [hnorm])
  have hval : ∫ b, F0 u b * ch b ∂lam = ∑' l : Λ, ∫ b in 𝓖, F (e (l, u)) b * ch b ∂lam := by
    rw [h𝓖.integral_eq_tsum'' _ hint1]
    refine tsum_congr fun l => ?_
    refine integral_congr_ae (ae_of_all _ fun b => ?_)
    change F0 u ((l : A) + b) * ch ((l : A) + b) = F (e (l, u)) b * ch b
    rw [hF0, hmul, hΛ, one_mul]
  rw [hval]
  exact hs.hasSum

end GlobalTheory.CompanionTheory.UnfoldFam
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainUnfoldingTwoSumsStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_unfolding_two_sums : ∀ {A X Y U : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] [Countable U] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : U → A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1)
    (Um : X → ℝ) (_ : Summable Um) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (_ : ∀ b, ∃ l : Λ, ∀ q, ‖F q b‖ ≤ Um (τ l q))
    (e : Λ × U → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l l' : Λ) u, τ l' (e (l, u)) = e (l' + l, u))
    (_ : ∀ (l : Λ) u b, F (e (l, u)) b = F0 u ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    (∀ u, Integrable (F0 u) lam ∧ ∫ b, ‖F0 u b‖ ∂lam ≤ ∑' l : Λ, Um (e (l, u))) ∧
    HasSum (fun u => ∫ b, F0 u b * ch b ∂lam) (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldFam.unfold_fam | exact GlobalTheory.CompanionTheory.UnfoldFam.unfold_fam | (intros; apply GlobalTheory.CompanionTheory.UnfoldFam.unfold_fam <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTermsUniformlySummable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTermsUniformlySummable
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf

theorem law_facts : ∀ {D : D7} {n : ℕ} {χ : (AE D)ˣ →* Circle} {s : ℂ} {f : G D n → ℂ}, IsHeckeChar D χ → Continuous f → IsLaw χ s f → (n : ℝ) / 2 < s.re →
    LeftInv (P D n ⊓ GF D n) f ∧
    (∀ q ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat q) = a.1 → Matrix.GeneralLinearGroup.det a = 1 → ∀ g, f (q * g) = f g) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ u : Cosets (P D n) (GF D n) → ℝ, Summable u ∧ ∀ q, ∀ g ∈ C, ‖term (P D n) (GF D n) f g q‖ ≤ u q := by
  intro D n χ s f hχ hc hl hs
  haveI := t2Space_adeleRing' (F := D.host.F)
  refine ⟨fun γ hγ g => ?_, fun q hq a ha h1 g => ?_, fun C hC => ?_⟩
  · obtain ⟨hp, hr⟩ := Subgroup.mem_inf.1 hγ
    obtain ⟨a, ha⟩ := exists_blkA hp
    obtain ⟨u, hu⟩ := det_rat hr a ha
    have h1 : absA D (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hu]; exact absE_inclR u
    have h2 : χ (Matrix.GeneralLinearGroup.det a) = 1 := by
      rw [hu]; exact hχ.2 u
    rw [hl γ hp a ha g, h1, h2]
    simp [npow]
  · rw [hl q hq a ha g, h1]
    simp [npow]
  · have hlaw : IndLaw (GlobalTheory.StdUnn.PolesModel.modP (D := D) (n := n))
        (χ.comp GlobalTheory.StdUnn.PolesModel.detP) (s + (n : ℂ) / 2) f := fun p g =>
      hl p p.2 (GlobalTheory.StdUnn.HeightExists.leviBlock (D := D) (n := n) p) rfl g
    have h1 : Continuous (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n)) :=
      PolesModel.isIwasawa.continuous_iwAbs GlobalTheory.StdUnn.Model.isClosed_P PolesModel.continuous_modP GlobalTheory.StdUnn.Model.isCompact_K
    have h2 : Continuous fun g => Real.log (iwAbs (PolesModel.modP (D := D) (n := n)) (K D n) g) :=
      (NNReal.continuous_coe.comp h1).log fun g => (NNReal.coe_pos.2 (iwAbs_pos _ _ g)).ne'
    have hcf : Continuous fun x : ℂ × G D n => flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s x.1 x.2 := by
      simp only [flatSec, npow_eq_exp (iwAbs_pos _ _ _)]
      exact (hc.comp continuous_snd).mul (((Complex.continuous_ofReal.comp (h2.comp continuous_snd)).mul
        (continuous_fst.sub continuous_const)).cexp)
    obtain ⟨u, hu, hb⟩ := exists_majorant (Φ := fun z => flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s z)
      (χ := χ.comp PolesModel.detP) (ρ := (n : ℝ) / 2) (σ := (n : ℝ) / 2) PolesModel.isIwasawa GlobalTheory.StdUnn.Model.isCompact_K
      hcf.continuousOn
      (fun z _ => by
        have := (PolesModel.isIwasawa (D := D) (n := n)).indLaw_flatSec hlaw z
        push_cast
        exact this) PolesModel.summable_spherical (S := {s}) isCompact_singleton (Set.singleton_subset_iff.2 hs) hC
    have e : flatSec (PolesModel.modP (D := D) (n := n)) (K D n) f s s = f := funext fun x => by
      simp [flatSec, npow_eq_exp (iwAbs_pos _ _ _)]
    refine ⟨u, hu, fun q g hg => ?_⟩
    have := hb q s rfl g hg
    rwa [e] at this

end GlobalTheory.CompanionTheory.ZUnf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinTermsUniformlySummableStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_terms_uniformly_summable : ∀ {D : D7} {n : ℕ} {χ : (AE D)ˣ →* Circle} {s : ℂ} {f : G D n → ℂ}, IsHeckeChar D χ → Continuous f → IsLaw χ s f → (n : ℝ) / 2 < s.re →
    LeftInv (P D n ⊓ GF D n) f ∧
    (∀ q ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat q) = a.1 → Matrix.GeneralLinearGroup.det a = 1 → ∀ g, f (q * g) = f g) ∧
    ∀ C : Set (G D n), IsCompact C → ∃ u : Cosets (P D n) (GF D n) → ℝ, Summable u ∧ ∀ q, ∀ g ∈ C, ‖term (P D n) (GF D n) f g q‖ ≤ u q := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.law_facts | exact GlobalTheory.CompanionTheory.ZUnf.law_facts | (intros; apply GlobalTheory.CompanionTheory.ZUnf.law_facts <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfolding
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

namespace GlobalTheory.CompanionTheory.ZUnf
open GlobalTheory.Eis

variable {D : D7} {n ρ p : ℕ}

theorem chz_add (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (a b : hermA D ρ) :
    chz ψ b₀ (a + b) = chz ψ b₀ a * chz ψ b₀ b := by
  simp only [chz, AddSubgroup.coe_add]
  rw [Matrix.mul_add, Matrix.trace_add, GlobalTheory.CompanionTheory.HermPoisson.halfTr_add', AddChar.map_add_eq_mul]

theorem chz_norm {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (a : hermA D ρ) :
    ‖chz ψ b₀ a‖ = 1 := hψ.2.1 _

theorem chz_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) : Continuous (chz ψ b₀) :=
  GlobalTheory.CompanionTheory.HermPoisson.continuous_chi hψ (b₀.1.map (incA D) : Mx D ρ ρ)

theorem chz_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D ρ) (l : ratHerm D ρ) :
    chz ψ b₀ l.1 = 1 :=
  GlobalTheory.CompanionTheory.HermPoisson.chi_rat hψ (m := (b₀.1.map (incA D) : Mx D ρ ρ)) ⟨b₀.1, rfl⟩ l

theorem continuous_jacobi_map_zero {hn : ρ + p = n} (M : Maps D hn) : Continuous fun z : hermA D ρ => M.nzx z 0 :=
  M.nzx_cont.comp (continuous_id.prodMk continuous_const)


set_option maxHeartbeats 1600000 in
theorem unfold_on {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    {b₀ : HermE D ρ} (hb₀ : b₀.1.det ≠ 0) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) {s : ℂ} {f : G D n → ℂ}
    (hf : Continuous f) (hl : IsLaw χ s f) (hs : (n : ℝ) / 2 < s.re) (C : Set (G D n)) (hC : IsCompact C) :
    ∃ Um : Cosets (P D n) (GF D n) → ℝ, Summable Um ∧
    ∃ e : ratHerm D ρ × (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) → Cosets (P D n) (GF D n),
      Function.Injective e ∧ ∀ g ∈ C,
      (∀ u, ‖Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)‖ ≤ ∑' l : ratHerm D ρ, Um (e (l, u))) ∧
      HasSum (fun u : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E =>
        Wz M m ψ b₀ f (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g)) (zc M m ψ b₀ (eisS f) g) := by
  obtain ⟨hinv, hdet, hmaj⟩ := GlobalTheory.T.eisenstein_terms_uniformly_summable hχ hf hl hs
  obtain ⟨hHaar, hFD, hvol⟩ := m.hz
  obtain ⟨hadd, hcsh, hcem, hrat⟩ := GlobalTheory.T.heisenberg_centre_rational_form M
  have hcolat := GlobalTheory.CompanionTheory.HermVol.isCoLat_herm (D := D) (r := ρ)
  haveI : Countable (ratHerm D ρ) := countable_ratHerm
  haveI : Countable (Cosets (P D n) (GF D n)) := countable_cosets
  haveI : Countable (Cosets (P D p) (GF D p)) := countable_cosets
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) := countable_mat ρ p
  obtain ⟨e, he, hfib, hτe, hterm⟩ := GlobalTheory.T.heisenberg_cosets_param_rational hn M
  obtain ⟨K0, hK0, hKc⟩ := hcolat.2
  have hcn := continuous_jacobi_map_zero M
  obtain ⟨Um, hUm, hub⟩ := hmaj ((fun d : hermA D ρ × G D n => M.nzx d.1 0 * d.2) '' (K0 ×ˢ C))
    ((hK0.prod hC).image ((hcn.comp continuous_fst).mul continuous_snd))
  refine ⟨Um, hUm, e, he, fun g hg => ?_⟩
  let F : Cosets (P D n) (GF D n) → hermA D ρ → ℂ := fun q b => term (P D n) (GF D n) f (M.nzx b 0 * g) q
  let F0 : Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E → hermA D ρ → ℂ := fun u z =>
    f (M.w * M.nzx z 0 * (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g))
  let ch : hermA D ρ → ℂ := fun b => conj (chz ψ b₀ b)
  let τ : ratHerm D ρ → Cosets (P D n) (GF D n) ≃ Cosets (P D n) (GF D n) := fun l =>
    rmulEquiv _ _ ⟨M.nzx l.1 0, (hrat l).1⟩
  have hτ : ∀ (l : ratHerm D ρ) q b, F q ((l : hermA D ρ) + b) = F (τ l q) b := fun l q b => by
    simp only [F]
    rw [hadd, mul_assoc]
    exact term_mul_left hinv ⟨M.nzx l.1 0, (hrat l).1⟩ _ q
  have hchc : Continuous ch := Complex.continuous_conj.comp (chz_cont hψ b₀)
  have hF : ∀ q, Continuous (F q) := fun q =>
    hf.comp (continuous_const.mul (hcn.mul continuous_const))
  have hF0 : ∀ (l : ratHerm D ρ) u b, F (e (l, u)) b = F0 u ((l : hermA D ρ) + b) := fun l u b => by
    simp only [F, F0]
    rw [hterm f hinv, hadd]
    congr 1
    have h1 : M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * (M.nzx b 0 * g) =
        M.nzx b 0 * (M.sh (u.2.map (incA D)) * M.emb (u.1.out : GF D p) * g) := by
      rw [← mul_assoc, mul_assoc (M.sh _), ← hcem, ← mul_assoc, ← hcsh]
      simp only [mul_assoc]
    simp only [mul_assoc] at h1 ⊢
    rw [h1]
  have key := GlobalTheory.T.fundamental_domain_unfolding_two_sums m.lz (ratHerm D ρ) m.𝓖 hFD hvol
    (fun q : Cosets (P D n) (GF D n) => zKer hn (ratOf q.out)) (⊥ : Submodule D.host.E (Fin ρ → D.host.E)) F F0 ch
    (fun q => (hF q).aestronglyMeasurable) hchc.aestronglyMeasurable
    (fun b => by simp only [ch, RCLike.norm_conj]; exact chz_norm hψ b₀ b)
    (fun a b => by simp only [ch]; rw [chz_add, map_mul])
    (fun l => by simp only [ch]; rw [chz_rat hψ b₀ l, map_one])
    Um hUm τ hτ
    (fun l q => by
      obtain ⟨ζ, -, hζ⟩ := (hrat l).2
      have := GlobalTheory.CompanionTheory.SwUnf.cosetCell_rmulEquiv (D := D) (n := n) q ⟨M.nzx l.1 0, (hrat l).1⟩ (bl hn ζ 0 0 0) hζ
      change (cosetCell (τ l q)).comap (zinc hn) = (cosetCell q).comap (zinc hn)
      rw [show cosetCell (τ l q) = cosetCell q from this])
    (fun b => by
      obtain ⟨γ, hγ, hb⟩ := hKc b
      refine ⟨-⟨γ, hγ⟩, fun q => ?_⟩
      have h1 := hτ (-⟨γ, hγ⟩) q (γ + b)
      have h2 : (((-⟨γ, hγ⟩ : ratHerm D ρ) : hermA D ρ) + (γ + b)) = b := by simp
      rw [h2] at h1
      rw [h1]
      exact hub _ _ ⟨(γ + b, g), ⟨hb, hg⟩, rfl⟩)
    e he hfib (fun l l' u => hτe l l' u (hrat l').1) hF0
    (fun y hy => by
      obtain ⟨ν, hν1, hν⟩ := GlobalTheory.T.nondegenerate_centre_character_cell hn hψ b₀ hb₀ y hy
      refine ⟨ν, ?_, fun q hq b => ?_⟩
      · intro h
        apply hν1
        have := congrArg (starRingEnd ℂ) h
        simpa [ch] using this
      · obtain ⟨x, hxP, a, ha, hd, hpe⟩ : ∃ x ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat x) = a.1 ∧
            Matrix.GeneralLinearGroup.det a = 1 ∧ (q.out : G D n) * M.nzx ν 0 = x * (q.out : G D n) := by
          obtain ⟨x, hx, a, ha, hd, hpe⟩ := hν (q.out : GF D n) (M.nzx ν 0) (q.out : GF D n).2 (ratOf q.out) (mat_ratOf _) hq
            (by rw [M.nzx_mat, adj_zero])
          exact ⟨x, hx, a, ha, hd, hpe⟩
        simp only [F, term]
        rw [hadd, mul_assoc (M.nzx ν 0), ← mul_assoc _ (M.nzx ν 0), hpe, mul_assoc, hdet x hxP a ha hd])
  refine ⟨fun u => ?_, ?_⟩
  · obtain ⟨hi, hle⟩ := key.1 u
    refine le_trans ?_ hle
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [F0, norm_mul, RCLike.norm_conj, chz_norm hψ b₀, mul_one]
  · exact key.2

theorem zUnfold : ZUnfold := by
  intro D n ρ p hn M m ψ hψ b₀ hb₀ χ hχ s f hf hl hs g
  refine ⟨?_, fun C hC => ?_⟩
  · obtain ⟨Um, -, e, -, h⟩ := unfold_on M m hψ hb₀ hχ hf hl hs {g} isCompact_singleton
    exact (h g rfl).2
  · obtain ⟨Um, hUm, e, he, h⟩ := unfold_on M m hψ hb₀ hχ hf hl hs C hC
    refine ⟨fun u => ∑' l : ratHerm D ρ, Um (e (l, u)), ?_, fun g hg u => (h g hg).1 u⟩
    have h1 : Summable (fun x : (Cosets (P D p) (GF D p) × Matrix (Fin ρ) (Fin p) D.host.E) × ratHerm D ρ => Um (e (x.2, x.1))) :=
      hUm.comp_injective (he.comp Prod.swap_injective)
    exact h1.prod

end GlobalTheory.CompanionTheory.ZUnf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfoldingStatement
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_jacobi_unfolding : ZUnfold := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.zUnfold | exact GlobalTheory.CompanionTheory.ZUnf.zUnfold | (intros; apply GlobalTheory.CompanionTheory.ZUnf.zUnfold <;> assumption)
end
