module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormCore

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HilbertSchmidtBlocks.HSBlocksMain
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HilbertSchmidtBlocks.Change
noncomputable section

open scoped Classical ComplexConjugate

namespace NormHilbertSchmidtBlocks

theorem sum_inner_change {E F ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (e : κ → E)
    (he : ∀ x y : E, ∑ k, inner ℂ x (e k) * inner ℂ (e k) y = inner ℂ x y)
    (A B : E →ₗ[ℂ] F) :
    ∑ k, inner ℂ (A (e k)) (B (e k)) = ∑ i, inner ℂ (A (b i)) (B (b i)) := by
  have hexp : ∀ x : E, ∑ i, inner ℂ (b i) x • b i = x := fun x => b.sum_repr' x
  have key : ∀ k, inner ℂ (A (e k)) (B (e k)) =
      ∑ i, ∑ i', (inner ℂ (b i) (e k) * inner ℂ (e k) (b i')) * inner ℂ (A (b i')) (B (b i)) := by
    intro k
    conv_lhs => rw [← hexp (e k)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      inner_conj_symm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, he, orthonormal_iff_ite.mp b.orthonormal, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem parseval_single {C' V' : Type*} [Fintype C'] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V']
    (x y : PiLp 2 (fun _ : C' => V')) :
    ∑ p : (Σ _ : C', Fin (Module.finrank ℂ V')),
      inner ℂ x (WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V')) *
      inner ℂ (WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V')) y =
      inner ℂ x y := by
  have h1 : ∀ (c : C') (v : V'),
      inner ℂ x (WithLp.toLp 2 (Pi.single c v : C' → V')) = inner ℂ (x c) v := by
    intro c v
    rw [PiLp.inner_apply, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      simp [Pi.single_apply, hd]
    · simp
  have h2 : ∀ (c : C') (v : V'),
      inner ℂ (WithLp.toLp 2 (Pi.single c v : C' → V')) y = inner ℂ v (y c) := by
    intro c v
    rw [PiLp.inner_apply, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      simp [Pi.single_apply, hd]
    · simp
  rw [Fintype.sum_sigma]
  simp only [h1, h2, OrthonormalBasis.sum_inner_mul_inner]
  exact (PiLp.inner_apply x y).symm

end NormHilbertSchmidtBlocks
end
end

noncomputable section

open scoped Classical ComplexConjugate

namespace NormHilbertSchmidtBlocks

open Formalism.L2.SG.NormCut

theorem hSBlocks_main : HSBlocks := by
  intro C C' V V' _ _ _ _ _ _ _ A B
  have hS : ∀ {W U : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      [NormedAddCommGroup U] [InnerProductSpace ℂ U] (S T : W →L[ℂ] U),
      inner ℂ (hsV S) (hsV T) =
        ∑ i, inner ℂ (S (stdOrthonormalBasis ℂ W i)) (T (stdOrthonormalBasis ℂ W i)) := by
    intro W U _ _ _ _ _ S T
    simp [hsV, PiLp.inner_apply]
  have hblk : ∀ (T : PiLp 2 (fun _ : C' => V') →L[ℂ] PiLp 2 (fun _ : C => V)) (ρ : C) (ρ' : C') (v : V'),
      blockOf T ρ ρ' v = T (WithLp.toLp 2 (Pi.single ρ' v : C' → V')) ρ := by
    intro T ρ ρ' v
    rfl
  have hch := sum_inner_change (stdOrthonormalBasis ℂ (PiLp 2 (fun _ : C' => V')))
    (fun p : (Σ _ : C', Fin (Module.finrank ℂ V')) =>
      WithLp.toLp 2 (Pi.single p.1 (stdOrthonormalBasis ℂ V' p.2) : C' → V'))
    (parseval_single) A.toLinearMap B.toLinearMap
  simp only [ContinuousLinearMap.coe_coe] at hch
  rw [hS, ← hch, Fintype.sum_sigma]
  simp only [hS]
  simp only [hblk, PiLp.inner_apply]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ' _ => ?_
  rw [Finset.sum_comm]

end NormHilbertSchmidtBlocks
end
end

theorem hilbert_schmidt_blocks : Formalism.L2.SG.NormCut.HSBlocks :=
  NormHilbertSchmidtBlocks.hSBlocks_main
