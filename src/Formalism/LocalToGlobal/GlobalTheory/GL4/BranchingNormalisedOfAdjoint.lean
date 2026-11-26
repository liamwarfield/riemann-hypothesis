module

public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.SharpRestriction.GlobalSchurBounds.IntegrableOfContinuousCircleMeasure
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
public import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL4.BranchingNormalisedOfAdjoint
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open MvPolynomial Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.MainNotions.flipTwoThree
open Formalism.REAL (fockF)

theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j h
  have := lam.anti h
  unfold DomWeight.natW
  omega

theorem weyl_eq_dual (r n : ℕ) (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) :
    weyl ℂ r n hn ν = dualWeyl ℂ r n ν :=
  le_antisymm (Formalism.GradedWeylDivisibility.weylLeDual ℂ r n hn ν hν) (Formalism.BranchingDeterminantCap.bs_dual_le_weyl hn ν hν)

theorem dualWeyl_fd (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℂ (dualWeyl ℂ r n ν) := by
  have hle : dualWeyl ℂ r n ν ≤ homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s) := by
    intro f hf
    have h1 : f ∈ weightedHomogeneousSubmodule ℂ (colW r n) ν := (Submodule.mem_inf.mp hf).1
    rw [mem_weightedHomogeneousSubmodule] at h1
    rw [mem_homogeneousSubmodule]
    intro m hm
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_weight_sum, h1 hm]
  have : FiniteDimensional ℂ (homogeneousSubmodule (Fin r × Fin n) ℂ (∑ s, ν s)) :=
    Module.Finite.iff_fg.mpr (homogeneousSubmodule_fg _ _ _)
  exact Submodule.finiteDimensional_of_le hle

theorem delSq_rowAct {n : ℕ} (sg : DomWeight n) (A : Matrix (Fin n) (Fin n) ℂ) (v : MvPolynomial (Fin n × Fin n) ℂ)
    (hv : v ∈ delSq ℂ n sg) : rowAct ℂ A v ∈ delSq ℂ n sg := by
  unfold delSq at hv ⊢
  rw [weyl_eq_dual n n le_rfl _ (natW_anti sg)] at hv ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n _ A v hv

theorem delSq_fd {n : ℕ} (sg : DomWeight n) : FiniteDimensional ℂ (delSq ℂ n sg) := by
  unfold delSq
  rw [weyl_eq_dual n n le_rfl _ (natW_anti sg)]
  exact dualWeyl_fd n n _

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL4.CTEqConjTranspose
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Matrix

section CSMat

variable {ι : Type} [Fintype ι]

end CSMat

section CSSpace

open Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_expand (S : HSpace E) (x y : S.V) :
    S.hT x y = ∑ i, ∑ j, star (S.frame.repr x i) * (S.gram i j * S.frame.repr y j) := by
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul,
    smul_eq_mul, starRingEnd_apply, HSpace.gram, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end CSSpace

section CSRecord

open Formalism.BasicNotions Formalism.MainNotions.flipTwoThree

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end CSRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end
