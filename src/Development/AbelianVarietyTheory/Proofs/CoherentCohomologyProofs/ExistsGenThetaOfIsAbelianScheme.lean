module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem exists_gen_theta_of_isAbelianScheme :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ M : LB B.left, M.IsLB → ∃ t : LB.Gen (Theta B M), t.IsGen := by
  intro K _ _ B _ hB M hM
  have := hB.comm
  exact GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety GlobalTheory.globalFns_holds K B hB (GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety K B hB) M hM

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSymmetricVeryAmple
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.SymVeryAmple

theorem exists_iso_pull_of_triv {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (f : X ⟶ X)
    (h : Triv (LB.LinComb H (K := Fin 2) ![f, 𝟙 X] ![1, -1])) : ∃ w : LB.Iso H (H.pull f), w.IsGen := by
  have e := (CechPic.cls_eq_zero_iff (LB.isLB_linComb hH _ _)).2 h
  rw [CechPic.cls_linComb hH, Fin.sum_univ_two] at e
  refine (CechPic.cls_eq_iff hH (LB.isLB_pull hH f)).1 ?_
  rw [CechPic.cls_pull hH]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, CechPic.pull_id, one_smul, neg_smul] at e
  exact (add_neg_eq_zero.1 e).symm

theorem exists_symmetric_veryAmple : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∃ (H : LB B.left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy B.hom H s ∧ ∃ w : LB.Iso H (H.pull (GrpObj.inv : B ⟶ B).left), w.IsGen := by
  intro K _ _ B _ hB
  have := hB.comm
  obtain ⟨H, m, s, hH, hs, ht⟩ := exists_symmetric_veryAmpleBy K B hB (GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety K B hB)
  exact ⟨H, m, s, hH, hs, exists_iso_pull_of_triv hH _ ht⟩

end GlobalTheory.SymVeryAmple
end
