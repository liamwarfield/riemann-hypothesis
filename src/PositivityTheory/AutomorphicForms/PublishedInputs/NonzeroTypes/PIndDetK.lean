module

public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorProductVectors

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.PIndDetK
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ

namespace P_indDetK

theorem eq_of_eqOn_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {s n : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = n) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Levi k fun a => Fin (d a)) W) (F F' : IndSp (stdBlocks d hd) ρ)
    (h : ∀ κ ∈ KO k (Fin n), F.1.1 κ = F'.1.1 κ) : F = F' := by
  have hfun : F.1.1 = F'.1.1 := by
    funext x
    obtain ⟨p, w, hw, rfl⟩ :=
      GlobalTheory.SmGL.MultiIrr.exists_parab_mul (GlobalTheory.SmGL.stdBlocks d hd) x
    rw [GlobalTheory.SmGL.parInd_law, GlobalTheory.SmGL.parInd_law,
      h w hw]
  exact Subtype.ext (Subtype.ext hfun)

end P_indDetK

theorem step_indDetK : InducedDeterminantTwist := by
  intro k _ _ _ _ s n d hd W _ _ ρ F F' h
  exact P_indDetK.eq_of_eqOn_KO d hd ρ F F' h

end UpperTheory.TNZ
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.TensorVector
noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.TNZ

namespace TensorVector

theorem tprod_ne_zero {ι : Type} [Fintype ι] {X : ι → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] (x : ∀ a, X a) (hx : ∀ a, x a ≠ 0) :
    PiTensorProduct.tprod ℂ x ≠ 0 := by
  choose ℓ hℓ using fun a => Module.Projective.exists_dual_eq_one ℂ (hx a)
  intro h
  have h1 := congrArg (PiTensorProduct.lift
    ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap ℓ)) h
  rw [PiTensorProduct.lift.tprod, map_zero, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply] at h1
  simp [hℓ] at h1

end TensorVector

theorem step_tensorVec : TensorProductVectors := by
  intro k _ _ _ _ s d X _ _ σ μ h
  choose x hx0 hx using h
  refine ⟨PiTensorProduct.tprod ℂ x, TensorVector.tprod_ne_zero x hx0, fun m hm => ?_⟩
  rw [piTensor_tprod]
  have : (fun a => σ a (m a) (x a)) =
      fun a => ((μ a (GeneralLinearGroup.det (m a)) : ℂˣ) : ℂ) • x a :=
    funext fun a => hx a (m a) (hm a)
  rw [this, MultilinearMap.map_smul_univ]
  simp only [RingHom.id_apply]

end UpperTheory.TNZ
end
end
