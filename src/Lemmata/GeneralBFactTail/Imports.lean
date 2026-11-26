module

public import Mathlib

@[expose] public section

universe u_1 u_2 u_3

namespace Bl.general_b_fact_tail

theorem goal1 :
    ∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : IsDomain R]
      [inst_2 : IsPrincipalIdealRing R] [inst_3 : AddCommGroup M] [inst_4 : _root_.Module R M]
      {ι : Type u_3} [inst_5 : Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M) (N : Submodule R M)
      (h : Module.finrank R ↥N = Module.finrank R M) (e : M ≃ₗ[R] ↥N),
      Associated (LinearMap.det (N.subtype ∘ₗ ↑e)) (∏ i : ι, Submodule.smithNormalFormCoeffs b h i) := by
  intro R M _ _ _ _ _ ι _ _ b N h e
  have ab_eq := Submodule.smithNormalFormBotBasis_def b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let e' : M ≃ₗ[R] N := b'.equiv (Submodule.smithNormalFormBotBasis b h) (Equiv.refl _)
  refine (LinearMap.associated_det_comp_equiv N.subtype e e').trans (Associated.of_eq ?_)
  have h1 := Module.Basis.det_comp b' (N.subtype ∘ₗ (e' : M →ₗ[R] N)) b'
  rw [Module.Basis.det_self, mul_one] at h1
  rw [← h1]
  have h2 : (⇑(N.subtype ∘ₗ (e' : M →ₗ[R] N)) ∘ ⇑b') =
      fun i => Submodule.smithNormalFormCoeffs b h i • b' i := by
    funext i
    simp only [Function.comp_apply, LinearMap.coe_comp, LinearEquiv.coe_coe, e',
      Module.Basis.equiv_apply, Equiv.refl_apply, Submodule.subtype_apply]
    exact ab_eq i
  rw [h2, AlternatingMap.map_smul_univ, Module.Basis.det_self, smul_eq_mul, mul_one]

end Bl.general_b_fact_tail
