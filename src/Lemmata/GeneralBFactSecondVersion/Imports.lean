module

public import Mathlib

@[expose] public section

namespace Bl.general_b_fact_second_version

theorem goal1 :
    ∀ {k A : Type} [inst : Field k] [inst_1 : Ring A] [inst_2 : Algebra k A] {W S : Type}
      [inst_3 : AddCommGroup W] [inst_4 : _root_.Module k W] [inst_5 : _root_.Module A W]
      [IsScalarTower k A W] [inst_7 : AddCommGroup S] [inst_8 : _root_.Module A S]
      [FiniteDimensional k W] [IsSemisimpleModule A W] [IsSimpleModule A S],
      (∀ (a : A), (∀ (w : W), a • w = 0) → ∀ (s : S), a • s = 0) → ∃ (f : W →ₗ[A] S), f ≠ 0 := by
  intro k A _ _ _ W S _ _ _ _ _ _ _ _ _ h
  classical
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  let b := Module.finBasis k W
  let φ : A →ₗ[A] (Fin (Module.finrank k W) → W) :=
    LinearMap.pi (fun i => LinearMap.toSpanSingleton A W (b i))
  let σ : A →ₗ[A] S := LinearMap.toSpanSingleton A S s
  have hker : LinearMap.ker φ ≤ LinearMap.ker σ := by
    intro a ha
    simp only [LinearMap.mem_ker] at ha ⊢
    have hb : ∀ i, a • b i = 0 := fun i => by
      simpa [φ] using congr_fun ha i
    have hw : ∀ w : W, a • w = 0 := by
      intro w
      have e : (DistribSMul.toLinearMap k W a) = 0 :=
        b.ext (fun i => hb i)
      exact LinearMap.congr_fun e w
    simpa [σ] using h a hw s
  let ψ₀ : LinearMap.range φ →ₗ[A] S :=
    (LinearMap.ker φ).liftQ σ hker ∘ₗ φ.quotKerEquivRange.symm.toLinearMap
  have hsm : IsSemisimpleModule A (Fin (Module.finrank k W) → W) := inferInstance
  obtain ⟨C, hC⟩ := ComplementedLattice.exists_isCompl (LinearMap.range φ)
  let Ψ : (Fin (Module.finrank k W) → W) →ₗ[A] S :=
    ψ₀ ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hΨ : Ψ (φ 1) = s := by
    have h1 : Submodule.linearProjOfIsCompl _ _ hC (φ 1) = ⟨φ 1, LinearMap.mem_range_self φ 1⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨φ 1, LinearMap.mem_range_self φ 1⟩
    simp only [Ψ, ψ₀, LinearMap.comp_apply, h1, LinearEquiv.coe_toLinearMap,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply]
    simp [σ]
  by_contra hne
  push_neg at hne
  have hz : Ψ = 0 := by
    apply LinearMap.pi_ext'
    intro i
    exact hne _
  rw [hz] at hΨ
  exact hs hΨ.symm

end Bl.general_b_fact_second_version
