module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocAbs

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeModel
open IsLocalRing UpperTheory.V.Hi

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeModel :
    ∀ (A M ι : Type) [CommRing A] [AddCommGroup M] [Module A M] (Y : Submodule A M) (op : ι → Module.End A M), CommOn Y op → ∃ (T : Type) (_ : CommRing T) (_ : Algebra A T) (j : T →ₐ[A] Module.End A Y) (t : ι → T), Function.Injective j ∧ j.range = heckeAlg Y op ∧ (∀ i, Restr (j (t i)) (op i)) ∧ Algebra.adjoin A (Set.range t) = ⊤ ∧ (IsNoetherianRing A → Module.Finite A Y → Module.Finite A T) := by
  intro A M ι _ _ _ Y op h
  have key : ∀ s ∈ {t : Module.End A Y | ∃ i, Restr t (op i)},
      ∀ t ∈ {t : Module.End A Y | ∃ i, Restr t (op i)}, s * t = t * s := by
    rintro s ⟨i, hi⟩ t ⟨j, hj⟩
    refine LinearMap.ext fun y => Subtype.ext ?_
    change (s (t y) : M) = t (s y)
    rw [hi, hj, hj, hi]
    exact h.2 i j y y.2
  have hc : ∀ a b : heckeAlg Y op, a * b = b * a := by
    exact isMulCommutative_iff.mp
      (Algebra.isMulCommutative_adjoin A (fun a ha b hb _ => key a ha b hb))
  let t : ι → heckeAlg Y op := fun i =>
    ⟨(op i).restrict (h.1 i), Algebra.subset_adjoin ⟨i, fun _ => rfl⟩⟩
  have htop : Algebra.adjoin A (Set.range t) = ⊤ := by
    have h1 : Set.range t = ((↑) : heckeAlg Y op → Module.End A Y) ⁻¹'
        {t : Module.End A Y | ∃ i, Restr t (op i)} := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i, fun _ => rfl⟩
      · rintro ⟨i, hi⟩
        exact ⟨i, Subtype.ext (LinearMap.ext fun y => Subtype.ext (hi y).symm)⟩
    rw [h1]
    exact Algebra.adjoin_adjoin_coe_preimage
  have hfin : IsNoetherianRing A → Module.Finite A Y → Module.Finite A (heckeAlg Y op) := by
    intro _ _
    obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := Y)
    let f : heckeAlg Y op →ₗ[A] (Fin n → Y) :=
      { toFun := fun t i => (t : Module.End A Y) (s i)
        map_add' := fun a b => by ext i; simp
        map_smul' := fun a b => by ext i; simp }
    have hf : Function.Injective f := by
      intro a b hab
      refine Subtype.ext (LinearMap.ext_on_range hs fun i => ?_)
      exact congrFun hab i
    exact Module.Finite.of_injective f hf
  exact ⟨heckeAlg Y op, { (inferInstance : Ring (heckeAlg Y op)) with mul_comm := hc },
    (inferInstance : Algebra A (heckeAlg Y op)), (heckeAlg Y op).val, t, Subtype.val_injective,
    Subalgebra.range_val _, fun i _ => rfl, htop, hfin⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.PointEig
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FibreNe
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.fibreNe :
    ∀ {T K M : Type*} [CommRing T] [Field K] [Algebra T K] [AddCommGroup M] [Module T M] [Module.Finite T M] [FaithfulSMul T M], Nontrivial (K ⊗[T] M) := by
  intro T K M _ _ _ _ _ _ _
  classical
  haveI hp : (RingHom.ker (algebraMap T K)).IsPrime := RingHom.ker_isPrime _
  set p : Ideal T := RingHom.ker (algebraMap T K) with hpdef
  let P : PrimeSpectrum T := ⟨p, hp⟩
  have hP : P ∈ Module.support T M := by
    rw [Module.support_eq_zeroLocus, (Module.annihilator_eq_bot).mpr inferInstance]
    simp
  have hV : Nontrivial (p.ResidueField ⊗[T] M) :=
    (Module.mem_support_iff_nontrivial_residueField_tensorProduct P).mp hP
  let f : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap T K) le_rfl (by
    intro x hx
    have hx' : algebraMap T K x ≠ 0 := fun h => hx ((RingHom.mem_ker).mpr h)
    exact (isUnit_iff_ne_zero.mpr hx'))
  letI : Algebra p.ResidueField K := f.toAlgebra
  haveI : IsScalarTower T p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap p (algebraMap T K) le_rfl _ r).symm
  let e := AlgebraTensorModule.cancelBaseChange T p.ResidueField K K M
  haveI : Nontrivial (K ⊗[p.ResidueField] (p.ResidueField ⊗[T] M)) :=
    TensorProduct.nontrivial_of_linearMap_injective_of_flat_right p.ResidueField
      K (p.ResidueField ⊗[T] M) (Algebra.linearMap p.ResidueField K)
      (algebraMap p.ResidueField K).injective
  exact e.symm.nontrivial
end

open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.pointEig :
    ∀ {Λ T K M : Type*} [CommRing Λ] [CommRing T] [Algebra Λ T] [Field K] [Algebra Λ K] [AddCommGroup M] [Module Λ M] [Module T M] [IsScalarTower Λ T M] [Module.Finite Λ M] [FaithfulSMul T M] (x : T →ₐ[Λ] K), ∃ y : K ⊗[Λ] M, y ≠ 0 ∧ ∀ t : T, (Algebra.lsmul Λ Λ M t).baseChange K y = x t • y := by
  intro Λ T K M _ _ _ _ _ _ _ _ _ _ _ x
  letI : Algebra T K := x.toRingHom.toAlgebra
  haveI : IsScalarTower Λ T K := IsScalarTower.of_algebraMap_eq fun r => (x.commutes r).symm
  haveI : Module.Finite T M := Module.Finite.of_restrictScalars_finite Λ T M
  have hne : Nontrivial (K ⊗[T] M) := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.fibreNe
  let φ : K ⊗[Λ] M →ₗ[K] K ⊗[T] M := TensorProduct.AlgebraTensorModule.lift
    ((LinearMap.restrictScalarsₗ Λ T M (K ⊗[T] M) K).comp
      (TensorProduct.AlgebraTensorModule.mk T K K M))
  have hφt : ∀ (k : K) (m : M), φ (k ⊗ₜ[Λ] m) = k ⊗ₜ[T] m := by
    intro k m
    simp [φ]
  let A : T → Module.End K (K ⊗[Λ] M) := fun t => (Algebra.lsmul Λ Λ M t).baseChange K
  have hA : ∀ (t : T) (k : K) (m : M), A t (k ⊗ₜ[Λ] m) = k ⊗ₜ[Λ] (t • m) := by
    intro t k m
    simp [A]
  have hc : ∀ s t, Commute (A s) (A t) := by
    intro s t
    show A s * A t = A t * A s
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [Module.End.mul_apply, Module.End.mul_apply, hA, hA, hA, hA, smul_comm]
    | add a b ha hb =>
      rw [Module.End.mul_apply, Module.End.mul_apply] at ha hb ⊢
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have hφA : ∀ t y, φ (A t y) = x t • φ y := by
    intro t y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul k m =>
      rw [hA, hφt, hφt, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
      congr 1
    | add a b ha hb =>
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), smul_add]
  have hφ0 : φ ≠ 0 := by
    intro h0
    have hall : ∀ p : K ⊗[T] M, p = 0 := by
      intro p
      induction p using TensorProduct.induction_on with
      | zero => rfl
      | tmul k m => rw [← hφt, h0, LinearMap.zero_apply]
      | add a b ha hb => rw [ha, hb, add_zero]
    obtain ⟨p, hp⟩ := exists_ne (0 : K ⊗[T] M)
    exact hp (hall p)
  exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot A hc (fun t => x t) φ hφ0 hφA
end
