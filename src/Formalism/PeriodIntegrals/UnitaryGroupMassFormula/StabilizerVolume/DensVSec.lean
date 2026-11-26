module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSS

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSec
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

theorem exists_leftInv_of_linIndep {K : Type} [CommRing K] [IsSemisimpleRing K] {a M : ℕ}
    (Z : Fin a → Fin M → K) (hZ : LinearIndependent K Z) :
    ∃ q : Fin M → Fin a → K, ∀ i i', ∑ k, Z i k * q k i' = if i = i' then 1 else 0 := by
  classical
  let ι : (Fin a → K) →ₗ[K] (Fin M → K) := Fintype.linearCombination K Z
  have hinj : Function.Injective ι := by
    intro x y hxy
    have h0 : ∑ i, (x - y) i • Z i = 0 := by
      have := congrArg (fun v => v) hxy
      simp only [ι, Fintype.linearCombination_apply] at this
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, this, sub_self]
    funext i
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hZ _ h0 i)
  obtain ⟨q, hq⟩ := exists_isCompl (LinearMap.range ι)
  let e := LinearEquiv.ofInjective ι hinj
  let p : (Fin M → K) →ₗ[K] (Fin a → K) :=
    e.symm.toLinearMap ∘ₗ (LinearMap.range ι).projectionOnto q hq
  have hp : ∀ x, p (ι x) = x := by
    intro x
    have e1 : ι x = ((e x : LinearMap.range ι) : Fin M → K) := rfl
    simp only [p, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [e1, Submodule.projectionOnto_apply_left, LinearEquiv.symm_apply_apply]
  refine ⟨fun k i' => p (Pi.single k 1) i', fun i i' => ?_⟩
  have hZi : Z i = ∑ k, Z i k • (Pi.single k (1 : K) : Fin M → K) := by
    funext j; simp [Finset.sum_apply, Pi.single_apply]
  have hι : ι (Pi.single i 1) = Z i := by
    simp [ι, Fintype.linearCombination_apply_single]
  have e1 : ∑ k, Z i k * p (Pi.single k 1) i' = p (Z i) i' := by
    conv_rhs => rw [hZi]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [e1, ← hι, hp, Pi.single_apply]
  by_cases h : i = i'
  · subst h; simp
  · simp [h, Ne.symm h]

theorem secGram_holds : SecGram := by
  intro F E _ _ _ _ _ σ hσ M J hJ hdet R _ _ hss a x hx
  have := hss
  let s := sigR R σ
  let Z : Fin a → Fin M → R ⊗[F] E := fun i => Matrix.vecMul (fun l => s (x i l)) (JR (F := F) R J)
  have hZh : ∀ i y, hR R σ J (x i) y = ∑ k, Z i k * y k := by
    intro i y
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hJu : IsUnit (JR (F := F) R J).det := by
    have e := RingHom.map_det (inclR (F := F) (E := E) R) J
    rw [RingHom.mapMatrix_apply] at e
    show IsUnit (J.map (inclR R)).det
    rw [← e]
    exact (isUnit_iff_ne_zero.2 hdet).map _
  have hZ : LinearIndependent (R ⊗[F] E) Z := by
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let v : Fin M → R ⊗[F] E := fun l => ∑ i, g i * s (x i l)
    have hv0 : Matrix.vecMul v (JR (F := F) R J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, v, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : v = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) R J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • x i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [v, map_sum, map_mul, s, sigR_invol R σ hσ, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hx _ hX0 i
    have e2 := congrArg s this
    simp only [s, sigR_invol R σ hσ, map_zero] at e2
    exact e2
  obtain ⟨q, hq⟩ := exists_leftInv_of_linIndep Z hZ
  refine ⟨q, fun S hS => ?_⟩
  have hh : algebraMap F (R ⊗[F] E) (1 / 2) + algebraMap F (R ⊗[F] E) (1 / 2) = 1 := by
    rw [← map_add (f := _), show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  have hsh : sigR R σ (algebraMap F (R ⊗[F] E) (1 / 2)) = algebraMap F (R ⊗[F] E) (1 / 2) :=
    (Algebra.TensorProduct.map (AlgHom.id F R) σ).commutes _
  have h1 : ∀ i j, hR R σ J (x i)
      (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i j := by
    intro i j
    rw [hZh]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have e3 : ∀ i', ∑ k, Z i k * (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * q k i') =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i' j * (if i = i' then 1 else 0) := fun i' => by
      rw [← hq i i', Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp only [e3, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∀ i j, hR R σ J
      (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) =
        algebraMap F (R ⊗[F] E) (1 / 2) * S i j := by
    intro i j
    rw [← hR_herm R σ hσ J hJ (x j), h1 j i, map_mul, hsh, hS i j]
  funext i j
  show hR R σ J (x i) (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') +
    hR R σ J (fun k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' i) * q k i') (x j) = S i j
  rw [h1, h2, ← add_mul, hh, one_mul]

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfTR
noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
open PI.AdicCompletionValuation

theorem exists_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  classical
  let L : (κ → Fin k → ℝ) ≃L[ℝ] (Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨Module.finrank ℝ (κ → Fin k → ℝ), (Homeomorph.piCongrRight fun _ => e).trans L.toHomeomorph, ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply, Homeomorph.piCongrRight_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← map_add (f := _)]
  congr 1
  funext i
  simp [he]

theorem exists_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  have hreal : ∀ v : NumberField.InfinitePlace F, v.IsReal := fun v => NumberField.IsTotallyReal.isReal v
  let e1 : Ainf F ≃ₜ (NumberField.InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal (hreal v)).toHomeomorph
  let L : (NumberField.InfinitePlace F → ℝ) ≃L[ℝ]
      (Fin (Module.finrank ℝ (NumberField.InfinitePlace F → ℝ)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨Module.finrank ℝ (NumberField.InfinitePlace F → ℝ), e1.trans L.toHomeomorph, ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← map_add (f := _)]
  congr 1
  funext v
  have hx : e1 (x + y) v = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hreal v) (x v + y v) := rfl
  have hx1 : e1 x v = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hreal v) (x v) := rfl
  have hx2 : e1 y v = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hreal v) (y v) := rfl
  rw [Pi.add_apply, hx, hx1, hx2, map_add (f := _)]

theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  obtain ⟨k, eA, heA⟩ := exists_coord_Ainf F
  let b : Module.Basis (Fin (Module.finrank F E)) F E := Module.finBasis F E
  let bR := Algebra.TensorProduct.basis (Ainf F) b
  let ℓ : (Ainf F ⊗[F] E) ≃ₗ[Ainf F] (Fin (Module.finrank F E) → Ainf F) := bR.equivFun
  have hc1 : Continuous ℓ := IsModuleTopology.continuous_of_linearMap ℓ.toLinearMap
  have hc2 : Continuous ℓ.symm := IsModuleTopology.continuous_of_linearMap ℓ.symm.toLinearMap
  let h1 : (Ainf F ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Ainf F) :=
    { toEquiv := ℓ.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }
  obtain ⟨n, e', he'⟩ := exists_coord_pi eA heA (Fin (Module.finrank F E))
  refine ⟨n, h1.trans e', ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply]
  rw [show h1 (x + y) = h1 x + h1 y from map_add ℓ x y, he']

theorem exists_coord_sub {X : Type} [AddCommGroup X] [TopologicalSpace X] {N : ℕ}
    (e : X ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (H : AddSubgroup X)
    (hH : IsClosed (H : Set X)) (hdiv : ∀ n : ℕ, 0 < n → ∀ x ∈ H, ∃ y ∈ H, n • y = x) :
    ∃ (m : ℕ) (eH : H ≃ₜ (Fin m → ℝ)), ∀ x y, eH (x + y) = eH x + eH y := by
  classical
  have e0 : e 0 = 0 := by simpa using he 0 0
  let eA : X →+ (Fin N → ℝ) := { toFun := e, map_zero' := e0, map_add' := he }
  have hcl : IsClosed (e '' (H : Set X)) := e.isClosed_image.mpr hH
  have hrat : ∀ x ∈ H, ∀ q : ℚ, (q : ℝ) • e x ∈ e '' (H : Set X) := by
    intro x hx q
    obtain ⟨y, hy, hyx⟩ := hdiv q.den q.pos x hx
    refine ⟨q.num • y, H.zsmul_mem hy _, ?_⟩
    have h1 : e (q.num • y) = q.num • e y := map_zsmul eA q.num y
    have h2 : (q.den : ℝ) • e y = e x := by
      rw [← hyx]
      have := map_nsmul eA q.den y
      simp only [eA, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [this, Nat.cast_smul_eq_nsmul]
    rw [h1, ← h2, smul_smul, ← Int.cast_smul_eq_zsmul ℝ]
    congr 1
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [Rat.cast_def]
    field_simp
  have hreal : ∀ x ∈ H, ∀ r : ℝ, r • e x ∈ e '' (H : Set X) := by
    intro x hx r
    have hS : IsClosed {t : ℝ | t • e x ∈ e '' (H : Set X)} :=
      hcl.preimage (continuous_id.smul continuous_const)
    have hsub : Set.range (Rat.cast : ℚ → ℝ) ⊆ {t : ℝ | t • e x ∈ e '' (H : Set X)} := by
      rintro _ ⟨q, rfl⟩; exact hrat x hx q
    have := hS.closure_subset_iff.mpr hsub
    rw [Rat.denseRange_cast.closure_range] at this
    exact this (Set.mem_univ r)
  let V : Submodule ℝ (Fin N → ℝ) :=
    { carrier := e '' (H : Set X)
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, H.add_mem ha hb, he a b⟩
      zero_mem' := ⟨0, H.zero_mem, e0⟩
      smul_mem' := by
        rintro r _ ⟨a, ha, rfl⟩
        exact hreal a ha r }
  let L : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let eI : H ≃ₜ V := e.image (H : Set X)
  refine ⟨Module.finrank ℝ V, eI.trans L.toHomeomorph, ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← map_add (f := _)]
  congr 1
  apply Subtype.ext
  show e ((x : X) + (y : X)) = e x + e y
  exact he x y

end PI.VolStabS
end
end
