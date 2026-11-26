module

public import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.H0IsoHomCohomologyClassZero

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.CohomologyMapTensorRightMorCompCohomologyConj
section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.TwistDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Smul

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]

theorem cochainsMap_smul (c : k) (f : A ⟶ B) : cochainsMap (c • f) = c • cochainsMap f := by
  ext n x : 3
  apply Subtype.ext
  funext y
  rfl


set_option backward.isDefEq.respectTransparency false in
theorem cohomologyMap_smul (c : k) (f : A ⟶ B) (n : ℕ) :
    cohomologyMap (c • f) n = c • cohomologyMap f n := by
  rw [cohomologyMap, cochainsMap_smul]
  dsimp [HomologicalComplex.homologyMap, cohomologyMap]
  rw [← ShortComplex.homologyMap_smul]
  rfl

end Smul

section Morphisms

variable (T : Rep.{u} k G) {M : Rep.{u} k G}


omit [TopologicalSpace G] [IsTopologicalGroup G] in
noncomputable def tensorRightMor (m : M) (hm : ∀ g : G, M.ρ g m = m) : T ⟶ T ⊗ M :=
  Rep.ofHom ⟨(TensorProduct.mk k T M).flip m, fun g => by
    ext t
    simp [Representation.tprod_apply, hm g]⟩



omit [TopologicalSpace G] [IsTopologicalGroup G] in
noncomputable def tensorFormMor (f : M →ₗ[k] k) (hf : ∀ (g : G) (m : M), f (M.ρ g m) = f m) :
    T ⊗ M ⟶ T :=
  Rep.ofHom ⟨(TensorProduct.rid k T).toLinearMap ∘ₗ LinearMap.lTensor T f, fun g => by
    ext t m
    simp [Representation.tprod_apply, hf g]⟩


end Morphisms

section TwistMap

variable (T : Rep.{u} k G) [IsDiscreteRep T] {M : Rep.{u} k G} [IsDiscreteRep M]
  (hM : ∀ (g : G) (m : M), M.ρ g m = m)

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep T] [IsDiscreteRep M] in
theorem tensorRightMor_add (m m' : M) :
    tensorRightMor T (m + m') (fun g => hM g _) =
      tensorRightMor T m (fun g => hM g m) + tensorRightMor T m' (fun g => hM g m') := by
  ext t
  change t ⊗ₜ[k] (m + m') = t ⊗ₜ[k] m + t ⊗ₜ[k] m'
  exact TensorProduct.tmul_add _ _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep T] [IsDiscreteRep M] in
theorem tensorRightMor_smul (c : k) (m : M) :
    tensorRightMor T (c • m) (fun g => hM g _) = c • tensorRightMor T m (fun g => hM g m) := by
  ext t
  change t ⊗ₜ[k] (c • m) = c • t ⊗ₜ[k] m
  exact TensorProduct.tmul_smul _ _ _

noncomputable def twistMap (n : ℕ) :
    TensorProduct k (cohomology T n) M →ₗ[k] cohomology (T ⊗ M) n :=
  TensorProduct.lift
    { toFun := fun x =>
        { toFun := fun m => (cohomologyMap (tensorRightMor T m (fun g => hM g m)) n).hom x
          map_add' := fun m m' => by
            rw [tensorRightMor_add T hM, cohomologyMap_add]
            rfl
          map_smul' := fun c m => by
            rw [tensorRightMor_smul T hM, cohomologyMap_smul, ModuleCat.hom_smul,
              LinearMap.smul_apply, RingHom.id_apply] }
      map_add' := fun x y => by
        ext m
        simp
      map_smul' := fun c x => by
        ext m
        simp }

theorem twistMap_tmul (n : ℕ) (x : cohomology T n) (m : M) :
    twistMap T hM n (x ⊗ₜ[k] m) = (cohomologyMap (tensorRightMor T m (fun g => hM g m)) n).hom x :=
  rfl

end TwistMap

section Subgroup

variable (N : Subgroup G) (T M : Rep.{u} k G)

variable [IsDiscreteRep T] [IsDiscreteRep M] (hM : ∀ (g : N) (m : M), M.ρ g m = m)

noncomputable def twistResMap (n : ℕ) :
    TensorProduct k (cohomology (Rep.res N.subtype T) n) M →ₗ[k]
      cohomology (Rep.res N.subtype (T ⊗ M)) n :=
  (cohomologyMap (resTensorIso N.subtype T M).inv n).hom ∘ₗ
    twistMap (M := Rep.res N.subtype M) (Rep.res N.subtype T) hM n

theorem twistResMap_tmul (n : ℕ) (x : cohomology (Rep.res N.subtype T) n) (m : M) :
    twistResMap N T M hM n (x ⊗ₜ[k] m) =
      (cohomologyMap (tensorRightMor (M := Rep.res N.subtype M) (Rep.res N.subtype T) m
        (fun g => hM g m) ≫ (resTensorIso N.subtype T M).inv) n).hom x := by
  rw [cohomologyMap_comp]
  rfl

end Subgroup

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Equiv

variable (T : Rep.{u} k G) [IsDiscreteRep T] {M : Rep.{u} k G} [IsDiscreteRep M]
  (hM : ∀ (g : G) (m : M), M.ρ g m = m)

include hM


omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep T] [IsDiscreteRep M] in
theorem form_invariant_of_forall_eq (f : M →ₗ[k] k) (g : G) (m : M) : f (M.ρ g m) = f m := by
  rw [hM]


omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep T] [IsDiscreteRep M] in
theorem tensorRightMor_comp_tensorFormMor (m : M) (f : M →ₗ[k] k) :
    tensorRightMor T m (fun g => hM g m) ≫
        tensorFormMor T f (form_invariant_of_forall_eq hM f) = f m • 𝟙 T := by
  ext t
  change f m • t = f m • t
  rfl


omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep T] [IsDiscreteRep M] in
theorem sum_tensorFormMor_comp_tensorRightMor {ι : Type*} [Fintype ι] (b : Module.Basis ι k M) :
    ∑ i, tensorFormMor T (b.coord i) (form_invariant_of_forall_eq hM _) ≫
        tensorRightMor T (b i) (fun g => hM g (b i)) = 𝟙 (T ⊗ M) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro t m
  rw [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
  change ∑ i, (b.coord i m • t) ⊗ₜ[k] b i = t ⊗ₜ[k] m
  simp_rw [Module.Basis.coord_apply, TensorProduct.smul_tmul]
  rw [← TensorProduct.tmul_sum, b.sum_repr]

noncomputable def twistInv {ι : Type*} [Fintype ι] (b : Module.Basis ι k M) (n : ℕ) :
    cohomology (T ⊗ M) n →ₗ[k] TensorProduct k (cohomology T n) M :=
  ∑ i, (TensorProduct.mk k (cohomology T n) M).flip (b i) ∘ₗ
    (cohomologyMap (tensorFormMor T (b.coord i) (form_invariant_of_forall_eq hM _)) n).hom

theorem twistMap_comp_twistInv {ι : Type*} [Fintype ι] (b : Module.Basis ι k M) (n : ℕ) :
    twistMap T hM n ∘ₗ twistInv T hM b n = LinearMap.id := by
  ext y
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [twistInv, LinearMap.comp_apply, LinearMap.sum_apply, map_sum,
    LinearMap.flip_apply, TensorProduct.mk_apply, twistMap_tmul, LinearMap.id_apply]
  simp_rw [← ModuleCat.comp_apply, ← cohomologyMap_comp]
  rw [← LinearMap.sum_apply, ← ModuleCat.hom_sum, ← cohomologyMap_sum,
    sum_tensorFormMor_comp_tensorRightMor, cohomologyMap_id]
  rfl

theorem twistInv_comp_twistMap {ι : Type*} [Fintype ι] (b : Module.Basis ι k M) (n : ℕ) :
    twistInv T hM b n ∘ₗ twistMap T hM n = LinearMap.id := by
  apply TensorProduct.ext'
  intro x m
  simp only [twistInv, LinearMap.comp_apply, LinearMap.sum_apply,
    LinearMap.flip_apply, TensorProduct.mk_apply, twistMap_tmul, LinearMap.id_apply]
  simp_rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, tensorRightMor_comp_tensorFormMor,
    cohomologyMap_smul, cohomologyMap_id, ModuleCat.hom_smul, LinearMap.smul_apply,
    Module.Basis.coord_apply, TensorProduct.smul_tmul]
  rw [← TensorProduct.tmul_sum, b.sum_repr]
  rfl

noncomputable def twistEquiv [Module.Free k M] [Module.Finite k M] (n : ℕ) :
    TensorProduct k (cohomology T n) M ≃ₗ[k] cohomology (T ⊗ M) n :=
  LinearEquiv.ofLinearMap (twistMap T hM n) (twistInv T hM (Module.Free.chooseBasis k M) n)
    (twistMap_comp_twistInv T hM _ n) (twistInv_comp_twistMap T hM _ n)

theorem twistMap_bijective [Module.Free k M] [Module.Finite k M] (n : ℕ) :
    Function.Bijective (twistMap T hM n) :=
  (twistEquiv T hM n).bijective

end Equiv

section Subgroup

variable (N : Subgroup G) (T M : Rep.{u} k G) [IsDiscreteRep T] [IsDiscreteRep M]
  (hM : ∀ (g : N) (m : M), M.ρ g m = m)

theorem cohomologyMap_resTensorIso_inv_bijective (n : ℕ) :
    Function.Bijective (cohomologyMap (resTensorIso N.subtype T M).inv n).hom := by
  refine Function.bijective_iff_has_inverse.2
    ⟨(cohomologyMap (resTensorIso N.subtype T M).hom n).hom, fun x => ?_, fun x => ?_⟩
  · rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, Iso.inv_hom_id, cohomologyMap_id]
    rfl
  · rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, Iso.hom_inv_id, cohomologyMap_id]
    rfl

noncomputable def twistResEquiv [Module.Free k M] [Module.Finite k M] (n : ℕ) :
    TensorProduct k (cohomology (Rep.res N.subtype T) n) M ≃ₗ[k]
      cohomology (Rep.res N.subtype (T ⊗ M)) n :=
  LinearEquiv.ofBijective (twistResMap N T M hM n)
    ((cohomologyMap_resTensorIso_inv_bijective N T M n).comp
      (twistMap_bijective (M := Rep.res N.subtype M) (Rep.res N.subtype T) hM n))

theorem twistResEquiv_apply [Module.Free k M] [Module.Finite k M] (n : ℕ)
    (z : TensorProduct k (cohomology (Rep.res N.subtype T) n) M) :
    twistResEquiv N T M hM n z = twistResMap N T M hM n z :=
  rfl

variable [N.Normal]

theorem cohomologyMap_tensorRightMor_comp_cohomologyConj (n : ℕ) (g : G) (m : M) :
    cohomologyMap (tensorRightMor (M := Rep.res N.subtype M) (Rep.res N.subtype T) m
        (fun h => hM h m) ≫ (resTensorIso N.subtype T M).inv) n ≫ cohomologyConj (T ⊗ M) N n g =
      cohomologyConj T N n g ≫
        cohomologyMap (tensorRightMor (M := Rep.res N.subtype M) (Rep.res N.subtype T) (M.ρ g m)
          (fun h => hM h _) ≫ (resTensorIso N.subtype T M).inv) n := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, ← cohomologyMapAlong_id_eq_cohomologyMap,
    cohomologyConj, cohomologyConj, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun a => ?_) n
  change (T ⊗ M).ρ g (a ⊗ₜ[k] m) = T.ρ g a ⊗ₜ[k] M.ρ g m
  rfl

theorem cohomologyConj_twistResMap_tmul (n : ℕ) (g : G)
    (x : cohomology (Rep.res N.subtype T) n) (m : M) :
    (cohomologyConj (T ⊗ M) N n g).hom (twistResMap N T M hM n (x ⊗ₜ[k] m)) =
      twistResMap N T M hM n ((cohomologyConj T N n g).hom x ⊗ₜ[k] M.ρ g m) := by
  rw [twistResMap_tmul, twistResMap_tmul, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    cohomologyMap_tensorRightMor_comp_cohomologyConj]

theorem cohomologyConj_comp_twistResMap (n : ℕ) (g : G) :
    (cohomologyConj (T ⊗ M) N n g).hom ∘ₗ twistResMap N T M hM n =
      twistResMap N T M hM n ∘ₗ TensorProduct.map (cohomologyConj T N n g).hom (M.ρ g) := by
  apply TensorProduct.ext'
  intro x m
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul]
  exact cohomologyConj_twistResMap_tmul N T M hM n g x m

theorem cohomologyConj_twistResEquiv [Module.Free k M] [Module.Finite k M] (n : ℕ) (g : G)
    (z : TensorProduct k (cohomology (Rep.res N.subtype T) n) M) :
    (cohomologyConj (T ⊗ M) N n g).hom (twistResEquiv N T M hM n z) =
      twistResEquiv N T M hM n (TensorProduct.map (cohomologyConj T N n g).hom (M.ρ g) z) :=
  LinearMap.congr_fun (cohomologyConj_comp_twistResMap N T M hM n g) z

noncomputable def quotientRep : Representation k (G ⧸ N) M :=
  QuotientGroup.lift N M.ρ fun g hg => by
    ext m
    exact hM ⟨g, hg⟩ m

omit [IsDiscreteRep T] [IsDiscreteRep M] [TopologicalSpace G] [IsTopologicalGroup G] in
@[simp]
theorem quotientRep_mk (g : G) (m : M) : quotientRep N M hM (g : G ⧸ N) m = M.ρ g m :=
  rfl

variable [CompactSpace N]

theorem twistResEquiv_cohomologyConjRep [Module.Free k M] [Module.Finite k M] (n : ℕ)
    (q : G ⧸ N) (z : TensorProduct k (cohomology (Rep.res N.subtype T) n) M) :
    cohomologyConjRep (T ⊗ M) N n q (twistResEquiv N T M hM n z) =
      twistResEquiv N T M hM n
        (((cohomologyConjRep T N n).tprod (quotientRep N M hM)) q z) := by
  induction q using QuotientGroup.induction_on with
  | H g =>
    rw [cohomologyConjRep_mk, cohomologyConj_twistResEquiv, Representation.tprod_apply]
    congr 2
    apply TensorProduct.ext'
    intro x m
    rw [TensorProduct.map_tmul, TensorProduct.map_tmul, cohomologyConjRep_mk, quotientRep_mk]

noncomputable def twistInvariantsEquiv [Module.Free k M] [Module.Finite k M] (n : ℕ) :
    ((cohomologyConjRep T N n).tprod (quotientRep N M hM)).invariants ≃ₗ[k]
      cohomologyConjInvariants (T ⊗ M) N n :=
  (twistResEquiv N T M hM n).ofSubmodules _ _ (by
    ext y
    rw [Submodule.mem_map_equiv, mem_cohomologyConjInvariants_iff, Representation.mem_invariants,
      Representation.mem_invariants]
    refine ⟨fun h q => ?_, fun h q => ?_⟩
    · rw [← LinearEquiv.apply_symm_apply (twistResEquiv N T M hM n) y,
        twistResEquiv_cohomologyConjRep, h q]
    · apply (twistResEquiv N T M hM n).injective
      rw [← twistResEquiv_cohomologyConjRep, LinearEquiv.apply_symm_apply, h q])

theorem twistInvariantsEquiv_apply [Module.Free k M] [Module.Finite k M] (n : ℕ)
    (z : ((cohomologyConjRep T N n).tprod (quotientRep N M hM)).invariants) :
    (twistInvariantsEquiv N T M hM n z : cohomology (Rep.res N.subtype (T ⊗ M)) n) =
      twistResEquiv N T M hM n z :=
  rfl

end Subgroup

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory Representation

universe u

section Eval

variable {k G : Type u} [Field k] [Group G]

noncomputable abbrev homRep (T M : Rep.{u} k G) : Rep.{u} k G :=
  Rep.of (T.ρ.linHom M.ρ)

theorem homRep_ρ_apply (T M : Rep.{u} k G) (g : G) (f : T →ₗ[k] M) :
    (homRep T M).ρ g f = M.ρ g ∘ₗ f ∘ₗ T.ρ g⁻¹ :=
  rfl

noncomputable def evalMor (T M : Rep.{u} k G) : T ⊗ homRep T M ⟶ M :=
  Rep.ofHom ⟨TensorProduct.lift (LinearMap.applyₗ (R := k) (M := T) (M₂ := M)), fun g => by
    ext t f
    change (M.ρ g ∘ₗ f ∘ₗ T.ρ g⁻¹) (T.ρ g t) = M.ρ g (f t)
    simp only [LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]⟩

theorem evalMor_hom_tmul (T M : Rep.{u} k G) (t : T) (f : T →ₗ[k] M) :
    (evalMor T M).hom (t ⊗ₜ[k] f) = f t :=
  rfl

theorem evalMor_bijective (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    Function.Bijective (evalMor T M).hom := by
  have : Module.Finite k T := Module.finite_of_finrank_eq_succ hT
  let b : Module.Basis (Fin 1) k T := Module.finBasisOfFinrankEq k T hT
  set t₀ := b 0
  have ht : ∀ t : T, b.coord 0 t • t₀ = t := fun t => by
    simpa using b.sum_repr t
  have hext : ∀ f g : T →ₗ[k] M, f t₀ = g t₀ → f = g := fun f g h =>
    b.ext fun i => by fin_cases i; exact h
  let φ : TensorProduct k T (T →ₗ[k] M) →ₗ[k] (T →ₗ[k] M) :=
    TensorProduct.lift (LinearMap.lsmul k (T →ₗ[k] M) ∘ₗ b.coord 0)
  have hφ : ∀ x : TensorProduct k T (T →ₗ[k] M), t₀ ⊗ₜ[k] φ x = x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t f =>
      simp only [φ, TensorProduct.lift.tmul, LinearMap.comp_apply, LinearMap.lsmul_apply]
      rw [← TensorProduct.smul_tmul, ht]
    | add x y hx hy => rw [map_add (f := _), TensorProduct.tmul_add, hx, hy]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : φ x = 0 := hext _ _ (by
      rw [← hφ x, evalMor_hom_tmul] at hx
      simpa using hx)
    rw [← hφ x, h0, TensorProduct.tmul_zero]
  · intro m
    refine ⟨t₀ ⊗ₜ[k] b.constr k (fun _ => m), ?_⟩
    change b.constr k (fun _ => m) (b 0) = m
    rw [Module.Basis.constr_basis]

noncomputable def evalInv (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    M ⟶ T ⊗ homRep T M :=
  let e := LinearEquiv.ofBijective (evalMor T M).hom.toLinearMap (evalMor_bijective T M hT)
  Rep.ofHom ⟨e.symm.toLinearMap, fun g => by
    ext m
    apply e.injective
    change e (e.symm (M.ρ g m)) = (evalMor T M).hom ((T ⊗ homRep T M).ρ g (e.symm m))
    rw [LinearEquiv.apply_symm_apply, (evalMor T M).hom.isIntertwining]
    change M.ρ g m = M.ρ g (e (e.symm m))
    rw [LinearEquiv.apply_symm_apply]⟩

theorem evalInv_comp_evalMor (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    evalInv T M hT ≫ evalMor T M = 𝟙 M := by
  ext m
  exact (LinearEquiv.ofBijective (evalMor T M).hom.toLinearMap
    (evalMor_bijective T M hT)).apply_symm_apply m

theorem evalMor_comp_evalInv (T M : Rep.{u} k G) (hT : Module.finrank k T = 1) :
    evalMor T M ≫ evalInv T M hT = 𝟙 _ := by
  ext x
  exact (LinearEquiv.ofBijective (evalMor T M).hom.toLinearMap
    (evalMor_bijective T M hT)).symm_apply_apply x

end Eval

section Descent

variable {k G : Type u} [Field k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (P : OpenSubgroup G) [(P : Subgroup G).Normal] (T M : Rep.{u} k G)
  [IsDiscreteRep T] [IsDiscreteRep M]
  (hT : ∀ (g : (P : Subgroup G)) (t : T), T.ρ g t = t)
  (hM : ∀ (g : (P : Subgroup G)) (m : M), M.ρ g m = m)


omit [IsTopologicalGroup G] [CompactSpace G] [(P : Subgroup G).Normal] [IsDiscreteRep T]
  [IsDiscreteRep M] in
include hT hM in
theorem homRep_ρ_of_mem (g : (P : Subgroup G)) (f : homRep T M) : (homRep T M).ρ g f = f := by
  apply LinearMap.ext
  intro t
  change M.ρ g (f (T.ρ (g : G)⁻¹ t)) = f t
  rw [hM, show ((g : G)⁻¹) = ((g⁻¹ : (P : Subgroup G)) : G) from rfl, hT]


omit [CompactSpace G] [(P : Subgroup G).Normal] [IsDiscreteRep T] [IsDiscreteRep M] in
include hT hM in
theorem isDiscreteRep_homRep : IsDiscreteRep (homRep T M) :=
  ⟨fun f => Subgroup.isOpen_mono (H₁ := (P : Subgroup G))
    (fun g hg => homRep_ρ_of_mem P T M hT hM ⟨g, hg⟩ f) P.isOpen⟩

theorem bijective_nsmul_of_ne_zero {V : Type*} [AddCommGroup V] [Module k V] {m : ℕ}
    (hm : (m : k) ≠ 0) : Function.Bijective fun v : V => m • v := by
  have h : (fun v : V => m • v) = fun v => (m : k) • v := funext fun v => (Nat.cast_smul_eq_nsmul k m v).symm
  rw [h]
  refine ⟨fun v w hvw => ?_, fun v => ⟨(m : k)⁻¹ • v, by simp [smul_smul, mul_inv_cancel₀ hm]⟩⟩
  have := congrArg (fun x => (m : k)⁻¹ • x) hvw
  simpa [smul_smul, inv_mul_cancel₀ hm] using this

variable [Module.Finite k M] (hTr : Module.finrank k T = 1)
  (hP : ((P : Subgroup G).index : k) ≠ 0)

noncomputable def coprimeTwistEquiv (n : ℕ) :
    haveI := isDiscreteRep_homRep P T M hT hM
    cohomology M n ≃ₗ[k]
      ((cohomologyConjRep T (P : Subgroup G) n).tprod
        (quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM))).invariants :=
  haveI := isDiscreteRep_homRep P T M hT hM
  haveI : Module.Finite k T := Module.finite_of_finrank_eq_succ hTr
  haveI : Module.Finite k (homRep T M) := inferInstanceAs (Module.Finite k (T →ₗ[k] M))
  (LinearEquiv.ofLinearMap (cohomologyMap (evalInv T M hTr) n).hom (cohomologyMap (evalMor T M) n).hom
      (by
        rw [← ModuleCat.hom_comp, ← cohomologyMap_comp, evalMor_comp_evalInv, cohomologyMap_id]
        rfl)
      (by
        rw [← ModuleCat.hom_comp, ← cohomologyMap_comp, evalInv_comp_evalMor, cohomologyMap_id]
        rfl)) ≪≫ₗ
    coprimeDescentEquiv P (T ⊗ homRep T M) (bijective_nsmul_of_ne_zero hP) n ≪≫ₗ
    (twistInvariantsEquiv (P : Subgroup G) T (homRep T M) (homRep_ρ_of_mem P T M hT hM) n).symm


include hTr hP in
theorem finrank_cohomology_eq_finrank_invariants (n : ℕ) :
    Module.finrank k (cohomology M n) = Module.finrank k
      ((cohomologyConjRep T (P : Subgroup G) n).tprod
        (quotientRep (P : Subgroup G) (homRep T M) (homRep_ρ_of_mem P T M hT hM))).invariants :=
  (coprimeTwistEquiv P T M hT hM hTr hP n).finrank_eq

end Descent

end GroundTheory.ProfCoh
