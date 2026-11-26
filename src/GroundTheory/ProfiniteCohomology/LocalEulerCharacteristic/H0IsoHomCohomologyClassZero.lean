module

public import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.ConjAction
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
public import GroundTheory.ProfiniteCohomology.Shapiro

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.H0IsoHomCohomologyClassZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section MapAlong

theorem H0Iso_hom_cohomology_class_zero (A : Rep.{u} k G) [IsDiscreteRep A] (z : cocycles A 0) :
    (((H0Iso A).hom.hom (cohomologyπ A 0 z) : A.ρ.invariants) : A) =
      cochainOf (A := A) (cocycleι (A := A) (p := 0) z) Fin.elim0 := by
  have h1 : (CochainComplex.isoHomologyπ₀ (cochainsComplex A)).inv.hom (cohomologyπ A 0 z) = z := by
    exact congrArg (fun φ => φ.hom z) (CochainComplex.isoHomologyπ₀ (cochainsComplex A)).hom_inv_id
  have h2 := congrArg (fun φ => φ.hom z) (cocyclesIso₀_hom_comp_f A)
  change (shortComplexH0 A).f.hom ((cocyclesIso₀ A).hom.hom z) =
    cocycleι (A := A) (p := 0) z at h2
  change (((cocyclesIso₀ A).hom.hom ((CochainComplex.isoHomologyπ₀ (cochainsComplex A)).inv.hom
    (cohomologyπ A 0 z)) : A.ρ.invariants) : A) = _
  rw [h1, ← h2]
  rfl

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {A : Rep.{u} k G} {B : Rep.{u} k H} [IsDiscreteRep A] [IsDiscreteRep B] (φ : H →* G)
  (hφ : Continuous φ) (f : Rep.res φ A ⟶ B)

theorem H0Iso_hom_cohomologyMapAlong (x : cohomology A 0) :
    (((H0Iso B).hom.hom ((cohomologyMapAlong φ hφ f 0).hom x) : B.ρ.invariants) : B) =
      f.hom (((H0Iso A).hom.hom x : A.ρ.invariants) : A) := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective A 0 x
  rw [cohomologyMapAlong_cohomologyπ, H0Iso_hom_cohomology_class_zero, H0Iso_hom_cohomology_class_zero,
    cochainOf_cocycleι_cocyclesMapAlong]
  change f.hom (cochainOf (A := A) (cocycleι (A := A) (p := 0) z) (⇑φ ∘ Fin.elim0)) = _
  rw [Subsingleton.elim (⇑φ ∘ Fin.elim0) Fin.elim0]

end MapAlong

section Conj

variable (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G) [N.Normal]

def invariantsConj (g : G) : (Rep.res N.subtype A).ρ.invariants →ₗ[k] (Rep.res N.subtype A).ρ.invariants where
  toFun a := ⟨A.ρ g a, fun m => by
    have hm : g⁻¹ * (m : G) * g ∈ N := by
      simpa using ‹N.Normal›.conj_mem _ m.2 g⁻¹
    change A.ρ m (A.ρ g a) = A.ρ g a
    have e : (m : G) * g = g * (g⁻¹ * m * g) := by group
    rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply]
    congr 1
    exact a.2 ⟨_, hm⟩⟩
  map_add' a b := Subtype.ext (map_add _ _ _)
  map_smul' c a := Subtype.ext (map_smul _ _ _)


theorem H0Iso_hom_cohomologyConj (g : G) (x : cohomology (Rep.res N.subtype A) 0) :
    (H0Iso (Rep.res N.subtype A)).hom.hom ((cohomologyConj A N 0 g).hom x) =
      invariantsConj A N g ((H0Iso (Rep.res N.subtype A)).hom.hom x) :=
  Subtype.ext (H0Iso_hom_cohomologyMapAlong _ _ _ x)

theorem cohomologyConj_H0Iso_inv (g : G) (a : (Rep.res N.subtype A).ρ.invariants) :
    (cohomologyConj A N 0 g).hom ((H0Iso (Rep.res N.subtype A)).inv.hom a) =
      (H0Iso (Rep.res N.subtype A)).inv.hom (invariantsConj A N g a) := by
  have h := H0Iso_hom_cohomologyConj A N g ((H0Iso (Rep.res N.subtype A)).inv.hom a)
  rw [H0Iso_hom_inv_apply] at h
  rw [← h, H0Iso_inv_hom_apply]

theorem δ_H0Iso_inv_invariantsConj {S : ShortComplex (Rep.{u} k G)} [IsDiscreteRep S.X₁]
    [IsDiscreteRep S.X₂] [IsDiscreteRep S.X₃] (hS : S.ShortExact) (g : G)
    (a : (Rep.res N.subtype S.X₃).ρ.invariants) :
    (δ (shortExact_map_res N hS) 0 1 rfl).hom
        ((H0Iso (Rep.res N.subtype S.X₃)).inv.hom (invariantsConj S.X₃ N g a)) =
      (cohomologyConj S.X₁ N 1 g).hom
        ((δ (shortExact_map_res N hS) 0 1 rfl).hom ((H0Iso (Rep.res N.subtype S.X₃)).inv.hom a)) := by
  rw [← cohomologyConj_H0Iso_inv]
  exact (congrArg (fun φ => φ.hom ((H0Iso (Rep.res N.subtype S.X₃)).inv.hom a))
    (δ_comp_cohomologyConj N hS 0 1 rfl g)).symm

end Conj

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Descent
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

universe u

section Nsmul

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

theorem bijective_nsmul_cohomology (B : Rep.{u} k Γ) [IsDiscreteRep B] (m : ℕ)
    (hB : Function.Bijective fun b : B => m • b) (n : ℕ) :
    Function.Bijective fun x : cohomology B n => m • x := by
  let L : B →ₗ[k] B := m • LinearMap.id
  let e : B ≃ₗ[k] B := LinearEquiv.ofBijective L hB
  have he : ∀ b : B, e b = m • b := fun _ => rfl
  let φ : B ⟶ B := Rep.ofHom ⟨e.symm.toLinearMap, fun g => by
    ext b
    apply e.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [he, ← map_nsmul, ← he, LinearEquiv.apply_symm_apply]⟩
  have h1 : (m • 𝟙 B) ≫ φ = 𝟙 B := by
    ext b
    change e.symm (m • b) = b
    rw [← he, LinearEquiv.symm_apply_apply]
  have h2 : φ ≫ (m • 𝟙 B) = 𝟙 B := by
    ext b
    change m • e.symm b = b
    rw [← he, LinearEquiv.apply_symm_apply]
  have hf : (fun x : cohomology B n => m • x) = (cohomologyMap (m • 𝟙 B) n).hom := by
    funext x
    rw [cohomologyMap_nsmul_id_apply]
  rw [hf]
  refine Function.bijective_iff_has_inverse.2 ⟨(cohomologyMap φ n).hom, fun x => ?_, fun x => ?_⟩
  · rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, h1, cohomologyMap_id]
    rfl
  · rw [← ModuleCat.comp_apply, ← cohomologyMap_comp, h2, cohomologyMap_id]
    rfl

end Nsmul

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G) [(U : Subgroup G).Normal] (A : Rep.{u} k G)
  [IsDiscreteRep A]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

section ResCores

noncomputable def coindTraceTermMor (c : G ⧸ (U : Subgroup G)) :
    Rep.res (U : Subgroup G).subtype
        (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) ⟶
      Rep.res (U : Subgroup G).subtype A :=
  Rep.ofHom ⟨coindTraceTerm (U : Subgroup G) A c, fun u => by
    ext f
    induction c using QuotientGroup.induction_on with
    | H x =>
      change coindTraceTerm (U : Subgroup G) A (x : G ⧸ (U : Subgroup G))
          ((Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)).ρ u f) =
        A.ρ u (coindTraceTerm (U : Subgroup G) A (x : G ⧸ (U : Subgroup G)) f)
      rw [coindTraceTerm_apply, coindTraceTerm_apply]
      change A.ρ x (f.1 (x⁻¹ * u)) = A.ρ u (A.ρ x (f.1 x⁻¹))
      have hv : x⁻¹ * (u : G) * x ∈ (U : Subgroup G) := by
        simpa using ‹(U : Subgroup G).Normal›.conj_mem _ u.2 x⁻¹
      have e : x⁻¹ * (u : G) = (U : Subgroup G).subtype ⟨_, hv⟩ * x⁻¹ := by
        simp only [Subgroup.subtype_apply]
        group
      rw [e, f.2 ⟨_, hv⟩ x⁻¹]
      change A.ρ x (A.ρ (x⁻¹ * u * x) (f.1 x⁻¹)) = A.ρ u (A.ρ x (f.1 x⁻¹))
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group⟩


omit [IsDiscreteRep A] in
theorem resFunctor_map_coindTrace :
    (Rep.resFunctor (U : Subgroup G).subtype).map (coindTrace (U : Subgroup G) A) =
      ∑ c : G ⧸ (U : Subgroup G), coindTraceTermMor U A c := by
  ext f
  change (coindTrace (U : Subgroup G) A).hom f = (∑ c, coindTraceTermMor U A c).hom f
  rw [coindTrace_hom_apply, Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
  rfl

instance isDiscreteRep_resFunctor_obj_coind_res :
    IsDiscreteRep ((Rep.resFunctor (U : Subgroup G).subtype).obj
      (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))) :=
  isDiscreteRep_res_subtype _ _

theorem cohomologyRes_comp_cohomologyMap_coindTraceTermMor (n : ℕ) (x : G) :
    cohomologyRes (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A))
        (U : Subgroup G) n ≫ cohomologyMap (coindTraceTermMor U A (x : G ⧸ (U : Subgroup G))) n =
      shapiroMap U (Rep.res (U : Subgroup G).subtype A) n ≫ cohomologyConj A (U : Subgroup G) n x := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap]
  conv_lhs => rw [← Category.id_comp (cohomologyRes _ _ n), ← cohomologyInnerConj_eq_id n
    (Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)) x]
  rw [cohomologyRes, cohomologyInnerConj, shapiroMap, cohomologyConj, ← cohomologyMapAlong_comp,
    ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun f => ?_) n
  change coindTraceTerm (U : Subgroup G) A (x : G ⧸ (U : Subgroup G))
      ((Rep.coind (U : Subgroup G).subtype (Rep.res (U : Subgroup G).subtype A)).ρ x f) =
    A.ρ x (f.1 1)
  rw [coindTraceTerm_apply]
  change A.ρ x (f.1 (x⁻¹ * x)) = A.ρ x (f.1 1)
  rw [inv_mul_cancel]

theorem cohomologyMap_sum {Γ : Type u} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {B C : Rep.{u} k Γ} [IsDiscreteRep B] [IsDiscreteRep C] {ι : Type*} (s : Finset ι)
    (f : ι → (B ⟶ C)) (n : ℕ) :
    cohomologyMap (∑ i ∈ s, f i) n = ∑ i ∈ s, cohomologyMap (f i) n := by
  classical
  induction s using Finset.induction with
  | empty => simp [cohomologyMap_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, cohomologyMap_add, ih]

theorem cohomologyCores_comp_cohomologyRes (n : ℕ) :
    cohomologyCores U A n ≫ cohomologyRes A (U : Subgroup G) n =
      ∑ c : G ⧸ (U : Subgroup G), cohomologyConj A (U : Subgroup G) n c.out := by
  rw [cohomologyCores, Category.assoc, cohomologyMap_comp_cohomologyRes, resFunctor_map_coindTrace,
    cohomologyMap_sum, Preadditive.comp_sum, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [(QuotientGroup.out_eq' c).symm]
  rw [cohomologyRes_comp_cohomologyMap_coindTraceTermMor, IsIso.inv_hom_id_assoc]

theorem cohomologyRes_cohomologyCores_apply (n : ℕ)
    (x : cohomology (Rep.res (U : Subgroup G).subtype A) n) :
    (cohomologyRes A (U : Subgroup G) n).hom ((cohomologyCores U A n).hom x) =
      ∑ c : G ⧸ (U : Subgroup G), (cohomologyConj A (U : Subgroup G) n c.out).hom x := by
  have h := congrArg (fun f => f.hom x) (cohomologyCores_comp_cohomologyRes U A n)
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.comp_apply, LinearMap.sum_apply]
    using h

end ResCores

section Descent

variable (hA : Function.Bijective fun a : A => (U : Subgroup G).index • a)
include hA


omit [(U : Subgroup G).Normal] in
theorem cohomologyRes_injective_of_bijective (n : ℕ) :
    Function.Injective (cohomologyRes A (U : Subgroup G) n).hom := by
  intro x y h
  have hc : ∀ z : cohomology A n, (cohomologyCores U A n).hom ((cohomologyRes A (U : Subgroup G) n).hom z) =
      (U : Subgroup G).index • z := fun z => by
    rw [← ModuleCat.comp_apply, cohomologyRes_comp_cohomologyCores]
    rfl
  apply (bijective_nsmul_cohomology A _ hA n).1
  change (U : Subgroup G).index • x = (U : Subgroup G).index • y
  rw [← hc, ← hc, h]

theorem range_cohomologyRes_of_bijective (n : ℕ) :
    LinearMap.range (cohomologyRes A (U : Subgroup G) n).hom =
      cohomologyConjInvariants A (U : Subgroup G) n := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact cohomologyRes_apply_mem_cohomologyConjInvariants A _ n z
  · intro x hx
    have hAU : Function.Bijective fun a : Rep.res (U : Subgroup G).subtype A =>
        (U : Subgroup G).index • a := hA
    have hbij := bijective_nsmul_cohomology (Rep.res (U : Subgroup G).subtype A) _ hAU n
    obtain ⟨x', hx'⟩ := hbij.2 x
    simp only at hx'
    have hinv : ∀ g : G, (cohomologyConj A (U : Subgroup G) n g).hom x' = x' := fun g => by
      apply hbij.1
      simp only
      rw [← map_nsmul, hx']
      exact hx g
    refine ⟨(cohomologyCores U A n).hom x', ?_⟩
    rw [cohomologyRes_cohomologyCores_apply]
    simp only [hinv, Finset.sum_const, Finset.card_univ]
    rw [← hx', Subgroup.index_eq_card, Nat.card_eq_fintype_card]

noncomputable def coprimeDescentEquiv (n : ℕ) :
    cohomology A n ≃ₗ[k] cohomologyConjInvariants A (U : Subgroup G) n :=
  LinearEquiv.ofBijective
    ((cohomologyRes A (U : Subgroup G) n).hom.codRestrict _
      (cohomologyRes_apply_mem_cohomologyConjInvariants A _ n))
    ⟨fun x y h => cohomologyRes_injective_of_bijective U A hA n (congrArg Subtype.val h),
      fun x => by
        obtain ⟨z, hz⟩ := (range_cohomologyRes_of_bijective U A hA n).ge x.2
        exact ⟨z, Subtype.ext hz⟩⟩

end Descent

end GroundTheory.ProfCoh
end

section -- merged from GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Scalars
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

section Bridge

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G]

def cochainsAddEquiv {A : Rep.{u} k G} {A' : Rep.{u} k' G} (e : A ≃+ A') (n : ℕ) :
    locallyConstantCochains A n ≃+ locallyConstantCochains A' n where
  toFun x := ⟨fun g => e (x.1 g), x.2.comp e⟩
  invFun x := ⟨fun g => e.symm (x.1 g), x.2.comp e.symm⟩
  left_inv _ := Subtype.ext (funext fun _ => e.symm_apply_apply _)
  right_inv _ := Subtype.ext (funext fun _ => e.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add e _ _)

variable [IsTopologicalGroup G] {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsDiscreteRep A]
  [IsDiscreteRep A'] (e : A ≃+ A') (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))


omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A] [IsDiscreteRep A'] in
include he in
theorem addEquiv_inhomogeneousCochains_d (i : ℕ) (f : (Fin i → G) → A) (g : Fin (i + 1) → G) :
    e ((inhomogeneousCochains.d A i).hom f g) =
      (inhomogeneousCochains.d A' i).hom (fun h => e (f h)) g := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply, map_add (f := _), map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hk : ∀ (c : ℕ) (a : A), ((-1 : k) ^ c) • a = ((-1 : ℤ) ^ c) • a := fun c a => by
    rw [← Int.cast_smul_eq_zsmul k]
    push_cast
    rfl
  have hk' : ∀ (c : ℕ) (a : A'), ((-1 : k') ^ c) • a = ((-1 : ℤ) ^ c) • a := fun c a => by
    rw [← Int.cast_smul_eq_zsmul k']
    push_cast
    rfl
  rw [hk, hk', map_zsmul]


include he in
theorem cochainsAddEquiv_d (i j : ℕ) (x : (cochainsComplex A).X i) :
    cochainsAddEquiv e j (((cochainsComplex A).d i j).hom x) =
      ((cochainsComplex A').d i j).hom (cochainsAddEquiv e i x) := by
  rcases eq_or_ne (i + 1) j with rfl | hij
  · rw [cochainsComplex_d, cochainsComplex_d]
    apply Subtype.ext
    funext g
    exact addEquiv_inhomogeneousCochains_d e he i x.1 g
  · have h' : ¬ (ComplexShape.up ℕ).Rel i j := hij
    rw [HomologicalComplex.shape _ _ _ h', HomologicalComplex.shape _ _ _ h']
    exact map_zero _

noncomputable def cochainsAbIso (i : ℕ) :
    (forget₂ (ModuleCat.{u} k) Ab).obj ((cochainsComplex A).X i) ≅
      (forget₂ (ModuleCat.{u} k') Ab).obj ((cochainsComplex A').X i) :=
  (cochainsAddEquiv e i).toAddCommGrpIso

noncomputable def cochainsScAbIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj ((cochainsComplex A).sc n) ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj ((cochainsComplex A').sc n) :=
  ShortComplex.isoMk (cochainsAbIso e _) (cochainsAbIso e _) (cochainsAbIso e _)
    (by
      ext x
      exact (cochainsAddEquiv_d e he _ _ x).symm)
    (by
      ext x
      exact (cochainsAddEquiv_d e he _ _ x).symm)

end Bridge

section HomologyAb

variable {k k' : Type u} [CommRing k] [CommRing k']

noncomputable def homologyAbIsoOfAbIso {S₁ : ShortComplex (ModuleCat.{u} k)}
    {S₂ : ShortComplex (ModuleCat.{u} k')}
    (σ : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj S₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k) Ab).obj S₁ ≅
      (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k') Ab).obj S₂ :=
  ((ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k) Ab)).app S₁).symm ≪≫
    (ShortComplex.homologyFunctor Ab).mapIso σ ≪≫
    (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k') Ab)).app S₂

theorem homologyMap_comp_homologyAbIsoOfAbIso
    {S₁ T₁ : ShortComplex (ModuleCat.{u} k)} {S₂ T₂ : ShortComplex (ModuleCat.{u} k')}
    (φ₁ : S₁ ⟶ T₁) (φ₂ : S₂ ⟶ T₂)
    (σS : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj S₂)
    (σT : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj T₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj T₂)
    (h : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.map φ₁ ≫ σT.hom =
      σS.hom ≫ (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.map φ₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k) Ab).map φ₁ ≫
        (homologyAbIsoOfAbIso σT).hom =
      (homologyAbIsoOfAbIso σS).hom ≫
        (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k') Ab).map φ₂ := by
  have n1 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k) Ab)).inv.naturality φ₁
  have n2 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k') Ab)).hom.naturality φ₂
  have n3 : ((forget₂ (ModuleCat.{u} k) Ab).mapShortComplex ⋙
        ShortComplex.homologyFunctor Ab).map φ₁ ≫ (ShortComplex.homologyFunctor Ab).map σT.hom =
      (ShortComplex.homologyFunctor Ab).map σS.hom ≫
        ((forget₂ (ModuleCat.{u} k') Ab).mapShortComplex ⋙ ShortComplex.homologyFunctor Ab).map φ₂ := by
    rw [Functor.comp_map, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp, h]
  simp only [homologyAbIsoOfAbIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  slice_lhs 1 2 => rw [n1]
  slice_lhs 2 3 => rw [n3]
  slice_lhs 3 4 => rw [n2]

end HomologyAb

section Cohomology

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsDiscreteRep A]
  [IsDiscreteRep A'] (e : A ≃+ A') (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

noncomputable def cohomologyAddEquivOfEquiv (n : ℕ) : cohomology A n ≃+ cohomology A' n :=
  (homologyAbIsoOfAbIso (cochainsScAbIso e he n)).addCommGroupIsoToAddEquiv

theorem cohomologyAddEquivOfEquiv_mapAlong {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {B : Rep.{u} k H} {B' : Rep.{u} k' H}
    [IsDiscreteRep B] [IsDiscreteRep B'] (eB : B ≃+ B')
    (heB : ∀ (h : H) (b : B), eB (B.ρ h b) = B'.ρ h (eB b))
    (f : Rep.res φ A ⟶ B) (f' : Rep.res φ A' ⟶ B') (hf : ∀ a : A, eB (f.hom a) = f'.hom (e a))
    (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv eB heB n ((cohomologyMapAlong φ hφ f n).hom x) =
      (cohomologyMapAlong φ hφ f' n).hom (cohomologyAddEquivOfEquiv e he n x) := by
  have key := homologyMap_comp_homologyAbIsoOfAbIso
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (cochainsMapAlong φ hφ f))
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (cochainsMapAlong φ hφ f'))
    (cochainsScAbIso e he n) (cochainsScAbIso eB heB n) (by
      ext x <;> exact Subtype.ext (funext fun _ => hf _))
  exact congrArg (fun f => f.hom x) key

theorem cohomologyAddEquivOfEquiv_cohomologyConj (N : Subgroup G) [N.Normal] (n : ℕ) (g : G)
    (x : cohomology (Rep.res N.subtype A) n) :
    cohomologyAddEquivOfEquiv (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
        (fun s a => he s a) n ((cohomologyConj A N n g).hom x) =
      (cohomologyConj A' N n g).hom
        (cohomologyAddEquivOfEquiv (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
          (fun s a => he s a) n x) :=
  cohomologyAddEquivOfEquiv_mapAlong (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
    (fun s a => he s a) (GroundTheory.GroupCoh.conjHom N g) (continuous_conjHom N g)
    (B := Rep.res N.subtype A) (B' := Rep.res N.subtype A') e (fun s a => he s a)
    (GroundTheory.GroupCoh.conjMor A N g) (GroundTheory.GroupCoh.conjMor A' N g) (fun a => he g a) n x

end Cohomology

section ZMod

variable {G : Type} [Group G] (l : ℕ) (A : Rep.{0} (ULift.{0} ℤ) G)
  (hA : ∀ a : A, l • a = 0)

noncomputable def zmodRepOfTorsion : Rep.{0} (ZMod l) G :=
  letI : Module (ZMod l) A := AddCommGroup.zmodModule hA
  Rep.of (X := A)
    { toFun := fun g => (A.ρ g).toAddMonoidHom.toZModLinearMap l
      map_one' := by
        ext a
        simp
      map_mul' := fun g h => by
        ext a
        simp [Module.End.mul_apply] }

def zmodRepOfTorsionEquiv : A ≃+ zmodRepOfTorsion l A hA :=
  AddEquiv.refl A

variable [TopologicalSpace G]

instance isDiscreteRep_zmodRepOfTorsion [IsDiscreteRep A] :
    IsDiscreteRep (zmodRepOfTorsion l A hA) :=
  ⟨fun a => isOpen_stabilizer A a⟩

variable [IsTopologicalGroup G] [IsDiscreteRep A]

noncomputable def cohomologyZModEquiv (n : ℕ) :
    cohomology A n ≃+ cohomology (zmodRepOfTorsion l A hA) n :=
  cohomologyAddEquivOfEquiv (zmodRepOfTorsionEquiv l A hA) (fun _ _ => rfl) n

end ZMod

end GroundTheory.ProfCoh
end
