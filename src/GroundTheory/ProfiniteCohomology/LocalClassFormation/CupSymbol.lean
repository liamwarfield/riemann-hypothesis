module

public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolUnramified
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolNorm
public import GroundTheory.LocalFields.LocalArtinBaseChange

@[expose] public section

section -- merged from GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbolPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel
open GroundTheory.LocalField.Abstract GroundTheory.LocalField.Abstract.ProfiniteInteger

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

section Top

variable (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem brauerInvZ_eq_inv_top (x : cohomology (galUnitsZ K Ω) 2) :
    brauerInvZ K Ω x = (localClassFormationZ K Ω).inv ⊤
      ((cohomologyRes (galUnitsZ K Ω) ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) 2).hom x) := by
  obtain ⟨y, rfl⟩ := (cohomologyULiftIntAddEquiv (galUnits.{0} K Ω) 2).surjective x
  rw [brauerInvZ_cohomologyULiftIntAddEquiv, localClassFormationZ_inv]
  have e := cohomologyULiftIntAddEquiv_cohomologyMapAlong (galUnits.{0} K Ω)
    (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))).subtype (continuous_subgroup_subtype _)
    (𝟙 (Rep.res (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))).subtype (galUnits.{0} K Ω)))
    (𝟙 (Rep.res (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))).subtype (galUnitsZ K Ω)))
    (fun _ => rfl) 2 y
  refine Eq.trans ?_ (congrArg (localInv K Ω ⊤)
    ((congrArg (cohomologyULiftIntAddEquiv (Rep.res (((⊤ : OpenSubgroup Gal(Ω/K)) :
      Subgroup Gal(Ω/K))).subtype (galUnits.{0} K Ω)) 2).symm e.symm).trans
      (AddEquiv.symm_apply_apply _ _))).symm
  rw [localInv_apply]
  have : IsSepClosure (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K _ Ω⟩
  have : IsGalois (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω :=
    IsGalois.tower_top_of_isGalois K _ Ω
  have hres : (openCohomologyIso (⊤ : OpenSubgroup Gal(Ω/K)) 2).hom.hom
      ((cohomologyMapAlong (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))).subtype
        (continuous_subgroup_subtype _) (𝟙 _) 2).hom y) =
      (brauerRes K (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) Ω).hom y := by
    rw [openCohomologyIso_hom, ← ModuleCat.comp_apply, ← cohomologyMapAlong_comp, brauerRes_eq]
    congr 1
  have hrank : Module.finrank K (fixedField ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) = 1 := by
    rw [← index_openSubgroup]
    exact Subgroup.index_top
  rw [hres, brauerInv_brauerRes, hrank, one_smul]

end Top

section Subgroups

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]


omit [IsSepClosure K Ω] in
instance isDiscreteRep_res_galUnitsZ (S : Subgroup Gal(Ω/K)) :
    IsDiscreteRep (Rep.res S.subtype (galUnitsZ K Ω)) :=
  isDiscreteRep_res_subtype _ _

def fixedToInvariants (H : Subgroup Gal(Ω/K)) (u : Abstract.fixedModule Ωˣ H) :
    (Rep.res H.subtype (galUnitsZ K Ω)).ρ.invariants :=
  ⟨Additive.ofMul (u : Ωˣ), fun h => by
    apply Additive.toMul.injective
    apply Units.ext
    exact (coe_galUnitsHom_apply K Ω (h : Gal(Ω/K)) _).trans
      ((mem_fixedModule_units_iff' H (u : Ωˣ)).1 u.2 h h.2)⟩

omit [IsSepClosure K Ω] in
theorem fixedToInvariants_mul (H : Subgroup Gal(Ω/K)) (u v : Abstract.fixedModule Ωˣ H) :
    fixedToInvariants H (u * v) = fixedToInvariants H u + fixedToInvariants H v :=
  rfl

theorem fixedToInvariants_norm (S : OpenSubgroup Gal(Ω/K)) (x : Abstract.fixedModule Ωˣ (S : Subgroup Gal(Ω/K))) :
    fixedToInvariants ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))
        (Abstract.norm Ωˣ ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) (S : Subgroup Gal(Ω/K)) x) =
      invariantsNormLE (galUnitsZ K Ω) (le_top : S ≤ ⊤) (fixedToInvariants (S : Subgroup Gal(Ω/K)) x) := by
  classical
  apply Subtype.ext
  rw [coe_invariantsNormLE]
  change Additive.ofMul (Abstract.normFun Ωˣ _ _ x) = _
  let _ := Fintype.ofFinite (((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) ⧸
    (S : Subgroup Gal(Ω/K)).subgroupOf ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)))
  rw [Abstract.normFun, finprod_eq_prod_of_fintype, ofMul_prod]
  refine Finset.sum_congr rfl fun c _ => ?_
  conv_lhs => rw [← QuotientGroup.out_eq' c]
  rw [Abstract.cosetSMul_mk]
  apply Additive.toMul.injective
  apply Units.ext
  exact (coe_galUnitsHom_apply K Ω _ _).symm

end Subgroups

section Transport

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem ord_eq_of_eq {E₁ E₂ : IntermediateField K Ω} [FiniteDimensional K E₁] [FiniteDimensional K E₂]
    (h : E₁ = E₂) (y : Ω) (h₁ : y ∈ E₁) (h₂ : y ∈ E₂) :
    ord (⟨y, h₁⟩ : E₁) = ord (⟨y, h₂⟩ : E₂) := by
  subst h
  rfl

theorem unramifiedDegree_eq_of_eq {E₁ E₂ : IntermediateField K Ω} [FiniteDimensional K E₁]
    [FiniteDimensional K E₂] (h : E₁ = E₂) (g₁ : Gal(Ω/E₁)) (g₂ : Gal(Ω/E₂)) (hg : ∀ y, g₁ y = g₂ y) :
    unramifiedDegree E₁ Ω g₁ = unramifiedDegree E₂ Ω g₂ := by
  subst h
  congr 1
  exact AlgEquiv.ext hg

end Transport

section OpenSubgroup

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

noncomputable def galUnitsZOpenHom (U : OpenSubgroup Gal(Ω/K)) :
    Rep.res (galFixedFieldEquivOpen U).toMonoidHom
        (Rep.res (U : Subgroup Gal(Ω/K)).subtype (galUnitsZ K Ω)) ⟶
      galUnitsZ (fixedField (U : Subgroup Gal(Ω/K))) Ω :=
  Rep.ofHom ⟨(AddMonoidHom.id (Additive Ωˣ)).toIntLinearMap, fun σ => by
    ext x
    rfl⟩

theorem galFixedFieldEquivOpen_symm_apply (U : OpenSubgroup Gal(Ω/K)) (σ : (U : Subgroup Gal(Ω/K)))
    (x : Ω) : ((galFixedFieldEquivOpen U).symm σ) x = (σ : Gal(Ω/K)) x := by
  conv_rhs => rw [← (galFixedFieldEquivOpen U).apply_symm_apply σ]
  rfl

end OpenSubgroup

section Prime

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem localClassFormationZ_inv_cupCharClassProf_of_prime (E : IntermediateField K Ω)
    [FiniteDimensional K E] (χ : Additive Gal(Ω/K) →ₜ+ QZ)
    (π : Abstract.fixedModule Ωˣ ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)))
    (hπ : (localClassFieldData K Ω).valuation (fixingOpenSubgroup E) π = Multiplicative.ofAdd 1)
    (σ : ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)))
    (hσ : (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) σ = Multiplicative.ofAdd 1)
    (hχ : ∀ g ∈ ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) ⊓
      (localClassFieldData K Ω).deg.ker, χ (Additive.ofMul g) = 0) :
    (localClassFormationZ K Ω).inv (fixingOpenSubgroup E)
      ((cupCharClassProf (Rep.res ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
          Subgroup Gal(Ω/K)).subtype (galUnitsZ K Ω))
        (contCharComp χ _ (continuous_subgroup_subtype _))).hom
          (fixedToInvariants _ π)) = χ (Additive.ofMul (σ : Gal(Ω/K))) := by
  have hSig : fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) = E := by
    rw [coe_fixingOpenSubgroup]
    exact InfiniteGalois.fixedField_fixingSubgroup E
  have hπmem : ((π : Ωˣ) : Ω) ∈
      fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) :=
    (mem_fixedField_iff _ _).2 fun g hg => (mem_fixedModule_units_iff' _ _).1 π.2 g hg
  let π' : (fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)))ˣ :=
    Units.mk0 ⟨_, hπmem⟩ (fun h => (π : Ωˣ).ne_zero (congrArg Subtype.val h))
  let χS : Additive Gal(Ω/fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
      Subgroup Gal(Ω/K))) →ₜ+ QZ :=
    contCharComp χ (AlgEquiv.restrictScalarsHom K) (continuous_restrictScalarsHom_of_tower _ _ _)
  let σ' := (galFixedFieldEquivOpen (fixingOpenSubgroup E)).symm σ

  have hcup : (cohomologyMapAlong (galFixedFieldEquivOpen (fixingOpenSubgroup E)).toMonoidHom
      (continuous_galFixedFieldEquivOpen _) (galUnitsZOpenHom (fixingOpenSubgroup E)) 2).hom
      ((cupCharClassProf (Rep.res ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
          Subgroup Gal(Ω/K)).subtype (galUnitsZ K Ω))
        (contCharComp χ _ (continuous_subgroup_subtype _))).hom (fixedToInvariants _ π)) =
      galCupClass _ Ω χS π' := by
    have hab : ((unitsInvariant _ Ω π' : (galUnitsZ _ Ω).ρ.invariants) : galUnitsZ _ Ω) =
        (galUnitsZOpenHom (fixingOpenSubgroup E)).hom (fixedToInvariants _ π : _) := by
      apply Additive.toMul.injective
      apply Units.ext
      rfl
    rw [cohomologyMapAlong_cupCharClassProf _ _ _ _ _ (unitsInvariant _ Ω π') hab]
    rfl
  have e := cohomologyULiftIntAddEquiv_cohomologyMapAlong
    (Rep.res ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)).subtype
      (galUnits.{0} K Ω))
    (galFixedFieldEquivOpen (fixingOpenSubgroup E)).toMonoidHom (continuous_galFixedFieldEquivOpen _)
    (galUnitsOpenHom (fixingOpenSubgroup E)) (galUnitsZOpenHom (fixingOpenSubgroup E))
    (fun _ => rfl) 2
  rw [localClassFormationZ_inv, localInv_apply, openCohomologyIso_hom,
    ← brauerInvZ_cohomologyULiftIntAddEquiv]
  refine (congrArg (brauerInvZ _ Ω) ((e _).trans ((congrArg _ (AddEquiv.apply_symm_apply _ _)).trans
    hcup))).trans ?_

  have hord : ord ((π' : fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
      Subgroup Gal(Ω/K)))) = 1 := by
    have h := valuation_fixingOpenSubgroup E π
    rw [hπ] at h
    have h' : ((ord ((unitsEquivFixingOpen K E π : Eˣ) : E) : ℤ) : ℤ̂) = ((1 : ℤ) : ℤ̂) := by
      rw [Int.cast_one]
      exact (Multiplicative.ofAdd.injective h).symm
    rw [← Int.cast_injective h']
    exact ord_eq_of_eq hSig _ _ _
  have hσ' : unramifiedDegree _ Ω σ' = Multiplicative.ofAdd 1 := by
    rw [← hσ, relDeg_fixingOpenSubgroup E σ]
    exact unramifiedDegree_eq_of_eq hSig _ _ (fun y => galFixedFieldEquivOpen_symm_apply _ σ y)
  have hψ : ∀ g ∈ (unramifiedDegree (fixedField ((fixingOpenSubgroup E : OpenSubgroup Gal(Ω/K)) :
      Subgroup Gal(Ω/K))) Ω).ker, χS (Additive.ofMul g) = 0 := by
    intro g hg
    set g₀ := galFixedFieldEquivOpen (fixingOpenSubgroup E) g
    have h1 : (localClassFieldData K Ω).relDeg (fixingOpenSubgroup E) g₀ = 1 := by
      rw [relDeg_fixingOpenSubgroup E g₀]
      refine (unramifiedDegree_eq_of_eq hSig.symm _ g (fun y => rfl)).trans hg
    rw [ClassFieldData.relDeg_eq_iff, one_pow] at h1
    exact hχ (g₀ : Gal(Ω/K)) ⟨g₀.2, h1⟩
  rw [brauerInvZ_galCupClass_of_unramified χS hψ hσ' π', hord, one_smul]
  change χ (Additive.ofMul (AlgEquiv.restrictScalarsHom K σ')) = _
  congr 2
  exact AlgEquiv.ext fun y => galFixedFieldEquivOpen_symm_apply _ σ y

end Prime

end GroundTheory.ProfCoh
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel
open GroundTheory.LocalField.Abstract

attribute [local instance 2000] Rep.hV2 Submodule.module Submodule.Quotient.module

section Zero

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cupCharClassProf_zero (A : Rep ℤ G) [IsDiscreteRep A] (a : A.ρ.invariants) :
    (cupCharClassProf A 0).hom a = 0 := by
  have h0 : charClassProf (0 : Additive G →ₜ+ QZ) = 0 := by
    unfold charClassProf
    rw [map_zero]
    exact map_zero _
  rw [cupCharClassProf, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp,
    LinearMap.comp_apply, cupRightProf_apply, h0, map_zero, map_zero]

end Zero

section Main

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem localClassFormationZ_inv_cupCharClassProf_of_prime' (S : OpenSubgroup Gal(Ω/K))
    (χ : Additive Gal(Ω/K) →ₜ+ QZ) (π : Abstract.fixedModule Ωˣ (S : Subgroup Gal(Ω/K)))
    (hπ : (localClassFieldData K Ω).valuation S π = Multiplicative.ofAdd 1)
    (σ : (S : Subgroup Gal(Ω/K)))
    (hσ : (localClassFieldData K Ω).relDeg S σ = Multiplicative.ofAdd 1)
    (hχ : ∀ g ∈ (S : Subgroup Gal(Ω/K)) ⊓ (localClassFieldData K Ω).deg.ker, χ (Additive.ofMul g) = 0) :
    (localClassFormationZ K Ω).inv S
      ((cupCharClassProf (Rep.res (S : Subgroup Gal(Ω/K)).subtype (galUnitsZ K Ω))
        (contCharComp χ _ (continuous_subgroup_subtype _))).hom (fixedToInvariants _ π)) =
      χ (Additive.ofMul (σ : Gal(Ω/K))) := by
  obtain ⟨E, hE, rfl⟩ : ∃ E : IntermediateField K Ω, ∃ _ : FiniteDimensional K E, fixingOpenSubgroup E = S :=
    ⟨fixedField (S : Subgroup Gal(Ω/K)), inferInstance,
      OpenSubgroup.ext fun x => by
        change x ∈ (fixedField (S : Subgroup Gal(Ω/K))).fixingSubgroup ↔ x ∈ (S : Subgroup Gal(Ω/K))
        rw [fixingSubgroup_fixedField_openSubgroup]⟩
  exact localClassFormationZ_inv_cupCharClassProf_of_prime E χ π hπ σ hσ hχ

end Main

section Reciprocity

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem brauerInvZ_galCupClass (χ : Additive Gal(Ω/K) →ₜ+ QZ) (a : Kˣ) (g : Gal(Ω/K))
    (hg : ∀ (y : Ω) (hy : y ∈ maximalAbelianExtension K Ω),
      g y = (localArtinMap K Ω a ⟨y, hy⟩ : Ω)) :
    brauerInvZ K Ω (galCupClass K Ω χ a) = χ (Additive.ofMul g) := by
  have := isDiscreteModule_units (K := K) (Ω := Ω)
  have hax := classFieldAxiom_units K Ω

  let U := charKerOpen χ
  let M : IntermediateField K Ω := fixedField (U : Subgroup Gal(Ω/K))
  have : FiniteDimensional K M :=
    inferInstanceAs (FiniteDimensional K (fixedFiniteGalois U).toIntermediateField)
  have : IsGalois K M := inferInstanceAs (IsGalois K (fixedFiniteGalois U).toIntermediateField)
  have hMU : M.fixingSubgroup = (U : Subgroup Gal(Ω/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨(U : Subgroup Gal(Ω/K)), U.toOpenSubgroup.isClosed⟩
  have hker : ∀ x : Gal(Ω/K), x ∈ M.fixingSubgroup ↔ χ (Additive.ofMul x) = 0 := fun x => by
    rw [hMU]
    change x ∈ charKer (charAdd χ) ↔ _
    rw [mem_charKer]
    exact ⟨fun h => QZ.toAddCircle.injective (h.trans (map_zero _).symm),
      fun h => (congrArg QZ.toAddCircle h).trans (map_zero _)⟩
  have : IsMulCommutative (M ≃ₐ[K] M) := ⟨⟨fun τ₁ τ₂ => by
    obtain ⟨g₁, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₁
    obtain ⟨g₂, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (E := Ω) τ₂
    rw [← map_mul, ← map_mul, ← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,
      IntermediateField.restrictNormalHom_ker, hker]
    simp only [mul_inv_rev, ofMul_mul, ofMul_inv, map_add (f := _), map_neg]
    abel⟩⟩
  have : IsAbelianGalois K M := ⟨⟩
  let L := fixingOpenSubgroup M

  let a' := (baseUnitsEquiv (K := K) (Ω := Ω)).symm a
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective
    (((localClassFieldData K Ω).reciprocityAbEquiv (le_top : L ≤ ⊤) hax).symm
      (a' : tateZero Ωˣ _ (L : Subgroup Gal(Ω/K))))
  obtain ⟨s, hs⟩ := ClassFieldData.exists_frobeniusLift_mk (D := localClassFieldData K Ω)
    (le_top : L ≤ ⊤) q
  let S := s.field L le_top
  let π₀ := ((localClassFieldData K Ω).exists_prime S).choose
  have hπ₀ : (localClassFieldData K Ω).valuation S π₀ = Multiplicative.ofAdd 1 :=
    ((localClassFieldData K Ω).exists_prime S).choose_spec

  have hrec : (QuotientGroup.mk a' : tateZero Ωˣ ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))
      (L : Subgroup Gal(Ω/K))) = (QuotientGroup.mk (norm Ωˣ _ (S : Subgroup Gal(Ω/K)) π₀) :
        tateZero Ωˣ ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) (L : Subgroup Gal(Ω/K))) := by
    have h1 := (localClassFieldData K Ω).reciprocityAbEquiv_of (le_top : L ≤ ⊤) hax
      ((⟨s.elt, s.mem⟩ : ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))) :
        ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) ⧸
          (L : Subgroup Gal(Ω/K)).subgroupOf ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)))
    rw [ClassFieldData.reciprocity_mk, hs] at h1
    refine ((MulEquiv.apply_symm_apply
      ((localClassFieldData K Ω).reciprocityAbEquiv (le_top : L ≤ ⊤) hax) _).symm.trans ?_).trans h1
    exact congrArg _ hq.symm
  obtain ⟨b, hb⟩ := (QuotientGroup.eq (s := (norm Ωˣ ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K))
    (L : Subgroup Gal(Ω/K))).range)).1 hrec
  have hdec : a' = norm Ωˣ ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) (S : Subgroup Gal(Ω/K)) π₀ *
      norm Ωˣ ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)) (L : Subgroup Gal(Ω/K)) b⁻¹ := by
    rw [map_inv, hb]
    group

  have hab : ((fixedToInvariants _ a' : Rep.res ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)).subtype
      (galUnitsZ K Ω)) : Additive Ωˣ) =
        ((unitsInvariant K Ω a : (galUnitsZ K Ω).ρ.invariants) : Additive Ωˣ) := by
    apply Additive.toMul.injective
    apply Units.ext
    change ((a' : Ωˣ) : Ω) = algebraMap K Ω a
    rw [← algebraMap_baseUnitsEquiv, MulEquiv.apply_symm_apply]
  have hres := cohomologyMapAlong_cupCharClassProf
    ((⊤ : OpenSubgroup Gal(Ω/K)) : Subgroup Gal(Ω/K)).subtype (continuous_subgroup_subtype _)
    (𝟙 _) χ (unitsInvariant K Ω a) (fixedToInvariants _ a') hab
  have hL0 : contCharComp χ (L : Subgroup Gal(Ω/K)).subtype (continuous_subgroup_subtype _) = 0 := by
    ext x
    exact (hker ((Additive.toMul x : (L : Subgroup Gal(Ω/K))) : Gal(Ω/K))).1 (Additive.toMul x).2
  have hχS : ∀ x ∈ (S : Subgroup Gal(Ω/K)) ⊓ (localClassFieldData K Ω).deg.ker,
      χ (Additive.ofMul x) = 0 := fun x hx => by
    rw [ClassFieldData.FrobeniusLift.field_inf_ker] at hx
    exact (hker x).1 hx.1
  rw [brauerInvZ_eq_inv_top, cohomologyRes_eq]
  change (localClassFormationZ K Ω).inv ⊤ ((cohomologyMapAlong _ _ (𝟙 _) 2).hom
    ((cupCharClassProf (galUnitsZ K Ω) χ).hom (unitsInvariant K Ω a))) = _
  rw [hres, hdec, fixedToInvariants_mul, map_add (f := _), map_add (f := _), fixedToInvariants_norm,
    fixedToInvariants_norm, ClassFormation.inv_cupCharClassProf_invariantsNormLE,
    ClassFormation.inv_cupCharClassProf_invariantsNormLE, hL0, cupCharClassProf_zero, map_zero,
    add_zero, localClassFormationZ_inv_cupCharClassProf_of_prime' S χ π₀ hπ₀
      ⟨s.elt, s.elt_mem_field le_top⟩ (s.relDeg_field le_top) hχS]

  have hsym : AlgEquiv.restrictNormalHom M s.elt =
      restrictAb M (le_maximalAbelianExtension M) (localArtinMap K Ω a) := by
    apply (bijective_abelianizationOf M).1
    rw [restrictAb_localArtinMap, of_localReciprocityAbelian_symm,
      show a = baseUnitsEquiv a' from (MulEquiv.apply_symm_apply _ a).symm,
      localReciprocity_symm_mk_baseUnitsEquiv, ← hq, ← hs]
    rfl
  have hgy : ∀ y ∈ M, g y = s.elt y := fun y hy => by
    rw [hg y (le_maximalAbelianExtension M hy)]
    have e := restrictAb_apply M (le_maximalAbelianExtension M) (localArtinMap K Ω a) ⟨y, hy⟩
    rw [← hsym] at e
    rw [← e]
    exact AlgEquiv.restrictNormal_commutes s.elt M ⟨y, hy⟩
  have hmem : g⁻¹ * s.elt ∈ M.fixingSubgroup := (mem_fixingSubgroup_iff _ _).2 fun y hy => by
    rw [AlgEquiv.mul_apply, ← hgy y hy]
    exact g.symm_apply_apply y
  have e := (hker _).1 hmem
  rw [ofMul_mul, map_add (f := _), ofMul_inv, map_neg, neg_add_eq_zero] at e
  exact e.symm

end Reciprocity

section Corollaries

variable {K Ω : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω] [ValuativeExtension K Ω]

theorem brauerInvZ_galCupClass_liftNormal (χ : Additive Gal(Ω/K) →ₜ+ QZ) (a : Kˣ) :
    brauerInvZ K Ω (galCupClass K Ω χ a) =
      χ (Additive.ofMul ((localArtinMap K Ω a).liftNormal Ω)) :=
  brauerInvZ_galCupClass χ a _ fun y hy =>
    AlgEquiv.liftNormal_commutes (localArtinMap K Ω a) Ω ⟨y, hy⟩

end Corollaries

end GroundTheory.ProfCoh
