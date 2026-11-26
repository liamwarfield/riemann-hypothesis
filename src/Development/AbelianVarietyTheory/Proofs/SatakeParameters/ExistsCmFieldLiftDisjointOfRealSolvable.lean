module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedAtValueHeckeCharCompIdeleNorm
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianTotallyRealExtPrescribedCompletion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDecompositionGroupsCoverOpenQuotient
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDecompositionGroupsCoverOpenQuotient
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.DecCover

theorem main : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (N : Subgroup (G F Ω)), IsOpen (N : Set (G F Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T ∧ ∀ g : G F Ω, ∃ u ∈ T, ∃ A' : ValuationSubring Ω, IsPlaceOver A' u ∧ ∃ x ∈ Dec (F := F) A', ∃ n ∈ N, g = x * n := by
  intro Ω _ F _ _ _ _ v N hN
  classical
  have : IsGalois F Ω := {}
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hN N.one_mem
  have hcheb := fun g : G F Ω =>
    GlobalTheory.Published.cheb_holds F Ω U.toSubgroup U.isOpen U.isNormal' g {v}
  choose u hu _ _ B hB _ σ hσ hσU using hcheb
  have hmem : ∀ g : G F Ω, (σ g)⁻¹ * g ∈ N := by
    intro g
    apply hU
    have h1 := U.isNormal'.conj_mem _ (hσU g) (σ g)⁻¹
    have h2 : (σ g)⁻¹ * (σ g * g⁻¹) * (σ g)⁻¹⁻¹ = ((σ g)⁻¹ * g)⁻¹ := by group
    rw [h2] at h1
    have h3 := U.toSubgroup.inv_mem h1
    rw [inv_inv] at h3
    exact h3
  have hopen : ∀ g : G F Ω, IsOpen {h : G F Ω | (σ g)⁻¹ * h ∈ N} := fun g =>
    hN.preimage (continuous_const_mul _)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun g : G F Ω => {h : G F Ω | (σ g)⁻¹ * h ∈ N}) hopen
    (fun g _ => Set.mem_iUnion.2 ⟨g, hmem g⟩)
  refine ⟨t.image u, ?_, fun g => ?_⟩
  · intro hv
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hv
    exact hu i (by simp [hi])
  · obtain ⟨i, hi, hgi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ g))
    refine ⟨u i, Finset.mem_image_of_mem u hi, B i, hB i, σ i, (hσ i).1, (σ i)⁻¹ * g, hgi, ?_⟩
    group

end GlobalTheory.DecCover

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDecompositionGroupsCoverOpenQuotientStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_decompositionGroups_cover_openQuotient : ∀ (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] [IsAlgClosure F Ω] (v : HeightOneSpectrum (𝓞 F)) (N : Subgroup (G F Ω)), IsOpen (N : Set (G F Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 F)), v ∉ T ∧ ∀ g : G F Ω, ∃ u ∈ T, ∃ A' : ValuationSubring Ω, IsPlaceOver A' u ∧ ∃ x ∈ Dec (F := F) A', ∃ n ∈ N, g = x * n := by
  first | exact @GlobalTheory.DecCover.main | exact GlobalTheory.DecCover.main | (intros; apply GlobalTheory.DecCover.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvable
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.KLift

theorem isOpen_map_restrictScalars {K L Ω : Type} [Field K] [Field L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [FiniteDimensional K L]
    (N : Subgroup (Ω ≃ₐ[L] Ω)) (hN : IsOpen (N : Set (Ω ≃ₐ[L] Ω))) :
    IsOpen ((N.map (AlgEquiv.restrictScalarsHom K)) : Set (Ω ≃ₐ[K] Ω)) := by
  obtain ⟨E', hE', hsub⟩ := (krullTopology_mem_nhds_one_iff L Ω _).1 (hN.mem_nhds N.one_mem)
  haveI : FiniteDimensional K E' := Module.Finite.trans L E'
  haveI : FiniteDimensional K (E'.restrictScalars K) := this
  refine Subgroup.isOpen_mono ?_ (IntermediateField.fixingSubgroup_isOpen (E'.restrictScalars K))
  intro g hg
  have hfix : ∀ x ∈ E', g x = x := fun x hx =>
    (IntermediateField.mem_fixingSubgroup_iff _ g).1 hg x hx
  let g' : Ω ≃ₐ[L] Ω := { g.toRingEquiv with commutes' := fun l => hfix _ (E'.algebraMap_mem l) }
  refine ⟨g', hsub ?_, ?_⟩
  · exact (IntermediateField.mem_fixingSubgroup_iff E' g').2 hfix
  · ext x; rfl

end GlobalTheory.KLift


open GlobalTheory.KLift in
theorem GlobalTheory.KLift.exists_cm_lift : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), v ∉ T ∧ ∀ F₁ : IntermediateField (maximalRealSubfield E) Ω, FiniteDimensional (maximalRealSubfield E) F₁ → IsGalois (maximalRealSubfield E) F₁ → IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) → (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) → (∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := maximalRealSubfield E) A' ≤ F₁.fixingSubgroup) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g : G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z) ∧ ∀ z ∈ F₁, ∃ x ∈ maximalRealSubfield M, algebraMap M Ω x = z := by
  intro Ω _ E _ _ _ _ _ v N hN
  classical
  haveI hFE : Algebra.IsAlgebraic (maximalRealSubfield E) E := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsAlgebraic (maximalRealSubfield E) Ω :=
    Algebra.IsAlgebraic.trans (maximalRealSubfield E) E Ω
  haveI hcF : IsAlgClosure (maximalRealSubfield E) Ω := ⟨IsAlgClosure.isAlgClosed E, inferInstance⟩
  obtain ⟨T, hvT, hT⟩ := GlobalTheory.T.finite_decompositionGroups_cover_openQuotient Ω (maximalRealSubfield E) v
    (N.map (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))) (isOpen_map_restrictScalars N hN)
  refine ⟨T, hvT, ?_⟩
  intro F₁ hfd hgal hsolv hreal hdec
  have hre : ∀ z ∈ F₁, ∀ φ : Ω →+* ℂ, star (φ z) = φ z := by
    intro z hz φ
    have h := ComplexEmbedding.isReal_iff.1 (hreal (φ.comp F₁.val.toRingHom))
    have := RingHom.congr_fun h ⟨z, hz⟩
    rw [ComplexEmbedding.conjugate_coe_eq] at this
    simpa using this
  let M : IntermediateField E Ω := IntermediateField.adjoin E (F₁ : Set Ω)
  have hF₁M : ∀ z ∈ F₁, z ∈ M := fun z hz => IntermediateField.subset_adjoin E _ hz
  have hfix : ∀ g : G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z := by
    intro g
    constructor
    · intro h z hz; exact h ⟨z, hF₁M z hz⟩
    · intro h x
      have hle : M ≤ IntermediateField.fixedField (Subgroup.zpowers g) := by
        refine IntermediateField.adjoin_le_iff.2 ?_
        intro z hz
        rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
        intro f hf
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hf
        exact (MulAction.mem_fixedBy_zpowers_iff_mem_fixedBy (g := g)).2 (h z hz) k
      exact (IntermediateField.mem_fixedField_iff _ _).1 (hle x.2) g (Subgroup.mem_zpowers g)
  haveI : Normal (maximalRealSubfield E) F₁ := hgal.to_normal
  haveI : Normal E Ω := IsAlgClosure.normal E Ω
  haveI : Normal (maximalRealSubfield E) Ω := IsAlgClosure.normal _ Ω
  have hmap : ∀ σ : Ω →ₐ[E] Ω, ∀ z ∈ F₁, σ z ∈ F₁ := by
    intro σ z hz
    exact IntermediateField.normal_iff_forall_map_le.1 inferInstance
      (σ.restrictScalars (maximalRealSubfield E)) ((IntermediateField.mem_map _).2 ⟨z, hz, rfl⟩)
  haveI hMn : Normal E M := by
    refine IntermediateField.normal_iff_forall_map_le.2 fun σ => ?_
    show (IntermediateField.adjoin E (F₁ : Set Ω)).map σ ≤ IntermediateField.adjoin E (F₁ : Set Ω)
    rw [IntermediateField.adjoin_map]
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact hF₁M _ (hmap σ z hz)
  haveI hMfd : FiniteDimensional E M := by
    let b := Module.finBasis (maximalRealSubfield E) F₁
    let S : Set Ω := Set.range (fun i => ((b i : F₁) : Ω))
    haveI : Finite S := (Set.finite_range _).to_subtype
    have hint : ∀ x ∈ S, IsIntegral E x := fun x _ => Algebra.IsIntegral.isIntegral x
    haveI := IntermediateField.finiteDimensional_adjoin hint
    have hle : M ≤ IntermediateField.adjoin E S := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      intro z hz
      have hsum := b.sum_repr ⟨z, hz⟩
      have h2 := congrArg (fun y : F₁ => (y : Ω)) hsum
      simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h2
      have : z = ∑ i, algebraMap E Ω ((b.repr ⟨z, hz⟩ i : maximalRealSubfield E) : E) * ((b i : F₁) : Ω) := by
        refine h2.symm.trans (Finset.sum_congr rfl fun i _ => ?_)
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E Ω]
        rfl
      rw [SetLike.mem_coe, this]
      exact sum_mem fun i _ => mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).toRingHom.injective
  haveI : NumberField M := NumberField.of_module_finite E M
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) _⟩
  haveI : IsGalois E M := ⟨⟩
  have hCM : IsCMField M := (GlobalTheory.T.cm_subfields_compositum_closed Ω E).2.2 M (F₁ : Set Ω) (fun x hx φ => by
      have := hre x hx φ
      rw [Complex.star_def] at this
      exact Complex.conj_eq_iff_im.1 this) rfl
  haveI : Group.IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) := hsolv
  have hsolvM : IsSolvable (M ≃ₐ[E] M) := by
    let ψ : (Ω ≃ₐ[E] Ω) →* (M ≃ₐ[E] M) := AlgEquiv.restrictNormalHom M
    let φ : (Ω ≃ₐ[E] Ω) →* (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
      (AlgEquiv.restrictNormalHom F₁).comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E))
    have hψ : Function.Surjective ψ := AlgEquiv.restrictNormalHom_surjective Ω
    have hker : ψ.ker = φ.ker := by
      ext g
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      have e1 : ψ g = 1 ↔ ∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x := by
        simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply]
        refine forall_congr' fun x => ?_
        rw [← (algebraMap M Ω).injective.eq_iff]
        show algebraMap M Ω (AlgEquiv.restrictNormal g M x) = _ ↔ _
        rw [AlgEquiv.restrictNormal_commutes]
      have e2 : φ g = 1 ↔ ∀ z ∈ F₁, g z = z := by
        simp only [AlgEquiv.ext_iff, AlgEquiv.one_apply]
        constructor
        · intro h z hz
          have := congrArg (algebraMap F₁ Ω) (h ⟨z, hz⟩)
          rw [show φ g ⟨z, hz⟩ = AlgEquiv.restrictNormal (AlgEquiv.restrictScalarsHom _ g) F₁ ⟨z, hz⟩
            from rfl, AlgEquiv.restrictNormal_commutes] at this
          exact this
        · intro h y
          apply (algebraMap F₁ Ω).injective
          show algebraMap F₁ Ω (AlgEquiv.restrictNormal (AlgEquiv.restrictScalarsHom _ g) F₁ y) = _
          rw [AlgEquiv.restrictNormal_commutes]
          exact h y y.2
      rw [e1, e2, hfix]
    let ρ : (M ≃ₐ[E] M) →* (F₁ ≃ₐ[maximalRealSubfield E] F₁) :=
      (QuotientGroup.kerLift φ).comp ((QuotientGroup.quotientMulEquivOfEq hker).toMonoidHom.comp
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.toMonoidHom)
    have hinj : Function.Injective ρ :=
      (QuotientGroup.kerLift_injective φ).comp ((QuotientGroup.quotientMulEquivOfEq hker).injective.comp
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.injective)
    exact solvable_of_solvable_injective hinj
  refine ⟨M, inferInstance, inferInstance, hCM, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨inferInstance, hsolvM, ?_⟩, hfix, ?_⟩
  · intro g
    obtain ⟨u, hu, A', hA', x, hx, n', hn', hgx⟩ :=
      hT (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) g)
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hn'
    have hxF : ∀ z ∈ F₁, x z = z := fun z hz =>
      (IntermediateField.mem_fixingSubgroup_iff F₁ x).1 (hdec u hu A' hA' hx) z hz
    have hyx : AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (g * n⁻¹) = x := by
      rw [map_mul, map_inv, hgx, mul_inv_cancel_right]
    have hyM : ∀ m : M, (g * n⁻¹) (algebraMap M Ω m) = algebraMap M Ω m :=
      (hfix (g * n⁻¹)).2 fun z hz => (DFunLike.congr_fun hyx z).trans (hxF z hz)
    refine ⟨{ (g * n⁻¹) with commutes' := hyM }, n, hn, ?_⟩
    ext w
    show g w = (g * n⁻¹) (n w)
    simp
  · intro z hz
    refine ⟨⟨z, hF₁M z hz⟩, ?_, rfl⟩
    intro φ
    letI : Algebra M ℂ := φ.toAlgebra
    let ψ : Ω →ₐ[M] ℂ := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h1 : φ ⟨z, hF₁M z hz⟩ = ψ z := (ψ.commutes ⟨z, hF₁M z hz⟩).symm
    rw [h1]
    exact hre z hz ψ.toRingHom
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCmFieldLiftDisjointOfRealSolvableStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmField_lift_disjoint_of_real_solvable : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra E Ω] [IsAlgClosure E Ω] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))), ∀ N : Subgroup (G E Ω), IsOpen (N : Set (G E Ω)) → ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), v ∉ T ∧ ∀ F₁ : IntermediateField (maximalRealSubfield E) Ω, FiniteDimensional (maximalRealSubfield E) F₁ → IsGalois (maximalRealSubfield E) F₁ → IsSolvable (F₁ ≃ₐ[maximalRealSubfield E] F₁) → (∀ φ : F₁ →+* ℂ, ComplexEmbedding.IsReal φ) → (∀ u ∈ T, ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Dec (F := maximalRealSubfield E) A' ≤ F₁.fixingSubgroup) → ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (_ : Algebra M Ω) (_ : IsAlgClosure M Ω) (_ : Algebra E M) (_ : IsScalarTower E M Ω), SolvDisj M N ∧ (∀ g : G E Ω, (∀ x : M, g (algebraMap M Ω x) = algebraMap M Ω x) ↔ ∀ z ∈ F₁, g z = z) ∧ ∀ z ∈ F₁, ∃ x ∈ maximalRealSubfield M, algebraMap M Ω x = z := by
  first | exact @GlobalTheory.KLift.exists_cm_lift | exact GlobalTheory.KLift.exists_cm_lift | (intros; apply GlobalTheory.KLift.exists_cm_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianOverSubfield
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AbOverSubfield

theorem exists_place_between {F K Ω : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [Algebra F Ω] [IsScalarTower F K Ω]
    {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)} (hA : IsPlaceOver A v) :
    ∃ w : HeightOneSpectrum (𝓞 K), IsPlaceOver A w := by
  have hint : ∀ x : 𝓞 K, algebraMap K Ω (x : K) ∈ A := fun x => by
    have h : IsIntegral A (algebraMap K Ω (x : K)) :=
      (x.isIntegral_coe.map (algebraMap K Ω).toIntAlgHom).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
    rw [← hy]
    exact y.2
  let f : 𝓞 K →+* A := ((algebraMap K Ω).comp (algebraMap (𝓞 K) K)).codRestrict A hint
  let P : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal A).comap f
  have hP : ∀ x : 𝓞 K, A.valuation (algebraMap K Ω (x : K)) < 1 ↔ x ∈ P := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  have hu : v.asIdeal = P.comap (algebraMap (𝓞 F) (𝓞 K)) := by
    ext x
    rw [← hA x, Ideal.mem_comap, ← hP, IsScalarTower.algebraMap_apply F K Ω]
    rfl
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hu, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  exact ⟨⟨P, inferInstance, hne⟩, hP⟩

end GlobalTheory.AbOverSubfield

namespace GlobalTheory.AbOverSubfield

end GlobalTheory.AbOverSubfield
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutRepDefiniteUnitarySpannedBySplitComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutRepDefiniteUnitarySpannedBySplitComponent
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

noncomputable section

namespace GlobalTheory.Cong

theorem locU_conj_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (w : HeightOneSpectrum (𝓞 E))
    (y : UA E a) {x : UA E a} (hx : x ∈ locU a w) : y * x * y⁻¹ ∈ locU a w := by
  simp only [locU, finU, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, map_mul, map_inv] at hx ⊢
  obtain ⟨h1, h2⟩ := hx
  exact ⟨by simp [h1], fun u hu => by simp [h2 u hu]⟩

theorem exists_locU_mul_comm {E : Type} [Field E] [NumberField E] [IsCMField E] (a : ℕ)
    (w : HeightOneSpectrum (𝓞 E)) (hw : IsSplitAt w) (g : UA E a) :
    ∃ x ∈ locU a w, ∃ y : UA E a, g = x * y ∧ ∀ z ∈ locU a w, y * z = z * y := by
  have hb := (GlobalTheory.T.definiteUnitaryLocalComponent_splitPlace_homeomorph E a w hw).1
  obtain ⟨x, hx⟩ := hb.2 (cLoc w g)
  have hx' : cLoc w (x : UA E a) = cLoc w g := hx
  refine ⟨x, x.2, (x : UA E a)⁻¹ * g, by group, fun z hz => ?_⟩
  have hy : cLoc w ((x : UA E a)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hx', inv_mul_cancel]
  have hc := locU_conj_mem w ((x : UA E a)⁻¹ * g) hz
  have he : (⟨_, hc⟩ : locU a w) = ⟨z, hz⟩ := hb.1 (by
    change cLoc w (_ * z * _) = cLoc w z
    rw [map_mul, map_mul, map_inv, hy]; group)
  have he' := congrArg Subtype.val he
  simp only at he'
  calc (x : UA E a)⁻¹ * g * z = ((x : UA E a)⁻¹ * g * z * ((x : UA E a)⁻¹ * g)⁻¹) * ((x : UA E a)⁻¹ * g) := by group
    _ = z * ((x : UA E a)⁻¹ * g) := by rw [he']

theorem span_comp_of_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, φ ∈ ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 := by
  intro E _ _ _ a U hU w hw σ hσ φ hφ
  set S := ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
    f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 with hS
  have hSU : S ≤ U := iSup_le fun f => by
    rintro _ ⟨v, rfl⟩; exact f.2.1 v
  obtain ⟨-, f0, hf0, hf0U, hf0e⟩ := hσ
  have hS0 : S ≠ ⊥ := by
    intro h
    apply hf0
    ext v
    have : f0 v ∈ S := (le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
      f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) ⟨f0, hf0U, hf0e⟩) ⟨v, rfl⟩
    rw [h, Submodule.mem_bot] at this
    simp [this]

  have hloc : ∀ x : locU a w, ∀ ψ ∈ S, RU E a x ψ ∈ S := by
    intro x ψ hψ
    rw [hS] at hψ
    refine Submodule.iSup_induction _ (motive := fun ψ => RU E a x ψ ∈ S) hψ ?_ ?_ ?_
    · intro f ψ hψ
      obtain ⟨v, rfl⟩ := hψ
      rw [← f.2.2 x v]
      exact le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
        f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) f ⟨_, rfl⟩
    · simp
    · intro ψ₁ ψ₂ h₁ h₂; simpa only [map_add] using add_mem h₁ h₂

  have hcen : ∀ y : UA E a, (∀ z ∈ locU a w, y * z = z * y) → ∀ ψ ∈ S, RU E a y ψ ∈ S := by
    intro y hy ψ hψ
    rw [hS] at hψ
    refine Submodule.iSup_induction _ (motive := fun ψ => RU E a y ψ ∈ S) hψ ?_ ?_ ?_
    · intro f ψ hψ
      obtain ⟨v, rfl⟩ := hψ
      let f' : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
          f (σ.ρ (cLoc w x) v) = RU E a x (f v)} :=
        ⟨RU E a y ∘ₗ f.1, fun v => hU.stable y _ (f.2.1 v), fun x v => by
          simp only [LinearMap.comp_apply]
          rw [f.2.2 x v, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul, hy x x.2]⟩
      exact le_iSup (fun f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v,
        f (σ.ρ (cLoc w x) v) = RU E a x (f v)} => LinearMap.range f.1) f' ⟨v, rfl⟩
    · simp
    · intro ψ₁ ψ₂ h₁ h₂; simpa only [map_add] using add_mem h₁ h₂
  have hstab : ∀ g, ∀ ψ ∈ S, RU E a g ψ ∈ S := by
    intro g ψ hψ
    obtain ⟨x, hx, y, rfl, hy⟩ := exists_locU_mul_comm a w hw g
    rw [map_mul, mul_apply_eq_comp]
    exact hloc ⟨x, hx⟩ _ (hcen y hy ψ hψ)
  rcases hU.irred S hSU hstab with h | h
  · exact absurd h hS0
  · rw [h]; exact hφ

end GlobalTheory.Cong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutRepDefiniteUnitarySpannedBySplitComponentStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, φ ∈ ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 := by
  first | (exact @GlobalTheory.Cong.span_comp_of_split) | (exact GlobalTheory.Cong.span_comp_of_split) | (intros; apply GlobalTheory.Cong.span_comp_of_split  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryIntegralBelowPlaceCompactOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryIntegralBelowPlaceCompactOpen
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev

noncomputable section

namespace GlobalTheory.Cong.AdaptLev

open GlobalTheory.BCT.GlobLev GroundTheory.Automorphic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem finPart_mem_integral_iff (k : finU (E := E) (n := a)) :
    finPart E a k ∈ AdelicGLn.integralFiniteGL E a ↔ ∀ u, cLoc u k.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
  rw [AdelicGLn.mem_integralFiniteGL_iff, ← map_inv]
  simp only [mem_KGL_iff_val, ← map_inv, GroundTheory.Global.mem_integralFiniteAdeles]
  exact ⟨fun h u => ⟨fun i j => h.1 i j u, fun i j => h.2 i j u⟩,
    fun h => ⟨fun i j u => (h u).1 i j, fun i j u => (h u).2 i j⟩⟩

theorem isOpen_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsOpen (GlobalTheory.LFun.KGL w (n := a) : Set (GL (Fin a) (w.adicCompletion E))) := by
  have hK := GlobalTheory.SmGL.SphCompletion.KO_completion (F := E) w a
  have h : IsOpen (GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin a) : Set (GL (Fin a) (w.adicCompletion E))) :=
    GlobalTheory.SplitFlip.isOpen_KO
  rwa [hK] at h

theorem isClosed_KGL (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) :
    IsClosed (GlobalTheory.LFun.KGL w (n := a) : Set (GL (Fin a) (w.adicCompletion E))) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_KGL w a)

theorem mem_intU_iff_of_mem_locU {w : HeightOneSpectrum (𝓞 E)} {x : UA E a} (hx : x ∈ locU a w) :
    x ∈ intU a w ↔ cLoc w x ∈ GlobalTheory.LFun.KGL w (n := a) :=
  ⟨fun h => (mem_intU.1 h).2 w (fun h' => h' rfl), mem_intU_of hx⟩

theorem isOpen_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsOpen (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
  have e : (((intU a w).subgroupOf (locU a w)) : Set (locU a w)) =
      (fun x : locU a w => cLoc w x.1) ⁻¹' (GlobalTheory.LFun.KGL w (n := a) : Set _) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    exact mem_intU_iff_of_mem_locU x.2
  rw [e]
  exact (isOpen_KGL w a).preimage ((continuous_cLoc w).comp continuous_subtype_val)

theorem isCompact_intU (w : HeightOneSpectrum (𝓞 E)) :
    IsCompact (intU a w : Set (UA E a)) := by
  haveI : ∀ u : HeightOneSpectrum (𝓞 E), T2Space (GL (Fin a) (u.adicCompletion E)) :=
    fun _ => Units.isEmbedding_embedProduct.t2Space
  let T : Set (finU (E := E) (n := a)) := {x | x.1 ∈ intU a w}
  have hK0 : IsCompact {x : finU (E := E) (n := a) | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} :=
    isClosedEmbedding_finU.isCompact_preimage
      ((AdelicGLn.isCompact_integralFiniteGL E a).image continuous_finGL_ad)
  have hTsub : T ⊆ {x : finU (E := E) (n := a) | ((x : UA E a) : GA E a) ∈
      finGL E a '' (AdelicGLn.integralFiniteGL E a : Set _)} := by
    intro x hx
    have hx' := mem_intU.1 hx
    have hall : ∀ u, cLoc u x.1 ∈ GlobalTheory.LFun.KGL u (n := a) := by
      intro u
      by_cases hu : Apart u w
      · rw [((GlobalTheory.Cong.LevelExt.mem_locU_iff x.1).1 hx'.1).2 u hu]
        exact one_mem _
      · exact hx'.2 u hu
    refine ⟨finPart E a x, (finPart_mem_integral_iff x).2 hall, ?_⟩
    have h1 : Matrix.GeneralLinearGroup.map (pInf E) ((x : UA E a) : GA E a) = 1 := x.2
    exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL]; rfl)
  have hTe : T = (⋂ u, ⋂ (_ : Apart u w), {x : finU (E := E) (n := a) | cLoc u x.1 = 1}) ∩
      ⋂ u, ⋂ (_ : ¬ Apart u w), {x : finU (E := E) (n := a) | cLoc u x.1 ∈ GlobalTheory.LFun.KGL u (n := a)} := by
    ext x
    simp only [T, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, mem_intU,
      GlobalTheory.Cong.LevelExt.mem_locU_iff]
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨x.2, h.1⟩, h.2⟩⟩
  have hTc : IsClosed T := by
    rw [hTe]
    refine (isClosed_iInter fun u => isClosed_iInter fun _ => ?_).inter
      (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    · exact isClosed_eq ((continuous_cLoc u).comp continuous_subtype_val) continuous_const
    · exact (isClosed_KGL u a).preimage ((continuous_cLoc u).comp continuous_subtype_val)
  have hT := (hK0.of_isClosed_subset hTc hTsub).image continuous_subtype_val
  have e : Subtype.val '' T = (intU a w : Set (UA E a)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy
      exact ⟨⟨y, ((GlobalTheory.Cong.LevelExt.mem_locU_iff y).1 (intU_le_locU w hy)).1⟩, hy, rfl⟩
  rwa [e] at hT

theorem intU_isCompact_isOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsCompact (GlobalTheory.Cong.AdaptLev.intU a w : Set (UA E a)) ∧ IsOpen (((GlobalTheory.Cong.AdaptLev.intU a w).subgroupOf (locU a w)) : Set (locU a w)) :=
  fun _ _ _ _ _ w => ⟨isCompact_intU w, isOpen_intU w⟩

end GlobalTheory.Cong.AdaptLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DefiniteUnitaryIntegralBelowPlaceCompactOpenStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryIntegralBelowPlace_compact_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (w : HeightOneSpectrum (𝓞 E)), IsCompact (GlobalTheory.Cong.AdaptLev.intU a w : Set (UA E a)) ∧ IsOpen (((GlobalTheory.Cong.AdaptLev.intU a w).subgroupOf (locU a w)) : Set (locU a w)) := by
  first | (exact @GlobalTheory.Cong.AdaptLev.intU_isCompact_isOpen) | (exact GlobalTheory.Cong.AdaptLev.intU_isCompact_isOpen) | (intros; apply GlobalTheory.Cong.AdaptLev.intU_isCompact_isOpen  <;> assumption)
end
end
