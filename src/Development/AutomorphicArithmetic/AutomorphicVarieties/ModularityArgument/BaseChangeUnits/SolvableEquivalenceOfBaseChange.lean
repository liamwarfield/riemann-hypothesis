module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCmCompositumMaximalRealSubfield
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepPropertiesInvariantUnderConjugation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TeichmullerCharacterSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvableCyclicSubextensionOverRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepresentationIrreduciblePrimeDimension
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolvableEquivalenceOfBaseChange
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc UpperTheory.V.Af.Sol

namespace UpperTheory.V.Z.Bc

def StepC : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M],
    (Module.finrank K M).Prime → IsCMField K → IsCMField M → Equi K Ω M

def SolE : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M],
    IsSolvable (M ≃ₐ[K] M) → IsCMField K → IsCMField M → Equi K Ω M

private theorem cusp_unique {F : Type} [Field F] [NumberField F] {n : ℕ} {sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop}
    {inf : (F →+* ℂ) → Multiset ℂ → Prop} (h : IsCusp n sat inf) : ∀ v B B', sat v B → sat v B' → B = B' := by
  rcases h with ⟨_, π, rfl, -⟩ | ⟨_, π, rfl, -⟩
  · exact fun _ _ _ h h' => h.unique h'
  · exact fun _ _ _ h h' => h.unique h'

private theorem not_both (F : Type) [Field F] [NumberField F] (h : IsTotallyReal F) (h' : IsTotallyComplex F) : False := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact (InfinitePlace.not_isReal_iff_isComplex.2 (h'.isComplex v)) (h.isReal v)

private theorem cm_of_rc (K E : Type) [Field K] [NumberField K] [IsCMField K] [Field E] [NumberField E] [Algebra K E] (h : RC E) : IsCMField E :=
  h.resolve_left fun h' => not_both E h' (isTotallyComplex_of_algebra K E)

theorem exDownC (H : HypothesesH) (cyc : CycC) : ExDownC := by
  have hA0 := algOfCyc H
  have hTo := UpperTheory.cyclotomicCharacter_plusPart hA0 UpperTheory.cyclotomic_char_conj_invariant
  have hDual := UpperTheory.dualBaseChange_of_frobeniusDuality_of_conjUnder UpperTheory.frobeniusDuality_complexConj UpperTheory.complexConj_place_under_eq
  have hNorm := UpperTheory.norm_character_of_frobenius_compatibility H.toClassicalTheorems UpperTheory.galois_character_frobenius_compatibility
  have hFin := UpperTheory.finiteCharacter_of_algebraic_cyclotomic hA0
  have hExt := UpperTheory.character_extends_to_galois_group
  have hEig := UpperTheory.hecke_eigenvalue_basic_properties
  have hSign := UpperTheory.sign_at_infinity_of_parallel_weight UpperTheory.adelicSolution_parallel
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ hp l _ ι n hn r π sat' inf' hpol hreg hc' hbc hatt
  haveI : IsAlgClosure (maximalRealSubfield K) Ω :=
    ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.trans (maximalRealSubfield K) K Ω⟩
  obtain ⟨μ, χ, c, P, hμ, hs, hc, hP⟩ := hTo K Ω l ι n r hpol
  have huniq : ∀ w B B', sat' w B → sat' w B' → B = B' := by
    rcases hc' with ⟨_, Q, rfl, -⟩ | ⟨_, Q, rfl, -⟩
    · exact fun _ _ _ h h' => h.unique h'
    · exact fun _ _ _ h h' => TR.CuspSub.HasSat.unique h h'
  have hbc' := hDual K M Ω l ι n r π sat' huniq hbc hatt μ χ c P hμ hc hP
  obtain ⟨η, hη, hev⟩ := (cyc K M hp inferInstance n hn).2.2 _ _ sat' inf'
    (Or.inl ⟨inferInstance, π, rfl, rfl⟩) hc' hbc _ _ (Or.inl ⟨inferInstance, _, rfl, rfl⟩) hbc'
  obtain ⟨δ, hδ, hδe⟩ := hNorm K M Ω l ι η hη
  obtain ⟨δ', hδ', hδc, hδo⟩ := hExt K M Ω l δ hδ
  have hA := (algOfCyc H (maximalRealSubfield K) Ω l ι).2.1
  have h1 : IsAlgChar ι μ := ⟨χ, hμ⟩
  have h2 := hFin.1 _ Ω l ι δ' hδo
  obtain ⟨χ', hχ'⟩ := (hA _ _ h1 (hA _ _ h2 h2).2).1
  have hs' : SameSign (μ * δ'⁻¹) := fun a b ha hb => by
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.inv_apply, hδc a ha, hδc b hb, hs a b ha hb]
  have hd : GlobalTheory.ContraPair.DualIsConjBy π (compNorm K χ') := by
    refine UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse H.litN.aut.js.1 H.litN.aut.gk K n hn π _ ?_
    have h3 := (conjSrc_injective (IsCMField.complexConj K).toRingEquiv).tendsto_cofinite.eventually hev
    filter_upwards [Bc.normGal K Ω l ι χ μ hμ, Bc.normGal K Ω l ι χ' _ hχ', hev, h3, hδe] with w ⟨hu, he⟩ ⟨hu', he'⟩
      ⟨_, B, hB, hB₁⟩ ⟨_, B', hB', _⟩ hw
    refine ⟨hu', B, B', hB, hB', ?_⟩
    have e1 : (μ * δ'⁻¹).comp (res (maximalRealSubfield K) Ω K) = μ.comp (res (maximalRealSubfield K) Ω K) * δ⁻¹ := by
      rw [← hδ']
      rfl
    rw [e1] at he'
    have e2 := (hEig K Ω l ι w).2.1 _ _ _ he' ((hEig K Ω l ι w).1 _ _ _ _ he hw)
    have e3 := hB₁.unique (GlobalTheory.SphGal.hasSatGL_twist K n _ (compNorm K χ) w _ hu (UpperTheory.theta_satake_parameters_inverse K n π w B' hB'))
    have e4 := congrArg (Multiset.map (· * ((compNorm K χ).val w)⁻¹)) e3
    simp only [Multiset.map_map, Function.comp_def, mul_inv_cancel_right] at e4
    rw [← e4, e2]
    refine Multiset.map_congr rfl fun a _ => ?_
    rw [mul_inv_rev, inv_inv, mul_assoc]
  obtain ⟨_, R, _, _, _, hR, hatt', -⟩ := exC H K Ω l ι n hn π χ' hreg (hSign _ Ω l ι χ' _ hχ' hs') hd
  exact ⟨R, hR.cont, hatt'⟩

theorem stepC (H : HypothesesH) (cyc : CycC) : StepC := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hp hK hM l _ ι n hn r hr hirr hpol
  obtain ⟨hup, hdown, -⟩ := cyc K M hp inferInstance n hn
  have hss : IsSSRep (r.comp (resG K M Ω)) := (Bc.irrBasic.1 _ Unit _ n _).2.1 hirr
  have hirr' : IsIrr r := (Bc.irrBasic.1 _ _ _ n r).1 _ hirr
  have hcont := continuous_restrictScalarsHom K M Ω
  constructor
  · rintro ⟨sat, inf, hc, hreg, hatt⟩
    rcases hup sat inf hc hreg with ⟨η, hη, ht⟩ | ⟨sat', inf', hc', hbc, hinf⟩
    · obtain ⟨δ, h1, -, h2, h3⟩ := UpperTheory.V.Sd.selfTwGal H.toClassicalTheorems K Ω l ι n r sat (cusp_unique hc) hr hatt η _ hp.pos hη.2.1 hη.1 ht
      exact (h1 (UpperTheory.schur_twist_holds _ _ _ n r (resG K M Ω) δ hirr (h3 M hη) h2)).elim
    · refine ⟨sat', inf', hc', fun τ => ?_, UpperTheory.satake_base_change_attached K M Ω l ι n r sat sat' (cusp_unique hc) hbc hatt hss⟩
      obtain ⟨m, hm, h⟩ := hreg (τ.comp (algebraMap K M))
      exact ⟨m, hinf τ m hm, h⟩
  · rintro ⟨sat', inf', hc', hreg', hatt'⟩
    obtain ⟨sat, inf, hc, hbc, hinf⟩ := hdown sat' inf' hc' hreg' (UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic UpperTheory.frobenius_conj_of_galois_conjugate_places UpperTheory.hecke_eigenvalue_basic_properties K M Ω l ι n r sat' hatt')
    have hreg : RegInf n inf := fun τ => by
      obtain ⟨m, hm, h⟩ := hreg' (ComplexEmbedding.lift M τ)
      have := hinf _ m hm
      rw [ComplexEmbedding.lift_comp_algebraMap] at this
      exact ⟨m, this, h⟩
    obtain ⟨r₁, hr₁, hatt₁⟩ := (show ∃ r₁ : G K Ω →* GL (Fin n) (Qbar l), Continuous r₁ ∧ AttachedSys ι r₁ sat by
      rcases hc with ⟨hC, π, rfl, rfl⟩ | ⟨hR, -⟩
      · refine exDownC H cyc K M Ω hp l ι n hn r π sat' inf' hpol ((GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_) hc' hbc hatt'
        obtain ⟨m, hm, h⟩ := hreg τ
        rw [CG.HasInfChar.infChar_eq (π := CG.mk π) hm]
        exact h
      · exact (not_both K hR inferInstance).elim)
    have hN := (UpperTheory.galois_representation_image_spec K M Ω).1
    have hss₁ := UpperTheory.semisimpleModule_restriction_to_normal_subgroup _ _ _ n r₁ (resG K M Ω) hN hatt₁.1
    have hatt₁' := UpperTheory.satake_base_change_attached K M Ω l ι n r₁ sat sat' (cusp_unique hc) hbc hatt₁ hss₁
    have hiso : RepIso (r₁.comp (resG K M Ω)) (r.comp (resG K M Ω)) := by
      refine isoOfFrob H.toClassicalTheorems M Ω l ι n _ _ (hr₁.comp hcont) (hr.comp hcont) hss₁ hss ?_
      filter_upwards [hatt₁'.2, hatt'.2] with w ⟨B, hB, h⟩ ⟨B', hB', h'⟩
      obtain rfl := cusp_unique hc' w B B' hB hB'
      exact ⟨_, h, h'⟩
    obtain ⟨δ, hδ, hiso'⟩ := UpperTheory.schur_extension _ _ _ n r r₁ (resG K M Ω) hN hirr hiso
    have hF := UpperTheory.finiteCharacter_of_algebraic_cyclotomic (algOfCyc H)
    obtain ⟨sat₂, inf₂, hc₂, hreg₂, hatt₂⟩ := twi H K Ω l ι n r₁ δ ⟨sat, inf, hc, hreg, hatt₁⟩
      (hF.1 K Ω l ι δ (hF.2 K M Ω l δ hδ))
    exact ⟨sat₂, inf₂, hc₂, hreg₂, (Bc.irrBasic.1 _ Unit _ n _).2.1 hirr',
      hatt₂.2.mono fun w ⟨B, hB, h⟩ => ⟨B, hB, h.of_iso hiso'⟩⟩

theorem degOneC (hS : StepC) : ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω],
    Module.finrank K M = 1 → IsCMField K → IsCMField M → Equi K Ω M := by
  have hP := UpperTheory.solvable_polarized_restriction
  have hC := UpperTheory.solvable_cyclic_subextension_over_rat
  have hA := UpperTheory.solvable_auxiliary_galois_extension
  have hR := UpperTheory.solvable_cm_compositum_maximalRealSubfield
  have hI := UpperTheory.galois_representation_irreducible_prime_dimension
  have hG := UpperTheory.galois_representation_image_spec
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ h1 hK hM l _ ι n hn r hr hirr hpol
  obtain ⟨L, _, _, _, hL, hp, hlt⟩ := hC (max n (Module.finrank ℚ M))
  obtain ⟨M', _, _, _, _, _, f, _, hd, hadj⟩ := hA M Ω L hp (lt_of_le_of_lt (le_max_right _ _) hlt)
  have hM' : IsCMField M' := cm_of_rc M M' (hR L M M' f hL hadj (Or.inr hM))
  letI : Algebra K M' := ((algebraMap M M').comp (algebraMap K M)).toAlgebra
  haveI : IsScalarTower K M M' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K M' Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K M Ω, IsScalarTower.algebraMap_apply M M' Ω]; rfl
  haveI : IsAlgClosure M' Ω :=
    { isAlgClosed := IsAlgClosure.isAlgClosed M
      isAlgebraic := Algebra.IsAlgebraic.tower_top (K := M) M' }
  have hbij : Function.Bijective (algebraMap K M) := by
    refine ⟨(algebraMap K M).injective, fun x => ?_⟩
    have : (⊥ : Subalgebra K M) = ⊤ := Subalgebra.bot_eq_top_iff_finrank_eq_one.2 h1
    have hx : x ∈ (⊥ : Subalgebra K M) := this ▸ Algebra.mem_top
    exact Algebra.mem_bot.1 hx
  haveI : IsGalois K M' :=
    IsGalois.of_equiv_equiv (F := M) (E := M') (f := (RingEquiv.ofBijective (algebraMap K M) hbij).symm) (g := RingEquiv.refl M') (by
      ext x
      obtain ⟨y, rfl⟩ := hbij.2 x
      have : (RingEquiv.ofBijective (algebraMap K M) hbij).symm (algebraMap K M y) = y :=
        (RingEquiv.ofBijective (algebraMap K M) hbij).symm_apply_apply y
      simp [this, IsScalarTower.algebraMap_apply K M M'])
  have hd' : Module.finrank K M' = Module.finrank ℚ L := by
    rw [← Module.finrank_mul_finrank K M M', h1, one_mul, hd]
  have hcomp : (r.comp (resG K M Ω)).comp (resG M M' Ω) = r.comp (resG K M' Ω) := by
    ext s; rfl
  obtain ⟨hN, hidx⟩ := hG M M' Ω
  have hirr' : IsIrr ((r.comp (resG K M Ω)).comp (resG M M' Ω)) :=
    hI _ _ _ n _ _ hN (by rw [hidx, hd]; exact hp) (by rw [hidx, hd]; exact lt_of_le_of_lt (le_max_left _ _) hlt) hirr
  have hc : Continuous (resG K M Ω) := by
    refine continuous_of_continuousAt_one _ fun U hU => ?_
    rw [map_one, krullTopology_mem_nhds_one_iff] at hU
    obtain ⟨E, hE, hEU⟩ := hU
    obtain ⟨s, hs⟩ : E.FG := E.fg_of_fg_toSubalgebra ((Subalgebra.fg_iff_finiteType _).2 (inferInstanceAs (Algebra.FiniteType K E)))
    haveI : FiniteDimensional M (IntermediateField.adjoin M (s : Set Ω)) :=
      IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
    rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
    refine ⟨IntermediateField.adjoin M (s : Set Ω), inferInstance, fun σ hσ => hEU ?_⟩
    have hle : (E : Set Ω) ⊆ IntermediateField.adjoin M (s : Set Ω) := by
      rw [← hs]
      exact (IntermediateField.adjoin_le_iff (F := K) (T := (IntermediateField.adjoin M (s : Set Ω)).restrictScalars K)).2 (IntermediateField.subset_adjoin M _)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ x (hle hx)
  have e1 := hS K M' Ω (hd' ▸ hp) hK hM' l ι n hn r hr (hcomp ▸ hirr') hpol
  have e2 := hS M M' Ω (hd ▸ hp) hM hM' l ι n hn (r.comp (resG K M Ω)) (hr.comp hc) hirr' (hP K M Ω l ι n r hpol)
  rw [hcomp] at e2
  exact e1.trans e2.symm

private theorem trans_equi (hP : PolRes) (K E M Ω : Type) [Field K] [NumberField K] [Field E] [NumberField E] [Field M] [NumberField M]
    [Field Ω] [Algebra K E] [Algebra E M] [Algebra K M] [IsScalarTower K E M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω]
    (h : ∀ [Algebra E Ω] [IsScalarTower K E Ω] [IsScalarTower E M Ω] [IsAlgClosure E Ω], Equi K Ω E ∧ Equi E Ω M) :
    Equi K Ω M := by
  letI : Algebra E Ω := ((algebraMap M Ω).comp (algebraMap E M)).toAlgebra
  haveI : IsScalarTower E M Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower K E Ω := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K M Ω, IsScalarTower.algebraMap_apply K E M]; rfl
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure E Ω := ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) E⟩
  obtain ⟨e1, e2⟩ := h
  intro l _ ι n hn r hr hirr hpol
  have hc : (r.comp (resG K E Ω)).comp (resG E M Ω) = r.comp (resG K M Ω) := rfl
  have i2 : IsIrr ((r.comp (resG K E Ω)).comp (resG E M Ω)) := hc ▸ hirr
  have i1 : IsIrr (r.comp (resG K E Ω)) := (UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ n _).1 _ i2
  rw [e1 l ι n hn r hr i1 hpol, ← hc]
  exact e2 l ι n hn _ (hr.comp (continuous_restrictScalarsHom K E Ω)) i2 (hP K E Ω l ι n r hpol)

private theorem solvable_equivalence_of_base_change (hS : StepC) (d : ℕ) :
    ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsAlgClosure M Ω] [IsGalois K M],
    Module.finrank K M = d → IsSolvable (M ≃ₐ[K] M) → IsCMField K → IsCMField M → Equi K Ω M := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hd hsol hK hM
  by_cases h1 : Module.finrank K M = 1
  · exact degOneC hS K M Ω h1 hK hM
  by_cases hp : (Module.finrank K M).Prime
  · exact hS K M Ω hp hK hM
  obtain ⟨E, hb, ht, hg, hE0⟩ := UpperTheory.solvable_cm_extension_tower K M hsol (Or.inr hK) (Or.inr hM) h1 hp
  have hE : IsCMField E := cm_of_rc K E hE0
  have hmul : Module.finrank K E * Module.finrank E M = d := by rw [Module.finrank_mul_finrank, hd]
  have p1 : 0 < Module.finrank K E := Module.finrank_pos
  have p2 : 0 < Module.finrank E M := Module.finrank_pos
  have n1 : Module.finrank K E ≠ 1 := fun h => hb (IntermediateField.finrank_eq_one_iff.1 h)
  have n2 : Module.finrank E M ≠ 1 := fun h => ht (IntermediateField.finrank_eq_one_iff_eq_top.1 h)
  have l1 : Module.finrank K E < d := by
    rw [← hmul]; exact lt_mul_of_one_lt_right p1 (by omega)
  have l2 : Module.finrank E M < d := by
    rw [← hmul]; exact lt_mul_of_one_lt_left p2 (by omega)
  haveI : Group.IsSolvable (M ≃ₐ[K] M) := hsol
  have s1 : IsSolvable (E ≃ₐ[K] E) :=
    Group.isSolvable_of_surjective (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) M)
  have s2 : IsSolvable (M ≃ₐ[E] M) :=
    Group.isSolvable_of_isSolvable_injective (f := (AlgEquiv.restrictScalarsHom K : (M ≃ₐ[E] M) →* (M ≃ₐ[K] M)))
      (AlgEquiv.restrictScalars_injective K)
  refine trans_equi UpperTheory.solvable_polarized_restriction K E M Ω ?_
  intro iA i1 i2 i3
  exact ⟨ih _ l1 K E Ω rfl s1 hK hE, @ih _ l2 E M Ω _ _ _ _ _ _ iA _ i2 i3 _ _ rfl s2 hE hM⟩

theorem solC_of_stepC (hS : StepC) : SolE := fun K M Ω _ _ _ _ _ _ _ _ _ _ _ _ hsol hK hM => solvable_equivalence_of_base_change hS _ K M Ω rfl hsol hK hM

theorem solC (H : HypothesesH) (cyc : CycC) : SolE := solC_of_stepC (stepC H cyc)

end UpperTheory.V.Z.Bc
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadLiftRealToComplexOfBaseChange
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Base UpperTheory.V.Published UpperTheory.V.Sd Formalism.L2.Host.CT UpperTheory.V.Z.Bc

def UpperTheory.V.Z.Bc.CyclicBaseChangeLiftRankTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E]
    [IsGalois F E], (Module.finrank F E).Prime → ∀ π : CuspSub F 2, (CG.mk π).IsRegAlg →
      (∃ η : HChar F, IsNormChar E η ∧ SelfTw (CG.mk π).HasSat η) ∨ ∃ P : CuspSub E 2,
        (∀ (τ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m) ∧
        WeakBC (CG.mk π).HasSat (CG.mk P).HasSat

private theorem normV_under {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

private theorem algSat_pow (n q f : ℕ) (B : Multiset ℂˣ) :
    algSat n (q ^ f) (B.map (· ^ f)) = (algSat n q B).map (· ^ f) := by
  have e : ∀ (q : ℕ) (B : Multiset ℂˣ),
      algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun q B => by
    simp only [algSat, Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map, Function.comp_def]
  simp only [e, Multiset.map_map, Function.comp_def]
  refine Multiset.map_congr rfl fun α _ => ?_
  have h : (((q ^ f : ℕ) : ℝ)) ^ (((n : ℝ) - 1) / 2) = ((q : ℝ) ^ (((n : ℝ) - 1) / 2)) ^ f := by
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q),
      ← Real.rpow_mul (Nat.cast_nonneg q), mul_comm]
  rw [h, mul_pow, Units.val_pow_eq_pow_val, Complex.ofReal_pow]

private theorem upCycI (hP : Af.Hypotheses₂) (hL : CyclicBaseChangeLiftRankTwo) (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E]
    [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    [IsGalois F E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (hp : (Module.finrank F E).Prime) (r : G F Ω →* GL (Fin 2) (Qbar l))
    (π : CuspSub F 2) (hr : Continuous r) (hreg : (CG.mk π).IsRegAlg) (hatt : AttC ι r π) (hirr : IsIrr (r.comp (galEmb F E Ω))) :
    ∃ P : CuspSub E 2, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
      ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m := by
  haveI : IsAlgClosure F Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans F E Ω⟩
  rcases hL F E hp π hreg with ⟨η, hη, hT⟩ | ⟨P, hinf, hbc⟩
  · obtain ⟨δ, hδ1, -, hiso, hres⟩ := UpperTheory.V.Sd.selfTwGal hP F Ω l ι 2 r (CG.mk π).HasSat
      (fun _ _ _ h h' => h.unique h') hr hatt η _ hp.pos hη.2.1 hη.1 hT
    exact (hδ1 (UpperTheory.schur_twist_holds _ _ _ 2 r _ δ hirr (hres E hη) hiso)).elim
  · refine ⟨P, (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_, ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 2 _).2.1 hirr, ?_⟩, hinf⟩
    · have h := hreg (τ.comp (algebraMap F E))
      have hm : π.HasInfChar (τ.comp (algebraMap F E)) ((CG.mk π).infChar (τ.comp (algebraMap F E))) :=
        ParLaws.hasInfChar_infChar (CG.mk π) _
      rw [CG.HasInfChar.infChar_eq (π := CG.mk P) (hinf τ _ hm)]
      exact h
    · filter_upwards [hbc, (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under F E).eventually hatt.2] with w h1 h2
      obtain ⟨B, hB, hPw⟩ := h1 _ (normV_under (K := F) w)
      obtain ⟨B', hB', hF⟩ := h2
      obtain rfl := hB.unique hB'
      refine ⟨_, hPw, ?_⟩
      have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w _ (normV_under (K := F) w)).1 2 r _ hF
      rw [← algSat_pow, ← normV_under] at h3
      exact h3

private theorem exists_prime_index (Γ : Type) [Group Γ] [Finite Γ] [Nontrivial Γ] [Group.IsSolvable Γ] :
    ∃ M : Subgroup Γ, M.Normal ∧ M.index.Prime := by
  obtain ⟨M, hM, hle⟩ := (eq_top_or_exists_le_coatom (commutator Γ)).resolve_left
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Γ).ne
  have hn : M.Normal := ⟨fun n hn g => by
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ M := hle (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    simpa using M.mul_mem h1 hn⟩
  refine ⟨M, hn, ?_⟩
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (n := Nat.card (Γ ⧸ M)) (mt Subgroup.index_eq_one.1 hM.1)
  haveI := Fact.mk hp
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hd
  have h1 : (Subgroup.zpowers g).comap (QuotientGroup.mk' M) = ⊤ := by
    refine hM.2 _ (lt_of_le_of_ne (fun x hx => ?_) fun e => ?_)
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M g
      have hx : x ∈ M := e ▸ Subgroup.mem_zpowers _
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx, orderOf_one] at hg
      exact hp.one_lt.ne hg
  have h2 : Subgroup.zpowers g = ⊤ :=
    Subgroup.comap_injective (QuotientGroup.mk'_surjective M) (h1.trans (Subgroup.comap_top _).symm)
  rw [Subgroup.index, ← Subgroup.card_top, ← h2, Nat.card_zpowers, hg]
  exact hp

private theorem closure_tower (K E Ω : Type) [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω] [Algebra E Ω]
    [IsScalarTower K E Ω] [Algebra.IsAlgebraic K E] [IsAlgClosure E Ω] : IsAlgClosure K Ω :=
  { isAlgClosed := IsAlgClosure.isAlgClosed E, isAlgebraic := Algebra.IsAlgebraic.trans K E Ω }

private theorem up_one (F E Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field E] [NumberField E]
    [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω]
    (h1 : Module.finrank F E = 1) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n) (hreg : (CG.mk π).IsRegAlg) (ha : AttC ι r π)
    (hi : IsIrr (r.comp (galEmb F E Ω))) : ∃ P : CuspSub E n, (CG.mk P).IsRegAlg ∧ AttC ι (r.comp (galEmb F E Ω)) P ∧
      ∀ (τ : E →+* ℂ) m, π.HasInfChar (τ.comp (algebraMap F E)) m → P.HasInfChar τ m := by
  obtain ⟨-, hat⟩ := ha
  let j : E ≃+* F := (RingEquiv.ofBijective (algebraMap F E) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)).symm
  refine ⟨UpperTheory.V.FieldIso.pullSub j π, UpperTheory.V.FieldIso.isRegAlg_pullSub j hreg,
    ⟨(UpperTheory.galoisRep_irreducibility_criterion.1 _ (G E Ω) _ n _).2.1 hi, ?_⟩, fun τ m hm => by
      have h := (UpperTheory.V.FieldIso.hasInfChar_pullSub j π _ m).2 hm
      rwa [show (τ.comp (algebraMap F E)).comp (j : E →+* F) = τ from RingHom.ext fun x => congrArg τ (j.symm_apply_apply x)] at h⟩
  filter_upwards [(plMap_injective j).tendsto_cofinite.eventually hat] with w hw
  obtain ⟨B, hB, hF⟩ := hw
  have hu : w.under (𝓞 F) = plMap j w := HeightOneSpectrum.ext (Ideal.ext fun x => Iff.rfl)
  have hn : normV w = normV (plMap j w) := by
    simpa only [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using (absNorm_plMap j w).symm
  refine ⟨B, UpperTheory.V.FieldIso.hasSat_pullSub j hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility F E Ω l ι w 1 (by rw [hu, pow_one, hn])).1 n r _ (hu ▸ hF)
  rw [hn, ← hu]
  simp only [pow_one, Multiset.map_id'] at h3
  exact h3

theorem UpperTheory.V.Z.Bc.upSolI_of :
    UpperTheory.V.Af.Hypotheses₂ → CyclicBaseChangeLiftRankTwo → UpSolI := by
  intro P hL F E Ω _ _ _ _ _ _ _ _ _ _ _ _ _ _ l _ ι
  induction hd : Module.finrank F E using Nat.strong_induction_on generalizing F with
  | _ d ih =>
  intro r π hc hreg ha hi
  by_cases h1 : Module.finrank F E = 1
  · exact up_one F E Ω h1 l ι 2 r π hreg ha hi
  haveI : Nontrivial (E ≃ₐ[F] E) := by
    rw [← Finite.one_lt_card_iff_nontrivial, IsGalois.card_aut_eq_finrank]
    have := Module.finrank_pos (R := F) (M := E)
    omega
  obtain ⟨M, hM, hp⟩ := exists_prime_index (E ≃ₐ[F] E)
  let K := IntermediateField.fixedField M
  haveI : IsGalois F K := IsGalois.of_fixedField_normal_subgroup M
  haveI : IsTotallyComplex K := isTotallyComplex_of_algebra F K
  haveI : Module.IsTorsionFree K Ω := DivisionSemiring.to_moduleIsTorsionFree
  haveI : IsAlgClosure K Ω := closure_tower K E Ω
  haveI : Group.IsSolvable (E ≃ₐ[K] E) :=
    Group.isSolvable_of_isSolvable_injective (f := AlgEquiv.restrictScalarsHom F) (AlgEquiv.restrictScalars_injective F)
  have hdeg : Module.finrank F K = M.index := by
    have h2 := Module.finrank_mul_finrank F K E
    rw [IntermediateField.finrank_fixedField_eq_card, ← IsGalois.card_aut_eq_finrank F E, ← M.index_mul_card] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hlt : Module.finrank K E < d := by
    rw [← hd, ← Module.finrank_mul_finrank F K E, hdeg]
    exact lt_mul_of_one_lt_left Module.finrank_pos hp.one_lt
  have e : r.comp (galEmb F E Ω) = (r.comp (galEmb F K Ω)).comp (galEmb K E Ω) := rfl
  rw [e] at hi ⊢
  obtain ⟨Q, q1, q2, q3⟩ := upCycI P hL F K Ω l ι (hdeg ▸ hp) r π hc hreg ha ((UpperTheory.galoisRep_irreducibility_criterion.1 _ _ _ 2 _).1 _ hi)
  obtain ⟨Q', p1, p2, p3⟩ := ih _ hlt K rfl _ Q (hc.comp (resFacts F K Ω l 2 r).1) q1 q2 hi
  refine ⟨Q', p1, p2, fun τ m hm => p3 τ m (q3 _ m ?_)⟩
  rwa [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq]

def UpperTheory.V.Z.Bc.QuadLiftRealToComplexRankTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Algebra F E],
    Module.finrank F E = 2 → ∀ π : TR.CuspSub F 2, π.IsRegAlg →
      (∃ η : HChar F, IsQuadCharOf E η ∧ IsoTwist π η) ∨ ∃ P : CuspSub E 2, Br.IsBC0 π P

theorem UpperTheory.V.Z.Bc.quadLiftRealToComplex_of_base_change (h : Br.QuadBC0) : QuadLiftRealToComplexRankTwo := fun F E _ _ _ _ _ _ _ h2 π hr => h F E h2 2 one_le_two π hr

theorem UpperTheory.V.Z.Bc.upQuadI_of (hP : Af.Hypotheses₂) (h : QuadLiftRealToComplexRankTwo) : UpQuadI := by
  intro F E Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι hE r π hr hreg hatt hirr
  obtain ⟨P, hBC⟩ := (h F E hE π hreg).resolve_left fun ⟨η, hη, ht⟩ =>
    UpperTheory.baseChange_noSelfTwist_of_frobenius_sign_irreducible (isoOfFrob hP) UpperTheory.frobenius_eigenvalues_twist UpperTheory.exists_quadratic_sign_character UpperTheory.frobenius_sign_compatibility UpperTheory.schur_twist_holds UpperTheory.galoisRep_irreducibility_criterion F E Ω l ι hE 2 r π hr hatt hirr η hη ht
  have h1 := UpperTheory.V.Br.bcAtt0 F E Ω l ι 2 r π P hBC
  exact ⟨P, h1.1 hreg, h1.2 hatt ((UpperTheory.galoisRep_irreducibility_criterion.1 _ Unit _ 2 _).2.1 hirr), hBC.inf⟩
end
