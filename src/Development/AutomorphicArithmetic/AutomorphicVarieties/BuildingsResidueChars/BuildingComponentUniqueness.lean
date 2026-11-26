module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SdDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeInvMulCharEqOfSimilitudePairing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeCharParallelWeight
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericUnitaryDualGl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.QbarInst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.DefiniteBC
open UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.building_component_uniqueness :
    CompUnique := by
  intro E _ _ _ n π hπ w hw V W _ _ _ _ ρ₁ ρ₂ h₁ h₂
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  let P : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  have key : ∀ {X : Type} [AddCommGroup X] [Module ℂ X] (τ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) X),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) τ →
      ∃ f : τ.IntertwiningMap (P.rep.comp s), f ≠ 0 := by
    rintro X _ _ τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict π hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key ρ₁ h₁
  obtain ⟨f', hf'⟩ := key ρ₂ h₂
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  exact (GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ P.rep s ρ₁ ρ₂ P.isIrreducible_rep h₁.1 h₂.1 hcomm f hf).2 f' hf'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HeckeEigenvalueBasicProperties
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem algSat_injective (n q : ℕ) (hq : q ≠ 0) (B B' : Multiset ℂˣ)
    (h : UpperTheory.V.Af.algSat n q B = UpperTheory.V.Af.algSat n q B') : B = B' := by
  unfold UpperTheory.V.Af.algSat at h
  have hc : ((((q : ℝ) ^ (((n : ℝ) - 1) / 2)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (q : ℝ) ^ (((n : ℝ) - 1) / 2) :=
      Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hq) _
    exact_mod_cast this.ne'
  have h1 := Multiset.map_injective (mul_right_injective₀ hc) h
  have h2 : ∀ s : Multiset ℂˣ, (do let a ← s; pure (a : ℂ)) =
      Multiset.map (fun a : ℂˣ => (a : ℂ)) s := fun s => Multiset.bind_singleton _ _
  rw [h2, h2] at h1
  exact Multiset.map_injective Units.val_injective h1

theorem UpperTheory.hecke_eigenvalue_basic_properties :
    UpperTheory.V.Af.Sol.EigBasic := by
  intro F Ω _ _ _ _ _ l _ ι v
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  refine ⟨?_, ?_, ?_⟩
  · intro δ δ' z z' hz hz' A' hA'
    obtain ⟨hi, hf⟩ := hz A' hA'
    obtain ⟨hi', hf'⟩ := hz' A' hA'
    refine ⟨fun s hs => ?_, fun τ hτ => ?_⟩
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hi s hs, hi' s hs, inv_one, mul_one]
    · rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, map_mul, Units.val_inv_eq_inv_val,
        map_inv₀, hf τ hτ, hf' τ hτ]
      push_cast
      rfl
  · intro δ z z' hz hz'
    apply Units.ext
    rw [← (hz A hA).2 σ hσ, ← (hz' A hA).2 σ hσ]
  · intro n r B B' hB hB'
    have e1 := (hB A hA).2 σ hσ
    have e2 := (hB' A hA).2 σ hσ
    rw [e1] at e2
    have e3 := congrArg Polynomial.roots e2
    rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e3
    have hq : Formalism.ConjugateSelfDual.normV v ≠ 0 := by
      unfold Formalism.ConjugateSelfDual.normV
      exact Nat.card_pos.ne'
    exact algSat_injective n _ hq B B' e3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumRestrictionOfLocalComponentUnitary
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.isoSum_restriction_of_local_component_unitary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ (w : Plc E) (j : GLw n w →* UA E n), (∀ g, j g ∈ locU n w) → (∀ g, cLoc w (j g) = g) → (∀ x ∈ locU n w, x = j (cLoc w x)) → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → IsoSum ((RU E n).comp j) σ τ := by
  intro E _ _ _ n π hπ w j hj1 hj2 hj3 τ hc
  obtain ⟨hirr, f, hf0, hfm, hf⟩ := hc
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  let F : Representation.IntertwiningMap τ.ρ (Ψ.rep.comp j) :=
    ⟨f.codRestrict _ hfm, fun g => LinearMap.ext fun v => Subtype.ext (by
      have h := hf ⟨j g, hj1 g⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hj2] at h
      exact h)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (GLw n w) Ψ.V τ.V τ.V Ψ.rep j τ.ρ τ.ρ
    Ψ.isIrreducible_rep hirr hirr (fun g => ⟨cLoc w (r g).1, fun y => by
      rw [← hj3 _ (r g).2]
      exact hr g ⟨j y, hj1 y⟩⟩) F hF0).1
  intro φ hφ
  have hmem : φ ∈ (⨆ i : Representation.IntertwiningMap τ.ρ (Ψ.rep.comp j),
      LinearMap.range i.toLinearMap).map π.subtype := by
    rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
  rw [Submodule.map_iSup] at hmem
  refine SetLike.le_def.1 (iSup_le fun i => ?_) hmem
  refine le_iSup_of_le ⟨π.subtype ∘ₗ i.toLinearMap, fun g v =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ i g v), ?_⟩ ?_
  · rintro _ ⟨v, rfl⟩
    exact (i.toLinearMap v).2
  · exact (LinearMap.range_comp _ _).ge
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnderChosenPlaceAndIsSplitAtOfDecompLe
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω), (∀ v, (s.w v).under (𝓞 (Lp L)) = v) ∧ ∀ w : Plc L, Dec (F := Lp L) (s.A (w.under (𝓞 (Lp L)))) ≤ (W.resP L Ω).range → IsSplitAt w := by
  intro l _ L Ω _ _ _ _ _ _ s
  obtain ⟨_, _, _, _, w, A, hAw, hAv, _⟩ := s
  refine ⟨fun v => ?_, fun w' hw' => UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (hAv _) hw' w' rfl⟩
  have h1 := hAw v
  have h2 := hAv v
  apply HeightOneSpectrum.ext
  ext x
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← h1 (algebraMap _ _ x), ← h2 x]
  have hx : ((algebraMap (𝓞 (Lp L)) (𝓞 L) x : 𝓞 L) : L) = algebraMap (Lp L) L (x : Lp L) := rfl
  rw [hx, ← IsScalarTower.algebraMap_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakePolarizationOfCuspidalTransfer
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem hasSat_invT {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} {π π' : TR.CuspSub F a}
    (h : IsInvTOf π π') {w : HeightOneSpectrum (𝓞 F)} {B : Multiset ℂˣ} (hB : π.HasSat w B) :
    π'.HasSat w (B.map (·⁻¹)) := by
  obtain ⟨e, he, -⟩ := h
  refine InvT.hasSatGL_invT e (fun g x => ?_) hB
  rw [TR.CuspSub.locRep_eq, TR.CuspSub.locRep_eq, he, InvT.locGL_invT]

private theorem isTwistOf_twist {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {a : ℕ} (π : TR.CuspSub F a)
    (χ : HChar F) : IsTwistOf π χ (π.twist χ) := by
  refine ⟨π.toTwist χ, (TR.dchi χ).toLinearMap, fun z u hu => ?_, fun k φ => ?_, fun k φ => ?_, fun X φ => ?_⟩
  · have e : u = TR.expU z := Units.ext (funext hu)
    rw [e]
    exact TR.chiInf_expU χ z
  all_goals simp [TR.CuspSub.op_toTwist, TR.opMul, TR.opAdd]

theorem UpperTheory.satakePolarization_of_cuspidalTransfer :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.Sol.PolSatR := by
  intro H F _ _ _ n hn π ψ h
  obtain ⟨π₁, h₁, -⟩ := UpperTheory.exists_contragredient_cuspSub F n π
  obtain ⟨B, hl, hr', hf, hc, hX⟩ := H.gkR F n π
  refine isSelfDualBy_of_iso B hl hr' hf hc hX h₁ (isTwistOf_twist π₁ ψ) (H.smoR F n hn _ _ ?_)
  filter_upwards [h] with w ⟨hu, S, hS, hE⟩
  refine ⟨S, hS, ?_⟩
  have e : (S.map (·⁻¹)).map (· * ψ.val w) = S := by
    rw [hE, Multiset.map_map]
    simp
  exact e ▸ (hasSat_invT h₁ hS).twist hu
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CyclotomicCharConjInvariant
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.cyclotomic_char_conj_invariant :
    UpperTheory.V.Af.Sol.CycConj := by
  intro F Ω _ _ _ _ _ l _ c hc
  obtain ⟨j, hj⟩ := hc
  haveI : CharZero Ω := j.charZero
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : Nat.Prime l).ne_zero⟩
  have hinv : ∀ (x : Ω) (m : ℕ), m ≠ 0 → x ^ m = 1 → c x = x⁻¹ := by
    intro x m hm hx
    apply j.injective
    rw [hj, map_inv₀]
    have hn : ‖j x‖ = 1 := Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hx, map_one]) hm
    have hs : Complex.normSq (j x) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn]; norm_num
    rw [Complex.inv_def, hs]; simp
  set g : Ω ≃+* Ω := MulSemiringAction.toRingAut (Formalism.ConjugateSelfDual.G F Ω) Ω c with hg
  have hcyc : cyclotomicCharacter Ω l g = -1 := by
    ext1
    refine PadicInt.ext_of_toZModPow.mp fun n => ?_
    rw [cyclotomicCharacter.toZModPow]
    have hk : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : Nat.Prime l).ne_zero⟩
    rw [← modularCyclotomicCharacter.unique Ω _ g (c := -1)]
    · simp
    · intro t ht
      have ht' : (t : Ω) ^ (l ^ n) = 1 := by
        rw [mem_rootsOfUnity] at ht
        simpa using congrArg Units.val ht
      have hdvd : l ^ n ∣ (-1 : ZMod (l ^ n)).val + 1 := by
        rw [← ZMod.natCast_eq_zero_iff]; push_cast; simp
      obtain ⟨m, hm⟩ := hdvd
      have hne : (t : Ω) ≠ 0 := t.ne_zero
      have key : (t : Ω) ^ (-1 : ZMod (l ^ n)).val = (t : Ω)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← pow_succ, hm, pow_mul, ht', one_pow]
      rw [key]
      exact hinv _ (l ^ n) (NeZero.ne _) ht'
  show Units.map _ (ReciprocityTheory.Gal.cycZ F Ω l c) = -1
  have : ReciprocityTheory.Gal.cycZ F Ω l c = -1 := hcyc
  rw [this]
  ext; simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AdelicSolutionParallel
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.adelicSolution_parallel :
    UpperTheory.V.Af.Sol.Parallel := by
  intro F _ _ _ χ a ha
  exact UpperTheory.heckeChar_parallel_weight F χ a ha
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeGaloisCompatibilityOfHeckeEigensystem
open UpperTheory.V.Af UpperTheory.V.Af.Gu

theorem UpperTheory.satake_galois_compatibility_of_hecke_eigensystem :
    HypothesesH → SatLink := by
  intro PH E _ _ _ a π
  have P := PH.toClassicalTheorems
  refine ⟨fun w σ hσ B => (satLoc P E a w σ).2 _ π.finPart ((locCompC P E a π w).2 σ hσ) B, ?_⟩
  exact ExLib.eventually_sat (satLoc P) π.finPart π.isSmooth_finPart fun w =>
    let ⟨⟨σ, hσ⟩, hi⟩ := locCompC P E a π w
    ⟨σ, hi σ hσ⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SolvablePolarizedRestriction
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.solvable_polarized_restriction :
    UpperTheory.V.Af.Sol.PolRes := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ l _ ι n r h
  obtain ⟨F₀, i1, i2, i3, i4, i5, i6, hF, μ, c, P, hμ, hs, hc, hp⟩ := h
  letI : Algebra F₀ M := ((algebraMap K M).comp (algebraMap F₀ K)).toAlgebra
  haveI : IsScalarTower F₀ K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower F₀ M Ω := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    simp [RingHom.algebraMap_toAlgebra, IsScalarTower.algebraMap_apply F₀ K Ω,
      IsScalarTower.algebraMap_apply K M Ω]
  refine ⟨F₀, i1, i2, inferInstance, inferInstance, this, i6, hF, μ, c, P, hμ, hs, hc, ?_⟩
  unfold IsPairing at hp ⊢
  intro t t' ht
  have e1 : ∀ u : G M Ω,
      AlgEquiv.restrictScalars F₀ (resG K M Ω u) = AlgEquiv.restrictScalars F₀ u := by
    intro u; ext x; rfl
  have e2 : ∀ u : G M Ω, resG F₀ M Ω u = resG F₀ K Ω (resG K M Ω u) := by
    intro u; ext x; rfl
  have key := hp (resG K M Ω t) (resG K M Ω t') (by rw [e1, e1]; exact ht)
  simpa [e2] using key
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalReciprocity
open UpperTheory.V.Af UpperTheory.V.Af.Gu

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem tw_sumList {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (s : ℝ) (L : List (WD h)) :
    (sumList L).lpTw s = sumList (L.map fun x => x.lpTw s) := by
  induction L with
  | nil =>
    change (WD.lpZero (h := h)).lpTw s = WD.lpZero (h := h)
    rw [WD.lpZero, WD.lpTw_mk]
    exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩
  | cons x L ih =>
    change (x.lpSum (sumList L)).lpTw s = (x.lpTw s).lpSum (sumList (L.map fun x => x.lpTw s))
    rw [WD.lpTw_sum, ih]

theorem UpperTheory.total_reciprocity :
    HypothesesH → RecTot := by
  intro H E Ω _ _ _ _ _ _ n c a d hn P w ρ σ _ hP hS τ e A h rc hrc
  have L := H.litN.loc
  have h1 := GlobalTheory.FormDict.RecTLaws.locProd_eq hrc hn σ τ e
  have h2 : ∀ i, rc (cls (ParLaws.toRep (σ i))) = sumList ((List.range (d i)).map fun k : ℕ =>
      (rc (cls (ParLaws.toRep (ρ i)))).lpTw (((d i : ℝ) - 1) / 2 - k)) := fun i => by
    have hd : ∑ _ : Fin (d i), a i = d i * a i := by simp
    exact GlobalTheory.T.local_langlands_speh_product _ _ _ w _ _ hrc (GlobalTheory.T.generic_unitary_dual_gl L.unit L.sq L.gen L.multi L.cos) L.cos (a i) (d i) _ hd (ρ i) (σ i)
      (hS i).1 (GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp E (a i) (P i) w (ρ i) (hP i))
      (GlobalTheory.DiscreteSpectrumCM.isSpehQuot_of_isSpeh hd (ρ i) (σ i) (hS i).2.2)
  rw [rec_algNorm hrc]
  change _ = (rc (cls (ParLaws.toRep τ))).lpTw _
  rw [h1, tw_sumList, List.map_ofFn]
  refine congrArg sumList (congrArg List.ofFn (funext fun i => ?_))
  rw [Function.comp_apply, h2, tw_sumList, List.map_map, List.ofFn_eq_map, ← List.map_coe_finRange_eq_range,
    List.map_map]
  refine congrArg sumList (List.map_congr_left fun k _ => ?_)
  simp only [Function.comp_apply, WD.lpTw_add]
  refine congrArg₂ WD.lpTw rfl ?_
  simp only [ex]
  push_cast
  ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open UpperTheory.V.Af UpperTheory.V.Af.Gu

private theorem theta_iso {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} {P : CuspSub E a} (h : P.IsCsd) :
    (GlobalTheory.ThetaPull.thetaSub P).Iso P := by
  obtain ⟨T, hT⟩ := h
  let L := (GlobalTheory.ThetaPull.pull E a).submoduleMap P.V
  refine ⟨L.symm.trans T, fun o φ => ?_⟩
  obtain ⟨φ, rfl⟩ := L.surjective φ
  have e : (GlobalTheory.ThetaPull.thetaSub P).op o (L φ) = L (P.op (thetaOp o) φ) :=
    Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1)
  rw [e]
  exact (congrArg T (L.symm_apply_apply _)).trans
    ((hT o φ).trans (congrArg (P.op o) (congrArg T (L.symm_apply_apply φ)).symm))

private theorem normV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) :
    normV (Bc.cPl w) = normV w := by
  change Nat.card (𝓞 E ⧸ (Bc.cPl w).asIdeal) = Nat.card (𝓞 E ⧸ w.asIdeal)
  rw [(GlobalTheory.Mem.Chr.conjPl_iff_comap _ _ _).1 (conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv w)]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (RingOfIntegers.mapRingEquiv _)
    (Ideal.map_comap_of_surjective _ (RingEquiv.surjective _) _).symm).toEquiv

private theorem qPow_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (s : ℝ) :
    (qPow (Bc.cPl w) s)⁻¹ = qPow w (-s) := by
  have e : qPow (Bc.cPl w) s = qPow w s := Units.ext (by rw [coe_qPow, coe_qPow, normV_cPl])
  rw [e, inv_eq_iff_mul_eq_one, ← qPow_add, add_neg_cancel, qPow_zero]

theorem UpperTheory.satake_parameters_complex_conjugate :
    SatConj := by
  intro E _ _ _ w
  refine ⟨fun a P hP B hB => ?_, fun c d S => ?_⟩
  · have e : CG.mk (GlobalTheory.ThetaPull.thetaSub P) = CG.mk P := Quotient.sound (theta_iso hP)
    exact e ▸ UpperTheory.theta_satake_parameters_inverse E a P w B hB
  · unfold satTot
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Multiset.coe_mapAddMonoidHom (fun x : ℂˣ => x⁻¹), map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Equiv.sum_comp Fin.revPerm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Multiset.coe_mapAddMonoidHom, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun x _ => ?_
    simp only [Function.comp_apply, mul_inv, qPow_cPl, Fin.revPerm_apply, Fin.val_rev]
    congr 2
    rw [Nat.cast_sub k.2]
    push_cast
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsoSumOfInjectiveEquivariantFamily
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.isoSum_of_injective_equivariant_family :
    ∀ (H M N : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (ρ : Representation ℂ H M) (ρ' : Representation ℂ H N) (Y : Submodule ℂ M) (Z : Submodule ℂ N) (τ : SmIrr H) (I : Type) [Finite I] (φ : I → M →ₗ[ℂ] N), IsoSum ρ' Z τ → (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) → (∀ i, ∀ y ∈ Y, φ i y ∈ Z) → (∀ i g, ∀ y ∈ Y, φ i (ρ g y) = ρ' g (φ i y)) → (∀ y ∈ Y, (∀ i, φ i y = 0) → y = 0) → IsoSum ρ Y τ := by
  intro H M N _ _ _ _ _ _ _ ρ ρ' Y Z τ I _ φ hZ hY hφ he hinj
  classical
  let := Fintype.ofFinite I
  let π : Representation ℂ H Y := (⟨Y, fun g v hv => hY g v hv⟩ : Subrepresentation ρ).toRepresentation
  let P : Representation ℂ H (I → N) :=
    { toFun := fun g => (ρ' g).compLeft I
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let j : Y →ₗ[ℂ] (I → N) := LinearMap.pi fun i => φ i ∘ₗ Y.subtype
  have hj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    exact Subtype.ext (hinj y y.2 fun i => congrFun hy i)
  have hs : ∀ i g x, LinearMap.single ℂ (fun _ : I => N) i (ρ' g x) = P g (LinearMap.single ℂ (fun _ : I => N) i x) := by
    intro i g x
    funext k
    change (Pi.single i (ρ' g x) : I → N) k = ρ' g ((Pi.single i x : I → N) k)
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  have hsing : ∀ i, ∀ z ∈ Z, LinearMap.single ℂ (fun _ : I => N) i z ∈
      ⨆ f : {f : τ.V →ₗ[ℂ] (I → N) // ∀ g v, f (τ.ρ g v) = P g (f v)}, LinearMap.range f.1 := by
    intro i z hz
    refine Submodule.iSup_induction _ (motive := fun z => LinearMap.single ℂ (fun _ : I => N) i z ∈ _) (hZ hz) ?_ ?_ ?_
    · rintro f _ ⟨s, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨LinearMap.single ℂ (fun _ : I => N) i ∘ₗ f.1, fun g v => by
        rw [LinearMap.comp_apply, f.2.1, hs]; rfl⟩ ⟨s, rfl⟩
    · rw [map_zero]; exact zero_mem _
    · intro a b ha hb
      rw [map_add]; exact add_mem ha hb
  have key := UpperTheory.V.PiLin.iso_sub τ.ρ π P τ.irred j hj (fun g y => funext fun i => he i g y y.2) (fun y => by
    rw [← Finset.univ_sum_single (j y)]
    exact Submodule.sum_mem _ fun i _ => hsing i _ (hφ i y y.2))
  intro y hy
  refine Submodule.iSup_induction _ (motive := fun z : Y => (z : M) ∈ _) (key ⟨y, hy⟩) ?_ ?_ ?_
  · rintro f _ ⟨s, rfl⟩
    refine Submodule.mem_iSup_of_mem ⟨Y.subtype ∘ₗ f.1, fun g v => ?_, ?_⟩ ⟨s, rfl⟩
    · exact congrArg Subtype.val (f.2 g v)
    · rintro _ ⟨v, rfl⟩; exact (f.1 v).2
  · exact zero_mem _
  · intro a b ha hb
    exact add_mem ha hb
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpehParameterStrings
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open GlobalTheory.DefiniteBC

private theorem spehInf_eq_sum_shifted_map (d : ℕ) (m : Multiset ℂ) :
    spehInf d m = ∑ k : Fin d, Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) m := by
  unfold spehInf
  rw [Fin.sum_univ_eq_sum_range (fun k => Multiset.map (fun x => x + (((d:ℂ) - 1) / 2 - (k:ℂ))) m) d]
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe, Multiset.sum_coe]

private theorem infOfWeight_nodup' (n : ℕ) (lam : Formalism.BasicNotions.DomWeight n) :
    (GlobalTheory.UnitaryBC.infOfWeight lam).Nodup := by
  unfold GlobalTheory.UnitaryBC.infOfWeight
  refine Multiset.Nodup.map ?_ Finset.univ.nodup
  intro a b h
  have h2 : ((lam.w a - (a:ℕ) : ℤ) : ℂ) = ((lam.w b - (b:ℕ) : ℤ) : ℂ) := by
    push_cast
    linear_combination h
  have h3 : lam.w a - (a:ℕ) = lam.w b - (b:ℕ) := by exact_mod_cast h2
  rcases lt_trichotomy a b with hab | hab | hab
  · have := lam.anti hab.le
    have : (a:ℕ) < (b:ℕ) := hab
    omega
  · exact hab
  · have := lam.anti hab.le
    have : (b:ℕ) < (a:ℕ) := hab
    omega

private theorem multiset_map_finset_sum {ι : Type*} (s : Finset ι) (g : ℂ → ℂ) (f : ι → Multiset ℂ) :
    Multiset.map g (∑ i ∈ s, f i) = ∑ i ∈ s, Multiset.map g (f i) :=
  map_sum (Multiset.mapAddMonoidHom g) f s

theorem UpperTheory.speh_parameter_strings :
    Strings := by
  intro n c d m lam h
  have hnd := infOfWeight_nodup' n lam
  refine ⟨fun i k => ?_, ?_⟩
  · have hle1 : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ spehInf (d i) (m i) := by
      rw [spehInf_eq_sum_shifted_map]
      exact Finset.single_le_sum (f := fun k : Fin (d i) => Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i))
        (fun _ _ => Multiset.zero_le _) (Finset.mem_univ k)
    have hle2 : spehInf (d i) (m i) ≤ ∑ j, spehInf (d j) (m j) :=
      Finset.single_le_sum (f := fun j => spehInf (d j) (m j)) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
    have hle : Multiset.map (fun x => x + (((d i:ℂ) - 1) / 2 - ((k:ℕ):ℂ))) (m i) ≤ GlobalTheory.UnitaryBC.infOfWeight lam :=
      h ▸ hle1.trans hle2
    refine ⟨(Multiset.nodup_of_le hle hnd).of_map _, fun z hz => ?_⟩
    have hmem := Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz)
    unfold GlobalTheory.UnitaryBC.infOfWeight at hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨j, -, hj⟩ := hmem
    refine ⟨lam.w j - (j:ℕ), ?_⟩
    unfold ex
    push_cast
    linear_combination (-1 : ℂ) * hj
  · rw [← h, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [spehInf_eq_sum_shifted_map, multiset_map_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun z _ => ?_
    simp only [Function.comp_apply]
    unfold ex
    push_cast
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SignAtInfinityOfParallelWeight
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

open ReciprocityTheory.Neutral.Bridge.HCFR

private theorem UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal {F : Type} [Field F] [NumberField F] (a : (F →+* ℂ) → ℤ)
    (a0 : ℤ) (ha : ∀ φ, a φ = a0) (w : InfinitePlace F) (hw : w.IsReal) :
    infPow a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = (-1) ^ a0 := by
  have hcont : Continuous (Complex.ofRealHom.comp
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw)) :=
    Complex.continuous_ofReal.comp
      (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).continuous
  let i0 : {i : w.Completion →+* ℂ // Continuous i} := ⟨_, hcont⟩
  have huniq : ∀ i : {i : w.Completion →+* ℂ // Continuous i}, i = i0 := by
    intro i
    apply Subtype.ext
    ext x
    let E := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hw
    let g : ℝ →+* ℂ := (i : w.Completion →+* ℂ).comp
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toRingHom
    have hg : Continuous g := i.2.comp E.symm.continuous
    have hg' := Complex.ringHom_eq_ofReal_of_continuous hg
    have hx : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm
        (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x) = x :=
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm_apply_apply x
    have := congrArg (fun f : ℝ →+* ℂ => f
      (NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hw x)) hg'
    simp only [g, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hx] at this
    simpa [i0] using this
  unfold infPow
  rw [Finset.prod_eq_single w]
  · rw [finprod_eq_single _ i0 (fun j hj => absurd (huniq j) hj)]
    rw [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_self, ha]
    simp
  · intro w' _ hne
    simp [ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_fst_ne F w w' hne]
  · intro h
    exact absurd (Finset.mem_univ w) h

theorem UpperTheory.sign_at_infinity_of_parallel_weight :
    UpperTheory.V.Af.Sol.Parallel → UpperTheory.V.Af.Sol.SignOf := by
  intro hP F Ω _ _ _ _ _ _ l _ ι χ μ hμ hs v v'
  obtain ⟨-, art, a, hart, halg, hlad⟩ := hμ
  have hpar := hP F χ a halg
  have key : ∀ w : InfinitePlace F, ∃ c : G F Ω, IsConjEl c ∧
      ((χ.locInf w (-1) : ℂˣ) : ℂ) = ι (μ c) * (-1) ^ (a v.embedding) := by
    intro w
    obtain ⟨j, c, hc, hw⟩ := GlobalTheory.HilbertFromArtin.exists_conj (Ω := Ω) w
      (NumberField.IsTotallyReal.isReal w)
    refine ⟨c, ⟨j, hc⟩, ?_⟩
    have hart' := GlobalTheory.HilbertFromArtin.art_sign_eq hart j c hc
    rw [hw] at hart'
    have h := hlad _ c hart'
    have hl : lPow ι a (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F w (-1)) = 1 := by
      simp [GlobalTheory.HeckeGal.lPow, ReciprocityTheory.Neutral.Bridge.HCFR.infIdele_snd, GlobalTheory.HeckeGal.locPow_one]
    rw [hl, mul_one, UpperTheory.infPow_infIdele_neg_one_of_const_of_isReal a (a v.embedding) (fun φ => hpar φ v.embedding) w
      (NumberField.IsTotallyReal.isReal w)] at h
    have h2 := congrArg ι h
    rw [RingEquiv.apply_symm_apply] at h2
    rw [h2]
    have hne : ((-1 : ℂ) ^ (a v.embedding)) ≠ 0 := zpow_ne_zero _ (by norm_num)
    rw [mul_assoc, inv_mul_cancel₀ hne, mul_one]
    rfl
  obtain ⟨c, hc, hcv⟩ := key v
  obtain ⟨c', hc', hcv'⟩ := key v'
  apply Units.ext
  rw [hcv, hcv', hs c c' hc hc']
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TwistLocalComponentsCompatible
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLaws GlobalTheory.LocGL
open UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.twist_local_components_compatible :
    TwistLoc := by
  intro E _ _ _ a P t w ρ hρ
  refine ⟨_, hρ.twist (GlobalTheory.HeckeGal.Model.absPow E t), ?_⟩
  refine (GlobalTheory.LocGL.IrrGL.tw_of ρ.ρ ρ.smooth ρ.irred _
    (isSmoothChar_loc (GlobalTheory.HeckeGal.Model.absPow E t) w)).symm.trans ?_
  unfold GlobalTheory.LocGL.IrrGL.nu
  congr 1
  exact GlobalTheory.HeightCounting.Blocks.loc_of_isAbsPow (GlobalTheory.HeckeGal.Model.absPow_isAbsPow E t) w
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepDirectSumAwayFromPlaces
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.SumParam

theorem UpperTheory.galoisRep_direct_sum_away_from_places :
    SumAway := by
  intro E Ω _ _ _ _ _ l _ ι a b r r' hr hr' w hl A h x x' hx hx'
  have c : Continuous fun g => ((r g : GL (Fin a) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin a) (Fin a) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr
  have c' : Continuous fun g => ((r' g : GL (Fin b) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin b) (Fin b) (Formalism.ConjugateSelfDual.Qbar l)) :=
    Units.continuous_val.comp hr'
  have cs : Continuous fun g => ((Formalism.MainNotions.SumRepresentations.At.sumRep r r' g : GL (Fin (a + b)) (Formalism.ConjugateSelfDual.Qbar l)) : Matrix (Fin (a + b)) (Fin (a + b)) (Formalism.ConjugateSelfDual.Qbar l)) := by
    simp only [coe_sumRep]
    exact (c.matrix_fromBlocks continuous_const continuous_const c').matrix_reindex _ _
  rw [← hx.wdOf_eq hl, ← hx'.wdOf_eq hl, ← wdOf_sumRep hl ι r r' c c']
  exact isWDOf_wdOf hl ι cs
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisCharacterFrobeniusCompatibility
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.galois_character_frobenius_compatibility :
    UpperTheory.V.Af.Sol.CharFrob := by
  intro F Ω _ _ _ _ _ l _ ι χ μ hχ
  obtain ⟨_, art, a, hart, _, hL⟩ := hχ
  have hl : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (l : 𝓞 F) ∉ v.asIdeal := by
    have hne : Ideal.span {(l : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
    refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hne).subset ?_)
    intro v hv
    simp only [Set.mem_setOf_eq, not_not] at hv ⊢
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hv
  filter_upwards [GlobalTheory.GalChar.unr_ae χ, hl] with v hu hv
  refine ⟨hu, fun A hA => ⟨(GlobalTheory.HeckeGal.IsLAdicOf.unr_iff hart hL (Or.inl hv) hA).2 hu, fun σ hσ => ?_⟩⟩
  have h := GlobalTheory.HeckeGal.IsLAdicOf.frob_unr hart hL (Or.inl hv) hu hA hσ
  rw [map_inv, Units.val_inv_eq_inv_val, h, inv_inv, RingEquiv.apply_symm_apply]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeInvariantOfFrobConjOfEigenvalueBasic
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

theorem UpperTheory.satake_invariant_of_frobConj_of_eigenvalue_basic :
    UpperTheory.V.Af.Sol.FrobConj → UpperTheory.V.Af.Sol.EigBasic → UpperTheory.V.Af.Sol.InvSat := by
  intro hFC hEB K M Ω _ _ _ _ _ _ _ _ _ _ _ _ l _ ι n r sat' hatt
  have hbad := Filter.eventually_cofinite.1 hatt.2
  have himg := hbad.image (fun w : HeightOneSpectrum (𝓞 M) => w.under (𝓞 K))
  have hev := (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M) himg.compl_mem_cofinite
  filter_upwards [hev] with w hw w' hw'
  have good : ∀ u : HeightOneSpectrum (𝓞 M), u.under (𝓞 K) = w.under (𝓞 K) →
      ∃ B, sat' u B ∧ FrobEig ι (r.comp (resG K M Ω)) u (algSat n (normV u) B) := by
    intro u hu
    by_contra hn
    exact hw ⟨u, hn, hu⟩
  obtain ⟨B, hB, hE⟩ := good w rfl
  obtain ⟨B', hB', hE'⟩ := good w' hw'
  obtain ⟨hN, hT⟩ := hFC K M Ω l ι n r w w' hw'
  have h1 := hT _ hE
  rw [← hN] at h1
  have hBB : B = B' := (hEB M Ω l ι w').2.2 n _ B B' h1 hE'
  exact ⟨B, hB, hBB ▸ hB'⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumTwoOfHodgeTate
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.sum_two_of_hodge_tate :
    HypothesesH → SumAway → SumHT → SumTwo := by
  intro H hA hT E Ω _ _ _ _ _ l _ ι a b r r' p p' HT HT' C C'
  obtain ⟨T⟩ := Loc.tiedP l
  have hv := GlobalTheory.BCGal.cont_sumRep r r' (Units.continuous_val.comp C.cont) (Units.continuous_val.comp C'.cont)
  have hc : Continuous (Formalism.MainNotions.SumRepresentations.At.sumRep r r') := by
    refine Units.continuous_iff.2 ⟨hv, ?_⟩
    simp only [← map_inv]
    exact hv.comp continuous_inv
  have hht := hT E Ω l a b r r' C.cont C'.cont HT HT' C.ht C'.ht
  refine ⟨hc, GlobalTheory.BCGal.ss_sumRep r r' C.ss C'.ss, hht, fun w A h rc hrc => ?_⟩
  obtain ⟨a1, b1⟩ := C.par w A h rc hrc
  obtain ⟨a2, b2⟩ := C'.par w A h rc hrc
  refine ⟨fun hw => hA E Ω l ι a b r r' C.cont C'.cont w hw A h _ _ (a1 hw) (a2 hw), fun O _ _ _ Bw hj => ?_⟩
  obtain ⟨p1, e1⟩ := b1 O Bw hj
  obtain ⟨p2, e2⟩ := b2 O Bw hj
  have p3 : IsPstAt (Loc.PP l) Bw ((Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype) := by
    refine H.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (hc.comp continuous_subtype_val)) ?_
    exact (hht w A h O Bw hj).1
  refine ⟨p3, ?_⟩
  have e : (Formalism.MainNotions.SumRepresentations.At.sumRep r r').comp (Dec (F := E) A).subtype =
      Formalism.MainNotions.SumRepresentations.At.sumRep (r.comp (Dec (F := E) A).subtype) (r'.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  rw [e] at p3 ⊢
  rw [GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l _ _ ⟨T⟩ ι E Ω A w O Bw h hj a b _ _ p1 p2 p3]
  exact (Lev.ssCalc E Ω A w h).2.1 _ _ _ _ e1 e2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CompatiblePolarizationOfLink
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem UpperTheory.compatible_polarization_of_link :
    HypothesesH → CompatCsd → SatLink → CompatPol := by
  intro PH hC hS E Ω _ _ _ _ _ _ l _ ι a ha P χ ξ m hreg hpol hξ hd σ hσ
  have Pr := PH.toClassicalTheorems
  obtain ⟨r, wt, HT, H⟩ := (GlobalTheory.T.local_global_of_gelfand_kazhdan Pr.litN.aut.gk).2 Pr.litN.aut.gal E Ω l ι a ha P χ hreg hpol
  have hatt : AttC ι r P := by
    refine ⟨H.ss, (((hS E a P).2).and (eventually_not_mem E l)).mono ?_⟩
    rintro w ⟨⟨B, hB⟩, hw⟩
    exact ⟨B, hB, satFrob Pr E Ω l ι a r H.cont w hw (σ w) B (((hS E a P).1 w _ (hσ w) B).1 hB)
      fun A h rc hrc => H.away w hw A h rc hrc _ (hσ w)⟩
  obtain ⟨art, hart⟩ := Pr.litN.aut.art E Ω
  obtain ⟨μ, hμc, hμ⟩ := hart.exists_isLAdicOf ι (isAlgPos_of_isAlg hξ)
  have hL := hC E Ω l ι a ha (tw r μ) (P.twist ξ) (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a _ μ H.cont hμc) (regAlg_twist hreg hξ) hd
    (Cq.attTwist E Ω l ι a r P hatt art ξ m μ hart hμ)
  obtain ⟨T⟩ := Loc.tiedP l
  refine ⟨r, HT, ⟨H.cont, H.ss, fun w A h O _ _ _ Bw hj => ?_, fun w A h rc hrc => ⟨fun hw => ?_, fun O _ _ _ Bw hj => ?_⟩⟩,
    H.weights⟩
  · exact ⟨(H.above _ _ ⟨T⟩ w A h O Bw hj).deRham, (H.above _ _ ⟨T⟩ w A h O Bw hj).jumps⟩
  · exact H.away w hw A h rc hrc _ (hσ w)
  · have hpst : IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := E) A).subtype) :=
      Pr.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (H.cont.comp continuous_subtype_val))
        (H.above _ _ ⟨T⟩ w A h O Bw hj).deRham
    obtain ⟨c1, c2⟩ := (hL w _ ((hσ w).twist ξ) A h rc hrc).2 O Bw hj
    exact ⟨hpst, Lev.untwistS Pr.litN.aut.chA Pr.litN.aut.chW Pr.litN.aut.berger E Ω l ι a r H.cont art ξ m μ hart
      (isAlgPos_of_isAlg hξ) hμc hμ w A h O Bw hj hpst c1 (σ w) rc hrc c2⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SumFamilyOfReductions
open UpperTheory.V.Af UpperTheory.V.Af.Gu
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.sum_family_of_reductions :
    SumTwo → SumRed → SumFam := by
  intro h2 hred E Ω _ _ _ _ _ l _ ι c hc
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  clear hc
  induction c with
  | zero =>
    intro N hN n hn r p HT H
    have hn' : N 0 = n := by simpa using hn
    subst hn'
    refine ⟨r 0, ⟨(H 0).cont, (H 0).ss, ?_, fun w => ((H 0).par w).congr fun A h rc _ => ?_⟩, fun hi => ⟨rfl, fun i => ?_⟩⟩
    · have e : (fun τ => ∑ i, HT i τ) = HT 0 := by
        funext τ
        simp
      rw [e]
      exact (H 0).ht
    · simp [sumList, WD.lpSum_zero]
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact hi
  | succ c ih =>
    intro N hN n hn r p HT H
    rw [Fin.sum_univ_succ] at hn
    subst hn
    obtain ⟨R, hR, -⟩ := ih (fun i => N i.succ) (fun i => hN i.succ) _ rfl (fun i => r i.succ) (fun i => p i.succ)
      (fun i => HT i.succ) (fun i => H i.succ)
    have hS := h2 E Ω l ι _ _ (r 0) R _ _ _ _ (H 0) hR
    refine ⟨Formalism.MainNotions.SumRepresentations.At.sumRep (r 0) R, ⟨hS.cont, hS.ss, ?_, fun w => (hS.par w).congr fun A h rc _ => ?_⟩, fun hi => ?_⟩
    · have e : (fun τ => ∑ i, HT i τ) = fun τ => HT 0 τ + ∑ i : Fin (c + 1), HT i.succ τ := by
        funext τ
        rw [Fin.sum_univ_succ]
      rw [e]
      exact hS.ht
    · rw [List.ofFn_succ (f := fun i => p i w A h rc)]
      rfl
    · refine absurd hi (hred _ _ _ _ _ _ (hN 0) ?_)
      exact le_trans (hN (Fin.succ 0)) (Finset.single_le_sum (f := fun i : Fin (c + 1) => N i.succ) (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0))
end
