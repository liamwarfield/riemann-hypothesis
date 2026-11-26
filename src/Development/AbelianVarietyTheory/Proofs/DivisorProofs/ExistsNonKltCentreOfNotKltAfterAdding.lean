module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingHeckeTranslateEqZeta
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAdding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAdding
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep.Centre

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem centreAt_of_dominatesStalk {E : DivOver p} {z : X} (h : DominatesStalk E.ring z) :
    CentreAt E z := by
  refine ⟨by rintro _ ⟨a, rfl⟩; exact h.1 a, ?_⟩
  rintro f ⟨a, ha⟩ h0
  have hinv : ((f⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring :=
    (E.ord_nonneg_iff f⁻¹).1 (by rw [E.ord_inv, h0]; simp)
  have hu : IsUnit a := by
    by_contra hu
    have h1 := (E.ring.coe_mem_nonunits_iff (a := ⟨_, h.1 a⟩)).mp (h.2 a hu)
    refine h1 (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))
    change algebraMap _ X.functionField a * _ = 1
    rw [ha]
    exact f.mul_inv
  obtain ⟨u, rfl⟩ := hu
  refine ⟨((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z), ?_⟩
  have e : algebraMap _ X.functionField
      ((u⁻¹ : (X.presheaf.stalk z)ˣ) : X.presheaf.stalk z) * (f : X.functionField) = 1 := by
    rw [← ha, ← map_mul, Units.inv_mul, map_one]
  exact (Units.inv_eq_of_mul_eq_one_left e).symm

theorem exists_centreAt {E : DivOver p} {x : X} (h : E.Through x) :
    ∃ z, z ⤳ x ∧ CentreAt E z :=
  have ⟨z, hz, hd⟩ := exists_specializes_dominatesStalk_of_regAt X E.ring x h
  ⟨z, hz, centreAt_of_dominatesStalk hd⟩

theorem exists_isLogEqn_add [IsLocallyNoetherian X] {n : ℕ} {Δ D : X → ℚ} {η : RatForms p n}
    {x : X} {m : ℕ} {g : X.functionFieldˣ} (hD : IsQCart D) (hm : 0 < m)
    (hg : IsLogEqn p Δ η x m g) :
    ∃ (m' : ℕ) (g' : X.functionFieldˣ), 0 < m' ∧ IsLogEqn p (Δ + D) η x m' g' := by
  obtain ⟨r, D₀, hr, -, rfl⟩ := hD
  obtain ⟨d, hd⟩ := D₀.exists_isEqn x
  obtain ⟨V, hV, hdV⟩ := hd.exists_nhds
  refine ⟨m * r, g ^ r * d ^ m, Nat.mul_pos hm hr, fun z hz E hE => ?_⟩
  have h1 := (hdV z (hz.mem_open V.isOpen hV)).mult_eq
  rw [← hE.ord_eq] at h1
  have h2 := hg z hz E hE
  have : (r : ℚ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [E.ord_mul, E.ord_pow, E.ord_pow, Pi.add_apply, qWeil, h1]
  push_cast
  rw [← h2]
  field_simp
  ring

theorem exists_isNkltCentre : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ KltAt p n (Δ + D) x →
    ∃ z, z ⤳ x ∧ IsNkltCentre p n (Δ + D) z := by
  intro X _ _ _ p n hp hn Δ D x hD hk hnk
  haveI : IsProper p := ((isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp).1
  obtain ⟨η, m, g, hη, hm, hg, -⟩ := hk
  obtain ⟨m', g', hm', hg'⟩ := exists_isLogEqn_add hD hm hg
  rw [hg'.kltAt_iff hn hη hm'] at hnk
  push_neg at hnk
  obtain ⟨E, hE, hd⟩ := hnk
  obtain ⟨z, hz, hc⟩ := exists_centreAt hE
  exact ⟨z, hz, E, η, m', g', hη, hm', fun w hw => hg' w (hw.trans hz), hc, hd⟩

end GlobalTheory.PairStep.Centre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAddingStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonKltCentre_of_not_klt_after_adding : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (Δ D : X → ℚ) (x : X), IsQCart D → KltAt p n Δ x → ¬ KltAt p n (Δ + D) x → ∃ z, z ⤳ x ∧ IsNkltCentre p n (Δ + D) z := by
  first | exact @GlobalTheory.PairStep.Centre.exists_isNkltCentre | exact GlobalTheory.PairStep.Centre.exists_isNkltCentre | (intros; apply GlobalTheory.PairStep.Centre.exists_isNkltCentre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldHomFlatSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldHomFlatSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem dualNumber_map_flat_surjective : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ ψ : DualNumber k →+* DualNumber K, ψ.comp (dnInl k) = (dnInl K).comp φ ∧ (dnFst K).comp ψ = φ.comp (dnFst k) ∧ Flat (spMap ψ) ∧ Surjective (spMap ψ) := by
  intro k K _ _ φ
  letI : Algebra k K := φ.toAlgebra
  let ψ₀ : DualNumber k →ₐ[k] DualNumber K :=
    DualNumber.lift ⟨(Algebra.ofId k (DualNumber K), DualNumber.eps),
      by simp, fun _ ↦ Commute.all _ _⟩
  have hψ₀ : ∀ x : DualNumber k, ψ₀ x = TrivSqZeroExt.inl (φ x.fst) + TrivSqZeroExt.inr (φ x.snd) := by
    intro x
    rw [DualNumber.lift_apply_apply]
    ext <;> simp [Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  let j : K →ₐ[k] DualNumber K := TrivSqZeroExt.inlAlgHom k K K
  let g : TensorProduct k (DualNumber k) K →ₐ[k] DualNumber K :=
    Algebra.TensorProduct.lift ψ₀ j (fun _ _ ↦ Commute.all _ _)
  let h : DualNumber K → TensorProduct k (DualNumber k) K := fun x ↦
    (1 : DualNumber k) ⊗ₜ[k] x.fst + (DualNumber.eps : DualNumber k) ⊗ₜ[k] x.snd
  have hadd : ∀ u v, h (u + v) = h u + h v := by
    intro u v
    simp only [h, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, TensorProduct.tmul_add]
    abel
  have hgh : ∀ x, g (h x) = x := by
    intro x
    simp only [h, g, map_add (f := _), Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
    ext <;> simp [j, hψ₀]
  have hhg : ∀ x, h (g x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [h]
    | tmul a b =>
      have e1 : a = TrivSqZeroExt.fst a • (1 : DualNumber k) + TrivSqZeroExt.snd a • DualNumber.eps := by
        ext <;> simp
      have f1 : TrivSqZeroExt.fst (ψ₀ a * j b) = TrivSqZeroExt.fst a • b := by
        simp [hψ₀, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
      have f2 : TrivSqZeroExt.snd (ψ₀ a * j b) = TrivSqZeroExt.snd a • b := by
        simp [hψ₀, j, Algebra.smul_def, RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
      show (1 : DualNumber k) ⊗ₜ[k] TrivSqZeroExt.fst (ψ₀ a * j b) +
        (DualNumber.eps : DualNumber k) ⊗ₜ[k] TrivSqZeroExt.snd (ψ₀ a * j b) = a ⊗ₜ[k] b
      rw [f1, f2, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, ← TensorProduct.add_tmul, ← e1]
    | add x y hx hy => rw [map_add (f := _), hadd, hx, hy]
  have hbij : Function.Bijective g := Function.bijective_iff_has_inverse.2 ⟨h, hhg, hgh⟩
  refine ⟨ψ₀.toRingHom, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a ↦ ?_
    ext <;> simp [hψ₀, TrivSqZeroExt.algebraMap_eq_inl', RingHom.algebraMap_toAlgebra]
  · refine RingHom.ext fun x ↦ ?_
    simp [hψ₀]
  · have hc : ψ₀.toRingHom = g.toRingHom.comp (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)) := by
      refine RingHom.ext fun x ↦ ?_
      simp [g, j, Algebra.TensorProduct.algebraMap_apply]
    have hff : (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)).FaithfullyFlat :=
      RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
    have h1 := (flat_and_surjective_SpecMap_iff
      (CommRingCat.ofHom (algebraMap (DualNumber k) (TensorProduct k (DualNumber k) K)))).2 hff
    have := h1.1
    have := h1.2
    let eR : TensorProduct k (DualNumber k) K ≃+* DualNumber K := (AlgEquiv.ofBijective g hbij).toRingEquiv
    have hi : IsIso (Spec.map (CommRingCat.ofHom g.toRingHom)) :=
      inferInstanceAs (IsIso (Spec.map eR.toCommRingCatIso.hom))
    rw [hc, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    exact ⟨inferInstance, inferInstance⟩

end GlobalTheory.DualOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberFieldHomFlatSurjectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualNumber_fieldHom_flat_surjective : ∀ (k K : Type) [Field k] [Field K] (φ : k →+* K), ∃ ψ : DualNumber k →+* DualNumber K, ψ.comp (dnInl k) = (dnInl K).comp φ ∧ (dnFst K).comp ψ = φ.comp (dnFst k) ∧ Flat (spMap ψ) ∧ Surjective (spMap ψ) := by
  first | exact @GlobalTheory.DualOpen.dualNumber_map_flat_surjective | exact GlobalTheory.DualOpen.dualNumber_map_flat_surjective | (intros; apply GlobalTheory.DualOpen.dualNumber_map_flat_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFr
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.SmoothStalk

theorem finitePresentation_algX {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [LocallyOfFinitePresentation p]
    (U : X.affineOpens) : (algX p U.1).FinitePresentation := by
  have h := HasRingHomProperty.appLE @LocallyOfFinitePresentation p inferInstance ⟨⊤, isAffineOpen_top _⟩ U le_top
  refine RingHom.FinitePresentation.comp h ?_
  refine RingHom.FinitePresentation.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective ?_
  have : RingHom.ker (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective
  rw [this]; exact Submodule.fg_bot

theorem smooth_stalk : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x : X) (hx : x ∈ U.1), letI := (algX p U.1).toAlgebra; letI := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra; Algebra.FinitePresentation k Γ(X, U.1) ∧ Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = n := by
  intro k _ X p n _ U x hx
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  refine ⟨?_, ?_⟩
  · exact finitePresentation_algX p U
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) p ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(X, U.1)), x ∈ X.basicOpen (t : Γ(X, U.1)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff U.2).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen U.2 (t : Γ(X, U.1))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(X, X.basicOpen (t : Γ(X, U.1))))
  set V := X.basicOpen (t : Γ(X, U.1))
  have hVU : V ≤ U.1 := X.basicOpen_le _
  have h₂ : (algX p V).IsStandardSmoothOfRelativeDimension n := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p hVU]
    exact h₁
  have hV : IsAffineOpen V := U.2.basicOpen _
  letI iA : Algebra k Γ(X, V) := (algX p V).toAlgebra
  letI iS : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxt).hom.toAlgebra
  letI iK : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra
  have hcomp : ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)) = (X.presheaf.germ V x hxt).hom.comp (algX p V) := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p hVU, ← RingHom.comp_assoc]
    congr 1
    rw [← X.presheaf.germ_res (homOfLE hVU) x hxt]
    rfl
  haveI : IsScalarTower k Γ(X, V) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' hcomp
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V) := h₂
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxt⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxt⟩
  haveI : Algebra.FormallyEtale Γ(X, V) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf ⟨x, hxt⟩).asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, V) (X.presheaf.stalk x)
  haveI : Nontrivial Γ(X, V) := (X.presheaf.germ V x hxt).hom.domain_nontrivial
  haveI : Module.Free Γ(X, V) Ω[Γ(X, V)⁄k] := by
    obtain ⟨ι, σ, _, _, P, -⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V)›.out
    exact P.free_kaehlerDifferential
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := Γ(X, V)) n
  haveI : Module.Finite Γ(X, V) Ω[Γ(X, V)⁄k] := Module.finite_of_rank_eq_nat hr
  have hfr : Module.finrank Γ(X, V) Ω[Γ(X, V)⁄k] = n := Module.finrank_eq_of_rank_eq hr
  let b := Module.Free.chooseBasis Γ(X, V) Ω[Γ(X, V)⁄k]
  let b' := IsBaseChange.basis b hbc
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  rw [Module.finrank_eq_card_basis b', ← hfr, Module.finrank_eq_card_basis b]

end GlobalTheory.SmoothStalk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFrStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_affineOpen_finitePresentation_stalkKaehler_free_rank : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x : X) (hx : x ∈ U.1), letI := (algX p U.1).toAlgebra; letI := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra; Algebra.FinitePresentation k Γ(X, U.1) ∧ Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = n := by
  first | exact @GlobalTheory.SmoothStalk.smooth_stalk | exact GlobalTheory.SmoothStalk.smooth_stalk | (intros; apply GlobalTheory.SmoothStalk.smooth_stalk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChevalleyExistsLeSupMaximalIdealPowOfAntitoneStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChevalleyExistsLeSupMaximalIdealPowOfAntitone
open IsLocalRing

namespace GlobalTheory.Chevalley

theorem exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion (A : Type) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] (F : AdicCompletion (maximalIdeal A) A) (n : ℕ) :
    ∃ a : A, F - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal A) A n F)
  refine ⟨a, ?_⟩
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal A).fg_of_isNoetherianRing,
    LinearMap.mem_ker, map_sub, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
  first
  | rw [Submodule.mkQ_apply, Algebra.algebraMap_self, RingHom.id_apply, ← ha, sub_self]
  | simp [← ha]

theorem exists_le_sup_maximalIdeal_pow_of_antitone :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A),
      Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) →
      (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A),
        (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈
          maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) →
        (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) →
      ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by
  intro A _ _ _ K J hK hmK hJ k
  let B := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing B := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : Module.Flat A B := AdicCompletion.flat_of_isNoetherian _
  haveI : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let f := algebraMap A B
  have hmB : ∀ n, maximalIdeal B ^ n = (maximalIdeal A ^ n).map f := fun n ↦ by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_pow]
  let K' : ℕ → Ideal B := fun e ↦ (K e).map f
  have hK' : Antitone K' := fun i j hij ↦ Ideal.map_mono (hK hij)
  have hmK' : ∀ e, maximalIdeal B ^ e ≤ K' e := fun e ↦ by
    rw [hmB]; exact Ideal.map_mono (hmK e)
  let N : Ideal B := ⨅ e, K' e
  have hNK : ∀ e, N ≤ K' e := fun e ↦ iInf_le _ e
  have hNJ : N ≤ J.map f := by
    intro F hF
    choose a ha using exists_sub_algebraMap_mem_maximalIdeal_pow_adicCompletion A F
    refine hJ F a ha fun n ↦ ?_
    have h1 : f (a n) ∈ K' n := by
      have : f (a n) = F - (F - f (a n)) := by abel
      rw [this]
      exact Submodule.sub_mem _ (hNK n hF) (hmK' n (ha n))
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (K n)]
    exact h1
  let P : ℕ → Submodule B (B ⧸ N) := fun e ↦ Submodule.map (Submodule.mkQ N) (K' e : Submodule B B)
  have hdir : Directed (· ≥ ·) P := fun i j ↦
    ⟨max i j, Submodule.map_mono (hK' (le_max_left i j)), Submodule.map_mono (hK' (le_max_right i j))⟩
  have hbot : (⨅ e, P e) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N x
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rw [Submodule.mem_iInf] at hx ⊢
    intro e
    have := Submodule.mem_comap.2 (hx e)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 (hNK e)] at this
    exact this
  obtain ⟨e, he⟩ := exists_le_maximalIdeal_pow_smul_of_directed B (B ⧸ N) ℕ P ⟨0⟩ hdir hbot k
  refine ⟨e, ?_⟩
  have hsm : (maximalIdeal B ^ k • (⊤ : Submodule B (B ⧸ N))) =
      Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B) := by
    have hI : (maximalIdeal B ^ k • (⊤ : Submodule B B)) = (maximalIdeal B ^ k : Submodule B B) := by
      rw [smul_eq_mul, Ideal.mul_top]
    rw [← Submodule.range_mkQ N, LinearMap.range_eq_map, ← Submodule.map_smul'', hI]
  have h2 : K' e ≤ maximalIdeal B ^ k ⊔ N := by
    intro y hy
    have h := he (Submodule.mem_map_of_mem (f := Submodule.mkQ N) hy)
    rw [hsm] at h
    have h' : y ∈ Submodule.comap (Submodule.mkQ N)
        (Submodule.map (Submodule.mkQ N) (maximalIdeal B ^ k : Submodule B B)) := h
    rw [Submodule.comap_map_mkQ] at h'
    rw [sup_comm]; exact h'
  have h3 : K' e ≤ (J ⊔ maximalIdeal A ^ k).map f := by
    rw [Ideal.map_sup, ← hmB]
    exact h2.trans (sup_le le_sup_right (hNJ.trans le_sup_left))
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (J ⊔ maximalIdeal A ^ k)]
  exact Ideal.map_le_iff_le_comap.1 h3

end GlobalTheory.Chevalley
end

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chevalley_exists_le_sup_maximalIdeal_pow_of_antitone : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (K : ℕ → Ideal A) (J : Ideal A), Antitone K → (∀ e, maximalIdeal A ^ e ≤ K e) → (∀ (F : AdicCompletion (maximalIdeal A) A) (a : ℕ → A), (∀ n, F - algebraMap A (AdicCompletion (maximalIdeal A) A) (a n) ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) ^ n) → (∀ n, a n ∈ K n) → F ∈ J.map (algebraMap A (AdicCompletion (maximalIdeal A) A))) → ∀ k : ℕ, ∃ e : ℕ, K e ≤ J ⊔ maximalIdeal A ^ k := by
  first | exact @GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone | exact GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone | (intros; apply GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCellOfIsFrameMat
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.LogPole

attribute [local instance] Over.cartesianMonoidalCategory Over.braidedCategory

section Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}}


open MonObj in
theorem isCombAtG_perm (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {m : ℕ} (p : Equiv.Perm (Fin m))
    (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (cf : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left)
    (h : IsCombAtG t x0 v cf w) : IsCombAtG t x0 (fun j => v (p j)) (fun j => cf (p j)) w := by
  obtain ⟨u, hu, hp⟩ := h
  refine ⟨fun j => u (p j), fun j => hu (p j), ?_⟩
  rw [← hp]
  letI : CommMonoid (tEpsG x0 ⟶ t.G) := Hom.commMonoid
  exact congrArg Over.Hom.left ((List.prod_ofFn (f := fun j => u (p j))).trans
    ((Equiv.prod_comp p u).trans (List.prod_ofFn (f := u)).symm))

end Comb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def permE {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) :
    (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n :=
  (Equiv.sigmaCongrRight p).trans e

theorem permE_apply {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (σ : E →+* ℂ) (j : Fin (Dw.mult σ)) :
    permE e p ⟨σ, j⟩ = e ⟨σ, p σ j⟩ := rfl

def IsFrameMat (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) {n : ℕ}
    (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left))
    (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J)
    (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)) : Prop :=
  ∀ (S : Type) [CommRing S] (z : Sp S ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) (hU : ⊤ ≤ (z ≫ toBase TF Z) ⁻¹ᵁ U.1)
    (hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k) (hx : (z ≫ inc₀ TF.X Z) ≫ TF.X.π = z ≫ toBase TF Z)
    (σ : E →+* ℂ) (i : Fin (Dw.mult σ)),
    IsCombAtG TF.Y.t (z ≫ toBase TF Z)
      (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩))
      (fun j => ev z W hz (C σ i j)) (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left

variable {TF : TorFlag Xo c} {Z : Comp Xo c} {U : TF.Y.X.affineOpens} {n : ℕ}
  {e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n} {v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)}

theorem isEigBasis_permE (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (h : IsEigBasis TF U e v) :
    IsEigBasis TF U (permE e p) v :=
  ⟨h.1, h.2.1, fun a τ i => h.2.2 a τ (p τ i)⟩

theorem isFrameMat_mono {W W₀ : (Y₀ TF.X Z).Opens} (hW : W ≤ W₀) {k : TF.X.F.J}
    {C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W₀)}
    (h : IsFrameMat TF Z U e v W₀ k C) :
    IsFrameMat TF Z U e v W k (fun σ => (C σ).map (resG (Y₀ TF.X Z) hW)) := by
  intro S _ z hz hU hk hx σ i
  have hz₀ : ⊤ ≤ z ⁻¹ᵁ W₀ := FlagMod.le_preimage_mono hW hz
  have h1 := h S z hz₀ hU hk hx σ i
  have e1 : (fun j => ev z W₀ hz₀ (C σ i j)) = fun j => ev z W hz (((C σ).map (resG (Y₀ TF.X Z) hW)) i j) :=
    funext fun j => (FlagMod.ev_res z hW hz hz₀ _).symm
  rw [e1] at h1
  exact h1

theorem isFrameMat_permE (p : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) {W : (Y₀ TF.X Z).Opens} {k : TF.X.F.J}
    {C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)}
    (h : IsFrameMat TF Z U e v W k C) :
    IsFrameMat TF Z U (permE e p) v W k (fun σ => (C σ).submatrix id (p σ)) := by
  intro S _ z hz hU hk hx σ i
  simp only [permE_apply, Matrix.submatrix_apply, id]
  exact isCombAtG_perm TF.Y.t (z ≫ toBase TF Z) (p σ)
    (fun j => spMap (dualMap (ev (z ≫ toBase TF Z) U.1 hU)) ≫ v (e ⟨σ, j⟩)) (fun j => ev z W hz (C σ i j))
    (tv (TF.X.F.vecAt k (z ≫ inc₀ TF.X Z) hk hx σ i)).left (h S z hz hU hk hx σ i)

theorem isCell_of_isFrameMat {W : (Y₀ TF.X Z).Opens} {k : TF.X.F.J}
    {L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)} (hW : IsAffineOpen W)
    (hWU : W ≤ toBase TF Z ⁻¹ᵁ U.1) (hWk : W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k) (hL : ∀ σ i j, i < j → L σ i j = 0)
    (hLd : ∀ σ i, IsUnit (L σ i i)) (hN : ∀ σ i j, j < i → N σ i j = 0) (hNd : ∀ σ i, N σ i i = 1)
    (h : IsFrameMat TF Z U e v W k fun σ => L σ * N σ) : IsCell TF Z U e v W k L N :=
  ⟨hW, hWU, hWk, hL, hLd, hN, hNd, h⟩

end GlobalTheory.LogPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundary
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoboundaryRoots

@[ext] structure CocExt (X A : Type) where
  fst : X
  snd : A

variable {X : Type} [AddCommGroup X] {A : Type} [CommGroup A]

theorem coc_zero_left (f : X → X → A)
    (hc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) (c : X) : f 0 c = f 0 0 := by
  have h := hc 0 0 c
  simp only [add_zero, zero_add] at h
  exact (mul_left_cancel h).symm

theorem mul_mul_mul_inv_inv' (x y z : A) : x * y * z * x⁻¹ * y⁻¹ = z := by
  calc x * y * z * x⁻¹ * y⁻¹ = z * (x * x⁻¹) * (y * y⁻¹) := by ac_rfl
    _ = z := by simp

def extGroup (f : X → X → A) (hs : ∀ a b, f a b = f b a)
    (hc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) : AddCommGroup (CocExt X A) :=
  letI : Add (CocExt X A) := ⟨fun p q => ⟨p.fst + q.fst, p.snd * q.snd * f p.fst q.fst⟩⟩
  letI : Zero (CocExt X A) := ⟨⟨0, (f 0 0)⁻¹⟩⟩
  letI : Neg (CocExt X A) := ⟨fun p => ⟨-p.fst, (p.snd * f p.fst (-p.fst) * f 0 0)⁻¹⟩⟩
  { add_assoc := fun p q r => by
        refine CocExt.ext (add_assoc p.fst q.fst r.fst) ?_
        show p.snd * q.snd * f p.fst q.fst * r.snd * f (p.fst + q.fst) r.fst
          = p.snd * (q.snd * r.snd * f q.fst r.fst) * f p.fst (q.fst + r.fst)
        calc p.snd * q.snd * f p.fst q.fst * r.snd * f (p.fst + q.fst) r.fst
            = p.snd * q.snd * r.snd * (f (p.fst + q.fst) r.fst * f p.fst q.fst) := by ac_rfl
          _ = p.snd * q.snd * r.snd * (f p.fst (q.fst + r.fst) * f q.fst r.fst) := by rw [hc]
          _ = _ := by ac_rfl
    zero_add := fun p => by
        refine CocExt.ext (zero_add p.fst) ?_
        show (f 0 0)⁻¹ * p.snd * f 0 p.fst = p.snd
        rw [coc_zero_left f hc p.fst, mul_comm (f 0 0)⁻¹ p.snd, inv_mul_cancel_right]
    add_zero := fun p => by
        refine CocExt.ext (add_zero p.fst) ?_
        show p.snd * (f 0 0)⁻¹ * f p.fst 0 = p.snd
        rw [hs p.fst 0, coc_zero_left f hc p.fst, inv_mul_cancel_right]
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun p => by
        refine CocExt.ext (neg_add_cancel p.fst) ?_
        show (p.snd * f p.fst (-p.fst) * f 0 0)⁻¹ * p.snd * f (-p.fst) p.fst = (f 0 0)⁻¹
        rw [hs (-p.fst) p.fst]; group
    add_comm := fun p q => by
        refine CocExt.ext (add_comm p.fst q.fst) ?_
        show p.snd * q.snd * f p.fst q.fst = q.snd * p.snd * f q.fst p.fst
        rw [hs, mul_comm p.snd q.snd] }

end GlobalTheory.CoboundaryRoots

namespace GlobalTheory

theorem symm_cocycle_isCoboundary : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [CommGroup A] (f : X → X → A), (∀ a b, f a b = f b a) → (∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) → ∃ g : X → A, ∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ := by
  intro X _ _ A _ f hs hc
  letI : AddCommGroup (GlobalTheory.CoboundaryRoots.CocExt X A) := GlobalTheory.CoboundaryRoots.extGroup f hs hc
  let bs := Module.Free.chooseBasis ℤ X
  let s : X →ₗ[ℤ] GlobalTheory.CoboundaryRoots.CocExt X A := bs.constr ℤ (fun i => ⟨bs i, 1⟩)
  let π : GlobalTheory.CoboundaryRoots.CocExt X A →+ X :=
    { toFun := GlobalTheory.CoboundaryRoots.CocExt.fst, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : π.toIntLinearMap.comp s = LinearMap.id :=
    bs.ext (fun i => by
      show π (s (bs i)) = bs i
      rw [show s (bs i) = ⟨bs i, 1⟩ from bs.constr_basis ℤ _ i]
      rfl)
  have hπ : ∀ x, (s x).fst = x := fun x => LinearMap.congr_fun hcomp x
  refine ⟨fun x => (s x).snd, fun a b => ?_⟩
  have h : (s (a + b)).snd = (s a).snd * (s b).snd * f (s a).fst (s b).fst :=
    congrArg GlobalTheory.CoboundaryRoots.CocExt.snd (s.map_add a b)
  rw [hπ, hπ] at h
  show f a b = (s (a + b)).snd * ((s a).snd)⁻¹ * ((s b).snd)⁻¹
  rw [h, GlobalTheory.CoboundaryRoots.mul_mul_mul_inv_inv']

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundaryStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_twoCocycle_free_abelian_isCoboundary : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [CommGroup A] (f : X → X → A), (∀ a b, f a b = f b a) → (∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) → ∃ g : X → A, ∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ := by
  first | exact @GlobalTheory.symm_cocycle_isCoboundary | exact GlobalTheory.symm_cocycle_isCoboundary | (intros; apply GlobalTheory.symm_cocycle_isCoboundary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellEigenbasisCombinationCoeffUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellEigenbasisCombinationCoeffUnique
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogPole

open GlobalTheory.Reg GlobalTheory.FlagMod
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)

attribute [local instance] Over.cartesianMonoidalCategory

theorem cell_eigComb_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : zw ≫ toBase TF Z = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (a b : Fin (Dw.mult σ) → S) (w' : Sp (DualNumber S) ⟶ TF.Y.t.G.left), IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) a w' → IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) b w' → a = b := by
  intro E _ _ _ H Dw l Xo c TF Z U n e v hv W k L N hC S _ zw hzw x hx hUx σ a b w' ha hb
  subst hx
  obtain ⟨-, -, hWk, hLz, hLu, hNz, hN1, hcomb⟩ := hC
  have hk : ⊤ ≤ (zw ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := fun p hp => hWk (hzw hp)
  have hxx : (zw ≫ inc₀ TF.X Z) ≫ TF.X.π = zw ≫ toBase TF Z := Category.assoc _ _ _
  have hvT : ∀ m, IsTanAtG TF.Y.t (zw ≫ toBase TF Z) (spMap (dualMap (ev (zw ≫ toBase TF Z) U.1 hUx)) ≫ v m) :=
    fun m => GlobalTheory.LieMet.isTan_map _ (spMap_ev _ U.2 hUx) (hv.1 m)
  let f : Fin (Dw.mult σ) → TanM (zw ≫ toBase TF Z) TF.Y.t.G := fun j => GlobalTheory.LieMet.tanOf (hvT (e ⟨σ, j⟩))
  have uniq : ∀ {w₁ w₂ : Sp (DualNumber S) ⟶ TF.Y.t.G.left} (cf : Fin (Dw.mult σ) → S),
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₁ →
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf w₂ → w₁ = w₂ := by
    intro w₁ w₂ cf h₁ h₂
    obtain ⟨u₁, hu₁, hw₁⟩ := h₁
    obtain ⟨u₂, hu₂, hw₂⟩ := h₂
    have hu : u₁ = u₂ := funext fun i => Over.OverMorphism.ext ((hu₁ i).trans (hu₂ i).symm)
    rw [← hw₁, ← hw₂, hu]
  have hsum : ∀ cf : Fin (Dw.mult σ) → S,
      IsCombAtG TF.Y.t (zw ≫ toBase TF Z) (fun j => (tv (f j)).left) cf (tv (∑ j, cf j • f j)).left :=
    fun cf => (GlobalTheory.LieMet.isComb_iff f cf _).2 rfl
  have hab : ∑ j, a j • f j = ∑ j, b j • f j :=
    GlobalTheory.LieMet.tan_ext ((uniq a (hsum a) ha).trans (uniq b (hsum b) hb).symm)
  let V := TF.X.F.vecAt k (zw ≫ inc₀ TF.X Z) hk hxx σ
  let C : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) S := (L σ * N σ).map (ev zw W hzw)
  have hV : ∀ i, V i = ∑ j, C i j • f j := fun i =>
    (GlobalTheory.LieMet.isComb_iff f _ _).1 (hcomb S zw hzw hUx hk hxx σ i)
  have hCdet : IsUnit C.det := by
    have hm : C = (L σ).map (ev zw W hzw) * (N σ).map (ev zw W hzw) := Matrix.map_mul
    rw [hm, Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · rw [Matrix.det_of_lowerTriangular _ (fun i j h => by
        show ev zw W hzw (L σ i j) = 0
        rw [hLz σ i j (OrderDual.toDual_lt_toDual.1 h), map_zero])]
      exact IsUnit.prod_univ_iff.2 fun i => (hLu σ i).map (ev zw W hzw)
    · rw [Matrix.det_of_upperTriangular (M := (N σ).map (ev zw W hzw)) (fun i j h => by
        show ev zw W hzw (N σ i j) = 0
        rw [hNz σ i j h, map_zero])]
      refine IsUnit.prod_univ_iff.2 fun i => ?_
      show IsUnit (ev zw W hzw (N σ i i))
      rw [hN1, map_one]; exact isUnit_one
  have hf' : ∀ j, f j = ∑ i, C⁻¹ j i • V i := fun j => by
    simp only [hV, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    have e2 : ∀ l, (∑ i, C⁻¹ j i * C i l) = (1 : Matrix _ _ S) j l := fun l => by
      rw [← Matrix.nonsing_inv_mul _ hCdet, Matrix.mul_apply]
    simp only [e2, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have key : ∀ cf : Fin (Dw.mult σ) → S, ∑ j, cf j • f j = ∑ i, Matrix.vecMul cf C⁻¹ i • V i := fun cf => by
    simp only [hf', Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, Matrix.vecMul, dotProduct]
  have hg : Matrix.vecMul a C⁻¹ = Matrix.vecMul b C⁻¹ := funext
    (Fintype.linearIndependent_iffₛ.1 (TF.X.F.linearIndependent_vecAt k _ hk hxx σ) _ _
      (by rw [← key, ← key, hab]))
  calc a = Matrix.vecMul (Matrix.vecMul a C⁻¹) C := by
        rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul b C⁻¹) C := by rw [hg]
    _ = b := by rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hCdet, Matrix.vecMul_one]

end GlobalTheory.LogPole
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigCellEigenbasisCombinationCoeffUniqueStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bigCell_eigenbasisCombination_coeff_unique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (W : (Y₀ TF.X Z).Opens) (k : TF.X.F.J) (L N : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) Γ(Y₀ TF.X Z, W)), IsCell TF Z U e v W k L N → ∀ (S : Type) [CommRing S] (zw : Sp S ⟶ Y₀ TF.X Z) (hzw : ⊤ ≤ zw ⁻¹ᵁ W) (x : Sp S ⟶ TF.Y.X) (hx : zw ≫ toBase TF Z = x) (hUx : ⊤ ≤ x ⁻¹ᵁ U.1) (σ : E →+* ℂ) (a b : Fin (Dw.mult σ) → S) (w' : Sp (DualNumber S) ⟶ TF.Y.t.G.left), IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) a w' → IsCombAtG TF.Y.t x (fun j => spMap (dualMap (ev x U.1 hUx)) ≫ v (e ⟨σ, j⟩)) b w' → a = b := by
  first | exact @GlobalTheory.LogPole.cell_eigComb_coeff_unique | exact GlobalTheory.LogPole.cell_eigComb_coeff_unique | (intros; apply GlobalTheory.LogPole.cell_eigComb_coeff_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisAffineOpenRestrictBasicOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisAffineOpenRestrictBasicOpen
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv

theorem spMap_res_chart {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) :
    spMap (X.presheaf.map (homOfLE hW).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
  IsAffineOpen.map_fromSpec U.2 W.2 (homOfLE hW).op

theorem tanBasis_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf w := by
  intro E _ _ _ H X t U W hW f _ n v hv hb
  open MonoidalCategory CartesianMonoidalCategory MonObj in
  open scoped CategoryTheory.Obj in
    let φ := (X.presheaf.map (homOfLE hW).op).hom
    let x := GlobalTheory.LogKS.chart U
    have := t.semi.comm
    have := t.semi.smooth
    have h₁ := isGrpPullback_pullback t.G x
    have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
    have h₃ := h₂.comp h₁
    have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
    have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
      Functor.isCommMonObj_obj
    obtain ⟨a₁, b₁⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t x _ _ h₁
    obtain ⟨-, b₃⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t _ _ _ h₃
    choose u hu using fun i => a₁ (v i) (hv i)
    have hbase : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hb⟩
    have hs : Smooth ((Over.pullback x).obj t.G).hom :=
      inferInstanceAs (Smooth (pullback.snd t.G.hom x))
    obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ _ _ _ h₂ hs n u hbase
    have e : Chart.dualMapR φ = dualMap φ := by
      ext a <;> rfl
    have key := (b₃ n u').1 hb'
    have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
        spMap (dualMap φ) ≫ v i := fun i => by
      rw [← Category.assoc, hu', e, Category.assoc, hu]
    rw [← funext e']
    rw [← spMap_res_chart U W hW]
    exact key.2

end GlobalTheory.LogKSDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentBasisAffineOpenRestrictBasicOpenStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangentBasis_affineOpen_restrict_basicOpen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (f : Γ(X, U.1)), W.1 = X.basicOpen f → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (GlobalTheory.LogKS.chart U) (v i)) → (∀ w, IsTanAtG t (GlobalTheory.LogKS.chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (GlobalTheory.LogKS.chart U) v cf w) → ∀ w, IsTanAtG t (GlobalTheory.LogKS.chart W) w → ∃! cf : Fin n → Γ(X, W.1), IsCombAtG t (GlobalTheory.LogKS.chart W) (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) cf w := by
  intro E _ _ _ H X t U W hW f _ n v hv hb
  open MonoidalCategory CartesianMonoidalCategory MonObj in
  open scoped CategoryTheory.Obj in
    let φ := (X.presheaf.map (homOfLE hW).op).hom
    let x := GlobalTheory.LogKS.chart U
    have := t.semi.comm
    have := t.semi.smooth
    have h₁ := isGrpPullback_pullback t.G x
    have h₂ := isGrpPullback_pullback ((Over.pullback x).obj t.G) (spMap φ)
    have h₃ := h₂.comp h₁
    have : IsCommMonObj ((Over.pullback x).obj t.G) := Functor.isCommMonObj_obj
    have : IsCommMonObj ((Over.pullback (spMap φ)).obj ((Over.pullback x).obj t.G)) :=
      Functor.isCommMonObj_obj
    obtain ⟨a₁, b₁⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t x _ _ h₁
    obtain ⟨-, b₃⟩ := GlobalTheory.LocM.FrameBase.lieBasis_iff t _ _ _ h₃
    choose u hu using fun i => a₁ (v i) (hv i)
    have hbase : IsLieBasis u := (b₁ n u).2 ⟨fun i => by rw [hu]; exact hv i, by rw [funext hu]; exact hb⟩
    have hs : Smooth ((Over.pullback x).obj t.G).hom :=
      inferInstanceAs (Smooth (pullback.snd t.G.hom x))
    obtain ⟨u', hb', hu'⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ _ _ _ h₂ hs n u hbase
    have e : Chart.dualMapR φ = dualMap φ := by
      ext a <;> rfl
    have key := (b₃ n u').1 hb'
    have e' : ∀ i, (u' i).left ≫ pullback.fst ((Over.pullback x).obj t.G).hom (spMap φ) ≫ pullback.fst t.G.hom x =
        spMap (dualMap φ) ≫ v i := fun i => by
      rw [← Category.assoc, hu', e, Category.assoc, hu]
    rw [← funext e']
    have hchart : spMap (X.presheaf.map (homOfLE hW).op).hom ≫ GlobalTheory.LogKS.chart U = GlobalTheory.LogKS.chart W :=
      IsAffineOpen.map_fromSpec U.2 W.2 (homOfLE hW).op
    rw [← hchart]
    exact key.2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatFactorThroughLocalScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatFactorThroughLocalScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem flat_stalkClosedPointTo {S : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R]
    (ξ : Spec R ⟶ S) [Flat ξ] : (Scheme.stalkClosedPointTo ξ).hom.Flat := by
  unfold Scheme.stalkClosedPointTo
  rw [CommRingCat.hom_comp]
  exact (Flat.stalkMap ξ _).comp
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso R).hom))

theorem exists_faithfullyFlat_factor_localScheme :
    ∀ (S : Scheme.{0}) (R₁ : Type) [CommRing R₁] [IsLocalRing R₁] (ξ : Sp R₁ ⟶ S) (x : S),
      ξ (closedPoint R₁) = x → Flat ξ → ∃ ξ' : Sp R₁ ⟶ Spec (S.presheaf.stalk x),
        ξ' ≫ S.fromSpecStalk x = ξ ∧ Flat ξ' ∧ Surjective ξ' ∧ QuasiCompact ξ' := by
  intro S R₁ _ _ ξ x hx hf
  subst hx
  have hflat := flat_stalkClosedPointTo (R := CommRingCat.of R₁) ξ
  refine ⟨Spec.map (Scheme.stalkClosedPointTo (R := CommRingCat.of R₁) ξ),
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of R₁) ξ,
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 hflat, ⟨?_⟩, inferInstance⟩
  set φ := (Scheme.stalkClosedPointTo (R := CommRingCat.of R₁) ξ).hom with hφ
  have hl : IsLocalHom φ := by rw [hφ]; infer_instance
  letI := φ.toAlgebra
  have : Module.Flat (S.presheaf.stalk (ξ (closedPoint R₁))) R₁ := hflat
  have : IsLocalHom (algebraMap (S.presheaf.stalk (ξ (closedPoint R₁))) R₁) := hl
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := S.presheaf.stalk (ξ (closedPoint R₁))) (B := R₁)
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := S.presheaf.stalk (ξ (closedPoint R₁))) (B := R₁)

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatFactorThroughLocalSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_faithfullyFlat_factor_through_local_scheme : ∀ (S : Scheme.{0}) (R₁ : Type) [CommRing R₁] [IsLocalRing R₁] (ξ : Sp R₁ ⟶ S) (x : S), ξ (closedPoint R₁) = x → Flat ξ → ∃ ξ' : Sp R₁ ⟶ Spec (S.presheaf.stalk x), ξ' ≫ S.fromSpecStalk x = ξ ∧ Flat ξ' ∧ Surjective ξ' ∧ QuasiCompact ξ' := by
  first | exact @GlobalTheory.Desc.exists_faithfullyFlat_factor_localScheme | exact GlobalTheory.Desc.exists_faithfullyFlat_factor_localScheme | (intros; apply GlobalTheory.Desc.exists_faithfullyFlat_factor_localScheme <;> assumption)
end
end
