module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffine
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AlgConn

namespace GlobalTheory.ZariskiConn

theorem preconnectedSpace_of_isLocalRing (Y : Scheme.{0}) [IsLocalRing Γ(Y, ⊤)] : PreconnectedSpace Y := by
  refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
  obtain ⟨ε, he, hεU⟩ := exists_idempotent_basicOpen_eq_of_isClopen Y U hU
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self ε with h | h
  · right
    rw [← hεU, Y.basicOpen_of_isUnit h]
    rfl
  · left
    have h0 : ε = 0 := by
      have h1 : (1 - ε) * ε = 0 := by rw [sub_mul, one_mul, he, sub_self]
      exact (h.mul_right_eq_zero).1 h1
    rw [← hεU, h0, Scheme.basicOpen_zero]
    rfl

theorem range_thick (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Set.range (thick O (maximalIdeal O) n) = {closedPoint O} := by
  haveI : Nontrivial (O ⧸ maximalIdeal O ^ (n + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal O).ne_top
      (Ideal.pow_le_self (Nat.succ_ne_zero n)))
  have key : ∀ Q : PrimeSpectrum (O ⧸ maximalIdeal O ^ (n + 1)),
      thick O (maximalIdeal O) n Q = closedPoint O := by
    intro Q
    refine PrimeSpectrum.ext ?_
    change Q.asIdeal.comap (Ideal.Quotient.mk _) = maximalIdeal O
    have hp : (Q.asIdeal.comap (Ideal.Quotient.mk (maximalIdeal O ^ (n + 1)))).IsPrime := inferInstance
    refine le_antisymm (le_maximalIdeal hp.ne_top) (hp.le_of_pow_le (n := n + 1) fun a ha => ?_)
    change Ideal.Quotient.mk _ a ∈ Q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact Q.asIdeal.zero_mem
  ext x
  constructor
  · rintro ⟨Q, rfl⟩
    exact key Q
  · rintro rfl
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (O ⧸ maximalIdeal O ^ (n + 1))
    exact ⟨⟨M, hM.isPrime⟩, key _⟩

theorem isPreconnected_closedFibre (O : Type) [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (hI : IsAdicComplete (maximalIdeal O) O) (Y : Scheme.{0}) (f : Y ⟶ Spec (.of O)) [hP : IsProper f]
    [PreconnectedSpace Y] : _root_.IsPreconnected (f ⁻¹' {closedPoint O}) := by
  let ι : ∀ n, pullback f (thick O (maximalIdeal O) n) ⟶ Y := fun n => pullback.fst _ _
  have hTn : ∀ n, Set.range (ι n) = f ⁻¹' {closedPoint O} := fun n => by
    have h := Scheme.Pullback.range_fst f (thick O (maximalIdeal O) n)
    rw [range_thick] at h
    exact h
  refine isPreconnected_closed_iff.2 fun A B hA hB hcov ⟨u, hu, huA⟩ ⟨u', hu', hu'B⟩ => ?_
  by_contra hcon
  have hdis : ∀ y, y ∈ f ⁻¹' {closedPoint O} → y ∈ A → y ∈ B → False :=
    fun y h1 h2 h3 => hcon ⟨y, h1, h2, h3⟩
  have hAB : ∀ n, (ι n ⁻¹' A)ᶜ = ι n ⁻¹' B := by
    intro n
    ext x
    have hx : ι n x ∈ f ⁻¹' {closedPoint O} := by rw [← hTn n]; exact ⟨x, rfl⟩
    exact ⟨fun h => (hcov hx).resolve_left h, fun h h' => hdis _ hx h' h⟩
  have hclo : ∀ n, IsClopen (ι n ⁻¹' A) := fun n =>
    ⟨hA.preimage (ι n).continuous,
      by rw [← isClosed_compl_iff, hAB n]; exact hB.preimage (ι n).continuous⟩
  choose h hhp hhU using fun n => GlobalTheory.exists_hom_spec_prod_self_preimage_eq_clopen O _
    (ι n ≫ f) _ (hclo n)
  haveI : IsProper (Over.mk f).hom := hP
  haveI : IsProper (Over.mk (twoπ O)).hom := isProper_twoπ O
  have htr : ∀ n, thickMap O (maximalIdeal O) n (Over.mk f) ≫ ι (n + 1) = ι n := fun n =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hc : ∀ n, thickMap O (maximalIdeal O) n (Over.mk f) ≫ h (n + 1) = h n := by
    intro n
    refine GlobalTheory.AlgConn.hom_ext_of_twoπ_of_basicOpen O _ _ _ ?_ ?_
    · refine (Category.assoc _ _ _).trans ?_
      refine (congrArg (thickMap O (maximalIdeal O) n (Over.mk f) ≫ ·) (hhp (n + 1))).trans ?_
      refine (Category.assoc _ _ _).symm.trans ?_
      exact (congrArg (· ≫ f) (htr n)).trans (hhp n).symm
    · refine TopologicalSpace.Opens.ext ?_
      refine Eq.trans ?_ (hhU n).symm
      refine Eq.trans (congrArg (thickMap O (maximalIdeal O) n (Over.mk f) ⁻¹' ·) (hhU (n + 1))) ?_
      rw [← htr n]
      rfl
  obtain ⟨g, hg, -⟩ := GlobalTheory.Published.FormalAlgebraisation.Morphisms.existsUnique_thick
    GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms hI (Over.mk f)
    (Over.mk (twoπ O)) h (fun n => hhp n) hc
  have hW : IsClopen ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) :=
    (isClopen_basicOpen_specProdSelfFirstIdempotent O).preimage g.left.continuous
  have h0 : ι 0 ⁻¹' ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) =
      ι 0 ⁻¹' A := by
    rw [← hhU 0, ← hg 0]
    rfl
  rw [← hTn 0] at hu hu'
  obtain ⟨x, rfl⟩ := hu
  obtain ⟨x', rfl⟩ := hu'
  rcases isClopen_iff.1 hW with hW0 | hW1
  · have hxA : x ∈ ι 0 ⁻¹' A := huA
    rw [← h0, hW0] at hxA
    simp at hxA
  · have hxA : x' ∈ ι 0 ⁻¹'
        ((g.left ⁻¹ᵁ (Spec (.of (O × O))).basicOpen (fst1 O) : Y.Opens) : Set Y) := by
      rw [hW1]; trivial
    rw [h0] at hxA
    exact hdis _ (by rw [← hTn 0]; exact ⟨x', rfl⟩) hxA hu'B

theorem exists_complete_flat (X : Scheme.{0}) [IsAffine X] [IsLocallyNoetherian X] (x : X) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsNoetherianRing O) (_ : IsLocalRing O),
      IsAdicComplete (maximalIdeal O) O ∧ ∃ g : Spec (.of O) ⟶ X, Flat g ∧ g (closedPoint O) = x := by
  let B : Type := X.presheaf.stalk x
  let O : Type := AdicCompletion (maximalIdeal B) B
  haveI : IsNoetherianRing O := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion B _
  let φ : X.presheaf.stalk x ⟶ CommRingCat.of O := CommRingCat.ofHom (algebraMap B O)
  haveI : IsLocalHom φ.hom := inferInstanceAs (IsLocalHom (algebraMap B O))
  haveI : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _)
  haveI : Flat (X.fromSpecStalk x) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk X x
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map φ ≫ X.fromSpecStalk x, inferInstance, ?_⟩
  refine (Scheme.Hom.comp_apply _ _ _).trans ?_
  exact (congrArg (X.fromSpecStalk x) (Spec_closedPoint (f := φ))).trans Scheme.fromSpecStalk_closedPoint

theorem isPreconnected_fibre : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) [IsProper f] [IsAffine X]
    [IsLocallyNoetherian X], Function.Bijective f.appTop →
    ∀ x : X, _root_.IsPreconnected (f.base ⁻¹' {x}) := by
  intro X Y f _ _ _ hf x
  obtain ⟨O, _, _, _, hO, g, hg, hx⟩ := exists_complete_flat X x
  haveI : IsIso f.appTop := (ConcreteCategory.isIso_iff_bijective _).2 hf
  have H := IsPullback.of_hasPullback f g
  haveI : IsIso (pullback.snd f g).appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  haveI : IsLocalRing Γ(pullback f g, ⊤) :=
    ((Scheme.ΓSpecIso (.of O)).symm ≪≫ asIso (pullback.snd f g).appTop).commRingCatIsoToRingEquiv.isLocalRing
  haveI := preconnectedSpace_of_isLocalRing (pullback f g)
  have hc := isPreconnected_closedFibre O hO _ (pullback.snd f g)
  have hw : ∀ y, f (pullback.fst f g y) = g (pullback.snd f g y) := fun y => by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hR : pullback.fst f g '' (pullback.snd f g ⁻¹' {closedPoint O}) = f.base ⁻¹' {x} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : pullback.snd f g y = closedPoint O := hy
      change f (pullback.fst f g y) = x
      rw [hw, hy', hx]
    · intro hz
      have h1 : f z = g (closedPoint O) := (show f z = x from hz).trans hx.symm
      obtain ⟨y, hy1, hy2⟩ := Scheme.Pullback.exists_preimage_pullback z _ h1
      exact ⟨y, hy2, hy1⟩
  rw [← hR]
  exact hc.image _ (pullback.fst f g).continuous.continuousOn

end GlobalTheory.ZariskiConn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreAffineStatement
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zariskiConnectedness_isPreconnected_fibre_affine : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) [IsProper f] [IsAffine X] [IsLocallyNoetherian X], Function.Bijective f.appTop → ∀ x : X, _root_.IsPreconnected (f.base ⁻¹' {x}) := by
  first | exact @GlobalTheory.ZariskiConn.isPreconnected_fibre | exact GlobalTheory.ZariskiConn.isPreconnected_fibre | (intros; apply GlobalTheory.ZariskiConn.isPreconnected_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveSectionsPreimageAffineProperBirational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveSectionsPreimageAffineProperBirational
open AlgebraicGeometry CategoryTheory

open TopologicalSpace

namespace GlobalTheory.ZariskiSections

theorem bijective_of_finite_of_fractionRing {A B K : Type} [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [CommRing B] [Field K] [Algebra A K] [IsFractionRing A K]
    (φ : A →+* B) (hφ : φ.Finite) (θ : B →+* K) (hθ : Function.Injective θ)
    (h : ∀ a, θ (φ a) = algebraMap A K a) : Function.Bijective φ := by
  refine ⟨fun a a' e => IsFractionRing.injective A K (by rw [← h, ← h, e]), fun b => ?_⟩
  letI := φ.toAlgebra
  have : Module.Finite A B := hφ
  have hb : _root_.IsIntegral A b := Algebra.IsIntegral.isIntegral b
  let θ' : B →ₐ[A] K := { θ with commutes' := fun a => h a }
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hb.map θ')
  exact ⟨a, hθ (by rw [h]; exact ha)⟩

theorem finite_appTop_restrict {Y Z : Scheme.{0}} (π : Y ⟶ Z) [IsProper π] [IsLocallyNoetherian Z]
    {V : Z.Opens} (hV : IsAffineOpen V) : (π ∣_ V).appTop.hom.Finite := by
  let f : (π ⁻¹ᵁ V).toScheme ⟶ Spec (.of Γ(Z, V)) := (π ∣_ V) ≫ hV.isoSpec.hom
  have : IsNoetherianRing Γ(Z, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  letI := GlobalTheory.algebraΓOfHom f
  have h1 := GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule _) 0
  have h2 : Module.Finite Γ(Z, V) Γ((π ⁻¹ᵁ V).toScheme, ⊤) :=
    Module.Finite.equiv ((GlobalTheory.coh.zeroUnitEquiv _).restrictScalars Γ(Z, V))
  let e := (Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ hV.isoSpec.hom.appTop
  haveI : IsIso hV.isoSpec.hom.appTop := by
    first
    | exact (inferInstance : IsIso (Scheme.Γ.map hV.isoSpec.hom.op))
    | exact Scheme.Hom.isIso_app _ ⊤ (by simp)
    | exact Scheme.Hom.isIso_app _ ⊤ (fun x _ => (ConcreteCategory.bijective_of_isIso hV.isoSpec.hom.base).2 x)
  haveI he' : IsIso e := by dsimp only [e]; infer_instance
  have h3 : (e ≫ (π ∣_ V).appTop).hom.Finite := by
    have he : e ≫ (π ∣_ V).appTop = (Scheme.ΓSpecIso (.of Γ(Z, V))).inv ≫ f.appTop := by
      simp only [e, f, Scheme.Hom.comp_appTop, Category.assoc]
    rw [he]
    exact h2
  have h4 : (π ∣_ V).appTop = inv e ≫ (e ≫ (π ∣_ V).appTop) := by rw [IsIso.inv_hom_id_assoc]
  rw [h4, CommRingCat.hom_comp]
  exact RingHom.Finite.comp h3
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso (inv e)).2)

theorem bijective_appTop_restrict : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y]
    [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z →
    ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ V : Z.Opens, IsAffineOpen V →
    Function.Bijective (π ∣_ V).appTop := by
  intro Y Z π _ _ _ _ hN U hU hiso V hV
  have hV0 : V.ι ''ᵁ ⊤ = V := Scheme.Opens.ι_image_top V
  have hO : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ = π ⁻¹ᵁ V := Scheme.Opens.ι_image_top _
  by_cases hne : (V : Set Z).Nonempty
  swap
  · have hVb : V = ⊥ := by
      ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨x, hx⟩
    have s1 : Subsingleton Γ(Z, V.ι ''ᵁ ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty (hV0.trans hVb))
    have s2 : Subsingleton Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty (by
        rw [hO]; ext x; simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        intro hx; exact hne ⟨_, hx⟩))
    exact ⟨fun a b _ => s1.elim a b, fun b => ⟨0, s2.elim _ _⟩⟩

  set η := genericPoint Z
  have hηU : η ∈ U := ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hηV : η ∈ V := ((genericPoint_spec Z).mem_open_set_iff V.isOpen).mpr (by simpa using hne)

  obtain ⟨y', hy'⟩ := (π ∣_ U).surjective ⟨η, hηU⟩
  set y : Y := y'.1
  have hy : π y = η := by
    have := congrArg Subtype.val hy'
    simpa [morphismRestrict_base_coe] using this
  haveI : IsIso (π.stalkMap y) :=
    (MorphismProperty.isomorphisms _).arrow_mk_iso_iff (morphismRestrictStalkMap π U y') |>.mp
      (inferInstance : IsIso ((π ∣_ U).stalkMap y'))
  have hyO : y ∈ (π ⁻¹ᵁ V).ι ''ᵁ ⊤ := by rw [hO]; show π y ∈ V; rw [hy]; exact hηV
  haveI : Nonempty (V.ι ''ᵁ ⊤) := ⟨⟨η, hV0.symm ▸ hηV⟩⟩
  haveI := GlobalTheory.IsNormalScheme.of_pred hN
  have hA : IsAffineOpen (V.ι ''ᵁ ⊤) := hV0.symm ▸ hV
  haveI := functionField_isFractionRing_of_isAffineOpen Z _ hA
  haveI := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hA
  let θ : Γ(Y, (π ⁻¹ᵁ V).ι ''ᵁ ⊤) ⟶ Z.functionField :=
    Y.presheaf.germ _ y hyO ≫ inv (π.stalkMap y) ≫ (Z.presheaf.stalkCongr (Inseparable.of_eq hy)).hom
  have hθ : Function.Injective θ.hom := by
    simp only [θ, CommRingCat.hom_comp, RingHom.coe_comp]
    exact ((ConcreteCategory.bijective_of_isIso _).1.comp (ConcreteCategory.bijective_of_isIso _).1).comp
      (germ_injective_of_isIntegral Y y hyO)
  refine bijective_of_finite_of_fractionRing (A := Γ(Z, V.ι ''ᵁ ⊤)) (K := Z.functionField)
    (π ∣_ V).appTop.hom (finite_appTop_restrict π hV) θ.hom hθ fun a => ?_
  have hle : (π ⁻¹ᵁ V).ι ''ᵁ ⊤ ≤ π ⁻¹ᵁ (V.ι ''ᵁ ⊤) := by rw [hO, hV0]
  have h1 : (π ∣_ V).appTop = π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op :=
    morphismRestrict_app π V ⊤
  have hyV : π y ∈ V.ι ''ᵁ ⊤ := by rw [hV0, hy]; exact hηV
  have key : (π.app (V.ι ''ᵁ ⊤) ≫ Y.presheaf.map (homOfLE hle).op) ≫ θ =
      Z.germToFunctionField (V.ι ''ᵁ ⊤) := by
    simp only [θ, Category.assoc]
    rw [TopCat.Presheaf.germ_res_assoc, ← Scheme.Hom.germ_stalkMap_assoc π (V.ι ''ᵁ ⊤) y hyV,
      IsIso.hom_inv_id_assoc]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ (Inseparable.of_eq hy).specializes'
  have := congrArg (fun g => g.hom a) key
  rw [← h1] at this
  exact this

end GlobalTheory.ZariskiSections
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveSectionsPreimageAffineProperBirationalStatement
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_sections_preimage_affine_proper_birational : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ V : Z.Opens, IsAffineOpen V → Function.Bijective (π ∣_ V).appTop := by
  first | exact @GlobalTheory.ZariskiSections.bijective_appTop_restrict | exact GlobalTheory.ZariskiSections.bijective_appTop_restrict | (intros; apply GlobalTheory.ZariskiSections.bijective_appTop_restrict <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ZariskiConn

theorem fibre_preconnected : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsProper π] [IsIntegral Y] [IsIntegral Z] [IsLocallyNoetherian Z], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ U : Z.Opens, (U : Set Z).Nonempty → IsIso (π ∣_ U) → ∀ z : Z, _root_.IsPreconnected (π.base ⁻¹' {z}) := by
  intro Y Z π _ _ _ _ hN U hU hiso z
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := z) trivial
  have hS := GlobalTheory.T.bijective_sections_preimage_affine_proper_birational Y Z π hN U hU hiso V hV
  haveI : IsAffine (V : Scheme) := hV
  have hC := GlobalTheory.T.zariskiConnectedness_isPreconnected_fibre_affine (V : Scheme) (π ⁻¹ᵁ V) (π ∣_ V) hS ⟨z, hzV⟩
  have key : π.base ⁻¹' {z} = (π ⁻¹ᵁ V).ι.base '' ((π ∣_ V).base ⁻¹' {⟨z, hzV⟩}) := by
    ext y
    constructor
    · intro hy
      have hy' : π.base y = z := hy
      have hyV : y ∈ π ⁻¹ᵁ V := by
        show π.base y ∈ V
        rw [hy']; exact hzV
      refine ⟨⟨y, hyV⟩, ?_, rfl⟩
      show (π ∣_ V).base ⟨y, hyV⟩ = ⟨z, hzV⟩
      exact Subtype.ext ((morphismRestrict_base_coe π V ⟨y, hyV⟩).trans hy')
    · rintro ⟨w, hw, rfl⟩
      have hw' : (π ∣_ V).base w = ⟨z, hzV⟩ := hw
      exact (morphismRestrict_base_coe π V w).symm.trans (congrArg Subtype.val hw')
  rw [key]
  exact hC.image _ (π ⁻¹ᵁ V).ι.base.hom.continuous.continuousOn

end GlobalTheory.ZariskiConn
