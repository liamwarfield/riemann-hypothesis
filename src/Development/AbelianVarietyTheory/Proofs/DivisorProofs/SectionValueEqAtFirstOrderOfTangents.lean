module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeDivisorEtalePullbackOrders
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAtFirstOrderOfTangents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRPowIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.BaseChRig

theorem valR_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X)
    {U : X.Opens} (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valR (spMap f ≫ x) U s = f (valR x U s) := by
  have hU' : ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U := fun q _ => hU (Set.mem_univ _)
  unfold valR
  rw [dif_pos hU, dif_pos hU']
  have e : (spMap f ≫ x).appLE U ⊤ hU' = x.appLE U ⊤ hU ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e]
  exact congrArg (fun φ => φ.hom ((x.appLE U ⊤ hU).hom s)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))

end GlobalTheory.MBLow.BaseChRig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAtFirstOrderOfTangents
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TangentFirstOrder

theorem fst_eq_of_tangent : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := by
  intro K C _ _ _ P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
  have key : ∀ {X : Scheme.{0}} (y : Sp (DualNumber C) ⟶ X) (U : X.Opens) (s : Γ(X, U)),
      (valR y U s).fst = valR (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ y) U s := by
    intro X y U s
    by_cases h : ⊤ ≤ y ⁻¹ᵁ U
    · exact (GlobalTheory.MBLow.BaseChRig.valR_spMap (TrivSqZeroExt.fstHom C C C).toRingHom y h s).symm
    · have h' : ¬ ⊤ ≤ (spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ y) ⁻¹ᵁ U :=
        fun h' => h ((GlobalTheory.ArcLie.le_iff_fst y U).2 h')
      unfold valR
      rw [dite_eq_right h, dite_eq_right h']
      rfl
  have sq : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ spMap (dualMap (algebraMap K C)) =
      spMap (algebraMap K C) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun x => ?_
    simp [dualMap]
  have e0 : spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yv = spMap (TrivSqZeroExt.fstHom C C C).toRingHom ≫ yw := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, hv1, Category.assoc, hw1]
    · rw [Category.assoc, hv2, Category.assoc, hw2, ← Category.assoc, ← Category.assoc, sq, Category.assoc,
        Category.assoc, hv, hw]
  have hU : ⊤ ≤ (spMap (algebraMap K C)) ⁻¹ᵁ (P.L.pull (eSec P.A)).U (fun _ => i₀) :=
    fun q hq => Set.mem_iInter.2 fun _ => hi hq
  have hr : valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ≠ 0 := by
    unfold valR
    rw [dite_eq_left hU]
    exact (((ρ.s fun _ => i₀).isUnit.map _).map _).ne_zero
  have h1 := congrArg TrivSqZeroExt.fst ev
  have h2 := congrArg TrivSqZeroExt.fst ew
  rw [key] at h1 h2
  rw [e0, h2] at h1
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inr, add_zero] at h1
  exact (mul_left_cancel₀ (pow_ne_zero k hr) h1).symm

end GlobalTheory.TangentFirstOrder
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionValueEqAtFirstOrderOfTangentsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_value_eq_at_first_order_of_tangents : ∀ (K C : Type) [Field K] [Field C] [Algebra K C] (P : PolAV (Sp K))
    (ρ : LB.Gen (P.L.pull (eSec P.A))) (k : ℕ) (t : LB.Sec (LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))))
    (i₀ : P.L.ι), ⊤ ≤ (spMap (algebraMap K C) ≫ eSec P.A) ⁻¹ᵁ P.L.U i₀ →
    ∀ (v w : epsR K ⟶ P.A), IsTangent v → IsTangent w →
    ∀ (yv yw : Sp (DualNumber C) ⟶ (Over.mk (spMap (algebraMap K C)) ⊗ P.A).left),
      yv ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yv ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ v.left →
      yw ≫ (fst (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (algebraMap C (DualNumber C)) →
      yw ≫ (snd (Over.mk (spMap (algebraMap K C))) P.A).left = spMap (dualMap (algebraMap K C)) ≫ w.left →
    ∀ (a b a' b' : C),
      valR yv ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) →
      valR yw ((LPow P.A P.L (k : ℤ) (Over.mk (spMap (algebraMap K C)))).U fun _ => i₀) (t.f fun _ => i₀) =
        TrivSqZeroExt.inl (valR (spMap (algebraMap K C)) ((P.L.pull (eSec P.A)).U fun _ => i₀) (ρ.s fun _ => i₀).val ^ k) *
          (TrivSqZeroExt.inl a' + TrivSqZeroExt.inr b') → a = a' := by
  intro K C hK hC hKC P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
  exact @GlobalTheory.TangentFirstOrder.fst_eq_of_tangent K C hK hC hKC P ρ k t i₀ hi v w hv hw yv yw hv1 hv2 hw1 hw2 a b a' b' ev ew
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFormallyUnramifiedStandardSmoothSameRelDi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFormallyUnramifiedStandardSmoothSameRelDi
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem etale_of_formallyUnramified_of_relDim : ∀ (A B C : Type) [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (g : ℕ),
    Algebra.IsStandardSmoothOfRelativeDimension g A B →
    Algebra.IsStandardSmoothOfRelativeDimension g A C →
    Algebra.FormallyUnramified B C → Algebra.Etale B C := by
  intro A B C _ _ _ _ _ _ _ g hB hC hU
  have : Algebra.IsStandardSmooth A B := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have : Algebra.IsStandardSmooth A C := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth g
  have hs : Function.Surjective (KaehlerDifferential.mapBaseChange A B C) := fun x =>
    (KaehlerDifferential.exact_mapBaseChange_map A B C x).mp (Subsingleton.elim _ _)
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange A B C) := by
    rcases subsingleton_or_nontrivial C with hC0 | hC0
    · intro x y _
      exact Subsingleton.elim (α := TensorProduct B C Ω[B⁄A]) x y
    · have : Nontrivial B := (algebraMap B C).domain_nontrivial
      have : Module.Free B Ω[B⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have : Module.Free C Ω[C⁄A] := Algebra.IsStandardSmooth.free_kaehlerDifferential
      have hr : Module.rank C Ω[C⁄A] = Module.rank C (TensorProduct B C Ω[B⁄A]) := by
        rw [Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g, Module.rank_baseChange,
          Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential g]
        simp
      obtain ⟨e⟩ := nonempty_linearEquiv_of_rank_eq hr
      have h2 : Function.Surjective (e.toLinearMap ∘ₗ KaehlerDifferential.mapBaseChange A B C) :=
        e.surjective.comp hs
      have h3 := OrzechProperty.injective_of_surjective_endomorphism _ h2
      exact fun x y hxy => h3 (by simp [hxy])
  have : Algebra.FormallySmooth B C := by
    rw [Algebra.formallySmooth_iff]
    constructor
    · exact Module.Projective.of_free
    · refine subsingleton_of_forall_eq 0 fun x => ?_
      have h₁ : Algebra.H1Cotangent.δ A B C x = 0 := by
        apply hinj
        rw [map_zero]
        exact (Algebra.H1Cotangent.exact_δ_mapBaseChange A B C).apply_apply_eq_zero x
      obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ A B C x).mp h₁
      rw [Subsingleton.elim y 0, map_zero]
  have : Algebra.FormallyEtale B C := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  have : Algebra.FinitePresentation B C := Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A B C
  exact ⟨inferInstance, inferInstance⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfFormallyUnramifiedStandardSmoothSameRelDiStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_formallyUnramified_standardSmooth_same_relDim : ∀ (A B C : Type) [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (g : ℕ), Algebra.IsStandardSmoothOfRelativeDimension g A B → Algebra.IsStandardSmoothOfRelativeDimension g A C → Algebra.FormallyUnramified B C → Algebra.Etale B C := by
  first | exact @GlobalTheory.etale_of_formallyUnramified_of_relDim | exact GlobalTheory.etale_of_formallyUnramified_of_relDim | (intros; apply GlobalTheory.etale_of_formallyUnramified_of_relDim <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimension
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem etale_of_formallyUnramified_of_smoothOfRelativeDimension {X Y Z : Scheme.{0}} (f : X ⟶ Y)
    (p : Y ⟶ Z) (g : ℕ) (hp : SmoothOfRelativeDimension g p)
    (hq : SmoothOfRelativeDimension g (f ≫ p)) [FormallyUnramified f] : Etale f := by
  refine (HasRingHomProperty.iff_exists_appLE (P := @Etale)
    (RingHom.Etale.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      fun R S _ _ _ r _ => RingHom.etale_algebraMap.mpr (.of_isLocalizationAway r)).left).mpr fun x => ?_
  obtain ⟨U, hU, V, hV, hxV, e, H⟩ := hp.exists_isStandardSmoothOfRelativeDimension (f x)
  obtain ⟨W, hW, hxW, e'⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ f ⁻¹ᵁ V from hxV)
  have e'' : W ≤ (f ≫ p) ⁻¹ᵁ U := e'.trans (f.preimage_mono e)
  have h1 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) (f ≫ p) hq ⟨U, hU⟩ ⟨W, hW⟩ e''
  rw [RingHom.locally_iff_isLocalization RingHom.isStandardSmoothOfRelativeDimension_respectsIso]
    at h1
  obtain ⟨s, hs, hfs⟩ := h1
  have hs' := iSup_basicOpen_of_span_eq_top _ _ hs
  have hx : x ∈ (⨆ i ∈ (s : Set Γ(X, W)), X.basicOpen i) := by rw [hs']; exact hxW
  have hx' : ∃ r ∈ s, x ∈ X.basicOpen r := by simpa using hx
  obtain ⟨r, hr, hxr⟩ := hx'
  have hloc : IsLocalization.Away r Γ(X, X.basicOpen r) := hW.isLocalization_basicOpen r
  have er : X.basicOpen r ≤ f ⁻¹ᵁ V := (X.basicOpen_le r).trans e'
  have h2 : ((f ≫ p).appLE U (X.basicOpen r)
      ((X.basicOpen_le r).trans e'')).hom.IsStandardSmoothOfRelativeDimension g := by
    rw [← (f ≫ p).appLE_map e'' (homOfLE (X.basicOpen_le r)).op]
    exact hfs r hr _
  have h3 : (f.appLE V (X.basicOpen r) er).hom.FormallyUnramified :=
    HasRingHomProperty.appLE @FormallyUnramified f inferInstance ⟨V, hV⟩
      ⟨X.basicOpen r, hW.basicOpen r⟩ er
  refine ⟨⟨V, hV⟩, ⟨X.basicOpen r, hW.basicOpen r⟩, hxr, er, ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE f p U V _ e er, CommRingCat.hom_comp] at h2
  letI := (p.appLE U V e).hom.toAlgebra
  letI := (f.appLE V (X.basicOpen r) er).hom.toAlgebra
  letI := ((f.appLE V (X.basicOpen r) er).hom.comp (p.appLE U V e).hom).toAlgebra
  haveI : IsScalarTower Γ(Z, U) Γ(Y, V) Γ(X, X.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact GlobalTheory.T.etale_of_formallyUnramified_standardSmooth_same_relDim Γ(Z, U) Γ(Y, V) Γ(X, X.basicOpen r) g H h2 h3

theorem isOpenImmersion_of_mono_of_smoothOfRelativeDimension :
    ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (p : Y ⟶ Z) (g : ℕ), SmoothOfRelativeDimension g p →
      SmoothOfRelativeDimension g (f ≫ p) → Mono f → IsOpenImmersion f := by
  intro X Y Z f p g hp hq hf
  have : Etale f := etale_of_formallyUnramified_of_smoothOfRelativeDimension f p g hp hq
  exact IsOpenImmersion.of_flat_of_mono f

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoOfSmoothOfRelativeDimensionStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenImmersion_of_mono_of_smoothOfRelativeDimension' : ∀ (X Y Z : Scheme.{0}) (f : X ⟶ Y) (p : Y ⟶ Z) (g : ℕ), SmoothOfRelativeDimension g p → SmoothOfRelativeDimension g (f ≫ p) → Mono f → IsOpenImmersion f := by
  first | exact @GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension | exact GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension | (intros; apply GlobalTheory.isOpenImmersion_of_mono_of_smoothOfRelativeDimension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFormsTensorSectionGenericFibreTransitionGer
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFormsTensorSectionGenericFibreTransitionGer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeySecRel

theorem appLE_map' {X Y : Scheme.{0}} (p : Y ⟶ X) {U V : X.Opens} (hVU : V ≤ U) {W : Y.Opens} (h : W ≤ p ⁻¹ᵁ V)
    (h' : W ≤ p ⁻¹ᵁ U) (a : Γ(X, U)) :
    (p.appLE V W h).hom ((X.presheaf.map (homOfLE hVU).op).hom a) = (p.appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem appLE_app' {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) {U : S.Opens} {W : Y.Opens}
    (h : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ U)) (h' : W ≤ (p ≫ π) ⁻¹ᵁ U) (a : Γ(S, U)) :
    (p.appLE _ W h).hom ((π.app U).hom a) = ((p ≫ π).appLE U W h').hom a := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.comp_appLE]

theorem appLE_sec_tens {X Y S : Scheme.{0}} (p : Y ⟶ X) (π : X ⟶ S) (A : LB X) (hA : A.IsLB) (δ : LB S)
    (σ : (CechPic.tens A (δ.pull π)).Sec) (l : A.ι) (i i' : δ.ι) (W : Y.Opens)
    (h : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i))
    (h' : W ≤ p ⁻¹ᵁ (CechPic.tens A (δ.pull π)).U (l, fun _ => i'))
    (hW : W ≤ (p ≫ π) ⁻¹ᵁ (δ.U i ⊓ δ.U i')) :
    (p.appLE _ W h).hom (σ.f (l, fun _ => i)) =
      ((p ≫ π).appLE _ W hW).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) * (p.appLE _ W h').hom (σ.f (l, fun _ => i')) := by
  have hh : W ≤ p ⁻¹ᵁ ((CechPic.tens A (δ.pull π)).U (l, fun _ => i) ⊓ (CechPic.tens A (δ.pull π)).U (l, fun _ => i')) :=
    fun y hy => ⟨h hy, h' hy⟩
  have e := congrArg (p.appLE _ W hh).hom (σ.compat (l, fun _ => i) (l, fun _ => i'))
  rw [map_mul, appLE_map' p _ hh h, appLE_map' p _ hh h'] at e
  rw [e]
  congr 1
  have h1 : W ≤ p ⁻¹ᵁ (A.U l) := fun y hy => (h hy).1
  have h11 : W ≤ p ⁻¹ᵁ (A.U l ⊓ A.U l) := fun y hy => ⟨h1 hy, h1 hy⟩
  have hg : (p.appLE _ W h11).hom (A.g l l : Γ(X, A.U l ⊓ A.U l)) = 1 := by
    have := congrArg (fun u : Γ(X, A.U l)ˣ => (p.appLE _ W h1).hom (u : Γ(X, A.U l))) (hA.g_self l)
    simp only [Units.val_one, map_one] at this
    rw [← this]
    exact (appLE_map' p _ h1 h11 _).symm
  have h2 : W ≤ p ⁻¹ᵁ ((δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i')) := fun y hy => ⟨(h hy).2, (h' hy).2⟩
  have hd : ((δ.pull π).g (fun _ => i) (fun _ => i') : Γ(X, (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i'))) =
      (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i) PUnit.unit))
        (inf_le_right.trans (LB.wchart_le δ (fun _ : PUnit => π) (fun _ => i') PUnit.unit)) :
        (δ.pull π).U (fun _ => i) ⊓ (δ.pull π).U (fun _ => i') ≤ π ⁻¹ᵁ (δ.U i ⊓ δ.U i'))).op).hom
        ((π.app _).hom (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) := by
    unfold LB.pull LB.LinComb
    dsimp only
    erw [Fintype.prod_unique, zpow_one]
    rfl
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) ((appLE_map' p _ hh h11 _).trans hg) (appLE_map' p _ hh h2 _)).trans ?_
  rw [_root_.one_mul]
  refine (congrArg (p.appLE _ W h2).hom hd).trans ?_
  have hW' : W ≤ p ⁻¹ᵁ (π ⁻¹ᵁ (δ.U i ⊓ δ.U i')) := hW
  exact (appLE_map' p _ h2 hW' _).trans (appLE_app' p π hW' hW _)

theorem genPt_appLE {S : Scheme.{0}} [IsIntegral S] (U : S.Opens) (hU : genericPoint S ∈ U) (a : Γ(S, U)) :
    ((KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU)).hom a =
      (Scheme.ΓSpecIso (CommRingCat.of (KeyVals.FF S))).inv.hom (S.presheaf.germ U (genericPoint S) hU a) := by
  have e := Scheme.fromSpecStalk_app (X := S) (x := genericPoint S) hU
  have : (KeyVals.genPt S).appLE U ⊤ (KeyVals.genPt_le U hU) =
      S.presheaf.germ U (genericPoint S) hU ≫ (Scheme.ΓSpecIso (S.presheaf.stalk (genericPoint S))).inv := by
    unfold KeyVals.genPt Scheme.Hom.appLE
    erw [e]
    simp only [Category.assoc]
    erw [← Functor.map_comp]
    refine congrArg (fun z => _ ≫ z) ?_
    refine (congrArg (fun z => _ ≫ (Spec (S.presheaf.stalk (genericPoint S))).presheaf.map z)
      (Subsingleton.elim _ (𝟙 _))).trans ?_
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [this]
  rfl

theorem locSec_eq_germ_mul : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), δ.IsLB → ∀ (i i' : δ.ι) (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i')
    (t t' : (KeyVals.bL L (KeyVals.genPt S)).L.Sec), KeyVals.IsLocSec σ i (KeyVals.genPt S) t →
    KeyVals.IsLocSec σ i' (KeyVals.genPt S) t' → ∀ j, t.f j =
      constFn (KeyVals.bG G (KeyVals.genPt S)).hom _ (S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) * t'.f j := by
  intro S _ G _ _ L δ σ _ i i' h2 t t' ht ht' j
  have hc : pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom =
      (KeyVals.bG G (KeyVals.genPt S)).hom ≫ KeyVals.genPt S := pullback.condition
  have hW : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      (pullback.fst G.hom (KeyVals.genPt S) ≫ G.hom) ⁻¹ᵁ (δ.U i ⊓ δ.U i') := by
    rw [hc]
    exact fun y _ => KeyVals.genPt_le _ h2 (Set.mem_univ _)
  have hl : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤
      pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ L.L.U (j PUnit.unit) :=
    LB.wchart_le L.L (fun _ : PUnit => pullback.fst G.hom (KeyVals.genPt S)) j PUnit.unit
  have h : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i) :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).1⟩
  have h' : (KeyVals.bL L (KeyVals.genPt S)).L.U j ≤ pullback.fst G.hom (KeyVals.genPt S) ⁻¹ᵁ
      (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i') :=
    fun y hy => ⟨hl hy, Set.mem_iInter.2 fun _ => (hW hy).2⟩
  rw [ht j h, ht' j h']
  refine (appLE_sec_tens _ G.hom L.L L.isLB δ σ _ i i' _ h h' hW).trans ?_
  congr 1
  unfold constFn
  rw [← genPt_appLE, ← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  have key : ∀ {Y : Scheme.{0}} (f f' : Y ⟶ S) (_ : f = f') (U : S.Opens) (W : Y.Opens) (a : W ≤ f ⁻¹ᵁ U)
      (a' : W ≤ f' ⁻¹ᵁ U) (x : Γ(S, U)), (f.appLE U W a).hom x = (f'.appLE U W a').hom x := by
    intro Y f f' e; subst e; intros; rfl
  exact key _ _ hc _ _ _ _ _

end GlobalTheory.KeySecRel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFormsTensorSectionGenericFibreTransitionGerStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFormsTensorSection_genericFibre_transitionGerm : ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), δ.IsLB → ∀ (i i' : δ.ι) (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i')
    (t t' : (KeyVals.bL L (KeyVals.genPt S)).L.Sec), KeyVals.IsLocSec σ i (KeyVals.genPt S) t →
    KeyVals.IsLocSec σ i' (KeyVals.genPt S) t' → ∀ j, t.f j =
      constFn (KeyVals.bG G (KeyVals.genPt S)).hom _ (S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i'))) * t'.f j := by
  first | exact @GlobalTheory.KeySecRel.locSec_eq_germ_mul | exact GlobalTheory.KeySecRel.locSec_eq_germ_mul | (intros; apply GlobalTheory.KeySecRel.locSec_eq_germ_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonUnitAtOfNotIsUnit
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.FibreCorr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z}

theorem mem_O_of_isHom (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {x : M.Z} {F : Ω} (hF : F ∈ M₁.O (π x)) : F ∈ M.O x := by
  simpa using hπ.map_mem_O hF

theorem norm_val_le_one' (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {q : ℕ} [Fact q.Prime] {y : Sp (OO q) ⟶ M.Z} {z : M₁.Z}
    (hy : π (y (cPt q)) = z) {F : Ω} (hF : F ∈ M₁.O z) : ‖M.val (gPt q ≫ y) F‖ ≤ 1 :=
  RatModel.norm_val_le_one rfl (mem_O_of_isHom hπ (hy ▸ hF))

theorem bound_mono {r s t : ℝ} {Q : Ω → Prop} {g : Ω → ℝ} (hs : s ≤ r) (H : r ≤ t ∨ ∃ h, Q h ∧ r ≤ g h) :
    s ≤ t ∨ ∃ h, Q h ∧ s ≤ g h :=
  H.imp hs.trans fun ⟨h, hq, hr⟩ => ⟨h, hq, hs.trans hr⟩

theorem nonUnitAt_of_not_isUnit {z : M₁.Z} {h : M₁.O z} (hh : ¬ IsUnit h) : NonUnitAt M₁ z h := by
  refine ⟨h.2, ?_⟩
  by_cases h0 : (h : Ω) = 0
  · exact Or.inl h0
  · exact Or.inr fun hi => hh ((RatModel.isUnit_O_iff h).2 ⟨h0, hi⟩)

theorem exists_nonUnit_pow (hπ : M₁.IsHom M (AlgHom.id o Ω) π) {q : ℕ} [Fact q.Prime] {y : Sp (OO q) ⟶ M.Z} {z : M₁.Z}
    (hy : π (y (cPt q)) = z) (e : ℕ) : ∀ F ∈ maximalIdeal (M₁.O z) ^ e, ∃ h : M₁.O z, ¬ IsUnit h ∧
      ‖M.val (gPt q ≫ y) (F : Ω)‖ ≤ ‖M.val (gPt q ≫ y) (h : Ω)‖ ^ e := by
  have hs : ∀ w, (gPt q ≫ y) w ⤳ y (cPt q) := RatModel.gPt_specializes rfl
  have hO : ∀ a : M₁.O z, (a : Ω) ∈ M.O (y (cPt q)) := fun a => mem_O_of_isHom hπ (hy ▸ a.2)
  have hadd : ∀ a b : M₁.O z, M.val (gPt q ≫ y) ((a + b : M₁.O z) : Ω) = M.val (gPt q ≫ y) a + M.val (gPt q ≫ y) b :=
    fun a b => RatModel.val_add hs (hO a) (hO b)
  have hmul : ∀ a b : M₁.O z, M.val (gPt q ≫ y) ((a * b : M₁.O z) : Ω) = M.val (gPt q ≫ y) a * M.val (gPt q ≫ y) b :=
    fun a b => RatModel.val_mul hs (hO a) (hO b)
  induction e with
  | zero =>
    intro F _
    refine ⟨0, not_isUnit_zero, ?_⟩
    rw [pow_zero]
    exact norm_val_le_one' hπ hy F.2
  | succ n ih =>
    intro F hF
    rw [pow_succ] at hF
    refine Submodule.mul_induction_on hF ?_ ?_
    · intro a ha b hb
      obtain ⟨h, hh, hle⟩ := ih a ha
      have hb' : ¬ IsUnit b := (mem_maximalIdeal b).1 hb
      rw [hmul, norm_mul]
      rcases le_total ‖M.val (gPt q ≫ y) (h : Ω)‖ ‖M.val (gPt q ≫ y) (b : Ω)‖ with hc | hc
      · refine ⟨b, hb', ?_⟩
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right (hle.trans (pow_le_pow_left₀ (norm_nonneg _) hc n)) (norm_nonneg _)
      · refine ⟨h, hh, ?_⟩
        rw [pow_succ]
        exact mul_le_mul hle hc (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
    · rintro a b ⟨h₁, hh₁, h₁le⟩ ⟨h₂, hh₂, h₂le⟩
      rw [hadd]
      rcases le_total ‖M.val (gPt q ≫ y) (h₁ : Ω)‖ ‖M.val (gPt q ≫ y) (h₂ : Ω)‖ with hc | hc
      · exact ⟨h₂, hh₂, (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (h₁le.trans (pow_le_pow_left₀ (norm_nonneg _) hc _)) h₂le)⟩
      · exact ⟨h₁, hh₁, (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le h₁le (h₂le.trans (pow_le_pow_left₀ (norm_nonneg _) hc _)))⟩

variable (hπ : M₁.IsHom M (AlgHom.id o Ω) π)

def approxIdeal (U : M.Z.Opens) (D : EffCartierData M.Z) (z : M₁.Z) (e : ℕ) : Ideal (M₁.O z) where
  carrier := {F | ∀ (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ M.Z), π (y (cPt q)) = z → Set.range (gPt q ≫ y) ⊆ U →
    ∀ f, EqAt M D (y (cPt q)) f → ‖M.val (gPt q ≫ y) (F : Ω)‖ ≤ ‖M.val (gPt q ≫ y) f‖ ∨
      ∃ h, NonUnitAt M₁ z h ∧ ‖M.val (gPt q ≫ y) (F : Ω)‖ ≤ ‖M.val (gPt q ≫ y) h‖ ^ e}
  add_mem' := by
    intro a b ha hb q _ y hy hU f hf
    have hs : ∀ w, (gPt q ≫ y) w ⤳ y (cPt q) := RatModel.gPt_specializes rfl
    have e1 : M.val (gPt q ≫ y) ((a + b : M₁.O z) : Ω) = M.val (gPt q ≫ y) a + M.val (gPt q ≫ y) b :=
      RatModel.val_add hs (mem_O_of_isHom hπ (hy ▸ a.2)) (mem_O_of_isHom hπ (hy ▸ b.2))
    rw [e1]
    rcases le_total ‖M.val (gPt q ≫ y) (a : Ω)‖ ‖M.val (gPt q ≫ y) (b : Ω)‖ with h | h
    · exact bound_mono ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le h le_rfl)) (hb q y hy hU f hf)
    · exact bound_mono ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl h)) (ha q y hy hU f hf)
  zero_mem' := by
    intro q _ y hy hU f hf
    left
    simp [RatModel.val_zero]
  smul_mem' := by
    intro c a ha q _ y hy hU f hf
    have hs : ∀ w, (gPt q ≫ y) w ⤳ y (cPt q) := RatModel.gPt_specializes rfl
    have e1 : M.val (gPt q ≫ y) ((c • a : M₁.O z) : Ω) = M.val (gPt q ≫ y) c * M.val (gPt q ≫ y) a :=
      RatModel.val_mul hs (mem_O_of_isHom hπ (hy ▸ c.2)) (mem_O_of_isHom hπ (hy ▸ a.2))
    rw [e1, norm_mul]
    exact bound_mono (mul_le_of_le_one_left (norm_nonneg _) (norm_val_le_one' hπ hy c.2)) (ha q y hy hU f hf)

def fibreIdeal (D : EffCartierData M.Z) (z : M₁.Z) : Ideal (M₁.O z) where
  carrier := {G | ∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x'}
  add_mem' := by
    intro a b ha hb x' hx f hf
    rw [Subalgebra.coe_add, add_div]
    exact add_mem (ha x' hx f hf) (hb x' hx f hf)
  zero_mem' := by
    intro x' hx f hf
    simp
  smul_mem' := by
    intro c a ha x' hx f hf
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_div_assoc]
    exact mul_mem (mem_O_of_isHom hπ (by rw [hx]; exact c.2)) (ha x' hx f hf)

variable {hπ}

theorem mem_fibreIdeal {D : EffCartierData M.Z} {z : M₁.Z} {G : M₁.O z} :
    G ∈ fibreIdeal hπ D z ↔ ∀ x' : M.Z, π x' = z → ∀ f', EqAt M D x' f' → (G : Ω) / f' ∈ M.O x' := Iff.rfl

theorem approxIdeal_antitone (U : M.Z.Opens) (D : EffCartierData M.Z) (z : M₁.Z) :
    Antitone (approxIdeal hπ U D z) := by
  intro e e' hee F hF q _ y hy hU f hf
  rcases hF q y hy hU f hf with h | ⟨h, hh, hle⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, hh, hle.trans (pow_le_pow_of_le_one (norm_nonneg _) (norm_val_le_one' hπ hy hh.1) hee)⟩

theorem pow_le_approxIdeal (U : M.Z.Opens) (D : EffCartierData M.Z) (z : M₁.Z) (e : ℕ) :
    maximalIdeal (M₁.O z) ^ e ≤ approxIdeal hπ U D z e := by
  intro F hF q _ y hy hU f hf
  obtain ⟨h, hh, hle⟩ := exists_nonUnit_pow hπ hy e F hF
  exact Or.inr ⟨h, nonUnitAt_of_not_isUnit hh, hle⟩

theorem isNoetherianRing_O [ArithBase o Ω] (M : RatModel o Ω) (z : M.Z) : IsNoetherianRing (M.O z) := by
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  exact isNoetherianRing_of_ringEquiv _ (M.stalkEquiv z)

end GlobalTheory.FibreCorr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipal
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

namespace GlobalTheory.IdealSpread

theorem exists_of_map_eq_span {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (M : Submonoid A)
    [IsLocalization M R] {J : Ideal A} (hJ : J.FG) (d : A)
    (h : J.map (algebraMap A R) = Ideal.span {algebraMap A R d}) :
    ∃ s ∈ M, s * d ∈ J ∧ ∀ j ∈ J, ∃ c, s * j = c * d := by

  obtain ⟨s₁, hs₁M, hs₁⟩ : ∃ s₁ ∈ M, s₁ * d ∈ J := by
    have hd : algebraMap A R d ∈ J.map (algebraMap A R) := h ▸ Ideal.subset_span rfl
    obtain ⟨⟨⟨a, ha⟩, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff M R).1 hd
    simp only at hm
    rw [← map_mul] at hm
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) hm
    refine ⟨c * m, M.mul_mem c.2 m.2, ?_⟩
    have : (c : A) * (d * m) = c * a := hc
    rw [show (c : A) * m * d = c * (d * m) by ring, this]
    exact J.mul_mem_left _ ha

  have hone : ∀ g ∈ J, ∃ t ∈ M, ∃ c, t * g = c * d := by
    intro g hg
    have hg' : algebraMap A R g ∈ Ideal.span {algebraMap A R d} := h ▸ Ideal.mem_map_of_mem _ hg
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hg'
    obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj M r
    simp only at ham
    have : algebraMap A R (m * g) = algebraMap A R (a * d) := by
      rw [map_mul, map_mul, ← ham, ← hr]; ring
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) this
    exact ⟨c * m, M.mul_mem c.2 m.2, c * a, by linear_combination hc⟩
  have key : ∀ T : Finset A, (∀ g ∈ T, ∃ t ∈ M, ∃ c, t * g = c * d) → ∃ t ∈ M, ∀ g ∈ T, ∃ c, t * g = c * d := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, M.one_mem, by simp⟩
    | insert a S haS ih =>
      intro hT
      obtain ⟨t, htM, ht⟩ := ih (fun g hg => hT g (Finset.mem_insert_of_mem hg))
      obtain ⟨t', ht'M, c', hc'⟩ := hT a (Finset.mem_insert_self a S)
      refine ⟨t * t', M.mul_mem htM ht'M, fun g hg => ?_⟩
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact ⟨t * c', by rw [mul_assoc, hc', mul_assoc]⟩
      · obtain ⟨c, hc⟩ := ht g hg
        exact ⟨t' * c, by rw [mul_comm t t', mul_assoc, hc, mul_assoc]⟩
  obtain ⟨S, rfl⟩ := hJ
  obtain ⟨t, htM, ht⟩ := key S fun g hg => hone g (Ideal.subset_span hg)
  have hall : ∀ j ∈ Ideal.span (S : Set A), ∃ c, t * j = c * d := by
    intro j hj
    induction hj using Submodule.span_induction with
    | mem x hx => exact ht x hx
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [mul_add, ha, hb, add_mul]⟩
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      exact ⟨a * b, by rw [smul_eq_mul, mul_left_comm, hb, mul_assoc]⟩
  refine ⟨s₁ * t, M.mul_mem hs₁M htM, ?_, fun j hj => ?_⟩
  · rw [mul_comm s₁ t, mul_assoc]
    exact Ideal.mul_mem_left _ _ hs₁
  · obtain ⟨c, hc⟩ := hall j hj
    exact ⟨s₁ * c, by rw [mul_assoc, hc, mul_assoc]⟩

end GlobalTheory.IdealSpread

namespace GlobalTheory.IdealSpread

theorem ideal_eq_span_of_germ (X : Scheme.{0}) (I : X.IdealSheafData) (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1)
    (d : Γ(X, U.1)) (hN : IsNoetherianRing Γ(X, U.1))
    (h : (I.ideal U).map (X.presheaf.germ U.1 x₀ hx).hom = Ideal.span {(X.presheaf.germ U.1 x₀ hx).hom d}) :
    ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ ∀ t : Γ(X, U.1), X.basicOpen t ≤ X.basicOpen s →
      I.ideal (X.affineBasicOpen t) = Ideal.span {resG X (X.basicOpen_le t) d} := by
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x₀) := (X.presheaf.germ U.1 x₀ hx).hom.toAlgebra
  haveI hL : IsLocalization.AtPrime (X.presheaf.stalk x₀) (U.2.primeIdealOf ⟨x₀, hx⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x₀, hx⟩
  obtain ⟨s, hsM, hsd, hsJ⟩ := exists_of_map_eq_span (R := X.presheaf.stalk x₀)
    (U.2.primeIdealOf ⟨x₀, hx⟩).asIdeal.primeCompl (IsNoetherian.noetherian (I.ideal U)) d h
  refine ⟨s, (X.mem_basicOpen s x₀ hx).2 (IsLocalization.map_units (X.presheaf.stalk x₀) ⟨s, hsM⟩), fun t ht => ?_⟩
  have hu : IsUnit (resG X (X.basicOpen_le t) s) := by
    have h0 : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
    have h1 := h0.map (resG X ht)
    have e : resG X ht (resG X (X.basicOpen_le s) s) = resG X (X.basicOpen_le t) s := by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
      rfl
    rwa [e] at h1
  rw [← I.map_ideal_basicOpen U t]
  change (I.ideal U).map (resG X (X.basicOpen_le t)) = _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    obtain ⟨c, hc⟩ := hsJ j hj
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨↑hu.unit⁻¹ * resG X (X.basicOpen_le t) c, ?_⟩
    have := congrArg (resG X (X.basicOpen_le t)) hc
    rw [map_mul, map_mul] at this
    rw [mul_assoc, ← this, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hm := Ideal.mem_map_of_mem (resG X (X.basicOpen_le t)) hsd
    rw [map_mul] at hm
    have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : Γ(X, X.basicOpen t)) hm
    rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this

end GlobalTheory.IdealSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipalStatement
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
theorem _root_.GlobalTheory.T.idealSheaf_eq_span_on_basicOpens_of_stalk_principal : ∀ (X : Scheme.{0}) (I : X.IdealSheafData) (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1) (d : Γ(X, U.1)), IsNoetherianRing Γ(X, U.1) → (I.ideal U).map (X.presheaf.germ U.1 x₀ hx).hom = Ideal.span {(X.presheaf.germ U.1 x₀ hx).hom d} → ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ ∀ t : Γ(X, U.1), X.basicOpen t ≤ X.basicOpen s → I.ideal (X.affineBasicOpen t) = Ideal.span {resG X (X.basicOpen_le t) d} := by
  first | exact @GlobalTheory.IdealSpread.ideal_eq_span_of_germ | exact GlobalTheory.IdealSpread.ideal_eq_span_of_germ | (intros; apply GlobalTheory.IdealSpread.ideal_eq_span_of_germ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemMaximalIdealExpLeNormVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ShortVec

theorem nonneg_of_tendsto {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) : 0 ≤ q a := by
  by_contra h
  have h : q a < 0 := not_le.1 h
  have hfin : {x | ¬ (0 : ℝ) ≤ q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_ge_atTop 0)
  have hv : ∀ n : ℕ, q (((n : ℤ) + 1) • a) = ((n : ℝ) + 1) ^ 2 * q a := fun n => by
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    ring
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℤ) + 1) • a) (fun m n e => ?_)
    (fun n => ?_) hfin
  · have e' := congrArg q e
    simp only [hv] at e'
    have e2 := mul_right_cancel₀ h.ne e'
    have e3 := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 e2
    exact_mod_cast add_right_cancel e3
  · simp only [Set.mem_setOf_eq, hv, not_le]
    exact mul_neg_of_pos_of_neg (by positivity) h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}

theorem val_mul_gen {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {a b : Ω}
    (ha : a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))))
    (hb : b ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)))) :
    M.val (gPt p ≫ y) (a * b) = M.val (gPt p ≫ y) a * M.val (gPt p ≫ y) b :=
  RatModel.val_mul (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)) ha hb

theorem norm_th_eq_and_HH_eq {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}
    (hc : y (cPt p) = z) (hR : ∀ a ∈ S.R, a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))))
    (hAt : S.At M y y₀) (τ : S.Test p y₀) {x₀ : S.Gam} (hx₀ : M.Div S.th x₀ z) :
    ‖M.val (gPt p ≫ y) (S.th x₀)‖ = τ.δ ∧ S.HH M z = τ.yy.ker := by
  have hsp := RatModel.gPt_specializes hc (IsLocalRing.closedPoint (PadicAlgCl p))
  have hy : ∀ x, y₀ ⟨S.th x, S.th_mem x⟩ = M.val (gPt p ≫ y) (S.th x) := fun x => hAt _
  have hmul : ∀ x, ‖M.val (gPt p ≫ y) (S.th x)‖ =
      ‖M.val (gPt p ≫ y) (S.th x / S.th x₀)‖ * ‖M.val (gPt p ≫ y) (S.th x₀)‖ := by
    intro x
    rw [← norm_mul, ← val_mul_gen y (RatModel.O_le_of_specializes hsp (hx₀.2 x))
      (hR _ (S.th_mem x₀)), div_mul_cancel₀ _ hx₀.1]
  have hδ : ‖M.val (gPt p ≫ y) (S.th x₀)‖ = τ.δ := by
    apply le_antisymm
    · rw [← hy]
      exact τ.δ_max.2 ⟨x₀, rfl⟩
    · obtain ⟨x₁, hx₁⟩ := τ.δ_max.1
      simp only [hy] at hx₁
      rw [← hx₁, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hc (hx₀.2 x₁))
  have key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x
    change M.Div S.th x z ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff hc (hx₀.2 x), hmul x, hδ]
    exact (mul_eq_right₀ τ.δ_pos.ne').symm
  refine ⟨hδ, ?_⟩
  rw [← τ.supp, ThetaSys.HH]
  congr 1
  ext x
  rw [key x, Set.mem_setOf_eq, hy]

theorem exists_open (S : ThetaSys o Ω) (M : RatModel o Ω) (b : Ω) :
    ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ S.R ≤ M.ringOn U ∧ b ∈ M.ringOn U := by
  obtain ⟨s, hs⟩ := S.fg
  refine ⟨⟨{z | b ∈ M.O z} ∩ ⋂ a ∈ s, {z | a ∈ M.O z},
    (M.isOpen_setOf_mem_O b).inter (isOpen_biInter_finset fun a _ => M.isOpen_setOf_mem_O a)⟩,
    ⟨genericPoint M.Z, ?_, ?_⟩, ?_, RatModel.mem_ringOn.2 fun z hz => hz.1⟩
  · simp [RatModel.O_genericPoint]
  · simp [RatModel.O_genericPoint]
  · rw [← hs]
    exact Algebra.adjoin_le fun a ha => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter₂.1 hz.2 a ha

end GlobalTheory.ShortVec

namespace GlobalTheory

open ShortVec

theorem exists_mem_maximalIdeal_exp_le_norm_val :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω),
    IsNormalScheme M.Z → M.HasDiv S.th → S.HasTests → ∀ (z₁ : M.Z), IsClosed ({z₁} : Set M.Z) →
    ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p), y (cPt p) = z₁ →
    (∀ a ∈ S.R, a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)))) → S.At M y y₀ →
    ∀ (τ : S.Test p y₀) (α : τ.X), (∀ v0, τ.q α ≤ τ.q (α + S.N • v0)) → 0 < τ.q α →
    ∃ h ∈ maximalIdeal (M.Z.presheaf.stalk z₁),
      Real.exp (-(τ.q α / S.N)) ≤ ‖M.val (gPt p ≫ y) (M.stalkHom z₁ h)‖ := by
  intro o Ω _ _ _ hb S M hn hd hT z hz p _ y y₀ hc hR hAt τ α hα hpos
  haveI := hb.ft
  haveI := hb.char
  obtain ⟨j, hj⟩ := hd z
  obtain ⟨hδ, hH⟩ := norm_th_eq_and_HH_eq hc hR hAt τ hj
  obtain ⟨k, hk, he⟩ := τ.eq α hα
  obtain ⟨U, hU, hRU, hbU⟩ := exists_open S M (S.FF _ (τ.wt α) k / S.th j)
  have hreg : S.FF _ (τ.wt α) k / S.th j ∈ M.O z := by
    refine ((classical_points_and_local_regularity o Ω M U fun x => ⟨hn.1 x, hn.2 x⟩).1 U le_rfl hU z hz).2 _ hbU fun p' _ y' hy' => ?_
    let w : Sp (PadicAlgCl p') := IsLocalRing.closedPoint (PadicAlgCl p')
    have hw : (gPt p' ≫ y') w ∈ (U : Set M.Z) := hy'.2 ⟨w, rfl⟩
    have hle : S.R ≤ M.O ((gPt p' ≫ y') w) := hRU.trans (RatModel.ringOn_le_O hw)
    let y₀' : S.R →+* PadicAlgCl p' :=
      (RatModel.valHom (gPt p' ≫ y') _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
    have hint : ∀ a : o, ‖y₀' (algebraMap o S.R a)‖ ≤ 1 := fun a =>
      hy'.norm_val_le_one (x := algebraMap o Ω a) ((M.O z).algebraMap_mem a)
    have hAt' : S.At M y' y₀' := fun _ => rfl
    obtain ⟨τ'⟩ := hT p' y₀' hint
    obtain ⟨hδ', hH'⟩ := norm_th_eq_and_HH_eq hy'.1 (fun a ha => hle ha) hAt' τ' hj
    obtain ⟨β, -, -, hβ⟩ := (thetaSys_norm_FF_le_exp o Ω S (test_weights o Ω S) p' y₀' τ' hint _ (τ.wt α) k hk
      τ.isoFree).2 (by rw [← hH', hH])
    have hexp : Real.exp (-(τ'.q β / S.N)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (nonneg_of_tendsto _ τ'.pos β) (Nat.cast_nonneg _)))
    have hmul := val_mul_gen y' (RatModel.ringOn_le_O hw hbU) (hle (S.th_mem j))
    rw [div_mul_cancel₀ _ hj.1] at hmul
    rw [hAt'] at hβ
    change ‖M.val (gPt p' ≫ y') (S.FF _ (τ.wt α) k)‖ ≤ _ at hβ
    rw [hmul, norm_mul, hδ', mul_comm] at hβ
    exact (le_of_mul_le_mul_left hβ τ'.δ_pos).trans hexp
  have hmul := val_mul_gen y (RatModel.O_le_of_specializes (RatModel.gPt_specializes hc _) hreg) (hR _ (S.th_mem j))
  rw [div_mul_cancel₀ _ hj.1] at hmul
  rw [hAt] at he
  change ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k)‖ = _ at he
  rw [hmul, norm_mul, hδ, mul_comm] at he
  have he' := mul_left_cancel₀ τ.δ_pos.ne' he
  have hN : (0 : ℝ) < S.N := by
    have := S.N_ge
    exact_mod_cast (by omega : 0 < S.N)
  have hlt : ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k / S.th j)‖ < 1 := by
    rw [he']
    exact Real.exp_lt_one_iff.2 (neg_neg_of_pos (div_pos hpos hN))
  have hnu := (RatModel.norm_val_lt_one_iff hc hreg).1 hlt
  refine ⟨(M.stalkEquiv z).symm ⟨_, hreg⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MulEquiv.isUnit_map]
    exact hnu
  · rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    exact he'.ge

end GlobalTheory
end
