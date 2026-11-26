module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomDescendsToSubfieldContainingFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomDescendsToSubfieldContainingFinset
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

private theorem surjective_flat_quasiCompact_spMap {k K : Type} [Field k] [Field K] (σ : k →+* K) :
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show Surjective (Spec.map (CommRingCat.ofHom σ))
    constructor
    intro x
    obtain ⟨y⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
    exact ⟨y, Subsingleton.elim _ _⟩
  · show Flat (Spec.map (CommRingCat.ofHom σ))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := σ.toAlgebra
    show Module.Flat k K
    infer_instance
  · show QuasiCompact (Spec.map (CommRingCat.ofHom σ))
    infer_instance

theorem _root_.GlobalTheory.hom_descends_to_subfield_containing_finset :
    ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X Y : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) (X₀ Y₀ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k)) (φ : X.left ⟶ X₀.left) (ψ : Y.left ⟶ Y₀.left), IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → IsPullback ψ Y.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) → QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFiniteType Y.hom → ∀ f : X ⟶ Y, ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ Y₁ : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k₁)) (φ₁ : X.left ⟶ X₁.left) (χ : X₁.left ⟶ X₀.left) (ψ₁ : Y.left ⟶ Y₁.left) (ω : Y₁.left ⟶ Y₀.left), IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap α) → φ₁ ≫ χ = φ → ψ₁ ≫ ω = ψ → φ₁ ≫ X₁.hom = X.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ψ₁ ≫ Y₁.hom = Y.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap β → ∃ f₁ : X₁ ⟶ Y₁, φ₁ ≫ f₁.left = f.left ≫ ψ₁ := by
  intro k K _ _ σ X Y X₀ Y₀ φ ψ hX hY hqc hqs hft f
  letI : Algebra k K := σ.toAlgebra
  have hσ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap σ) :=
    surjective_flat_quasiCompact_spMap σ
  haveI := _root_.GlobalTheory.quasiCompact_descendsAlong_fpqc
  haveI := _root_.GlobalTheory.quasiSeparated_descendsAlong_fpqc
  haveI : QuasiCompact X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqc
  haveI : QuasiSeparated X₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hX.flip hσ hqs
  haveI : LocallyOfFiniteType Y₀.hom :=
    MorphismProperty.of_isPullback_of_descendsAlong hY.flip hσ hft
  haveI : IsLocallyNoetherian (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) := by
    show IsLocallyNoetherian (Spec (CommRingCat.of k)); infer_instance
  haveI : LocallyOfFinitePresentation Y₀.hom :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.2 inferInstance
  have hX' : IsPullback φ X.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) := hX
  have hΦ : (hX'.isoPullback.inv ≫ f.left ≫ ψ) ≫ Y₀.hom =
      pullback.fst X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k K)) ≫ X₀.hom := by
    simp only [Category.assoc, hY.w, Over.w_assoc]
    rw [hX'.isoPullback_inv_snd_assoc]
    exact pullback.condition.symm
  obtain ⟨R, Ψ, hRfg, hΨ, hRΨ⟩ :=
    _root_.GlobalTheory.Spread.exists_fg_comp_eq X₀.hom Y₀.hom (hX'.isoPullback.inv ≫ f.left ≫ ψ) hΦ
  obtain ⟨s, hs⟩ := hRfg
  refine ⟨s, ?_⟩
  intro k₁ _ α β hβα hsβ X₁ Y₁ φ₁ χ ψ₁ ω hX₁ hY₁ hφ₁ hψ₁ hφ₁s hψ₁s
  letI : Algebra k k₁ := α.toAlgebra
  have hβα' : ∀ r : k, β (α r) = σ r := fun r => by rw [← hβα]; rfl
  let β' : k₁ →ₐ[k] K := { β with commutes' := fun r => hβα' r }
  have hβinj : Function.Injective β' := β.injective
  have hle : R ≤ β'.range := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := hsβ hx
    exact ⟨y, rfl⟩
  let g : R →ₐ[k] k₁ :=
    (AlgEquiv.ofInjective β' hβinj).symm.toAlgHom.comp (Subalgebra.inclusion hle)
  have hg : ∀ x : R, β' (g x) = R.val x := fun x =>
    congrArg Subtype.val ((AlgEquiv.ofInjective β' hβinj).apply_symm_apply (Subalgebra.inclusion hle x))
  have hX₁' : IsPullback χ X₁.hom X₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hX₁
  have hY₁' : IsPullback ω Y₁.hom Y₀.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁)) := hY₁
  have hm : (hX₁'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom g ≫ Ψ) ≫ Y₀.hom =
      X₁.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k k₁) := by
    simp only [Category.assoc, hΨ, _root_.GlobalTheory.Spread.bcMap_fst_assoc,
      hX₁'.isoPullback_hom_fst_assoc]
    exact hX₁'.w
  have key : φ₁ ≫ hX₁'.isoPullback.hom =
      hX'.isoPullback.hom ≫ _root_.GlobalTheory.Spread.bcMap X₀.hom β' := by
    apply pullback.hom_ext
    · rw [Category.assoc, hX₁'.isoPullback_hom_fst, hφ₁, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_fst, hX'.isoPullback_hom_fst]
    · rw [Category.assoc, hX₁'.isoPullback_hom_snd, hφ₁s, Category.assoc,
        _root_.GlobalTheory.Spread.bcMap_snd, hX'.isoPullback_hom_snd_assoc]
  refine ⟨Over.homMk (hY₁'.lift _ X₁.hom hm) (hY₁'.lift_snd _ _ _), ?_⟩
  show φ₁ ≫ hY₁'.lift _ X₁.hom hm = f.left ≫ ψ₁
  apply hY₁'.hom_ext
  · rw [Category.assoc, hY₁'.lift_fst, Category.assoc, hψ₁, reassoc_of% key,
      _root_.GlobalTheory.Spread.bcMap_comp_of_eq_assoc X₀.hom g β' R.val hg, hRΨ,
      Iso.hom_inv_id_assoc]
  · rw [Category.assoc, hY₁'.lift_snd, hφ₁s, Category.assoc, hψ₁s, Over.w_assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomDescendsToSubfieldContainingFinsetStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.hom_descends_to_subfield_containing_finset_alt : ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X Y : Over (Sp K)) (X₀ Y₀ : Over (Sp k)) (φ : X.left ⟶ X₀.left) (ψ : Y.left ⟶ Y₀.left), IsPullback φ X.hom X₀.hom (spMap σ) → IsPullback ψ Y.hom Y₀.hom (spMap σ) → QuasiCompact X.hom → QuasiSeparated X.hom → LocallyOfFiniteType Y.hom → ∀ f : X ⟶ Y, ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ Y₁ : Over (Sp k₁)) (φ₁ : X.left ⟶ X₁.left) (χ : X₁.left ⟶ X₀.left) (ψ₁ : Y.left ⟶ Y₁.left) (ω : Y₁.left ⟶ Y₀.left), IsPullback χ X₁.hom X₀.hom (spMap α) → IsPullback ω Y₁.hom Y₀.hom (spMap α) → φ₁ ≫ χ = φ → ψ₁ ≫ ω = ψ → φ₁ ≫ X₁.hom = X.hom ≫ spMap β → ψ₁ ≫ Y₁.hom = Y.hom ≫ spMap β → ∃ f₁ : X₁ ⟶ Y₁, φ₁ ≫ f₁.left = f.left ≫ ψ₁ := by
  first | exact @GlobalTheory.hom_descends_to_subfield_containing_finset | exact GlobalTheory.hom_descends_to_subfield_containing_finset | (intros; apply GlobalTheory.hom_descends_to_subfield_containing_finset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawAbelianSchemeProperClosure
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawAbelianSchemeProperClosure
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem isGrpPullback_of_dominant {W S Z : Scheme.{0}} (j : W ⟶ S) [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] {H : Over S} [GrpObj H] [Flat H.hom] {G : Over Z} [GrpObj G]
    [IsSeparated G.hom] {y : S ⟶ Z} {f : H.left ⟶ G.left} (hf : IsPullback f H.hom G.hom y)
    (h : IsGrpPullback ((Over.pullback j).obj H) G (j ≫ y) (pullback.fst H.hom j ≫ f)) :
    IsGrpPullback H G y f := by
  let e : H ≅ (Over.pullback y).obj G :=
    Over.isoMk hf.isoPullback hf.isoPullback_hom_snd
  have he : e.hom.left ≫ pullback.fst G.hom y = f := hf.isoPullback_hom_fst
  have hs : IsSeparated ((Over.pullback y).obj G).hom := by
    change IsSeparated (pullback.snd G.hom y)
    infer_instance
  have h₁ : IsGrpPullback ((Over.pullback j).obj H) ((Over.pullback y).obj G) j
      (pullback.fst H.hom j ≫ e.hom.left) :=
    (isGrpPullback_pullback G y).cancel (h.congr rfl (by rw [Category.assoc, he]))
      (by rw [Category.assoc, Over.w]; exact pullback.condition)
  have h₂ : IsMonHom e.hom :=
    ExtUnique.isMonHom_of_isGrpPullback (isGrpPullback_pullback H j) h₁ (𝟙 _) e.hom
      (by rw [Over.id_left, Category.id_comp])
  exact ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G y)).congr (Category.id_comp _) he

theorem Core.nonempty_law : ∀ C : Core, SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → (∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a) → (∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a) → Nonempty C.Law := by
  rintro C hsm hcart ⟨m, hm⟩ ⟨i, hi⟩
  have := C.proper
  have hsep : IsSeparated C.GG.hom := by
    change IsSeparated (C.G.ι ≫ C.P.hom)
    infer_instance
  have hsmooth : Smooth C.GG.hom := SmoothOfRelativeDimension.smooth C.g _
  have hne : Nonempty C.U.toScheme := C.ne.to_subtype
  have hpb : IsPullback C.a C.A.hom C.GG.hom C.U.ι := by
    have w : C.a ≫ C.GG.hom = C.A.hom ≫ C.U.ι := by
      rw [← C.cart.w, Category.assoc]; rfl
    refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
      (fun s => C.cart.lift (s.fst ≫ C.G.ι) s.snd (by rw [Category.assoc]; exact s.condition))
      (fun s => ?_) (fun s => C.cart.lift_snd _ _ _) (fun s t h₁ h₂ => ?_)⟩⟩
    · rw [← cancel_mono C.G.ι, Category.assoc]
      exact C.cart.lift_fst _ _ _
    · apply C.cart.hom_ext
      · rw [C.cart.lift_fst, ← h₁, Category.assoc]
      · rw [C.cart.lift_snd, h₂]
  let e : 𝟙_ (Over C.Z) ⟶ C.GG := Over.homMk C.e C.e_sec
  obtain ⟨grp, -, hη, -, comm, pull⟩ :=
    grpObj_of_dense_open C.Z C.U.toScheme C.U.ι C.GG C.A C.a hpb m i e hm hi C.e_zero
  refine ⟨{ smooth := hsm, zero := congrArg (fun z => z.left) hη, pull := pull, test := fun p _ y τ => ?_ }⟩
  obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing τ.V (FractionRing τ.V)
  have := τ.smooth
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  exact isGrpPullback_of_dominant (Out.jK τ.V) (hcart p y τ) ((τ.φ_cart.comp pull).congr τ.yK_fac τ.φ_f)

end GlobalTheory.ZJ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawAbelianSchemeProperClosureStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.nonempty_law_abelianSchemeProperClosure : ∀ C : Core, SmoothOfRelativeDimension C.g C.GG.hom → C.TestCart → (∃ m : C.GG ⊗ C.GG ⟶ C.GG, ∀ φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left, IsSquare C.a φ₂ → φ₂ ≫ m.left = (μ[C.A]).left ≫ C.a) → (∃ i : C.GG ⟶ C.GG, C.a ≫ i.left = (ι[C.A]).left ≫ C.a) → Nonempty C.Law := by
  first | exact @GlobalTheory.ZJ.Core.nonempty_law | exact GlobalTheory.ZJ.Core.nonempty_law | (intros; apply GlobalTheory.ZJ.Core.nonempty_law <;> assumption)
end
end
