module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveClosureIsProjOver
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralClosureFiniteLocalOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataTorsionStructureAlgClosed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoMorphismRestrictOfLocalDominantSections
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

open GlobalTheory.Points

theorem isIso_pullback_snd_of_dominant_section {X Y V : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (q : V ⟶ Y) [IsOpenImmersion q] (g : V ⟶ X) [IsDominant g] (h : g ≫ f = q) : IsIso (pullback.snd f q) := by
  let σ : V ⟶ pullback f q := pullback.lift g (𝟙 V) (by rw [h, Category.id_comp])
  have e1 : σ ≫ pullback.fst f q = g := pullback.lift_fst _ _ _
  have e2 : σ ≫ pullback.snd f q = 𝟙 V := pullback.lift_snd _ _ _
  have : IsReduced (pullback f q) := isReduced_of_isOpenImmersion (pullback.fst f q)
  have : IsDominant (σ ≫ pullback.fst f q) := e1 ▸ inferInstance
  have : IsDominant σ := IsDominant.of_comp_of_isOpenImmersion σ (pullback.fst f q)
  refine ⟨σ, ?_, e2⟩
  refine ext_of_isDominant_of_isSeparated (pullback.snd f q) ?_ σ ?_
  · rw [Category.assoc, e2, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem isIso_of_local_dominant_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (h : ∀ y : Y, ∃ (V : Scheme.{0}) (q : V ⟶ Y) (_ : IsOpenImmersion q) (g : V ⟶ X),
      y ∈ Set.range q ∧ IsDominant g ∧ g ≫ f = q) : IsIso f := by
  choose V q hq g hy hg e using h
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y V q fun y => ⟨y, hy y⟩
  exact IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms _) 𝒰 fun y =>
    haveI := hq y
    haveI := hg y
    isIso_pullback_snd_of_dominant_section f (q y) (g y) (e y)

theorem isIso_morphismRestrict_of_local_dominant_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (W : Y.Opens) (h : ∀ y ∈ W, ∃ (V : Scheme.{0}) (q : V ⟶ Y) (_ : IsOpenImmersion q) (g : V ⟶ X),
      y ∈ Set.range q ∧ Set.range q ⊆ W ∧ IsDominant g ∧ g ≫ f = q) : IsIso (f ∣_ W) := by
  have : IsSeparated (f ∣_ W) := IsZariskiLocalAtTarget.restrict (P := @IsSeparated) ‹_› W
  refine isIso_of_local_dominant_sections _ fun y => ?_
  obtain ⟨V, q, hq, g, ⟨v, hv⟩, hW, hg, e⟩ := h y.1 y.2
  have h1 : Set.range q ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
  have h2 : Set.range g ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact hW ⟨w, by rw [← e]; rfl⟩
  have e1 := IsOpenImmersion.lift_fac W.ι q h1
  have e2 := IsOpenImmersion.lift_fac (f ⁻¹ᵁ W).ι g h2
  have : IsOpenImmersion (IsOpenImmersion.lift W.ι q h1 ≫ W.ι) := e1.symm ▸ hq
  have : IsDominant (IsOpenImmersion.lift (f ⁻¹ᵁ W).ι g h2 ≫ (f ⁻¹ᵁ W).ι) := e2.symm ▸ hg
  refine ⟨V, IsOpenImmersion.lift W.ι q h1, IsOpenImmersion.of_comp _ W.ι, IsOpenImmersion.lift (f ⁻¹ᵁ W).ι g h2,
    ⟨v, ?_⟩, IsDominant.of_comp_of_isOpenImmersion _ (f ⁻¹ᵁ W).ι, ?_⟩
  · refine Subtype.ext ?_
    rw [← hv]
    conv_rhs => rw [← e1]
    rfl
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e2, e, e1]

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M M' : RatModel o Ω}

theorem IsNm.isIso_morphismRestrict {J : Type} [Finite J] {u : J → Ω} (h' : M'.IsNm u)
    (hn : ∀ z, IsIntegrallyClosed (M.O z)) {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' (AlgHom.id o Ω) f) (W : M.Z.Opens)
    (hW : ∀ z ∈ W, ∃ i, M.Div u i z) : IsIso (f ∣_ W) := by
  have := M.sep
  have : IsSeparated (f ≫ M.s) := hf.inducedModelMorphism_comp_structureMap.symm ▸ M'.sep
  have : IsSeparated f := IsSeparated.of_comp f M.s
  refine isIso_morphismRestrict_of_local_dominant_sections f W fun z hz => ?_
  obtain ⟨i, hi⟩ := hW z hz
  obtain ⟨U, hU, hD, hR⟩ := h'.2 i hi.1
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := W ⊓ ⟨_, M.isOpen_setOf_div u i⟩) (x := z) ⟨hz, hi⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint M'.Z, hD ▸ div_genericPoint hi.1⟩ (V := V) ⟨z, hzV⟩
    fun x hx => mem_ringOn.2 fun w hw =>
      Div.map_mem_O_of_isIntegral (M' := M) (φ := AlgHom.id o Ω) (t := u) (i := i) (z := w) (hle hw).2 ((hR x).1 hx)
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hzV⟩)
  have hid : ∀ {Y : Scheme.{0}} (a : Sp Ω ⟶ Y), spMap (AlgHom.id o Ω).toRingHom ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hzV⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hzV, hV.range_fromSpec ▸ fun w hw => (hle hw).1,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hzV⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hf

end RatModel

theorem isIso_morphismRestrict_of_isNm_prod : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (M' : RatModel o Ω) (J J' : Type) [Finite J] [Finite J'] (t : J → Ω) (t' : J' → Ω) (f : M'.Z ⟶ M.Z), M.IsNm t → M'.IsNm (fun q : J × J' => t q.1 * t' q.2) → IsProper M'.s → M.IsHom M' (AlgHom.id o Ω) f → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ i', M.Div t' i' z) → IsIso (f ∣_ W) := by
  intro o Ω _ _ _ M M' J J' _ _ t t' f h h' _ hf W hW
  refine h'.isIso_morphismRestrict (RatModel.isIntegrallyClosed_O (fun x => ⟨h.isNormalScheme.1 x, h.isNormalScheme.2 x⟩)) hf W fun z hz => ?_
  obtain ⟨i, hi⟩ := h.1 z
  obtain ⟨i', hi'⟩ := hW z hz
  exact ⟨(i, i'), RatModel.div_prod_iff.2 ⟨hi, hi'⟩⟩

end GlobalTheory.ZH
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAtTestOfCen
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem exists_at_test_of_cen :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.HasTests → S.Over₀ M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) := by
  intro o Ω _ _ _ _ S M U₀ hT hO z p _ y hy
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    hy.norm_val_le_one (x := algebraMap o Ω a) ((M.O z).algebraMap_mem a)
  exact ⟨y₀, fun _ => rfl, hn, hT p y₀ hn⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem exists_sectionHom {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (a : T.left ⟶ S) (ha : a = T.hom ≫ f) :
    ∃ ρ : (T ⟶ G') →* (Over.mk a ⟶ G), (∀ x, (ρ x).left = x.left ≫ φ) ∧ Function.Surjective ρ := by
  subst ha
  refine ⟨pushHom h T, fun _ => rfl, fun c => ?_⟩
  exact ⟨Over.homMk (h.1.lift c.left T.hom (Over.w c)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem eSec_comp_of_isGrpPullback {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    eSec G' ≫ φ = (f : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left) ≫ eSec G := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  have e₁ : (1 : 𝟙_ (Over S') ⟶ G') = η[G'] := by
    rw [Hom.one_def]; simp
  rw [e₁] at e
  refine e.trans ?_
  show (toUnit _ ≫ η[G]).left = _
  simp [eSec]

theorem exists_fac_residue (V K : Type) [CommRing V] [IsLocalRing V] [Field K] (r : Sp K ⟶ Sp V)
    (hr : Set.range r = {IsLocalRing.closedPoint V}) :
    ∃ s : Sp K ⟶ Sp (IsLocalRing.ResidueField V), s ≫ spMap (IsLocalRing.residue V) = r := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective r
  have h : PrimeSpectrum.comap ψ.hom (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint V := by
    have : (Spec.map ψ) (IsLocalRing.closedPoint K) ∈ Set.range (Spec.map ψ) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  let ψ' : V →+* K := ψ.hom
  have : IsLocalHom ψ' := (IsLocalRing.isLocalHom_iff_comap_closedPoint ψ').2 h
  refine ⟨spMap (IsLocalRing.ResidueField.lift ψ'), ?_⟩
  rw [← Spec.map_comp]
  congr 1

theorem Core.Test.exists_isGt_fibre {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (K : Type) [Field K] (r : Sp K ⟶ Sp τ.V) (hr : Set.range r = {IsLocalRing.closedPoint τ.V}) :
    ∃ (G₁ : Over (Sp K)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (E : SplitExt (Sp K)) (φ : G₁.left ⟶ τ.H.left),
      E.IsGt G₁ ∧ IsGrpPullback G₁ τ.H r φ := by
  obtain ⟨s, rfl⟩ := exists_fac_residue τ.V K r hr
  obtain ⟨S, hS⟩ := τ.split
  obtain ⟨E, -, -, -, -, hE⟩ := gtBaseChange _ _ s S _ hS
  have : IsCommMonObj ((Over.pullback (spMap (IsLocalRing.residue τ.V))).obj τ.H) := Functor.isCommMonObj_obj
  exact ⟨_, _, Functor.isCommMonObj_obj, E, _, hE,
    (isGrpPullback_pullback _ s).comp (isGrpPullback_pullback τ.H _)⟩

theorem Core.Test.eSec_comp_f {C : Core} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y) :
    (eSec τ.H ≫ τ.f : Sp τ.V ⟶ C.G.toScheme) = τ.y₀ ≫ C.e := by
  have := C.proper
  have : IsSeparated C.GG.hom := inferInstanceAs (IsSeparated (C.G.ι ≫ C.P.hom))
  have : IsDominant (Out.jK τ.V) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
    rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective τ.V _)]
    exact bot_le)⟩
  refine ext_of_isDominant_of_isSeparated C.GG.hom ?_ (Out.jK τ.V) ?_
  · have h₁ : (eSec τ.H ≫ τ.H.hom : Sp τ.V ⟶ Sp τ.V) = 𝟙 _ := Over.w η[τ.H]
    have h₂ : C.e ≫ C.GG.hom = 𝟙 _ := C.e_sec
    rw [Category.assoc, Category.assoc, τ.f_over, h₂, Category.comp_id]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.y₀) h₁).trans (Category.id_comp _))
  · have h₁ := @eSec_comp_of_isGrpPullback _ _ _ _ (_) (_) _ _ τ.φ_cart
    have h₂ := eSec_comp_of_isGrpPullback (isGrpPullback_pullback τ.H (Out.jK τ.V))
    rw [← reassoc_of% τ.yK_fac, C.e_zero]
    refine Eq.trans ?_ ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.a) h₁) |>.trans (Category.assoc _ _ _))
    rw [τ.φ_f]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) h₂.symm).trans (Category.assoc _ _ _))

theorem Core.fibLaw_of_testCart : ∀ C : Core, C.TestCart → C.FibLaw := by
  intro C hC p _ y y' τ τ' K _ _ r r' hr hr' hy c d c' d' hc hd
  obtain ⟨G₁, _, _, E₁, φ₁, g₁, h₁⟩ := τ.exists_isGt_fibre K r hr
  obtain ⟨G₂, _, _, E₂, φ₂, g₂, h₂⟩ := τ'.exists_isGt_fibre K r' hr'
  have P₁ := h₁.1.paste_horiz (hC p y τ)
  have P₂ := h₂.1.paste_horiz (hC p y' τ')
  let i : G₁ ⟶ G₂ := Over.homMk (P₂.lift (φ₁ ≫ τ.f) G₁.hom (by rw [P₁.w, hy])) (P₂.lift_snd _ _ _)
  have hi : i.left ≫ φ₂ ≫ τ'.f = φ₁ ≫ τ.f := P₂.lift_fst _ _ _
  have u₁ : η[G₁].left ≫ φ₁ ≫ τ.f = (r ≫ τ.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ.f) (eSec_comp_of_isGrpPullback h₁)).trans
      ((Category.assoc _ _ _).trans (congrArg (r ≫ ·) τ.eSec_comp_f)))
  have u₂ : η[G₂].left ≫ φ₂ ≫ τ'.f = (r' ≫ τ'.y₀ ≫ C.e : Sp K ⟶ C.G.toScheme) :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ τ'.f) (eSec_comp_of_isGrpPullback h₂)).trans
      ((Category.assoc _ _ _).trans (congrArg (r' ≫ ·) τ'.eSec_comp_f)))
  have hone : η[G₁] ≫ i = η[G₂] := by
    apply Over.OverMorphism.ext
    apply P₂.hom_ext
    · rw [Over.comp_left, Category.assoc, hi, u₁, u₂]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ C.e) hy).trans (Category.assoc _ _ _))
    · rw [Over.w, Over.w]
  have := isMonHom_of_isGt_of_one K E₁ E₂ G₁ G₂ g₁ g₂ i hone
  obtain ⟨ρ₁, l₁, s₁⟩ := exists_sectionHom h₁ (Over.mk (𝟙 _)) r (Category.id_comp _).symm
  obtain ⟨ρ₂, l₂, -⟩ := exists_sectionHom h₂ (Over.mk (𝟙 _)) r' (Category.id_comp _).symm
  have key : ∀ x, (ρ₁ x).left ≫ τ.f = (ρ₂ (x ≫ i)).left ≫ τ'.f := fun x => by
    rw [l₁, l₂, Over.comp_left, Category.assoc, Category.assoc, Category.assoc, hi]
  have inj : ∀ (x) (z : Over.mk r' ⟶ τ'.H), (ρ₁ x).left ≫ τ.f = z.left ≫ τ'.f → z = ρ₂ (x ≫ i) := fun x z hz => by
    apply Over.OverMorphism.ext
    apply (hC p y' τ').hom_ext
    · exact hz.symm.trans (key x)
    · rw [Over.w, Over.w]
  obtain ⟨c, rfl⟩ := s₁ c
  obtain ⟨d, rfl⟩ := s₁ d
  obtain rfl := inj c c' hc
  obtain rfl := inj d d' hd
  constructor
  · rw [← map_mul, ← map_mul, ← MonObj.mul_comp]
    exact key _
  · rw [← map_inv, ← map_inv, ← GrpObj.inv_comp]
    exact key _

end GlobalTheory.ZJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesianStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
theorem _root_.GlobalTheory.T.fibreLaw_of_testCartesian : ∀ C : Core, C.TestCart → C.FibLaw := by
  first | exact @GlobalTheory.ZJ.Core.fibLaw_of_testCart | exact GlobalTheory.ZJ.Core.fibLaw_of_testCart | (intros; apply GlobalTheory.ZJ.Core.fibLaw_of_testCart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterion
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterion
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.CosetCrit

theorem posDef_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) : q.PosDef := by
  intro x hx
  by_contra h
  have hinj : Function.Injective fun k : ℤ => k • x := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually_gt_atTop 0
  obtain ⟨k, hk⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul] at hk
  have : (0 : ℝ) ≤ ((k * k : ℤ) : ℝ) := by exact_mod_cast mul_self_nonneg k
  nlinarith [not_lt.1 h]

theorem tendsto_class {X : Type} [AddCommGroup X] [Module.Free ℤ X] {q : QuadraticMap ℤ X ℝ}
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (y : X) {m : ℕ} (hm : m ≠ 0) :
    Filter.Tendsto (fun χ => q (y + m • χ)) Filter.cofinite Filter.atTop := by
  have hinj : Function.Injective fun χ : X => y + m • χ := fun a b h => by
    have h1 : (m : ℤ) • a = (m : ℤ) • b := by simpa using h
    exact smul_right_injective X (by exact_mod_cast hm : (m : ℤ) ≠ 0) h1
  exact hq.comp hinj.tendsto_cofinite

theorem exists_char_pow {C X : Type} [Field C] [IsAlgClosed C] [AddCommGroup X] [Module.Free ℤ X]
    (t : Multiplicative X →* Cˣ) {k : ℕ} (hk : 0 < k) : ∃ t' : Multiplicative X →* Cˣ, t' ^ k = t := by
  have hroot : ∀ u : Cˣ, ∃ v : Cˣ, v ^ k = u := fun u => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : C) hk
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hk.ne'] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose r hr using hroot
  let e := Module.Free.chooseBasis ℤ X
  let f : X →ₗ[ℤ] Additive Cˣ :=
    e.constr ℤ fun i => Additive.ofMul (r (t (Multiplicative.ofAdd (e i))))
  have hf : k • f = (MonoidHom.toAdditiveRight t).toIntLinearMap := e.ext fun i => by
    simp only [f, LinearMap.smul_apply, Module.Basis.constr_basis, ← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft f.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hf x.toAdd)

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C]
  {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}


omit [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] in
theorem norm_txT_le (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (χ : N.X) :
    ‖N.txT m p χ‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ) / (m : ℝ) ^ 2)) := by
  rw [(GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 m hm p χ]
  exact mul_le_of_le_one_right (Real.exp_pos _).le (hI.th _)


omit [CompleteSpace C] [IsAlgClosed C] in
theorem norm_tx_le (hI : N.Int q) {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + m • χ₀) ≤ q (p.1.1.toAdd + m • χ)) :
    ‖N.tx m p‖ ≤ Real.exp (-(q (p.1.1.toAdd + m • χ₀) / (m : ℝ) ^ 2)) := by
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (Real.exp_pos _).le fun χ => ?_
  refine (norm_txT_le hI hm p χ).trans (Real.exp_le_exp.2 (neg_le_neg ?_))
  exact div_le_div_of_nonneg_right (h₀ χ) (by positivity)


omit [IsUltrametricDist C] [CompleteSpace C] in
theorem exists_lift {n g : ℕ} (hn : (n : C) ≠ 0) (hT : N.Tors n g) (j : ℕ) {t : N.A} (ht : t ^ n = 1) :
    ∃ γ : N.Gt, γ ^ n ^ (j + 1) = 1 ∧ γ.b ^ n ^ j = t := by
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.degenerationData_torsion_structure_algClosed C N n g hn hT j
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  obtain ⟨γ₀, rfl⟩ := h1 t
  obtain ⟨s, hs⟩ := (N.exists_tor_iff (γ₀ ^ n)).2 (by rw [NumD.Gt.pow_b, ht])
  obtain ⟨s', rfl⟩ := exists_char_pow s hn0
  obtain ⟨γ, hγ⟩ := h2 (γ₀ * (N.tor s')⁻¹)
  refine ⟨γ, ?_, ?_⟩
  · rw [pow_succ, pow_mul, hγ, mul_pow, inv_pow, ← N.tor_pow, hs, mul_inv_cancel]
  · rw [← NumD.Gt.pow_b, hγ]
    simp

theorem exists_norm_tx_ge (hI : N.Int q) {n g : ℕ} (hp : n.Prime) (ho : Odd n) (hn : ‖(n : C)‖ = 1)
    (hT : N.Tors n g) {j : ℕ} (hj : 1 ≤ j) (p : N.QT ((n ^ j) ^ 2)) {χ₀ : N.X}
    (h₀ : ∀ χ, q (p.1.1.toAdd + n ^ j • χ₀) ≤ q (p.1.1.toAdd + n ^ j • χ)) :
    ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧
      Real.exp (-(q (p.1.1.toAdd + n ^ j • χ₀) / ((n ^ j : ℕ) : ℝ) ^ 2)) ≤ ‖N.tx (n ^ j) (p * h)‖ := by
  have hn0 : (n : C) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hm : Odd (n ^ j) := ho.pow
  have hm0 : 0 < n ^ j := hm.pos
  have hP := posDef_of_tendsto hI.pos
  have hQ : ∀ γ : N.Gt, γ ^ n ^ (j + 1) = 1 → (1, γ) ∈ N.QT ((n ^ j) ^ 2) := fun γ hγ => by
    obtain ⟨c, hc⟩ : n ^ (j + 1) ∣ (n ^ j) ^ 2 := by
      rw [← pow_mul]
      exact pow_dvd_pow n (by omega)
    rw [NumD.mem_QT, hc, pow_mul, hγ, one_pow]
    exact N.io_zero.symm
  obtain ⟨t, ht, hth⟩ := hT.good (N.c χ₀ * p.1.2.b ^ n ^ j)
  obtain ⟨γ, hγ, hγb⟩ := exists_lift hn0 hT j ht
  set p₁ : N.QT ((n ^ j) ^ 2) := p * ⟨(1, γ), hQ γ hγ⟩ with hp₁
  have hy : p₁.1.1 = p.1.1 := mul_one _
  have hb : p₁.1.2 = p.1.2 * γ := rfl
  haveI : NeZero (n : C) := ⟨hn0⟩
  haveI : NeZero n := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C n
  have hr : ∀ x : ℝ, Real.exp (-1) ^ x = Real.exp (-x) := fun x => by
    rw [← Real.exp_mul, neg_one_mul]
  have hsq : (0 : ℝ) < ((n ^ j : ℕ) : ℝ) ^ 2 := by positivity
  obtain ⟨s, hs, hle⟩ := GlobalTheory.exists_torsion_twist_tsum_norm_ge C N.X n ζ hp.pos hn hζ
    (N.txT (n ^ j) p₁) (fun χ => q (p.1.1.toAdd + n ^ j • χ) / ((n ^ j : ℕ) : ℝ) ^ 2) (Real.exp (-1))
    (Real.exp_pos _) (by simpa using Real.exp_lt_exp.2 (show (-1 : ℝ) < 0 by norm_num))
    ((tendsto_class hI.pos _ hm0.ne').atTop_div_const hsq)
    (fun χ => by rw [hr, ← hy]; exact norm_txT_le hI hm p₁ χ) χ₀
    (by rw [hr, (GlobalTheory.T.norm_rep_generators_and_thetaSeriesTerm C N q hI).2 _ hm p₁ χ₀, hy, hb, NumD.Gt.mul_b, mul_pow, hγb, ← mul_assoc, hth,
          mul_one])
    (fun μ hμ => by
      refine div_lt_div_of_pos_right ?_ hsq
      have := GlobalTheory.ClassMin.lt_of_min_class_of_ne_zero hP (N := ((n ^ j : ℕ) : ℤ)) (n := (n : ℤ))
        (a := p.1.1.toAdd + n ^ j • χ₀) (by exact_mod_cast hm0.ne') (by exact_mod_cast hp.two_le)
        (fun w => by rw [natCast_zsmul, add_assoc, ← smul_add]; exact h₀ _) hμ
      rwa [mul_comm, mul_smul, natCast_zsmul, natCast_zsmul, add_assoc, ← smul_add] at this)
  obtain ⟨s', rfl⟩ := exists_char_pow s hm0
  have hs' : s' ^ n ^ (j + 1) = 1 := by rw [pow_succ, pow_mul, hs]
  have hγ' : (γ * N.tor s') ^ n ^ (j + 1) = 1 := by
    rw [mul_pow, hγ, ← N.tor_pow, hs', N.tor_one, mul_one]
  refine ⟨⟨(1, γ * N.tor s'), hQ _ hγ'⟩, rfl, hγ', ?_⟩
  set p₂ : N.QT ((n ^ j) ^ 2) := p * ⟨(1, γ * N.tor s'), hQ _ hγ'⟩ with hp₂
  have hone : ∀ x, ‖(s' x : C)‖ = 1 := fun x => by
    have h1 : ‖(s' x : C)‖ ^ n ^ (j + 1) = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hs', MonoidHom.one_apply,
        Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.ne_zero)).1 h1
  have hterm : ∀ χ, N.txT (n ^ j) p₂ χ =
      ((s' p₁.1.1 : C) ^ (((n ^ j) ^ 2 - 1) / 2) * (s' p₁.1.1 : C)) *
        (N.txT (n ^ j) p₁ χ * ((s' ^ n ^ j) (Multiplicative.ofAdd χ) : C)) := fun χ => by
    rw [(GlobalTheory.T.thetaConstantTerm_representative_dependence C N (n ^ j) hm p₁ p₂ χ).2 s' ((mul_one _).trans hy.symm) (mul_assoc _ _ _).symm,
      ofAdd_add, ofAdd_nsmul, map_mul, map_pow, ofAdd_toAdd, MonoidHom.pow_apply]
    push_cast
    ring
  rw [NumD.tx, funext hterm, tsum_mul_left, norm_mul, norm_mul, norm_pow, hone, one_pow, one_mul, one_mul,
    ← hr]
  exact hle

end GlobalTheory.CosetCrit

theorem GlobalTheory.tx_coset_criterion : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ n g : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n g → ∀ j : ℕ, 1 ≤ j → (∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 ∧ (‖N.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)) ∧ (∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ ‖N.tx (n ^ j) (p * h)‖ = 1) ∧ ∀ p : N.QT ((n ^ j) ^ 2), ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ N.tx (n ^ j) (p * h) ≠ 0 := by
  intro C _ _ _ _ N q hI n g hp ho hn hT j hj
  have hm : Odd (n ^ j) := ho.pow
  have hP := GlobalTheory.CosetCrit.posDef_of_tendsto hI.pos
  have hsq : (0 : ℝ) < ((n ^ j : ℕ) : ℝ) ^ 2 := by have := hm.pos; positivity
  have hmin : ∀ p : N.QT ((n ^ j) ^ 2), ∃ χ₀, ∀ χ,
      q (p.1.1.toAdd + n ^ j • χ₀) ≤ q (p.1.1.toAdd + n ^ j • χ) := fun p =>
    (GlobalTheory.CosetCrit.tendsto_class hI.pos _ hm.pos.ne').exists_forall_le
  have h1 : ∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 := fun p => by
    obtain ⟨χ₀, h₀⟩ := hmin p
    refine (GlobalTheory.CosetCrit.norm_tx_le hI hm p h₀).trans (Real.exp_le_one_iff.2 (neg_nonpos.2 ?_))
    exact div_nonneg (hP.nonneg _) hsq.le
  refine ⟨fun p => ⟨h1 p, fun h => ?_⟩, fun p hp1 => ?_, fun p => ?_⟩
  · obtain ⟨χ₀, h₀⟩ := hmin p
    have h2 := GlobalTheory.CosetCrit.norm_tx_le hI hm p h₀
    rw [h, Real.one_le_exp_iff, neg_nonneg] at h2
    refine ⟨-χ₀, ?_⟩
    rw [smul_neg, eq_neg_iff_add_eq_zero]
    by_contra h3
    exact (div_pos (hP _ h3) hsq).not_ge h2
  · obtain ⟨h, ha, hb, hc⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge hI hp ho hn hT hj p (χ₀ := 0) (fun χ => by
      rw [hp1, toAdd_one, smul_zero, add_zero, map_zero]
      exact hP.nonneg _)
    refine ⟨h, ha, hb, le_antisymm (h1 _) ?_⟩
    simpa [hp1] using hc
  · obtain ⟨χ₀, h₀⟩ := hmin p
    obtain ⟨h, ha, hb, hc⟩ := GlobalTheory.CosetCrit.exists_norm_tx_ge hI hp ho hn hT hj p h₀
    exact ⟨h, ha, hb, norm_pos_iff.1 ((Real.exp_pos _).trans_le hc)⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterionStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tx_coset_norm_one_and_ne_zero : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ n g : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n g → ∀ j : ℕ, 1 ≤ j → (∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 ∧ (‖N.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)) ∧ (∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ ‖N.tx (n ^ j) (p * h)‖ = 1) ∧ ∀ p : N.QT ((n ^ j) ^ 2), ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ N.tx (n ^ j) (p * h) ≠ 0 := by
  first | exact @GlobalTheory.tx_coset_criterion | exact GlobalTheory.tx_coset_criterion | (intros; apply GlobalTheory.tx_coset_criterion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FFTTNeZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.Test.FF_ne_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
    {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)
    (hs : ∀ c : S.perp τ.yy.ker →+ ZMod S.N,
      ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c)
    (T : AddSubgroup S.Gam) (hT : T = S.perp τ.yy.ker) (c : T →+ ZMod S.N) : S.FF T c ≠ 0 := by
  subst hT
  obtain ⟨α, hα, rfl⟩ := hs c
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  intro h0
  have h1 : (⟨S.FF _ (τ.wt α) k, hk⟩ : S.R) = 0 := Subtype.ext (congrFun h0 k)
  rw [h1, map_zero, norm_zero] at h
  exact (mul_pos τ.δ_pos (Real.exp_pos _)).ne h

theorem FF_TT_ne_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) := by
  intro o Ω _ _ _ _ S M U₀ hO hL hT hI hZ hW ξ c
  obtain ⟨x, -, hx, -, hxI⟩ := hZ.2.2.2 ξ ⊤ trivial
  obtain ⟨p, hp, y, hy⟩ := (hL.1 U₀ le_rfl hO.ne x hx).1
  obtain ⟨y₀, hA, -, ⟨τ⟩⟩ := hT x p y hy
  refine τ.FF_ne_zero (hW p y₀ τ).1 _ ?_ c
  rw [← (hI x p y y₀ τ hy hA).2]
  unfold ThetaSys.TT ThetaSys.HH
  rw [hxI]

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FfDivFfMemOfSpecializes
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.FirstIneq

theorem perp_anti_of_le {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    {A B : AddSubgroup S.Gam} (h : A ≤ B) : S.perp B ≤ S.perp A :=
  fun _ ha x hx => ha x (h hx)

theorem ff_mem_ring {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)
    (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem ff_div_ff_mem_of_specializes : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → S.FF _ c k / S.FF _ c' k' ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ hO hLL hT hS hG hW hB hE z ξ c c' k k' _ hs hc _ hd'
  haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  obtain ⟨x, hxW, hxc, hξx, hI⟩ :=
    hG.2.2.2 ξ ⟨_, M.isOpen_setOf_div (S.FF (S.TT M ξ) c') k'⟩ hd'
  have hH : S.HH M x = S.HH M ξ := by unfold ThetaSys.HH; rw [hI]
  have hTT : S.TT M ξ = S.TT M x := by unfold ThetaSys.TT; rw [hH]
  have hHz : S.HH M z ≤ S.HH M ξ := AddSubgroup.closure_mono (hG.2.1 ξ z hs)
  have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (ff_mem_ring S _ c k)
  have hf' : S.FF _ c' k' ∈ M.ringOn U₀ := hO.le (ff_mem_ring S _ c' k')
  have hi : (S.FF _ c' k')⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c' k' (hG.1 ξ).1 hd'.1
  refine RatModel.O_le_of_specializes hξx ((hLL.1 U₀ le_rfl hO.ne x hxc).2 _ ?_ ?_)
  · rw [div_eq_mul_inv]
    exact mul_mem hf hi
  intro p _ y hy
  obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT x p y hy
  have hker : S.HH M ξ = τ.yy.ker := hH ▸ (hS x p y y₀ τ hy hAt).2
  have hperp : S.perp τ.yy.ker = S.TT M ξ := by rw [← hker]; rfl
  obtain ⟨α, hα, hwt⟩ := (hW p y₀ τ).1 (c'.comp (AddSubgroup.inclusion hperp.le))
  have h1 := (hB p y₀ τ hint (S.TT M z) c k (ff_mem_ring S _ c k) (hG.1 z).1).1
    (hperp.le.trans (perp_anti_of_le S hHz))
    (((hG.1 z).1.1.trans (hG.1 z).2.le).trans (hHz.trans hker.le)) α hα
    (fun t h₁ h₂ => by rw [hwt]; exact hc t h₁ (hperp.le h₂))
  have hE' : ∀ (T : AddSubgroup S.Gam), T = S.TT M x → ∀ (c : T →+ ZMod S.N) (k : _),
      M.Div (S.FF T c) k x →
      (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) →
      ‖M.val (gPt p ≫ y) (S.FF T c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N)) := by
    rintro T rfl c k h h'
    exact hE x p y y₀ τ hy hAt c k α h hα h'
  have h2 := hE' _ hTT c' k' hxW (fun t h₁ h₂ => by rw [hwt]; rfl)
  rw [hAt, ← h2] at h1
  set yg := gPt p ≫ y with hyg
  have w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : yg w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
  have hsp := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton yg w)
  have e1 : M.val yg (S.FF _ c' k') * M.val yg (S.FF _ c' k')⁻¹ = 1 := by
    rw [← RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf') (RatModel.ringOn_le_O hw hi),
      mul_inv_cancel₀ hd'.1, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf) (RatModel.ringOn_le_O hw hi),
    norm_mul, ← norm_one (α := PadicAlgCl p), ← e1, norm_mul]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

end GlobalTheory.ZH.FirstIneq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.QuadraticMapNonnegOfTendstoCofinite
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

theorem quadraticMap_nonneg_of_tendsto_cofinite {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    (q : QuadraticMap ℤ X ℝ) (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (x : X) : 0 ≤ q x := by
  by_contra hneg
  push_neg at hneg
  have hx : x ≠ 0 := by
    rintro rfl
    simp at hneg
  have hinj : Function.Injective (fun n : ℤ => n • x) := smul_left_injective ℤ hx
  have h1 := (hq.comp hinj.tendsto_cofinite).eventually (Filter.eventually_gt_atTop 0)
  obtain ⟨n, hn⟩ := h1.exists
  simp only [Function.comp, QuadraticMap.map_smul, zsmul_eq_mul, Int.cast_mul] at hn
  nlinarith [mul_self_nonneg (n : ℝ)]

namespace RatModel
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}

theorem dotProduct_div_mem_O {J : Type} [Fintype J] {a₀ : M.Z} {v e : J → Ω} {t : Ω}
    (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) : (v ⬝ᵥ e) / t ∈ M.O a₀ := by
  rw [div_eq_mul_inv]
  exact mul_mem (sum_mem fun j _ => mul_mem (hv j) (he j)) ht

theorem val_dotProduct_div {K : Type} [Field K] {y : Sp K ⟶ M.Z} {a₀ : M.Z} (h : ∀ w, y w ⤳ a₀)
    {J : Type} [Fintype J] {v e : J → Ω} {t : Ω} (hv : ∀ j, v j ∈ M.O a₀) (he : ∀ j, e j ∈ M.O a₀)
    (ht0 : t ≠ 0) (ht' : t ∈ M.O a₀) (ht : t⁻¹ ∈ M.O a₀) :
    M.val y ((v ⬝ᵥ e) / t) = (∑ j, M.val y (v j) * M.val y (e j)) / M.val y t := by
  have h1 : M.val y t * M.val y t⁻¹ = 1 := by
    rw [← val_mul h ht' ht, mul_inv_cancel₀ ht0, val_one]
  have h2 : ∀ s : Finset J, M.val y (∑ j ∈ s, v j * e j) = ∑ j ∈ s, M.val y (v j) * M.val y (e j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [val_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        val_add h (mul_mem (hv a) (he a)) (sum_mem fun j _ => mul_mem (hv j) (he j)),
        val_mul h (hv a) (he a), ih]
  rw [div_eq_mul_inv, div_eq_mul_inv, dotProduct,
    val_mul h (sum_mem fun j _ => mul_mem (hv j) (he j)) ht, h2, eq_inv_of_mul_eq_one_right h1]

end RatModel

namespace ThetaSys
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}

theorem Test.norm_pair_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {h : S.Gam} (hh : h ∈ τ.yy.ker) {u : S.J → PadicAlgCl p} (hu : u ∈ τ.E) :
    ‖∑ j, u j * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨α, l, i, hα, hl, rfl⟩ := hu
    have h1 := τ.le α hα h hh i
    simp only [_root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ Real.exp (τ.q α / S.N) * (τ.δ * Real.exp (-(τ.q α / S.N))) :=
          mul_le_mul hl h1 (norm_nonneg _) (Real.exp_pos _).le
      _ = τ.δ := by rw [Real.exp_neg]; field_simp
  | zero => simpa using τ.δ_pos.le
  | add a b _ _ ha hb =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  | smul c a _ ha =>
    have hc : ‖(c : PadicAlgCl p)‖ ≤ 1 := (mem_OO_iff _).1 c.2
    have : ∀ j, (c • a) j = (c : PadicAlgCl p) * a j := fun j => rfl
    simp only [this, _root_.mul_assoc]
    rw [← Finset.mul_sum, norm_mul]
    calc _ ≤ 1 * τ.δ := mul_le_mul hc ha (norm_nonneg _) zero_le_one
      _ = τ.δ := _root_.one_mul _

theorem Test.norm_proj_zero_le {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) (i : S.J) :
    ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ ≤ τ.δ := by
  subst hT
  have := τ.le 0 (fun v0 => by
    rw [map_zero]; exact quadraticMap_nonneg_of_tendsto_cofinite τ.q τ.pos _) h hh i
  simpa only [map_zero, zero_div, neg_zero, Real.exp_zero, _root_.mul_one] using this

theorem Test.exists_norm_proj_zero_eq {p : ℕ} [Fact p.Prime] {y : S.R →+* PadicAlgCl p} (τ : S.Test p y)
    {T : AddSubgroup S.Gam} (hT : T = S.perp τ.yy.ker) {h : S.Gam} (hh : h ∈ τ.yy.ker) :
    ∃ i, ‖∑ j, y (algebraMap o S.R (S.proj T 0 j i)) * y ⟨S.ev h j, S.ev_mem h j⟩‖ = τ.δ := by
  subst hT
  have := τ.unit0 h hh
  simpa only [map_zero] using this

theorem val_pair_div {M : RatModel o Ω} {U₀ : M.Z.Opens} (hO : S.Over₀ M U₀) {U : Set M.Z}
    (hU : U ⊆ U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} (hc : M.Cen U z y)
    {y₀ : S.R →+* PadicAlgCl p} (hat : S.At M y y₀) {v : S.J → Ω} (hv : ∀ j, v j ∈ M.ringOn U)
    (h : S.Gam) {x₀ : S.Gam} (hx : S.th x₀ ≠ 0) :
    M.val (gPt p ≫ y) ((v ⬝ᵥ S.ev h) / S.th x₀) =
      (∑ j, M.val (gPt p ≫ y) (v j) * y₀ ⟨S.ev h j, S.ev_mem h j⟩) / M.val (gPt p ≫ y) (S.th x₀) := by
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hζ : (gPt p ≫ y) w ∈ U := hc.2 ⟨w, rfl⟩
  have hs := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (gPt p ≫ y) w)
  rw [RatModel.val_dotProduct_div hs (fun j => RatModel.ringOn_le_O hζ (hv j))
    (fun j => RatModel.ringOn_le_O (hU hζ) (hO.le (S.ev_mem h j))) hx
    (RatModel.ringOn_le_O (hU hζ) (hO.le (S.th_mem x₀)))
    (RatModel.ringOn_le_O (hU hζ) (hO.th_unit x₀ hx))]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hat]

end ThetaSys

theorem coord_regular_and_unit : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → S.IsEE M U₀ EE → ∀ ξ : M.Z, ∀ x₀ ∈ S.supI M ξ, ∀ h ∈ S.HH M ξ, (∀ v ∈ EE.E ξ, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O ξ) ∧ ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧ S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M ξ) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O ξ := by
  intro o Ω _ _ _ _ S M U₀ EE hO hLL hT hsup hstr hEE
  have closed : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ x₀ ∈ S.supI M z, ∀ h ∈ S.HH M z,
      (∀ v ∈ EE.E z, (v ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z) ∧
      ∃ i, (fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h ≠ 0 ∧
        S.th x₀ / ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) ∈ M.O z := by
    intro z hz x₀ hx₀ h hh
    have hx : S.th x₀ ≠ 0 := hx₀.1
    refine ⟨fun v hv => ?_, ?_⟩
    · let V : M.Z.Opens := ⟨⋂ j, {a | v j ∈ M.O a}, isOpen_iInter_of_finite fun j => M.isOpen_setOf_mem_O _⟩
      have hV : (V : Set M.Z).Nonempty := ⟨genericPoint M.Z, Set.mem_iInter.2 fun j => by
        simp only [Set.mem_setOf_eq, M.O_genericPoint]; trivial⟩
      have hvV : ∀ j, v j ∈ M.ringOn ((U₀ ⊓ V : M.Z.Opens) : Set M.Z) := fun j =>
        RatModel.mem_ringOn.2 fun a ha => Set.mem_iInter.1 ha.2 j
      refine (hLL.1 (U₀ ⊓ V) inf_le_left (M.nonempty_inf hO.ne hV) z hz).2 _ ?_ ?_
      · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
          (fun j => RatModel.ringOn_le_O ha (hvV j))
          (fun j => RatModel.ringOn_le_O ha.1 (hO.le (S.ev_mem h j)))
          (RatModel.ringOn_le_O ha.1 (hO.th_unit x₀ hx))
      · intro p _ y hc
        have hc0 : M.Cen U₀ z y := ⟨hc.1, fun a ha => (hc.2 ha).1⟩
        obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc0
        obtain ⟨h1, h2⟩ := hsup z p y y₀ τ hc0 hat
        rw [ThetaSys.val_pair_div hO (fun (a : M.Z) (ha : a ∈ (U₀ ⊓ V : M.Z.Opens)) => ha.1) hc hat hvV h hx, norm_div, (h1 x₀).1 hx₀,
          div_le_one τ.δ_pos]
        refine τ.norm_pair_le (h2 ▸ hh) (u := fun j => M.val (gPt p ≫ y) (v j)) ?_
        rw [← hEE.2 z p y y₀ τ hc0 hat]
        exact Submodule.subset_span ⟨v, hv, rfl⟩
    · have hw : ∀ i j, algebraMap o Ω (S.proj (S.TT M z) 0 j i) ∈ M.ringOn (U₀ : Set M.Z) :=
        fun i j => Subalgebra.algebraMap_mem _ _
      have hval : ∀ i (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p)
          (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ →
          ‖M.val (gPt p ≫ y) (((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀)‖ =
            ‖∑ j, y₀ (algebraMap o S.R (S.proj (S.TT M z) 0 j i)) * y₀ ⟨S.ev h j, S.ev_mem h j⟩‖ / τ.δ := by
        intro i p _ y y₀ τ hc hat
        rw [ThetaSys.val_pair_div hO subset_rfl hc hat (hw i) h hx, norm_div,
          ((hsup z p y y₀ τ hc hat).1 x₀).1 hx₀]
        congr 2
        exact Finset.sum_congr rfl fun j _ => by rw [hat (algebraMap o S.R _)]; rfl
      have hmem : ∀ i, ((fun j => algebraMap o Ω (S.proj (S.TT M z) 0 j i)) ⬝ᵥ S.ev h) / S.th x₀ ∈ M.O z := by
        intro i
        refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ ?_
        · exact RatModel.mem_ringOn.2 fun a ha => RatModel.dotProduct_div_mem_O
            (fun j => RatModel.ringOn_le_O ha (hw i j))
            (fun j => RatModel.ringOn_le_O ha (hO.le (S.ev_mem h j)))
            (RatModel.ringOn_le_O ha (hO.th_unit x₀ hx))
        · intro p _ y hc
          obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
          have h2 := (hsup z p y y₀ τ hc hat).2
          rw [hval i p y y₀ τ hc hat, div_le_one τ.δ_pos]
          exact τ.norm_proj_zero_le (by rw [← h2]; rfl) (h2 ▸ hh) i
      obtain ⟨p, _, y, hc⟩ := (hLL.1 U₀ le_rfl hO.ne z hz).1
      obtain ⟨y₀, hat, -, ⟨τ⟩⟩ := hT z p y hc
      have h2 := (hsup z p y y₀ τ hc hat).2
      obtain ⟨i, hi⟩ := τ.exists_norm_proj_zero_eq (T := S.TT M z) (by rw [← h2]; rfl) (h2 ▸ hh)
      have h3 := hval i p y y₀ τ hc hat
      rw [hi, div_self τ.δ_pos.ne', RatModel.norm_val_eq_one_iff hc.1 (hmem i), RatModel.isUnit_O_iff] at h3
      refine ⟨i, fun h0 => h3.1 (by simp only [h0, zero_div]), ?_⟩
      simpa only [inv_div] using h3.2
  intro ξ x₀ hx₀ h hh
  obtain ⟨U, b, hξU, -, hb⟩ := EE.loc ξ
  obtain ⟨x, hxU, hxc, hsp, hI⟩ := hstr.2.2.2 ξ U hξU
  have hH : S.HH M x = S.HH M ξ := by simp only [ThetaSys.HH, hI]
  have hTT : S.TT M x = S.TT M ξ := by simp only [ThetaSys.TT, hH]
  obtain ⟨c1, c2⟩ := closed x hxc x₀ (hI ▸ hx₀) h (hH ▸ hh)
  have hle := RatModel.O_le_of_specializes hsp
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [hb ξ hξU] at hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact hle (c1 v (by rw [hb x hxU]; exact Submodule.subset_span hv))
    | zero => simp
    | add a c _ _ ha hc => rw [add_dotProduct, add_div]; exact add_mem ha hc
    | smul c a _ ha =>
      have : c • a = (c : Ω) • a := rfl
      rw [this, smul_dotProduct, smul_eq_mul, mul_div_assoc]
      exact mul_mem c.2 ha
  · rw [hTT] at c2
    obtain ⟨i, h1, h2⟩ := c2
    exact ⟨i, h1, hle h2⟩

end GlobalTheory.ZH
end
end
