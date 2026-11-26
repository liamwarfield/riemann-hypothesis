module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfGenericNormalLocalBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGensOfDataFrom

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTranslationsMovingClosedPointsIntoOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MoverFibre

theorem isIrreducible_fibre_fst : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, IsIrreducible ((fst G G).left ⁻¹' {x}) := by
  intro R _ G _ hG x
  let j := G.left.fromSpecResidueField x
  let p₁ : pullback G.hom G.hom ⟶ G.left := pullback.fst G.hom G.hom
  have hp : (fst G G).left = p₁ := rfl
  have hirr0 := GlobalTheory.SemiAbFibre.irreducibleSpace_fibre _ G hG _ (j ≫ G.hom)
  haveI hirr : IrreducibleSpace (pullback G.hom (j ≫ G.hom) : Scheme.{0}) := hirr0
  let e : pullback G.hom (j ≫ G.hom) ≅ p₁.fiber x :=
    pullbackSymmetry _ _ ≪≫ (pullbackRightPullbackFstIso G.hom G.hom j).symm ≪≫ pullbackSymmetry _ _
  have hr := (IrreducibleSpace.isIrreducible_univ (pullback G.hom (j ≫ G.hom) : Scheme.{0})).image _
      ((e.hom ≫ Scheme.Hom.fiberι p₁ x).continuous.continuousOn)
  rw [Set.image_univ] at hr
  have hrange : Set.range (e.hom ≫ Scheme.Hom.fiberι p₁ x) = Set.range (Scheme.Hom.fiberι p₁ x) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨e.hom z, by rw [Scheme.Hom.comp_apply]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨e.inv z, by rw [Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, e.inv_hom_id]; rfl⟩
  show IsIrreducible (p₁ ⁻¹' {x})
  rw [← Scheme.Hom.range_fiberι p₁ x, ← hrange]
  exact hr

end GlobalTheory.MoverFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIrreducibleFibreFstStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, IsIrreducible ((fst G G).left ⁻¹' {x}) := by
  first | exact @GlobalTheory.MoverFibre.isIrreducible_fibre_fst | exact GlobalTheory.MoverFibre.isIrreducible_fibre_fst | (intros; apply GlobalTheory.MoverFibre.isIrreducible_fibre_fst <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} →
      IsClosed ((snd G G).left '' N) := by
  intro R _ _ G _ hG x hx hxc N hN hNZ
  have hlft : LocallyOfFiniteType G.hom := by
    haveI := hG.smooth; infer_instance
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) :=
    GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed R G hlft x hx hxc
  set k := G.left.fromSpecResidueField x
  set f := G.hom
  let i := pullback.snd k (pullback.fst f f)
  have hrange : Set.range i = (pullback.fst f f) ⁻¹' {x} := by
    simp only [i, Scheme.Pullback.range_snd, k, Scheme.range_fromSpecResidueField]
  have hcomp : i ≫ pullback.snd f f =
      (pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f :=
    (pullbackRightPullbackFstIso_hom_snd f f k).symm
  have hcl : IsClosedMap (i ≫ pullback.snd f f) := by
    rw [hcomp]
    haveI := hfin
    haveI : IsFinite (pullback.snd (k ≫ f) f) := inferInstance
    exact ((pullbackRightPullbackFstIso f f k).hom ≫ pullback.snd (k ≫ f) f).isClosedMap
  have hNi : (snd G G).left '' N = (i ≫ pullback.snd f f) '' (i ⁻¹' N) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.image_comp, Set.image_preimage_eq_of_subset]
    · rfl
    · rw [hrange]; exact hNZ
  rw [hNi]
  exact hcl _ (hN.preimage i.continuous)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImageSndOfSubsetSemiAbelianFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_image_snd_of_subset_semiAbelian_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) → ∀ N : Set (G ⊗ G).left, IsClosed N → N ⊆ (fst G G).left ⁻¹' {x} → IsClosed ((snd G G).left '' N) := by
  first | exact @GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | exact GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint | (intros; apply GlobalTheory.Mum.isClosed_image_snd_of_subset_fibre_closedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSemiAbelianSquareSameProjections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSemiAbelianSquareSameProjections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem eq_of_specializes_of_fst_eq_of_snd_eq :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
      ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) →
      ∀ p q : (G ⊗ G).left, (fst G G).left p = x → (fst G G).left q = x →
        (snd G G).left p = (snd G G).left q → p ⤳ q → p = q := by
  intro R _ _ G _ hG x hx hxc p q hp hq hpq hs
  haveI : Smooth G.hom := hG.smooth
  have hfin : IsFinite (G.left.fromSpecResidueField x ≫ G.hom) := GlobalTheory.T.isFinite_fromSpecResidueField_comp_of_closed R G inferInstance x hx hxc

  let j : pullback (pullback.fst G.hom G.hom) (G.left.fromSpecResidueField x) ⟶ pullback G.hom G.hom :=
    pullback.fst _ _
  let e := pullbackSymmetry (pullback.fst G.hom G.hom) (G.left.fromSpecResidueField x) ≪≫
    pullbackRightPullbackFstIso G.hom G.hom (G.left.fromSpecResidueField x)
  have hk : j ≫ pullback.snd G.hom G.hom = e.hom ≫ pullback.snd _ _ := by
    simp [e, j, pullbackRightPullbackFstIso_hom_snd]
  have hkf : IsFinite (j ≫ pullback.snd G.hom G.hom) := by rw [hk]; infer_instance
  have hr : Set.range j = (pullback.fst G.hom G.hom) ⁻¹' {x} := by
    simp only [j, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  obtain ⟨p', rfl⟩ : p ∈ Set.range j := by rw [hr]; exact hp
  obtain ⟨q', rfl⟩ : q ∈ Set.range j := by rw [hr]; exact hq
  have hs' : p' ⤳ q' := (j.isEmbedding.toIsInducing.specializes_iff).mp hs
  have := (GlobalTheory.finite_fibre_and_eq_of_specializes_of_isFinite _ _ _ hkf
    ((j ≫ pullback.snd G.hom G.hom) q')).2 p' q' (by simpa using hpq) rfl hs'
  rw [this]

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSpecializesSemiAbelianSquareSameProjectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_specializes_semiAbelian_square_same_projections : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ x : G.left, G.hom x = closedPoint R → IsClosed ({x} : Set G.left) → ∀ p q : (G ⊗ G).left, (fst G G).left p = x → (fst G G).left q = x → (snd G G).left p = (snd G G).left q → p ⤳ q → p = q := by
  first | exact @GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq | exact GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq | (intros; apply GlobalTheory.Mum.eq_of_specializes_of_fst_eq_of_snd_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTranslationsMovingClosedPointsIntoOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_open_mul_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (V : G.left.Opens), (∃ v ∈ V, G.hom v = closedPoint R) → ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R ∧ IsClosed ({x} : Set G.left)) → ∃ O : G.left.Opens, (∃ u ∈ O, G.hom u = closedPoint R) ∧ ∀ (Ω : Type) [Field Ω] (t : Sp Ω ⟶ Sp R) (x a : Over.mk t ⟶ G), (∀ z, x.left z ∈ s) → (∀ z, a.left z ∈ O) → ∀ z, (x * a).left z ∈ V := by
  intro R _ _ _ G _ _ hG V hV s hs
  obtain ⟨v, hvV, hvc⟩ := hV
  set F : Set G.left := G.hom ⁻¹' {closedPoint R} with hFdef
  have hFc : IsClosed F := (isClosed_singleton_closedPoint R).preimage G.hom.continuous
  have hcond : ∀ p : (G ⊗ G).left, G.hom ((snd G G).left p) = G.hom ((fst G G).left p) := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun h : (G ⊗ G).left ⟶ Sp R => h p) pullback.condition.symm
  have hsurj : ∀ x : G.left, G.hom x = closedPoint R → (snd G G).left '' ((fst G G).left ⁻¹' {x}) = F := by
    intro x hx
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      show G.hom _ = closedPoint R
      rw [hcond p, show (fst G G).left p = x from hp, hx]
    · intro hw
      obtain ⟨p, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) x w (hx.trans hw.symm)
      exact ⟨p, h1, h2⟩
  have hmu : ∀ p : (G ⊗ G).left, G.hom (μ[G].left p) = G.hom ((fst G G).left p) := fun p => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Over.w μ[G]]
    rfl
  let Ψ : G ⊗ G ⟶ G ⊗ G := lift (fst G G) ((fst G G)⁻¹ * snd G G)
  have hΨ1 : Ψ ≫ fst G G = fst G G := lift_fst _ _
  have hΨ2 : Ψ ≫ μ[G] = snd G G := by
    show fst G G * ((fst G G)⁻¹ * snd G G) = snd G G
    exact mul_inv_cancel_left _ _
  have hmsurj : ∀ x : G.left, G.hom x = closedPoint R → μ[G].left '' ((fst G G).left ⁻¹' {x}) = F := by
    intro x hx
    ext w
    constructor
    · rintro ⟨p, hp, rfl⟩
      show G.hom _ = closedPoint R
      rw [hmu p, show (fst G G).left p = x from hp, hx]
    · intro hw
      obtain ⟨q, hq, rfl⟩ := (hsurj x hx).symm ▸ hw
      refine ⟨Ψ.left q, ?_, ?_⟩
      · show (fst G G).left (Ψ.left q) = x
        rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hΨ1]; exact hq
      · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hΨ2]
  have hFirr : IsIrreducible F := by
    rw [← hsurj v hvc]
    exact (GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian R G hG v).image _ (snd G G).left.continuous.continuousOn
  set gpt := hFirr.genericPoint
  have hgp : IsGenericPoint gpt F := by
    have := hFirr.isGenericPoint_genericPoint_closure
    rwa [hFc.closure_eq] at this

  have gen_of : ∀ (f : (G ⊗ G).left → G.left), Continuous f → ∀ (Z : Set (G ⊗ G).left) (ξ : (G ⊗ G).left),
      IsGenericPoint ξ Z → f '' Z = F → f ξ = gpt := by
    intro f hf Z ξ hξ hZ
    refine IsGenericPoint.eq ?_ hgp
    show closure {f ξ} = F
    apply le_antisymm
    · exact hFc.closure_subset_iff.2 (Set.singleton_subset_iff.2 (hZ ▸ ⟨ξ, hξ.mem, rfl⟩))
    · rw [← hZ, ← hξ.def, ← Set.image_singleton]
      exact image_closure_subset_closure_image hf
  let T : G.left → Set G.left := fun x =>
    (snd G G).left '' ((fst G G).left ⁻¹' {x} ∩ μ[G].left ⁻¹' (V : Set G.left)ᶜ)
  have hTc : ∀ x ∈ s, IsClosed (T x) := by
    intro x hx
    refine GlobalTheory.T.isClosed_image_snd_of_subset_semiAbelian_fibre R G hG x (hs x hx).1 (hs x hx).2 _ ?_ Set.inter_subset_left
    exact ((hs x hx).2.preimage (fst G G).left.continuous).inter
      (V.isOpen.isClosed_compl.preimage μ[G].left.continuous)
  have hgpV : gpt ∈ (V : Set G.left) := (hgp.specializes (show v ∈ F from hvc)).mem_open V.isOpen hvV
  have hgpT : ∀ x ∈ s, gpt ∉ T x := by
    intro x hx ⟨n, ⟨hn1, hn2⟩, hn3⟩
    have hZc : IsClosed ((fst G G).left ⁻¹' {x}) := (hs x hx).2.preimage (fst G G).left.continuous
    have hZi := GlobalTheory.T.isIrreducible_preimage_fst_of_isSemiAbelian R G hG x
    have hξ : IsGenericPoint hZi.genericPoint ((fst G G).left ⁻¹' {x}) := by
      have := hZi.isGenericPoint_genericPoint_closure
      rwa [hZc.closure_eq] at this
    have e2 := gen_of _ (snd G G).left.continuous _ _ hξ (hsurj x (hs x hx).1)
    have em := gen_of _ μ[G].left.continuous _ _ hξ (hmsurj x (hs x hx).1)
    have hnξ : hZi.genericPoint = n :=
      GlobalTheory.T.eq_of_specializes_semiAbelian_square_same_projections R G hG x (hs x hx).1 (hs x hx).2 _ _ hξ.mem hn1 (e2.trans hn3.symm) (hξ.specializes hn1)
    exact hn2 (hnξ ▸ em ▸ hgpV)
  refine ⟨⟨(⋃ x ∈ (s : Set G.left), T x)ᶜ,
    isOpen_compl_iff.2 (s.finite_toSet.isClosed_biUnion hTc)⟩, ⟨gpt, ?_, hgp.mem⟩, ?_⟩
  · show gpt ∉ ⋃ x ∈ (s : Set G.left), T x
    simp only [Set.mem_iUnion, not_exists]
    exact fun x hx => hgpT x hx
  · intro Ω _ t x a hx ha z
    by_contra hz
    let q : Over.mk t ⟶ G ⊗ G := lift x a
    have h1 : (fst G G).left (q.left z) = x.left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    have h2 : (snd G G).left (q.left z) = a.left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    have h3 : μ[G].left (q.left z) = (x * a).left z := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left]; rfl
    have hO := ha z
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hO
    exact hO (x.left z) (hx z) ⟨q.left z, ⟨h1, by simp only [Set.mem_preimage, Set.mem_compl_iff, h3]; exact hz⟩, h2⟩

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTranslationsMovingClosedPointsIntoOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_translations_moving_closedPoints_into_open : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (V : G.left.Opens), (∃ v ∈ V, G.hom v = closedPoint R) → ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R ∧ IsClosed ({x} : Set G.left)) → ∃ O : G.left.Opens, (∃ u ∈ O, G.hom u = closedPoint R) ∧ ∀ (Ω : Type) [Field Ω] (t : Sp Ω ⟶ Sp R) (x a : Over.mk t ⟶ G), (∀ z, x.left z ∈ s) → (∀ z, a.left z ∈ O) → ∀ z, (x * a).left z ∈ V := by
  first | exact @GlobalTheory.Mum.exists_open_mul_mem | exact GlobalTheory.Mum.exists_open_mul_mem | (intros; apply GlobalTheory.Mum.exists_open_mul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenDescendingFiniteFreeBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBasicOpenFiniteFreeBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemIff
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem algebraMap_norm_mem_span_singleton (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] (f : B) :
    algebraMap A B (Algebra.norm A f) ∈ Ideal.span {f} := by
  set g : B →ₗ[A] B := Algebra.lmul A B f with hg
  set p := g.charpoly
  obtain ⟨q, hq⟩ := Polynomial.X_dvd_sub_C (p := p)
  have h0 : Polynomial.aeval f p = 0 := by
    have h1 : Polynomial.aeval g p = 0 := LinearMap.aeval_self_charpoly g
    rw [hg, Polynomial.aeval_algHom_apply] at h1
    have h2 := congrArg (fun u : B →ₗ[A] B => u 1) h1
    simpa using h2
  have h3 := congrArg (Polynomial.aeval f) hq
  simp only [map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, h0, zero_sub] at h3
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, map_mul,
    show algebraMap A B (g.charpoly.coeff 0) = -(f * Polynomial.aeval f q) by
      rw [← h3, neg_neg]]
  exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)))

theorem norm_not_mem_iff (A B : Type) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] (f : B) (P : PrimeSpectrum A) :
    Algebra.norm A f ∉ P.asIdeal ↔
      ∀ Q : PrimeSpectrum B, Q.asIdeal.comap (algebraMap A B) = P.asIdeal → f ∉ Q.asIdeal := by
  constructor
  · intro hN Q hQ hf
    apply hN
    rw [← hQ, Ideal.mem_comap]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hf (algebraMap_norm_mem_span_singleton A B f)
  · intro h hN
    let Rₘ := Localization.AtPrime P.asIdeal
    let Sₘ := Localization (Algebra.algebraMapSubmonoid B P.asIdeal.primeCompl)
    have hnu : ¬ IsUnit (algebraMap B Sₘ f) := by
      intro hu
      have h1 := hu.map (Algebra.norm Rₘ (S := Sₘ))
      rw [Algebra.norm_localization A P.asIdeal.primeCompl] at h1
      exact (IsLocalization.AtPrime.isUnit_to_map_iff Rₘ P.asIdeal _).mp h1 hN
    obtain ⟨M, hM, hfM⟩ := exists_max_ideal_of_mem_nonunits hnu
    haveI : Module.Finite Rₘ Sₘ := Module.Finite.of_basis
      ((Module.Free.chooseBasis A B).localizationLocalization Rₘ P.asIdeal.primeCompl Sₘ)
    have hMc : M.comap (algebraMap Rₘ Sₘ) = IsLocalRing.maximalIdeal Rₘ :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := Rₘ) M)
    refine h ⟨M.comap (algebraMap B Sₘ), hM.isPrime.comap _⟩ ?_ hfM
    show (M.comap (algebraMap B Sₘ)).comap (algebraMap A B) = P.asIdeal
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq A Rₘ Sₘ,
      ← Ideal.comap_comap, hMc]
    exact Localization.AtPrime.under_maximalIdeal

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemIffStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_not_mem_iff_forall_over_not_mem : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [Module.Free A B] (f : B) (P : PrimeSpectrum A), Algebra.norm A f ∉ P.asIdeal ↔ ∀ Q : PrimeSpectrum B, Q.asIdeal.comap (algebraMap A B) = P.asIdeal → f ∉ Q.asIdeal := by
  first | exact @GlobalTheory.Mum.norm_not_mem_iff | exact GlobalTheory.Mum.norm_not_mem_iff | (intros; apply GlobalTheory.Mum.norm_not_mem_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBasicOpenFiniteFreeBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.NormBC

open TensorProduct

theorem norm_map_of_basis {A A' B B' : Type} [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
    [Algebra A B] [Algebra A' B'] (ρ : A →+* A') (ψ : B →+* B')
    (hc : ∀ a, ψ (algebraMap A B a) = algebraMap A' B' (ρ a)) {J : Type} [Fintype J] [DecidableEq J]
    (e : Module.Basis J A B) (e' : Module.Basis J A' B') (he : ∀ i, ψ (e i) = e' i) (f : B) :
    Algebra.norm A' (ψ f) = ρ (Algebra.norm A f) := by
  rw [Algebra.norm_eq_matrix_det e, Algebra.norm_eq_matrix_det e', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]
  have h : ψ f * e' j = ∑ k, ρ (e.repr (f * e j) k) • e' k := by
    rw [← he j, ← map_mul]
    conv_lhs => rw [← e.sum_repr (f * e j)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Algebra.smul_def, map_mul, hc, he]
  rw [h, e'.repr_sum_self]

theorem exists_basis_of_ringEquiv {S₀ A T₀ B : Type} [CommRing S₀] [CommRing A] [CommRing T₀]
    [CommRing B] [Algebra S₀ A] [Algebra S₀ T₀] [Algebra A B] {J : Type}
    (c : Module.Basis J S₀ T₀) (Φ : A ⊗[S₀] T₀ ≃+* B) (hΦ : ∀ a, Φ (a ⊗ₜ 1) = algebraMap A B a) :
    ∃ e : Module.Basis J A B, ∀ i, e i = Φ (1 ⊗ₜ c i) := by
  let L : A ⊗[S₀] T₀ ≃ₗ[A] B := Φ.toAddEquiv.toLinearEquiv (fun a x => by
    show Φ (a • x) = a • Φ x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← hΦ]
    rfl)
  exact ⟨(Algebra.TensorProduct.basis A c).map L, fun i => by
    simp [L, Algebra.TensorProduct.basis_apply]⟩

theorem exists_basis_Gamma {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁] {J : Type}
    [Fintype J] (c' : Module.Basis J R R₁) :
    letI := ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
    Nonempty (Module.Basis J Γ(Sp R, ⊤) Γ(Sp R₁, ⊤)) := by
  letI := ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  let σ : Γ(Sp R, ⊤) ≃+* R := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let σ₁ : Γ(Sp R₁, ⊤) ≃+* R₁ := (Scheme.ΓSpecIso (CommRingCat.of R₁)).commRingCatIsoToRingEquiv
  have hnat : ∀ a, σ₁ (algebraMap Γ(Sp R, ⊤) Γ(Sp R₁, ⊤) a) = algebraMap R R₁ (σ a) := fun a => by
    have h := congrArg (fun φ => φ.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R R₁)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    rw [AffDesc.appTop_eq_appLE] at h
    exact h
  let E : Γ(Sp R₁, ⊤) ≃ₗ[Γ(Sp R, ⊤)] (J → Γ(Sp R, ⊤)) :=
    { toFun := fun y i => σ.symm (c'.repr (σ₁ y) i)
      invFun := fun g => σ₁.symm (∑ i, σ (g i) • c' i)
      map_add' := fun y y' => by funext i; simp
      map_smul' := fun a y => by
        funext i
        simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
        rw [Algebra.smul_def, map_mul, hnat, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
          smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
      left_inv := fun y => by
        simp only [RingEquiv.apply_symm_apply, c'.sum_repr, RingEquiv.symm_apply_apply]
      right_inv := fun g => by
        funext i
        simp only [RingEquiv.apply_symm_apply, c'.repr_sum_self, RingEquiv.symm_apply_apply] }
  exact ⟨Module.Basis.ofEquivFun E⟩

theorem mem_primeIdealOf_iff' {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (s : Γ(X, U)) : s ∈ (hU.primeIdealOf x).asIdeal ↔ x.1 ∉ X.basicOpen s := by
  have h : (hU.primeIdealOf x : Spec Γ(X, U)) ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s ↔
      x.1 ∈ X.basicOpen s := by
    conv_rhs => rw [← hU.fromSpec_primeIdealOf x]
    rfl
  rw [← h, hU.fromSpec_preimage_basicOpen]
  exact not_not.symm

end GlobalTheory.Mum.NormBC

namespace GlobalTheory.Mum.NormBC

open TensorProduct

theorem exists_norm_basicOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁]
    [Module.Finite R R₁] [Module.Free R R₁] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁)
    (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → ∀ (V : X.Opens),
    IsCompact (V : Set X) → IsQuasiSeparated (V : Set X) → ∀ f : Γ(X₁, b ⁻¹ᵁ V), ∃ n : Γ(X, V),
    ∀ x : X, x ∈ X.basicOpen n ↔ x ∈ V ∧ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
  intro R R₁ _ _ _ _ _ X X₁ p p₁ b H V hVc hVq f
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · refine ⟨0, fun x => ?_⟩
    exact absurd (Subsingleton.elim _ _ : (p x).asIdeal = ⊤) (p x).isPrime.ne_top
  let c' := Module.Free.chooseBasis R R₁
  letI a0 : Algebra Γ(Sp R, ⊤) Γ(Sp R₁, ⊤) :=
    ((spMap (algebraMap R R₁)).appLE ⊤ ⊤ le_top).hom.toAlgebra
  obtain ⟨c⟩ := exists_basis_Gamma c'
  letI aX : ∀ U : X.Opens, Algebra Γ(Sp R, ⊤) Γ(X, U) := fun U => (p.appLE ⊤ U le_top).hom.toAlgebra
  letI aB : ∀ U : X.Opens, Algebra Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) :=
    fun U => (b.appLE U (b ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  have key : ∀ U : X.Opens, IsIso (pushoutSection H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
      (show b ⁻¹ᵁ U = b ⁻¹ᵁ U ⊓ p₁ ⁻¹ᵁ ⊤ by simp)) →
      ∃ e : Module.Basis (Module.Free.ChooseBasisIndex R R₁) Γ(X, U) Γ(X₁, b ⁻¹ᵁ U),
        ∀ i, e i = (p₁.appLE ⊤ (b ⁻¹ᵁ U) (by simp)).hom (c i) := by
    intro U hU
    let Φ := (CommRingCat.isPushout_tensorProduct Γ(Sp R, ⊤) Γ(X, U) Γ(Sp R₁, ⊤)).isoPushout.hom ≫
      pushoutSection H (US := ⊤) (UT := ⊤) (UX := U) le_top le_top
        (show b ⁻¹ᵁ U = b ⁻¹ᵁ U ⊓ p₁ ⁻¹ᵁ ⊤ by simp)
    have : IsIso Φ := by dsimp only [Φ]; infer_instance
    let Φe : Γ(X, U) ⊗[Γ(Sp R, ⊤)] Γ(Sp R₁, ⊤) ≃+* Γ(X₁, b ⁻¹ᵁ U) :=
      (asIso Φ).commRingCatIsoToRingEquiv
    have fΦ : ∀ a t, Φe (a ⊗ₜ t) =
        (b.appLE U (b ⁻¹ᵁ U) le_rfl).hom a * (p₁.appLE ⊤ (b ⁻¹ᵁ U) (by simp)).hom t :=
      fun a t => AffDesc.isoPushout_desc_tmul _ _ _ a t
    obtain ⟨e, he⟩ := exists_basis_of_ringEquiv c Φe (fun a => by rw [fΦ, map_one, _root_.mul_one]; rfl)
    exact ⟨e, fun i => by rw [he, fΦ, map_one, _root_.one_mul]⟩
  haveI : Module.Flat R R₁ := inferInstance
  haveI : Flat (spMap (algebraMap R R₁)) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  obtain ⟨e, he⟩ := key V (isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H le_top le_top _
    (isAffineOpen_top _) (isAffineOpen_top _) hVc hVq)
  refine ⟨Algebra.norm Γ(X, V) f, fun x => ?_⟩
  by_cases hxV : x ∈ V
  swap
  · exact ⟨fun h => absurd (X.basicOpen_le _ h) hxV, fun h => absurd h.1 hxV⟩
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset hxV
  have hUV' : U ≤ V := hUV
  haveI : IsAffineHom b := MorphismProperty.of_isPullback H.flip inferInstance
  have hU₁ : IsAffineOpen (b ⁻¹ᵁ U) := hU.preimage b
  obtain ⟨e', he'⟩ := key U (isIso_pushoutSection_of_isAffineOpen H le_top le_top _
    (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have hUV₁ : b ⁻¹ᵁ U ≤ b ⁻¹ᵁ V := b.preimage_mono hUV'
  let ρ := X.presheaf.map (homOfLE hUV').op
  let ψ := X₁.presheaf.map (homOfLE hUV₁).op
  have hn : Algebra.norm Γ(X, U) (ψ.hom f) = ρ.hom (Algebra.norm Γ(X, V) f) := by
    refine norm_map_of_basis ρ.hom ψ.hom (fun a => ?_) e e' (fun i => ?_) f
    · change (b.appLE V _ le_rfl ≫ X₁.presheaf.map _).hom a = (X.presheaf.map _ ≫ b.appLE U _ le_rfl).hom a
      rw [Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
    · rw [he, he']
      exact congrArg (fun φ => CommRingCat.Hom.hom φ (c i)) (Scheme.Hom.appLE_map p₁ _ _)
  haveI : Module.Free Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) := Module.Free.of_basis e'
  haveI : Module.Finite Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) := Module.Finite.of_basis e'
  have I := GlobalTheory.T.norm_not_mem_iff_forall_over_not_mem Γ(X, U) Γ(X₁, b ⁻¹ᵁ U) (ψ.hom f) (hU.primeIdealOf ⟨x, hxU⟩)
  have hsq := IsAffineOpen.SpecMap_appLE_fromSpec b hU hU₁ le_rfl
  have hpt : ∀ Q, b (hU₁.fromSpec Q) = hU.fromSpec (Spec.map (b.appLE U (b ⁻¹ᵁ U) le_rfl) Q) :=
    fun Q => by rw [← Scheme.Hom.comp_apply, ← hsq, Scheme.Hom.comp_apply]
  have hfib : (∀ Q : PrimeSpectrum Γ(X₁, b ⁻¹ᵁ U),
      Q.asIdeal.comap (algebraMap Γ(X, U) Γ(X₁, b ⁻¹ᵁ U)) = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal →
        ψ.hom f ∉ Q.asIdeal) ↔ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
    constructor
    · intro h z hz
      have hzU : z ∈ b ⁻¹ᵁ U := by show b z ∈ U; rw [hz]; exact hxU
      have hzf : z ∈ X₁.basicOpen (ψ.hom f) := by
        by_contra hcon
        have hm := (mem_primeIdealOf_iff' hU₁ ⟨z, hzU⟩ (ψ.hom f)).2 hcon
        refine h _ ?_ hm
        have e1 : hU.fromSpec (Spec.map (b.appLE U (b ⁻¹ᵁ U) le_rfl) (hU₁.primeIdealOf ⟨z, hzU⟩)) =
            hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) :=
          (hpt _).symm.trans (by rw [hU₁.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]; exact hz)
        exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective e1)
      rw [Scheme.basicOpen_res] at hzf
      exact hzf.2
    · intro h Q hQ hfQ
      have hz := h (hU₁.fromSpec Q) ((hpt Q).trans ((congrArg hU.fromSpec (PrimeSpectrum.ext hQ)).trans
        (hU.fromSpec_primeIdealOf ⟨x, hxU⟩)))
      have hzU : hU₁.fromSpec Q ∈ b ⁻¹ᵁ U := by
        have : hU₁.fromSpec Q ∈ Set.range hU₁.fromSpec := ⟨Q, rfl⟩
        rwa [hU₁.range_fromSpec] at this
      have hz' : hU₁.fromSpec Q ∈ X₁.basicOpen (ψ.hom f) := by
        rw [Scheme.basicOpen_res]; exact ⟨hzU, hz⟩
      have hz'' : Q ∈ hU₁.fromSpec ⁻¹ᵁ X₁.basicOpen (ψ.hom f) := hz'
      rw [hU₁.fromSpec_preimage_basicOpen] at hz''
      exact hz'' hfQ
  have hbx : x ∈ X.basicOpen (Algebra.norm Γ(X, V) f) ↔
      Algebra.norm Γ(X, U) (ψ.hom f) ∉ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
    rw [mem_primeIdealOf_iff', not_not, hn, Scheme.basicOpen_res]
    exact ⟨fun h => ⟨hxU, h⟩, fun h => h.2⟩
  rw [hbx, I, hfib]
  exact ⟨fun h => ⟨hxV, h⟩, fun h => h.2⟩

end GlobalTheory.Mum.NormBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBasicOpenFiniteFreeBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_basicOpen_finiteFree_baseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] [Module.Finite R R₁] [Module.Free R R₁] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → ∀ (V : X.Opens), IsCompact (V : Set X) → IsQuasiSeparated (V : Set X) → ∀ f : Γ(X₁, b ⁻¹ᵁ V), ∃ n : Γ(X, V), ∀ x : X, x ∈ X.basicOpen n ↔ x ∈ V ∧ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
  first | exact @GlobalTheory.Mum.NormBC.exists_norm_basicOpen | exact GlobalTheory.Mum.NormBC.exists_norm_basicOpen | (intros; apply GlobalTheory.Mum.NormBC.exists_norm_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBetweenFinsetAndOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBetweenFinsetAndOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_basicOpen_between_finset_and_open : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (V : X.Opens), V ≤ W → ∀ s : Finset X, (∀ x ∈ s, x ∈ V) → ∃ f : Γ(X, W), X.basicOpen f ≤ V ∧ ∀ x ∈ s, x ∈ X.basicOpen f := by
  classical
  intro X W hW V hVW s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · refine ⟨0, ?_, fun x hx => absurd hx (Finset.notMem_empty x)⟩
    rw [Scheme.basicOpen_zero]
    exact bot_le
  set Z : Set (PrimeSpectrum Γ(X, W)) := {p | hW.fromSpec p ∉ V} with hZ
  have hZc : IsClosed Z := by
    have h := (hW.fromSpec ⁻¹ᵁ V).isOpen.isClosed_compl
    exact h
  let P : X → Ideal Γ(X, W) := fun x => if h : x ∈ W then (hW.primeIdealOf ⟨x, h⟩).asIdeal else ⊤
  have hPx : ∀ x (h : x ∈ W), P x = (hW.primeIdealOf ⟨x, h⟩).asIdeal := fun x h => by
    simp only [P, dif_pos h]
  have hP : ∀ i ∈ s, i ≠ x₀ → i ≠ x₀ → (P i).IsPrime := by
    intro x hx _ _
    rw [hPx x (hVW (hs x hx))]
    exact (hW.primeIdealOf _).isPrime
  have key : ¬ ((PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) ⊆
      ⋃ i ∈ (↑s : Set X), (P i : Set Γ(X, W))) := by
    rw [Ideal.subset_union_prime x₀ x₀ hP]
    rintro ⟨x, hx, hle⟩
    have hxW : x ∈ W := hVW (hs x hx)
    rw [hPx x hxW] at hle
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈
        PrimeSpectrum.zeroLocus (PrimeSpectrum.vanishingIdeal Z : Set Γ(X, W)) :=
      (PrimeSpectrum.mem_zeroLocus _ _).2 hle
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq] at hmem
    apply hmem
    show hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ V
    rw [hW.fromSpec_primeIdealOf]
    exact hs x hx
  obtain ⟨f, hfI, hfP⟩ := Set.not_subset.mp key
  refine ⟨f, ?_, ?_⟩
  · intro y hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    obtain ⟨p, rfl⟩ : y ∈ Set.range hW.fromSpec := by rw [hW.range_fromSpec]; exact hyW
    have hp : p ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := hy
    rw [hW.fromSpec_preimage_basicOpen] at hp
    by_contra hnot
    have hpZ : p ∈ Z := hnot
    exact (PrimeSpectrum.mem_basicOpen _ _).1 hp
      ((PrimeSpectrum.mem_vanishingIdeal _ _).1 hfI p hpZ)
  · intro x hx
    have hxW : x ∈ W := hVW (hs x hx)
    have hf : f ∉ (hW.primeIdealOf ⟨x, hxW⟩).asIdeal := by
      intro h
      apply hfP
      rw [Set.mem_iUnion₂]
      exact ⟨x, hx, by rw [hPx x hxW]; exact h⟩
    have hmem : hW.primeIdealOf ⟨x, hxW⟩ ∈ hW.fromSpec ⁻¹ᵁ X.basicOpen f := by
      rw [hW.fromSpec_preimage_basicOpen]
      exact (PrimeSpectrum.mem_basicOpen _ _).2 hf
    have h2 : hW.fromSpec (hW.primeIdealOf ⟨x, hxW⟩) ∈ X.basicOpen f := hmem
    rwa [hW.fromSpec_primeIdealOf] at h2

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasicOpenBetweenFinsetAndOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basicOpen_between_finset_and_open' : ∀ (X : Scheme.{0}) (W : X.Opens), IsAffineOpen W → ∀ (V : X.Opens), V ≤ W → ∀ s : Finset X, (∀ x ∈ s, x ∈ V) → ∃ f : Γ(X, W), X.basicOpen f ≤ V ∧ ∀ x ∈ s, x ∈ X.basicOpen f := by
  first | exact @GlobalTheory.Mum.exists_basicOpen_between_finset_and_open | exact GlobalTheory.Mum.exists_basicOpen_between_finset_and_open | (intros; apply GlobalTheory.Mum.exists_basicOpen_between_finset_and_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenDescendingFiniteFreeBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_isAffineOpen_of_preimage_le_affine : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁]
    [Module.Finite R R₁] [Module.Free R R₁] [Nontrivial R₁] [IsLocalRing R] (X X₁ : Scheme.{0})
    (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) →
    IsSeparated p → QuasiCompact p → ∀ (W : X₁.Opens), IsAffineOpen W → ∀ s : Finset X,
    (∀ z : X₁, b z ∈ s → z ∈ W) → ∃ O : X.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R R₁ _ _ _ _ _ _ _ X X₁ p p₁ b H _ _ W hW s hs
  classical

  have hg : IsFinite (spMap (algebraMap R R₁)) := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hff : Flat (spMap (algebraMap R R₁)) ∧ Surjective (spMap (algebraMap R R₁)) := by
    rw [flat_and_surjective_SpecMap_iff]
    exact RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  have : Flat (spMap (algebraMap R R₁)) := hff.1
  have : Surjective (spMap (algebraMap R R₁)) := hff.2
  have : IsFinite b := MorphismProperty.of_isPullback H.flip hg
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p

  let O' : X.Opens := ⟨(b '' (W : Set X₁)ᶜ)ᶜ, (b.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hsO' : ∀ x ∈ s, x ∈ O' := by
    rintro x hx ⟨z, hz, rfl⟩
    exact hz (hs z hx)
  have key : ∀ x ∈ s, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ O' := by
    intro x hx
    obtain ⟨U, hU, hxU, hUO⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (hsO' x hx)
    exact ⟨U, hU, hxU, hUO⟩
  choose U hU hxU hUO using key
  let V : X.Opens := ⨆ x : s, U x.1 x.2
  have hVO : V ≤ O' := iSup_le fun x => hUO x.1 x.2
  have hsV : ∀ x ∈ s, x ∈ V := fun x hx => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hx⟩, hxU x hx⟩
  have hVc : IsCompact (V : Set X) := by
    rw [TopologicalSpace.Opens.coe_iSup]
    exact isCompact_iUnion fun x => (hU x.1 x.2).isCompact
  have hVq : IsQuasiSeparated (V : Set X) := IsQuasiSeparated.of_quasiSeparatedSpace _
  have hVW : b ⁻¹ᵁ V ≤ W := by
    intro z hz
    by_contra h
    exact hVO hz ⟨z, h, rfl⟩

  have hfin : (b ⁻¹' (s : Set X)).Finite :=
    s.finite_toSet.preimage' fun x _ => b.finite_preimage_singleton x
  obtain ⟨f, hfV, hft⟩ := GlobalTheory.T.exists_basicOpen_between_finset_and_open' X₁ W hW (b ⁻¹ᵁ V) hVW hfin.toFinset
    (fun z hz => hsV _ ((hfin.mem_toFinset).1 hz))
  let f' : Γ(X₁, b ⁻¹ᵁ V) := X₁.presheaf.map (homOfLE hVW).op f
  have hf' : X₁.basicOpen f' = X₁.basicOpen f := by
    rw [Scheme.basicOpen_res]
    exact inf_eq_right.2 hfV
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_norm_basicOpen_finiteFree_baseChange R R₁ X X₁ p p₁ b H V hVc hVq f'
  refine ⟨X.basicOpen n, ?_, fun x hx => (hn x).2 ⟨hsV x hx, fun z hz => ?_⟩⟩
  swap
  · rw [hf']
    exact hft z ((hfin.mem_toFinset).2 (by simpa [hz] using hx))

  have hle : b ⁻¹ᵁ X.basicOpen n ≤ X₁.basicOpen f := by
    intro z hz
    rw [← hf']
    exact ((hn (b z)).1 hz).2 z rfl
  have hA : IsAffineOpen (b ⁻¹ᵁ X.basicOpen n) := by
    let g : Γ(X₁, X₁.basicOpen f) := X₁.presheaf.map (homOfLE hfV).op (b.app V n)
    have e : X₁.basicOpen g = b ⁻¹ᵁ X.basicOpen n := by
      rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
      exact inf_eq_right.2 hle
    rw [← e]
    exact (hW.basicOpen f).basicOpen g
  have : IsAffine (b ⁻¹ᵁ X.basicOpen n).toScheme := hA
  exact isAffine_of_isPullback_of_flat_surjective
    ((isPullback_morphismRestrict b (X.basicOpen n)).paste_vert H)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenDescendingFiniteFreeBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_descending_finiteFreeBaseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] [Module.Finite R R₁] [Module.Free R R₁] [Nontrivial R₁] [IsLocalRing R] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → IsSeparated p → QuasiCompact p → ∀ (W : X₁.Opens), IsAffineOpen W → ∀ s : Finset X, (∀ z : X₁, b z ∈ s → z ∈ W) → ∃ O : X.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  first | exact @GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine | exact GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine | (intros; apply GlobalTheory.Mum.exists_isAffineOpen_of_preimage_le_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateBaseChangeAffineOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateBaseChangeAffineOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

set_option synthInstance.maxHeartbeats 400000 in
theorem translate_baseChange_affineOpen : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (G : Over (Sp R)) [GrpObj G] (V : G.left.Opens), IsAffineOpen V → ∀ (a : Over.mk (spMap ρ) ⟶ G), ∃ W : (pullback G.hom (spMap ρ)).Opens, IsAffineOpen W ∧ ∀ (Ω : Type) [Field Ω] (z : Sp Ω ⟶ pullback G.hom (spMap ρ)) (t : Sp Ω ⟶ Sp R) (x a' : Over.mk t ⟶ G), x.left = z ≫ pullback.fst _ _ → a'.left = z ≫ pullback.snd _ _ ≫ a.left → (∀ w, (x * a').left w ∈ V) → ∀ w, z w ∈ W := by
  intro R R₁ _ _ ρ G _ V hV a
  let f := spMap ρ
  let G₁ := (Over.pullback f).obj G
  let a₁ : Over.mk (𝟙 (Sp R₁)) ⟶ G₁ :=
    Over.homMk (pullback.lift (f := G.hom) (g := f) a.left (𝟙 (Sp R₁))
      ((Over.w a).trans (Category.id_comp _).symm))
      (by show pullback.lift _ _ _ ≫ pullback.snd G.hom f = 𝟙 _; simp)
  let e : G₁ ⟶ Over.mk (𝟙 (Sp R₁)) := Over.homMk G₁.hom (by simp)
  let c : G₁ ⟶ G₁ := e ≫ a₁
  have hc : ∀ g : G₁ ⟶ G₁, g ≫ c = c := fun g =>
    by rw [← Category.assoc]; congr 1; ext; simp [e]
  let T : G₁ ⟶ G₁ := 𝟙 G₁ * c
  let T' : G₁ ⟶ G₁ := 𝟙 G₁ * c⁻¹
  have h₁ : T ≫ T' = 𝟙 G₁ := by
    simp only [T', MonObj.comp_mul, Category.comp_id, GrpObj.comp_inv, hc, T, mul_inv_cancel_right]
  have h₂ : T' ≫ T = 𝟙 G₁ := by
    simp only [T, MonObj.comp_mul, Category.comp_id, T', hc, inv_mul_cancel_right]
  haveI : IsIso T := ⟨⟨T', h₁, h₂⟩⟩
  haveI : IsIso T.left := Functor.map_isIso (Over.forget _) T
  haveI : IsAffineHom (pullback.fst G.hom f) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback G.hom f).flip
      (inferInstanceAs (IsAffineHom (spMap ρ)))
  refine ⟨(T.left ≫ pullback.fst G.hom f) ⁻¹ᵁ V, hV.preimage _, ?_⟩
  intro Ω _ z t x a' hx ha hxa w
  have ht : t = (z ≫ pullback.snd G.hom f) ≫ f := by
    have h0 : x.left ≫ G.hom = t := Over.w x
    rw [← h0, hx, Category.assoc, pullback.condition, Category.assoc]
  subst ht
  let Z : Over (Sp R₁) := Over.mk (z ≫ pullback.snd G.hom f)
  let z' : Z ⟶ G₁ := Over.homMk z (by simp [G₁, Z])
  have key := (isGrpPullback_pullback G f).2 Z z' (z' ≫ c) x a' (by simpa [z'] using hx)
    (by rw [ha]; simp [z', c, e, a₁, G₁, pullback.lift_fst]; rfl)
  have hT : z' * (z' ≫ c) = z' ≫ T := by simp only [T, MonObj.comp_mul, Category.comp_id]
  rw [hT] at key
  have : (z ≫ T.left ≫ pullback.fst G.hom f) w ∈ V := by
    have e2 : z ≫ T.left ≫ pullback.fst G.hom f = (x * a').left := by
      rw [key]; simp [z']
    rw [e2]; exact hxa w
  simpa using this

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateBaseChangeAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_translate_baseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (G : Over (Sp R)) [GrpObj G] (V : G.left.Opens), IsAffineOpen V → ∀ (a : Over.mk (spMap ρ) ⟶ G), ∃ W : (pullback G.hom (spMap ρ)).Opens, IsAffineOpen W ∧ ∀ (Ω : Type) [Field Ω] (z : Sp Ω ⟶ pullback G.hom (spMap ρ)) (t : Sp Ω ⟶ Sp R) (x a' : Over.mk t ⟶ G), x.left = z ≫ pullback.fst _ _ → a'.left = z ≫ pullback.snd _ _ ≫ a.left → (∀ w, (x * a').left w ∈ V) → ∀ w, z w ∈ W := by
  first | exact @GlobalTheory.Mum.translate_baseChange_affineOpen | exact GlobalTheory.Mum.translate_baseChange_affineOpen | (intros; apply GlobalTheory.Mum.translate_baseChange_affineOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFinsetClosedFibreSemiAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_affine_open_of_finset_closedFibre :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ s : Finset G.left,
    (∀ x ∈ s, G.hom x = closedPoint R) → ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R _ _ _ hR G _ _ hG s hs
  haveI : IsNoetherianRing R := hR.1
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : IsSeparated G.hom := hG.separated
  haveI : Smooth G.hom := hG.smooth
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom

  rcases s.eq_empty_or_nonempty with hs0 | ⟨x₀, hx₀⟩
  · exact ⟨⊥, isAffineOpen_bot _, by simp [hs0]⟩

  have hcl : ∀ x : G.left, ∃ y ∈ closure ({x} : Set G.left), IsClosed ({y} : Set G.left) :=
    fun x => isClosed_closure.exists_closed_singleton ⟨x, subset_closure rfl⟩
  choose f hfx hfc using hcl
  have hsp : ∀ x, x ⤳ f x := fun x => specializes_iff_mem_closure.2 (hfx x)
  have hcp : IsClosed ({closedPoint R} : Set (Sp R)) := isClosed_singleton_closedPoint R
  have hfib : ∀ x ∈ s, G.hom (f x) = closedPoint R := by
    intro x hx
    have h1 : G.hom x ⤳ G.hom (f x) := (hsp x).map G.hom.continuous
    rw [hs x hx] at h1
    have h2 := specializes_iff_mem_closure.1 h1
    exact closure_minimal (subset_refl _) hcp h2
  classical
  let s' : Finset G.left := s.image f
  have hs' : ∀ y ∈ s', G.hom y = closedPoint R ∧ IsClosed ({y} : Set G.left) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hfib x hx, hfc x⟩
  suffices H : ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ y ∈ s', y ∈ O by
    obtain ⟨O, hO, hyO⟩ := H
    exact ⟨O, hO, fun x hx => (hsp x).mem_open O.2 (hyO _ (Finset.mem_image_of_mem f hx))⟩

  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens)
    (show x₀ ∈ (⊤ : G.left.Opens) from trivial)

  obtain ⟨O, ⟨u, huO, hu⟩, hmove⟩ :=
    GlobalTheory.T.exists_open_translations_moving_closedPoints_into_open R G hG V ⟨x₀, hxV, hs x₀ hx₀⟩ s' hs'

  obtain ⟨R₁, _, _, _, ρ, a, hfin, het, ha, haO⟩ :=
    GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR G hG.smooth O ⟨u, huO, hu⟩
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hfin.2.2
  haveI : Algebra.Etale R R₁ := het
  haveI : Module.Flat R R₁ := inferInstance
  haveI : Module.Free R R₁ := Module.free_of_flat_of_isLocalRing

  let A : Over.mk (spMap ρ) ⟶ G := Over.homMk a ha
  obtain ⟨W, hW, hzW⟩ := GlobalTheory.T.exists_affineOpen_translate_baseChange R R₁ ρ G V hV A

  have hpb : IsPullback (pullback.fst G.hom (spMap ρ)) (pullback.snd G.hom (spMap ρ)) G.hom
      (spMap (algebraMap R R₁)) := IsPullback.of_hasPullback G.hom (spMap ρ)
  refine GlobalTheory.T.exists_affineOpen_descending_finiteFreeBaseChange R R₁ G.left (pullback G.hom (spMap ρ)) G.hom (pullback.snd _ _) (pullback.fst _ _)
    hpb inferInstance inferInstance W hW s' ?_
  intro z hz
  let Ω := (pullback G.hom (spMap ρ)).residueField z
  let z' : Sp Ω ⟶ pullback G.hom (spMap ρ) := (pullback G.hom (spMap ρ)).fromSpecResidueField z
  have hz' : ∀ w, z' w = z := fun w => Scheme.fromSpecResidueField_apply z w
  let t : Sp Ω ⟶ Sp R := z' ≫ pullback.fst _ _ ≫ G.hom
  let x : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.fst _ _) (by simp [t])
  let a' : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.snd _ _ ≫ a)
    (by simp only [t, Over.mk_hom, Category.assoc, ha, pullback.condition])
  have hx : ∀ w, x.left w ∈ s' := by
    intro w
    show (z' ≫ pullback.fst _ _) w ∈ s'
    rw [Scheme.Hom.comp_apply, hz']
    exact hz
  have ha' : ∀ w, a'.left w ∈ O := by
    intro w
    show (z' ≫ pullback.snd _ _ ≫ a) w ∈ O
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact haO ⟨_, rfl⟩
  have hV' := hmove Ω t x a' hx ha'
  have := hzW Ω z' t x a' rfl rfl hV' (closedPoint Ω)
  first
    | exact (Scheme.fromSpecResidueField_apply z _) ▸ this
    | simpa only [hz'] using this
    | (convert this using 1; exact (hz' _).symm)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFinsetClosedFibreSemiAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineOpen_finset_closedFibre_semiAbelian : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ s : Finset G.left, (∀ x ∈ s, G.hom x = closedPoint R) → ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  first | exact @GlobalTheory.Mum.exists_affine_open_of_finset_closedFibre | exact GlobalTheory.Mum.exists_affine_open_of_finset_closedFibre | (intros; apply GlobalTheory.Mum.exists_affine_open_of_finset_closedFibre <;> assumption)
end
