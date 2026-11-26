module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDescentSeparatedEmbedding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpLawAndUnitAgreeOfOpenInDescentModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSmoothGroupOverNbhd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsCommMonObjOfDominant
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SplitExtComm

theorem isCommMonObj_of_dominant {S S' : Scheme.{0}} {f : S' ⟶ S} [QuasiCompact f]
    [IsSchemeTheoreticallyDominant f] {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
    [Flat A.hom] [IsSeparated A.hom] {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ)
    [IsCommMonObj A'] : IsCommMonObj A := by
  have := ExtUnique.flat_tensorObj A A
  have key : ∀ (T : Over S') (t : Over.mk (T.hom ≫ f) ⟶ A ⊗ A),
      t ≫ (β_ A A).hom ≫ μ[A] = t ≫ μ[A] := fun T t => by
    obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ fst _ _)
    obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ snd _ _)
    obtain rfl : t = lift (pushPt h.1.w x) (pushPt h.1.w y) :=
      CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
    rw [lift_braiding_hom_assoc]
    exact Over.OverMorphism.ext ((h.2 T y x _ _ rfl rfl).trans
      ((congrArg (fun z => z.left ≫ φ) (_root_.mul_comm y x)).trans (h.2 T x y _ _ rfl rfl).symm))
  refine ⟨?_⟩
  refine ExtUnique.over_hom_ext_of_isPullback (IsPullback.of_hasPullback (A ⊗ A).hom f) ?_
  exact congrArg (fun z => z.left) (key (Over.mk (pullback.snd (A ⊗ A).hom f))
    (Over.homMk (pullback.fst (A ⊗ A).hom f) (by simpa using pullback.condition)))

end GlobalTheory.SplitExtComm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGroupRangeUnionClosedFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

variable {S P : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {h₁ : H₁.left ⟶ P} {h₂ : H₂.left ⟶ P}
  {pS : P ⟶ S}

theorem mul_mem_range (e₁ : h₁ ≫ pS = H₁.hom) (e₂ : h₂ ≫ pS = H₂.hom) [IsOpenImmersion h₂]
    (hm : MulAgree H₁ H₂ h₁ h₂) {T : Scheme.{0}} {t : T ⟶ S} (a b : Over.mk t ⟶ H₁)
    (ha : ∀ y, h₁ (a.left y) ∈ Set.range h₂) (hb : ∀ y, h₁ (b.left y) ∈ Set.range h₂) :
    ∀ y, h₁ ((a * b).left y) ∈ Set.range h₂ := by
  have lift : ∀ c : Over.mk t ⟶ H₁, (∀ y, h₁ (c.left y) ∈ Set.range h₂) →
      ∃ c' : Over.mk t ⟶ H₂, c.left ≫ h₁ = c'.left ≫ h₂ := by
    intro c hc
    let c'' := IsOpenImmersion.lift h₂ (c.left ≫ h₁) (by rintro _ ⟨y, rfl⟩; exact hc y)
    have ec : c'' ≫ h₂ = c.left ≫ h₁ := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk c'' ?_, ec.symm⟩
    show c'' ≫ H₂.hom = t
    rw [← e₂, ← Category.assoc, ec, Category.assoc, e₁, Over.w c]
    rfl
  obtain ⟨a', ea⟩ := lift a ha
  obtain ⟨b', eb⟩ := lift b hb
  have := hm T t t a b a' b' ea eb
  intro y
  rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

end GlobalTheory.OpenSubgrp

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

theorem comp_inv' {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G) :
    ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  (Category.assoc _ _ _).symm

theorem range_subset : ∀ (S P : Scheme.{0}) (H₁ H₂ : Over S) [GrpObj H₁] [GrpObj H₂] (h₁ : H₁.left ⟶ P)
    (h₂ : H₂.left ⟶ P), ∀ pS : P ⟶ S, h₁ ≫ pS = H₁.hom → h₂ ≫ pS = H₂.hom → IsOpenImmersion h₁ →
    IsOpenImmersion h₂ → Smooth H₁.hom → GeometricallyConnected H₁.hom → MulAgree H₁ H₂ h₁ h₂ →
    OneAgree (𝟙 S) (𝟙 S) H₁ H₂ h₁ h₂ → Set.range h₁ ⊆ Set.range h₂ := by
  intro S P H₁ H₂ _ _ h₁ h₂ pS e₁ e₂ _ _ _ _ hm ho
  have : GeometricallyIntegral H₁.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth S H₁
  let WO : H₁.left.Opens := h₁ ⁻¹ᵁ h₂.opensRange
  have hW : ∀ x, x ∈ WO ↔ h₁ x ∈ Set.range h₂ := fun x => Iff.rfl

  have hone : ∀ s : S, ∃ y ∈ WO, H₁.hom y = s := by
    intro s
    refine ⟨(1 : Over.mk (𝟙 S) ⟶ H₁).left s, ?_, ?_⟩
    · rw [hW, ← Scheme.Hom.comp_apply, ho S (𝟙 S) (𝟙 S) rfl, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    · rw [← Scheme.Hom.comp_apply, Over.w]; rfl
  let f := fst H₁ H₁
  let g := snd H₁ H₁
  let a : H₁ ⊗ H₁ ⟶ H₁ := g⁻¹ * f
  let O : (H₁ ⊗ H₁).left.Opens := a.left ⁻¹ᵁ WO ⊓ g.left ⁻¹ᵁ WO
  let Y : Over S := Over.mk (O.ι ≫ (H₁ ⊗ H₁).hom)
  let j : Y ⟶ H₁ ⊗ H₁ := Over.homMk O.ι rfl
  have e1 : (j ≫ g) * (j ≫ a) = j ≫ f := by
    rw [MonObj.comp_mul, comp_inv', mul_inv_cancel_left]
  have inW : ∀ y, h₁ ((j ≫ f).left y) ∈ Set.range h₂ := by
    rw [← e1]
    exact OpenSubgrp.mul_mem_range e₁ e₂ hm (j ≫ g) (j ≫ a) (fun y => y.2.2) (fun y => y.2.1)
  have hg : GeometricallyIrreducible f.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst H₁.hom H₁.hom))
  have m2 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, g.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨y, hy, e⟩ := hone (H₁.hom z)
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z y e.symm
    exact ⟨w, by rw [← hw2] at hy; exact hy, hw1⟩
  have m1 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, a.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨w, hw1, hw2⟩ := m2 z
    let b : H₁ ⊗ H₁ ⟶ H₁ ⊗ H₁ := lift f (f * g⁻¹)
    have b1 : b ≫ a = g := by
      rw [MonObj.comp_mul, comp_inv', lift_fst, lift_snd, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    have b2 : b ≫ f = f := lift_fst _ _
    refine ⟨b.left w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b1]; exact hw1
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b2]; exact hw2
  rintro _ ⟨z, rfl⟩
  have hi : IsIrreducible (f.left ⁻¹' {z}) := by
    rw [← f.left.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι z).continuous.continuousOn
  obtain ⟨w, hw, e⟩ := m1 z
  obtain ⟨w', hw', e'⟩ := m2 z
  obtain ⟨y, hy, k₁, k₂⟩ := hi.2 _ _ (a.left ⁻¹ᵁ WO).2 (g.left ⁻¹ᵁ WO).2 ⟨w, e, hw⟩ ⟨w', e', hw'⟩
  have := inW ⟨y, k₁, k₂⟩
  convert this using 2
  exact hy.symm

end GlobalTheory.OpenSubgrp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianIdentityComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] (j : G₀ ⟶ G)

abbrev RangeIsId : Prop := ∀ x : G.left, x ∈ Set.range j.left ↔
  x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))

include j in
theorem unit_mem_fibre (s : S) : (η[G]).left s ∈ G.hom ⁻¹' {s} := by
  show G.hom ((η[G]).left s) = s
  rw [← Scheme.Hom.comp_apply, Over.w]
  rfl

theorem isConnected_fibre [IsOpenImmersion j.left] (hr : RangeIsId j) (s : S) :
    _root_.IsConnected (G₀.hom ⁻¹' {s}) := by
  have hw : ∀ x, G.hom (j.left x) = G₀.hom x := fun x => by
    rw [← Scheme.Hom.comp_apply, Over.w]
  have himg : j.left '' (G₀.hom ⁻¹' {s}) = connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hr (j.left x)).1 ⟨x, rfl⟩
      rwa [hw, show G₀.hom x = s from hx] at this
    · intro hy
      have hys : G.hom y = s := connectedComponentIn_subset (G.hom ⁻¹' {s}) _ hy
      obtain ⟨x, rfl⟩ := (hr y).2 (by rwa [hys])
      exact ⟨x, by rw [Set.mem_preimage, ← hw, hys]; rfl, rfl⟩
  have hc : _root_.IsConnected (connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s)) :=
    isConnected_connectedComponentIn_iff.mpr (unit_mem_fibre j s)
  rw [← himg] at hc
  exact ⟨hc.nonempty.of_image, j.left.isOpenEmbedding.isInducing.isPreconnected_image.1 hc.isPreconnected⟩

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGroupRangeUnionClosedFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.UnionLocal

theorem awayMap_notMem {R : Type} [CommRing R] (g : R) (w : Sp (Localization.Away g)) : g ∉ (awayMap g w).asIdeal := by
  intro h
  have : algebraMap R (Localization.Away g) g ∈ w.asIdeal := h
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this (IsLocalization.Away.algebraMap_isUnit g))

theorem mul_left_comp {S T T' : Scheme.{0}} {H : Over S} [GrpObj H] {t : T ⟶ S} {t' : T' ⟶ S} (k : T' ⟶ T)
    (a b : Over.mk t ⟶ H) (a₁ b₁ : Over.mk t' ⟶ H) (ha : a₁.left = k ≫ a.left) (hb : b₁.left = k ≫ b.left) :
    (a₁ * b₁).left = k ≫ (a * b).left := by
  have ht : k ≫ t = t' := by
    have e1 : a.left ≫ H.hom = t := Over.w a
    have e2 : a₁.left ≫ H.hom = t' := Over.w a₁
    rw [← e1, ← e2, ha]; exact (Category.assoc _ _ _).symm
  let κ : Over.mk t' ⟶ Over.mk t := Over.homMk k ht
  have e1 : a₁ = κ ≫ a := Over.OverMorphism.ext ha
  have e2 : b₁ = κ ≫ b := Over.OverMorphism.ext hb
  rw [e1, e2, ← MonObj.comp_mul]
  rfl

theorem mulAgree_pullback {S S' S₂ P : Scheme.{0}} {H : Over S} [GrpObj H] {H' : Over S'} [GrpObj H'] {A : Over S₂} [GrpObj A]
    {t : S' ⟶ S} {π : H'.left ⟶ H.left} (hπ : IsGrpPullback H' H t π) {h : H.left ⟶ P} {i : A.left ⟶ P}
    (hm : MulAgree H A h i) : MulAgree H' A (π ≫ h) i := by
  intro T t₁ t₂ a b a' b' ha hb
  have w : ∀ c : Over.mk t₁ ⟶ H', (c.left ≫ π) ≫ H.hom = t₁ ≫ t := fun c => by
    have e : c.left ≫ H'.hom = t₁ := Over.w c
    rw [Category.assoc, hπ.1.w, ← Category.assoc, e]
  let a₀ : Over.mk (t₁ ≫ t) ⟶ H := Over.homMk (a.left ≫ π) (w a)
  let b₀ : Over.mk (t₁ ≫ t) ⟶ H := Over.homMk (b.left ≫ π) (w b)
  have e := hπ.2 (Over.mk t₁) a b a₀ b₀ rfl rfl
  have e2 := hm T (t₁ ≫ t) t₂ a₀ b₀ a' b' ((Category.assoc _ _ _).trans ha) ((Category.assoc _ _ _).trans hb)
  rw [← e2, ← Category.assoc]
  exact congrArg (· ≫ h) e.symm

theorem openIn_pullback {P S₀ S S' Y : Scheme.{0}} (p : P ⟶ S₀) (u : S ⟶ S₀) [Mono u] (q : Y ⟶ S) (h : Y ⟶ P)
    [IsOpenImmersion h] (w : h ≫ p = q ≫ u) (t : S' ⟶ S) :
    OpenIn (pullback.fst q t ≫ h) (pullback.snd q t) p (t ≫ u) := by
  have w' : (pullback.fst q t ≫ h) ≫ p = pullback.snd q t ≫ t ≫ u := by
    rw [Category.assoc, w, pullback.condition_assoc]
  refine ⟨w', ?_⟩
  have hsq : CommSq (pullback.fst q t) (pullback.lift _ _ w') h (pullback.fst p (t ≫ u)) := ⟨by rw [pullback.lift_fst]⟩
  have hc : ∀ c : PullbackCone h (pullback.fst p (t ≫ u)), c.fst ≫ q = (c.snd ≫ pullback.snd p (t ≫ u)) ≫ t := fun c => by
    rw [← cancel_mono u, Category.assoc, ← w, ← Category.assoc, c.condition, Category.assoc, pullback.condition]
    simp only [Category.assoc]
  have hp : IsPullback (pullback.fst q t) (pullback.lift _ _ w') h (pullback.fst p (t ≫ u)) := by
    refine IsPullback.of_isLimit' hsq (PullbackCone.IsLimit.mk hsq.w (fun c => pullback.lift c.fst _ (hc c))
      (fun c => pullback.lift_fst _ _ _) (fun c => ?_) (fun c m hm1 hm2 => ?_))
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, c.condition]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    · apply pullback.hom_ext
      · rw [pullback.lift_fst, hm1]
      · rw [pullback.lift_snd, ← hm2, Category.assoc, pullback.lift_snd]
  exact MorphismProperty.of_isPullback hp ‹_›

theorem exists_point {P S₀ S : Scheme.{0}} (p : P ⟶ S₀) (s : S ⟶ S₀) (H₁ H₂ : Over S) [GrpObj H₁] [GrpObj H₂]
    (h₁ : H₁.left ⟶ P) (h₂ : H₂.left ⟶ P) (o₁ : OpenIn h₁ H₁.hom p s) (o₂ : OpenIn h₂ H₂.hom p s)
    (hs : Smooth H₁.hom) (hc : GeometricallyConnected H₁.hom) (hm : MulAgree H₁ H₂ h₁ h₂) (ho : OneAgree s s H₁ H₂ h₁ h₂)
    (y : H₁.left) : ∃ y' : H₂.left, h₂ y' = h₁ y ∧ H₂.hom y' = H₁.hom y := by
  obtain ⟨w₁, o₁⟩ := o₁
  obtain ⟨w₂, o₂⟩ := o₂
  have key : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ S} (a : Over.mk t₁ ⟶ H₁) (a' : Over.mk t₂ ⟶ H₂),
      a.left ≫ pullback.lift h₁ H₁.hom w₁ = a'.left ≫ pullback.lift h₂ H₂.hom w₂ ↔ a.left ≫ h₁ = a'.left ≫ h₂ ∧ t₁ = t₂ := by
    intro T t₁ t₂ a a'
    have e1 : a.left ≫ H₁.hom = t₁ := Over.w a
    have e2 : a'.left ≫ H₂.hom = t₂ := Over.w a'
    constructor
    · intro h
      have f1 := congrArg (· ≫ pullback.fst p s) h
      have f2 := congrArg (· ≫ pullback.snd p s) h
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at f1 f2
      exact ⟨f1, e1.symm.trans (f2.trans e2)⟩
    · rintro ⟨h, h'⟩
      apply pullback.hom_ext
      · simpa only [Category.assoc, pullback.lift_fst] using h
      · simp only [Category.assoc, pullback.lift_snd]
        exact e1.trans (h'.trans e2.symm)
  obtain ⟨y', hy'⟩ := GlobalTheory.OpenSubgrp.range_subset S (pullback p s) H₁ H₂ (pullback.lift h₁ H₁.hom w₁) (pullback.lift h₂ H₂.hom w₂)
    (pullback.snd p s) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) o₁ o₂ hs hc
    (fun T t₁ t₂ a b a' b' ha hb => (key _ _).2 ⟨hm T t₁ t₂ a b a' b' ((key _ _).1 ha).1 ((key _ _).1 hb).1, ((key _ _).1 ha).2⟩)
    (fun T t₁ t₂ e => by
      have e' : t₁ = t₂ := by simpa using e
      exact (key _ _).2 ⟨ho T t₁ t₂ (by rw [e']), e'⟩) ⟨y, rfl⟩
  refine ⟨y', ?_, ?_⟩
  · have := congrArg (pullback.fst p s) hy'
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst] at this
  · have := congrArg (pullback.snd p s) hy'
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd, pullback.lift_snd] at this

theorem exists_connected (σ : Setup) (E : Emb σ) (g : σ.R) (H' : Over (Sp (Localization.Away g))) [GrpObj H']
    (h' : H'.left ⟶ E.P) (hl : E.LocGrp g H' h') :
    ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ GeometricallyConnected H.hom := by
  obtain ⟨hsm, hqc, hop, hp, hm⟩ := hl
  obtain ⟨H, _, j, hj, hjo, hr⟩ := GlobalTheory.identityComponentOpen _ H' hsm
  have hw : j.left ≫ H'.hom = H.hom := Over.w j
  have hsm₀ : Smooth H.hom := by rw [← hw]; infer_instance
  have : IsNoetherianRing (Localization.Away g) := IsLocalization.isNoetherianRing (Submonoid.powers g) _ inferInstance
  have : IsLocallyNoetherian H'.left := LocallyOfFiniteType.isLocallyNoetherian H'.hom
  have : CompactSpace H'.left := QuasiCompact.compactSpace_of_compactSpace H'.hom
  have : IsNoetherian H'.left := {}
  have hqc₀ : QuasiCompact H.hom := by rw [← hw]; infer_instance
  refine ⟨H, inferInstance, j.left ≫ h', ⟨hsm₀, hqc₀, inferInstance, by rw [Category.assoc, hp, ← Category.assoc, hw], ?_⟩,
    GlobalTheory.SS.NeutralPart.geometricallyConnected_of_section H.hom (η[H]).left (Over.w _)
      (GlobalTheory.SemiStableId.isConnected_fibre j hr)⟩
  intro T t₁ t₂ a b a' b' ha hb
  rw [← hm T t₁ t₂ (a ≫ j) (b ≫ j) a' b' ((Category.assoc _ _ _).trans ha) ((Category.assoc _ _ _).trans hb),
    ← MonObj.mul_comp, Over.comp_left, Category.assoc]

theorem lift_open (σ : Setup) (x : Sp σ.R) {T : Scheme.{0}} (c : T ⟶ (σ.C x).G.left) (d : T ⟶ Sp (Localization.Away σ.f))
    (e : c ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) = d ≫ awayMap σ.f) : ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c := by
  refine ⟨IsOpenImmersion.lift (σ.V x).ι c ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨τ, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (σ.hV x _).2 ?_
  have h1 := awayMap_notMem σ.f (d τ)
  rw [← Scheme.Hom.comp_apply, ← e] at h1
  exact h1

theorem chart_mul_generic (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (s : T ⟶ Sp (FractionRing (σ.C x).R))
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := _root_.GlobalTheory.Desc.ChartLaw.chart_mul_generic (T := T) σ E x s t₂ a b a' b' ha hb

theorem chart_mul_flat (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (t₁ : T ⟶ Sp (σ.C x).R) [Flat t₁]
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk t₁ ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := _root_.GlobalTheory.Desc.ChartLaw.chart_mul_flat (T := T) σ E x t₁ t₂ a b a' b' ha hb

theorem chart_mulAgree (σ : Setup) (E : Emb σ) (x : Sp σ.R) : MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  intro T t₁ t₂ a b a' b' ha hb
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  have := (σ.C x).semi.smooth
  obtain ⟨w, -⟩ := E.openIn x
  have hl : ∀ (c : Over.mk t₁ ⟶ (σ.C x).G) (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA →
      ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c.left ∧ l ≫ σ.φ x = c'.left := by
    intro c c' h
    obtain ⟨l, hl⟩ := lift_open σ x c.left (c'.left ≫ σ.A.hom) (by
      rw [← w, ← Category.assoc, h, Category.assoc, E.cartA.w, Category.assoc])
    refine ⟨l, hl, ?_⟩
    rw [← cancel_mono E.ιA, Category.assoc, E.onV, ← Category.assoc, hl]
    exact h
  obtain ⟨la, ha1, ha2⟩ := hl a a' ha
  obtain ⟨lb, hb1, hb2⟩ := hl b b' hb
  let q : (σ.V x).toScheme ⟶ Sp (σ.C x).R := (σ.V x).ι ≫ (σ.C x).G.hom
  have hq : la ≫ q = lb ≫ q := by
    have e1 : a.left ≫ (σ.C x).G.hom = t₁ := Over.w a
    have e2 : b.left ≫ (σ.C x).G.hom = t₁ := Over.w b
    simp only [q, ← Category.assoc, ha1, hb1]
    exact e1.trans e2.symm
  have hu : pullback.snd q q ≫ σ.φ x ≫ σ.A.hom = pullback.fst q q ≫ σ.φ x ≫ σ.A.hom := by
    rw [← cancel_mono (awayMap σ.f)]
    simp only [Category.assoc]
    rw [(σ.cart x).w]
    exact (pullback.condition_assoc (f := q) (g := q) _).symm
  let a₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.fst q q ≫ (σ.V x).ι) (Category.assoc _ _ _)
  let b₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.snd q q ≫ (σ.V x).ι)
    ((Category.assoc _ _ _).trans pullback.condition.symm)
  let a₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.fst q q ≫ σ.φ x) (Category.assoc _ _ _)
  let b₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.snd q q ≫ σ.φ x)
    ((Category.assoc _ _ _).trans hu)
  have h := chart_mul_flat σ E x (pullback.fst q q ≫ q) _ a₀ b₀ a₁ b₁
    ((Category.assoc _ _ _).trans ((congrArg (pullback.fst q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (pullback.snd q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
  let k := pullback.lift la lb hq
  have k1 : k ≫ pullback.fst q q = la := pullback.lift_fst _ _ _
  have k2 : k ≫ pullback.snd q q = lb := pullback.lift_snd _ _ _
  rw [mul_left_comp k a₀ b₀ a b (ha1.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb1.symm.trans (by rw [← k2]; exact Category.assoc _ _ _)),
    mul_left_comp k a₁ b₁ a' b' (ha2.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb2.symm.trans (by rw [← k2]; exact Category.assoc _ _ _))]
  exact (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) h).trans (Category.assoc _ _ _).symm)

theorem mem_range_iff (σ : Setup) (E : Emb σ) (g : σ.R) (H : Over (Sp (Localization.Away g))) [GrpObj H] (h : H.left ⟶ E.P)
    (hl : E.LocGrp g H h) (hc : GeometricallyConnected H.hom) (x : Sp σ.R) (hx : g ∉ x.asIdeal) (z : E.P) (hz : E.p z = x) :
    z ∈ Set.range h ↔ ∃ y : (σ.C x).G.left, (σ.C x).G.hom y = closedPoint _ ∧ E.emb x y = z := by
  obtain ⟨hsm, -, hop, hp, hm⟩ := hl
  have hcen : spMap (σ.ρ x) (closedPoint (σ.C x).R) = x := by rw [← σ.hρ]; exact (σ.C x).centre
  have hu : IsUnit (σ.ρ x g) := by
    by_contra hn
    apply hx
    have : g ∈ (spMap (σ.ρ x) (closedPoint (σ.C x).R)).asIdeal := hn
    rwa [hcen] at this
  let t : Sp (σ.C x).R ⟶ Sp (Localization.Away g) := spMap (IsLocalization.Away.lift g hu)
  have ht : t ≫ awayMap g = spMap (σ.ρ x) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]
  have o₂ : OpenIn (pullback.fst H.hom t ≫ h) ((Over.pullback t).obj H).hom E.p (spMap (σ.ρ x)) :=
    ht ▸ openIn_pullback E.p (awayMap g) H.hom h hp t
  have s₂ : Smooth ((Over.pullback t).obj H).hom := inferInstanceAs (Smooth (pullback.snd H.hom t))
  have c₂ : GeometricallyConnected ((Over.pullback t).obj H).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom t))
  have s₁ := (σ.C x).semi.smooth
  have fl : Flat (spMap (σ.ρ x)) := Flat.SpecMap_iff.2 (σ.flat x)
  have m₁ := chart_mulAgree σ E x
  have m₂ := mulAgree_pullback (isGrpPullback_pullback H t) hm
  constructor
  · rintro ⟨v, rfl⟩
    have e : H.hom v = t (closedPoint (σ.C x).R) := by
      apply (awayMap g).isOpenEmbedding.injective
      have e1 : (H.hom ≫ awayMap g) v = x := by rw [← hp]; exact hz
      have e2 : (t ≫ awayMap g) (closedPoint (σ.C x).R) = x := by rw [ht]; exact hcen
      exact e1.trans e2.symm
    obtain ⟨v₂, hv1, hv2⟩ := Scheme.Pullback.exists_preimage_pullback (f := H.hom) (g := t) v _ e
    obtain ⟨ma, oa⟩ := GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ _ _ ((Over.pullback t).obj H) (σ.C x).G _ _ fl fl inferInstance inferInstance
      o₂ (E.openIn x) m₂ m₁
    obtain ⟨y, hy1, hy2⟩ := exists_point E.p _ ((Over.pullback t).obj H) (σ.C x).G _ _ o₂ (E.openIn x) s₂ c₂ ma oa v₂
    exact ⟨y, hy2.trans hv2, hy1.trans (congrArg h hv1)⟩
  · rintro ⟨y, -, rfl⟩
    obtain ⟨ma, oa⟩ := GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ _ _ (σ.C x).G ((Over.pullback t).obj H) _ _ fl fl inferInstance inferInstance
      (E.openIn x) o₂ m₁ m₂
    obtain ⟨v, hv, -⟩ := exists_point E.p _ (σ.C x).G ((Over.pullback t).obj H) _ _ (E.openIn x) o₂ s₁
      (σ.C x).semi.geomConnected ma oa y
    exact ⟨pullback.fst H.hom t v, hv⟩

theorem exists_locGrp_range_eq : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal} := by
  intro σ E hC x
  obtain ⟨g, hg, H', _, h', hl', -⟩ := GlobalTheory.T.exists_local_smooth_group_over_nbhd σ E hC x
  obtain ⟨H, _, h, hl, hgc⟩ := exists_connected σ E g H' h' hl'
  refine ⟨g, hg, H, inferInstance, h, hl, ?_⟩
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    have hpz : g ∉ (E.p (h v)).asIdeal := by
      rw [← Scheme.Hom.comp_apply, hl.2.2.2.1, Scheme.Hom.comp_apply]
      exact awayMap_notMem g _
    obtain ⟨y, hy, hyz⟩ := (mem_range_iff σ E g H h hl hgc _ hpz _ rfl).1 ⟨v, rfl⟩
    exact ⟨⟨_, y, hy, hyz⟩, hpz⟩
  · rintro ⟨⟨x₀, y, hy, rfl⟩, hz⟩
    have hx₀ : E.p (E.emb x₀ y) = x₀ := by
      obtain ⟨w, -⟩ := E.openIn x₀
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply, hy, ← σ.hρ x₀]
      exact (σ.C x₀).centre
    have hz' : g ∉ x₀.asIdeal := by rw [← hx₀]; exact hz
    exact (mem_range_iff σ E g H _ hl hgc x₀ hz' _ hx₀).2 ⟨y, hy, rfl⟩

end GlobalTheory.Desc.UnionLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGroupRangeUnionClosedFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localGroup_range_union_closedFibres : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal} := by
  first | exact @GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq | exact GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq | (intros; apply GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocalGroups
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocalGroups
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.UnionFib

theorem exists_ringHom_extend {A R Ω : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [Field Ω]
    [IsAlgClosed Ω] (φ : A →+* R) [IsLocalHom φ] (hφ : ((residue R).comp φ).Finite) (ψ : A →+* Ω) [IsLocalHom ψ] :
    ∃ u : R →+* Ω, u.comp φ = ψ := by
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra
  letI : Algebra (ResidueField A) Ω := (ResidueField.lift ψ).toAlgebra
  have hf : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hφ
    exact RingHom.Finite.of_comp_finite hφ
  haveI : Module.Finite (ResidueField A) (ResidueField R) := hf
  let l : ResidueField R →ₐ[ResidueField A] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨l.toRingHom.comp (residue R), RingHom.ext fun a => ?_⟩
  exact l.commutes (residue A a)

theorem exists_geom_lift {X S : Scheme.{0}} {j : X ⟶ S} {A : Over X} [GrpObj A] {x : S} (C : Chart j A x) (Ω : Type)
    [Field Ω] [IsAlgClosed Ω] (p : Sp Ω ⟶ S) (hp : p (closedPoint Ω) = x) : ∃ q : Sp Ω ⟶ Sp C.R, q ≫ C.ξ = p := by
  obtain ⟨ψ, hl, hψ⟩ : ∃ ψ : S.presheaf.stalk (C.ξ (closedPoint C.R)) ⟶ CommRingCat.of Ω,
      IsLocalHom ψ.hom ∧ Spec.map ψ ≫ S.fromSpecStalk _ = p := by
    rw [C.centre, ← hp]
    exact ⟨Scheme.stalkClosedPointTo p, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk p⟩
  obtain ⟨u, hu⟩ := exists_ringHom_extend (Scheme.stalkClosedPointTo C.ξ).hom C.etc.2.2 ψ.hom
  refine ⟨spMap u, ?_⟩
  have e : Scheme.stalkClosedPointTo C.ξ ≫ CommRingCat.ofHom u = ψ := CommRingCat.hom_ext hu
  rw [← hψ, ← e, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

theorem isPullback_of_mono {A P G S X : Scheme.{0}} {i : A ⟶ P} {a : A ⟶ S} {p : P ⟶ X} {j : S ⟶ X} (κ : G ⟶ P)
    [Mono κ] {e : A ⟶ G} (h : IsPullback i a p j) (he : e ≫ κ = i) : IsPullback e a (κ ≫ p) j := by
  have w : e ≫ κ ≫ p = a ≫ j := by rw [← h.w, ← he, Category.assoc]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift (s.fst ≫ κ) s.snd (by rw [Category.assoc]; exact s.condition))
    (fun s => ?_) (fun s => h.lift_snd _ _ _) (fun s t h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono κ, Category.assoc, he]
    exact h.lift_fst _ _ _
  · apply h.hom_ext
    · rw [h.lift_fst, ← h₁, Category.assoc, he]
    · rw [h.lift_snd, h₂]

variable {σ : Setup} (E : Emb σ)

theorem rho_closedPoint (x : Sp σ.R) : spMap (σ.ρ x) (closedPoint _) = x := by
  rw [← σ.hρ]; exact (σ.C x).centre

theorem range_subset : Set.range E.ιA ⊆ E.U := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨v, h1, h2⟩ := Scheme.exists_preimage_of_isPullback (σ.cart ((σ.A.hom ≫ awayMap σ.f) a)) a (closedPoint _)
    (rho_closedPoint _).symm
  refine ⟨_, (σ.V _).ι v, h2, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← E.onV, Scheme.Hom.comp_apply, h1]

theorem isPullback_chart (hC : σ.Common) {G : Scheme.{0}} (κ : G ⟶ E.P) [IsOpenImmersion κ] (hκ : Set.range κ = E.U)
    (x : Sp σ.R) : ∃ m : (σ.C x).G.left ⟶ G, m ≫ κ = E.emb x ∧
      IsPullback m (σ.C x).G.hom (κ ≫ E.p) (spMap (σ.ρ x)) := by
  obtain ⟨w, hw⟩ := E.openIn x
  let l := pullback.lift (E.emb x) (σ.C x).G.hom w
  have l1 : l ≫ pullback.fst _ _ = E.emb x := pullback.lift_fst _ _ _
  have l2 : l ≫ pullback.snd _ _ = (σ.C x).G.hom := pullback.lift_snd _ _ _
  have hr : Set.range (E.emb x) ⊆ Set.range κ := by
    rintro _ ⟨y, rfl⟩
    have e1 : pullback.fst E.p (spMap (σ.ρ x)) (l y) = E.emb x y := by rw [← Scheme.Hom.comp_apply, l1]
    rw [hκ, ← e1]
    exact (Emb.fst_mem_U_iff σ E hC x (l y)).2 ⟨y, e1.symm, by rw [← Scheme.Hom.comp_apply, l2]⟩
  refine ⟨IsOpenImmersion.lift κ _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have sq : IsPullback (IsOpenImmersion.lift κ _ hr) l κ (pullback.fst E.p (spMap (σ.ρ x))) := by
    refine IsOpenImmersion.isPullback _ _ _ _ (by rw [l1, IsOpenImmersion.lift_fac]) ?_
    ext z
    constructor
    · intro hz
      have hz' : pullback.fst E.p (spMap (σ.ρ x)) z ∈ E.U := hκ ▸ hz
      obtain ⟨x', y', hy', e⟩ := hz'
      obtain ⟨Ω, _, s, t', o, hst, hs, ht⟩ :=
        Sat.exists_field_pt (pullback.fst E.p (spMap (σ.ρ x))) (E.emb x') z y' e.symm
      obtain ⟨w', -⟩ := E.openIn x'
      obtain ⟨t, h1, h2⟩ := (Sat.transfer σ E hC x x' Ω (s ≫ pullback.snd _ _) (t' ≫ (σ.C x').G.hom) o
        (by rw [Scheme.Hom.comp_apply, ht]; exact hy')
        (by rw [Category.assoc, Category.assoc, ← pullback.condition, ← w', reassoc_of% hst])).2 t' rfl
      have : t ≫ l = s := by
        apply pullback.hom_ext
        · rw [Category.assoc, l1, h2, hst]
        · rw [Category.assoc, l2, h1]
      exact ⟨t o, by rw [← Scheme.Hom.comp_apply, this, hs]⟩
    · rintro ⟨y, rfl⟩
      exact hr ⟨y, by rw [← Scheme.Hom.comp_apply, l1]⟩
  have := sq.paste_vert (IsPullback.of_hasPullback E.p (spMap (σ.ρ x)))
  rwa [l2] at this

theorem alpha_comp (x : Sp σ.R) :
    (σ.C x).α ≫ E.ιA = pullback.fst (σ.C x).G.hom (jK (σ.C x).R) ≫ E.emb x := by
  have hr : Set.range (pullback.fst (σ.C x).G.hom (jK (σ.C x).R)) ⊆ Set.range (σ.V x).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine (σ.hV x _).2 ?_
    have e : spMap (σ.ρ x) ((σ.C x).G.hom (pullback.fst (σ.C x).G.hom (jK (σ.C x).R) z)) =
        awayMap σ.f ((σ.C x).y (pullback.snd (σ.C x).G.hom (jK (σ.C x).R) z)) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        pullback.condition_assoc, (σ.C x).hy, σ.hρ]
    intro hm
    have h1 : σ.f ∈ (spMap (σ.ρ x) ((σ.C x).G.hom (pullback.fst (σ.C x).G.hom (jK (σ.C x).R) z))).asIdeal := hm
    rw [e] at h1
    have h2 : algebraMap σ.R (Localization.Away σ.f) σ.f ∈
      ((σ.C x).y (pullback.snd (σ.C x).G.hom (jK (σ.C x).R) z)).asIdeal := h1
    exact (PrimeSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h2 (IsLocalization.Away.algebraMap_isUnit σ.f))
  have h := σ.compat x _ (𝟙 _) (IsOpenImmersion.lift (σ.V x).ι _ hr)
    (by rw [Category.id_comp, IsOpenImmersion.lift_fac])
  rw [Category.id_comp] at h
  rw [h, Category.assoc, E.onV, IsOpenImmersion.lift_fac_assoc]

theorem isSemiAbelian_of_ext (hC : σ.Common) (G : Over (Sp σ.R)) [GrpObj G] (κ : G.left ⟶ E.P) [IsOpenImmersion κ]
    (hκ : Set.range κ = E.U) (hG : G.hom = κ ≫ E.p) [Smooth G.hom] [QuasiCompact G.hom] {e : σ.A.left ⟶ G.left}
    (he : e ≫ κ = E.ιA) (h : IsGrpPullback σ.A G (awayMap σ.f) e) : IsSemiAbelian G := by
  have := E.sep
  have hsep : IsSeparated G.hom := by rw [hG]; infer_instance
  have key : ∀ x, ∃ m, IsGrpPullback (σ.C x).G G (σ.C x).ξ m := fun x => by
    obtain ⟨m, hm, sq⟩ := isPullback_chart E hC κ hκ x
    rw [← hG, ← σ.hρ] at sq
    obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing (σ.C x).R (FractionRing (σ.C x).R)
    have := (σ.C x).semi.smooth
    refine ⟨m, ZJ.isGrpPullback_of_dominant (jK (σ.C x).R) sq (((σ.C x).gen.comp h).congr (σ.C x).hy ?_)⟩
    rw [← cancel_mono κ, Category.assoc, Category.assoc, he, hm]
    exact alpha_comp E x
  have fib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Sp Ω ⟶ Sp σ.R), ∃ (x : Sp σ.R) (q : Sp Ω ⟶ Sp (σ.C x).R)
      (i : (Over.pullback q).obj (σ.C x).G ≅ (Over.pullback p).obj G), IsMonHom i.hom := fun Ω _ _ p => by
    obtain ⟨q, hq⟩ := exists_geom_lift (σ.C (p (closedPoint Ω))) Ω p rfl
    obtain ⟨m, hm⟩ := key (p (closedPoint Ω))
    obtain ⟨i, hi, -⟩ := grpPullback_iso (((isGrpPullback_pullback _ q).comp hm).congr hq rfl)
      (isGrpPullback_pullback G p)
    exact ⟨_, q, i, hi⟩
  refine ⟨?_, ‹_›, hsep, ‹_›, SemiAbelianCompare.geometricallyConnected_of_isAlgClosed _ fun Ω _ _ p => ?_,
    fun Ω _ _ p => ?_⟩
  · have := σ.ab.comm
    have : IsSchemeTheoreticallyDominant (awayMap σ.f) :=
      ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _
        (IsLocalization.injective (Localization.Away σ.f) (powers_le_nonZeroDivisors_of_noZeroDivisors σ.hf))
    exact SplitExtComm.isCommMonObj_of_dominant h
  · obtain ⟨x, q, i, -⟩ := fib Ω p
    have := (σ.C x).semi.geomConnected
    have : ConnectedSpace ((Over.pullback q).obj (σ.C x).G).left :=
      GeometricallyConnected.geometrically_connectedSpace (f := (σ.C x).G.hom) q _ _ (IsPullback.of_hasPullback _ _)
    have := isIso_inv_left i.symm
    exact (i.symm.inv.left).surjective.connectedSpace (i.symm.inv.left).continuous
  · obtain ⟨x, q, i, hi⟩ := fib Ω p
    obtain ⟨T⟩ := (σ.C x).semi.fibres Ω q
    exact ⟨torusExtOfIso i T⟩

end GlobalTheory.Desc.UnionFib

namespace GlobalTheory.Desc


open UnionFib GroupGlue in
theorem Emb.hasExt_of_locGrp : ∀ (σ : Setup) (E : Emb σ), σ.Common → (∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal}) → HasExt (awayMap σ.f) σ.A := by
  intro σ E hC hloc
  choose g hg H iH h hL hr using hloc
  have oi : ∀ x, IsOpenImmersion (h x) := fun x => (hL x).2.2.1
  have ra : ∀ a : σ.R, Set.range (awayMap a) = {z : Sp σ.R | a ∉ z.asIdeal} := fun a =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  have hU : IsOpen E.U := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨Set.range (h (E.p z)), by rw [hr]; exact Set.inter_subset_left, (h _).isOpenEmbedding.isOpen_range,
      by rw [hr]; exact ⟨hz, hg _⟩⟩
  let U : E.P.Opens := ⟨E.U, hU⟩
  have hι : Set.range U.ι = E.U := Scheme.Opens.range_ι U
  let G : Over (Sp σ.R) := Over.mk (U.ι ≫ E.p)
  let 𝒰 : (Sp σ.R).OpenCover := Scheme.Cover.mkOfCovers (Sp σ.R) (fun x => Sp (Localization.Away (g x)))
    (fun x => awayMap (g x)) (fun x => by
      obtain ⟨y, hy⟩ : x ∈ Set.range (awayMap (g x)) := by rw [ra]; exact hg x
      exact ⟨x, y, hy⟩)
  have hs : ∀ x, Set.range (h x) ⊆ Set.range U.ι := fun x => by rw [hι, hr]; exact Set.inter_subset_left
  let H' : ∀ i : 𝒰.I₀, Over (𝒰.X i) := H
  letI iH' : ∀ i : 𝒰.I₀, GrpObj (H' i) := iH
  let ψ : ∀ i : 𝒰.I₀, (H' i).left ⟶ G.left := fun x => IsOpenImmersion.lift U.ι (h x) (hs x)
  have hψι : ∀ x : Sp σ.R, ψ x ≫ U.ι = h x := fun x => IsOpenImmersion.lift_fac _ _ _
  have hψ : ∀ i, IsPullback (ψ i) (H' i).hom G.hom (𝒰.f i) := fun (x : Sp σ.R) => by
    have : IsOpenImmersion (ψ x ≫ U.ι) := by rw [hψι]; exact oi x
    have : IsOpenImmersion (ψ x) := IsOpenImmersion.of_comp _ U.ι
    refine (IsOpenImmersion.isPullback (H x).hom (ψ x) (awayMap (g x)) (U.ι ≫ E.p) ?_ ?_).flip
    · rw [reassoc_of% (hψι x)]; exact (hL x).2.2.2.1
    · ext z
      constructor
      · intro hz
        have hz' : E.p (U.ι z) ∈ Set.range (awayMap (g x)) := hz
        rw [ra] at hz'
        obtain ⟨y, hy⟩ : U.ι z ∈ Set.range (h x) := by rw [hr]; exact ⟨z.2, hz'⟩
        refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
        rw [← hy, ← hψι]; rfl
      · rintro ⟨y, rfl⟩
        refine ⟨(H x).hom y, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← (hL x).2.2.2.1, ← hψι]; rfl
  have op : ∀ x, OpenIn (h x) (H x).hom E.p (awayMap (g x)) := fun x => by
    refine ⟨(hL x).2.2.2.1, ?_⟩
    have : IsOpenImmersion (pullback.lift (h x) (H x).hom (hL x).2.2.2.1 ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact oi x
    exact IsOpenImmersion.of_comp _ (pullback.fst E.p (awayMap (g x)))
  have hm : MulCompat ψ := fun (x y : Sp σ.R) S u v a a' b b' e₁ e₂ => by
    have := (hL x).1
    have := (hL y).1
    have k := (GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ (awayMap (g x)) (awayMap (g y)) (H x) (H y) (h x) (h y) inferInstance inferInstance
      inferInstance inferInstance (op x) (op y) (hL x).2.2.2.2 (hL y).2.2.2.2).1 S u v a a' b b'
      (by rw [← hψι, ← hψι, reassoc_of% e₁]) (by rw [← hψι, ← hψι, reassoc_of% e₂])
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hψι, hψι]
    exact k
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  have hA : Set.range E.ιA ⊆ Set.range U.ι := by rw [hι]; exact range_subset E
  let e : σ.A.left ⟶ G.left := IsOpenImmersion.lift U.ι _ hA
  have he : e ≫ U.ι = E.ιA := IsOpenImmersion.lift_fac _ _ _
  have hp : IsGrpPullback σ.A G (awayMap σ.f) e := by
    refine ⟨isPullback_of_mono U.ι E.cartA he, fun T a b a₀ b₀ ha hb => ?_⟩
    refine ext_small 𝒰 (T.hom ≫ awayMap σ.f) fun (x : Sp σ.R) S k u hu => ?_
    obtain ⟨c, hc⟩ := exists_rep hψ (T := Over.mk (T.hom ≫ awayMap σ.f)) hu a₀
    obtain ⟨d, hd⟩ := exists_rep hψ (T := Over.mk (T.hom ≫ awayMap σ.f)) hu b₀
    rw [← rep_mul hG (T := Over.mk (T.hom ≫ awayMap σ.f)) hu hc hd]
    let r : Over.mk (k ≫ T.hom) ⟶ T := Over.homMk k rfl
    have k' := (hL x).2.2.2.2 S u (k ≫ T.hom) c d (r ≫ a) (r ≫ b)
      (by rw [← hψι, reassoc_of% hc, ha, ← he]; simp [r]) (by rw [← hψι, reassoc_of% hd, hb, ← he]; simp [r])
    rw [← MonObj.comp_mul] at k'
    rw [← cancel_mono U.ι, Category.assoc, hψι, Category.assoc, Category.assoc, he]
    exact k'.trans (Category.assoc _ _ _)
  have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have : IsZariskiLocalAtTarget @QuasiCompact.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : Smooth G.hom := of_charts @Smooth hψ fun x => (hL x).1
  have : QuasiCompact G.hom := of_charts @QuasiCompact hψ fun x => (hL x).2.1
  exact ⟨G, iG, e, isSemiAbelian_of_ext E hC G U.ι hι rfl he hp, hp⟩

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsToSemiAbelianOfLocalGroupsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendsToSemiAbelian_of_local_groups : ∀ (σ : Setup) (E : Emb σ), σ.Common → (∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal}) → HasExt (awayMap σ.f) σ.A := by
  first | exact @GlobalTheory.Desc.Emb.hasExt_of_locGrp | exact GlobalTheory.Desc.Emb.hasExt_of_locGrp | (intros; apply GlobalTheory.Desc.Emb.hasExt_of_locGrp <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem Setup.hasExt (σ : Setup) : HasExt (awayMap σ.f) σ.A := by
  have hc : σ.Common := GlobalTheory.T.abelianSchemeDescentData_charts_common σ
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_descentSeparatedEmbedding σ hc
  exact GlobalTheory.T.extendsToSemiAbelian_of_local_groups σ E hc (GlobalTheory.T.exists_localGroup_range_union_closedFibres σ E hc)

theorem hasExt_of_setup : ∀ σ : Setup, HasExt (awayMap σ.f) σ.A := Setup.hasExt

end GlobalTheory.Desc
