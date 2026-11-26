module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.MfCoords
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductConjugate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEigenTangentsPullback

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverCoordsExist
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverCoordsExist
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
private theorem isLocallyNoetherian_of_closedImmersion_pSpace (o : Type) [CommRing o] [IsNoetherianRing o] (X : Scheme.{0}) (N : ℕ)
    (i : X ⟶ PSpace o N) [IsClosedImmersion i] : IsLocallyNoetherian X := by
  refine isLocallyNoetherian_of_affine_cover
    (S := fun j : Fin (N + 1) => ⟨i ⁻¹ᵁ GlobalTheory.ProjSpace.chart o N j,
      (GlobalTheory.ProjSpace.isAffineOpen_chart o N j).preimage i⟩) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    have hx : i x ∈ (⨆ j, GlobalTheory.ProjSpace.chart o N j) := by
      rw [GlobalTheory.ProjSpace.iSup_chart]
      trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨j, hj⟩
  · intro j
    letI := GlobalTheory.ProjSpace.algebraSections o N (GlobalTheory.ProjSpace.chart o N j)
    haveI : IsNoetherianRing Γ(PSpace o N, GlobalTheory.ProjSpace.chart o N j) :=
      isNoetherianRing_of_ringEquiv _ (GlobalTheory.ProjSpace.chartAlgEquiv o N j).toRingEquiv
    exact isNoetherianRing_of_surjective _ _ (i.app (GlobalTheory.ProjSpace.chart o N j)).hom
      (Scheme.Hom.app_surjective i _ (GlobalTheory.ProjSpace.isAffineOpen_chart o N j))

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → ∀ (Ω : Type) [Field Ω] [Algebra o Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ξ ≫ s = spMap (algebraMap o Ω) → ∃ (n : ℕ) (x : Fin n → Ω), CoordTie o ξ x := by
  intro o _ _ X s hs Ω _ _ ξ hξ hcomp
  obtain ⟨N, i, hi, rfl⟩ := hs
  haveI := isLocallyNoetherian_of_closedImmersion_pSpace o X N i
  have hZ := GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes X Ω ξ hξ
  let U : X.Opens := ⟨{q | genPt ξ ⤳ q}, hZ.isOpen⟩
  have hr : Set.range ξ ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : y = closedPoint Ω := Subsingleton.elim _ _
    subst this
    exact specializes_rfl
  let ξ' : Sp Ω ⟶ U := IsOpenImmersion.lift U.ι ξ hr
  have hfac : ξ' ≫ U.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _
    (by rw [Scheme.Opens.range_ι]; exact hZ.isClosed)
  have hξ2 : IsCptGen (ξ' ≫ U.ι) := by rw [hfac]; exact hξ
  have hgen' : IsCptGen ξ' := PositivityTheory.HtPt.Mf.isCptGen_of_comp ξ' U.ι hξ2
  have h1 : U.ι (genPt ξ') = genPt ξ := by
    change (ξ' ≫ U.ι) (closedPoint Ω) = ξ (closedPoint Ω)
    rw [hfac]
  have hall : ∀ q, genPt ξ' ⤳ q := by
    intro q
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff, h1]
    exact q.2
  obtain ⟨t, ht, heq⟩ := PositivityTheory.HtPt.Mf.exists_point (ξ' ≫ U.ι ≫ i)
    (by simpa [Category.assoc, reassoc_of% hfac] using hcomp)
  have hct : CoordTie o ξ' t := PositivityTheory.HtPt.Mf.coordTie_of_all (i := U.ι ≫ i) hgen' hall heq
  have h2 : genPt (ξ' ≫ U.ι) = genPt ξ := by rw [hfac]
  have hsurj : ∀ q : Cpt (ξ' ≫ U.ι), ∃ p : Cpt ξ', PositivityTheory.HtPt.Mf.push ξ' U.ι p = q := by
    intro q
    have hq : genPt ξ ⤳ q.1 := by
      rw [← h2]
      exact q.2
    exact ⟨⟨⟨q.1, hq⟩, hall _⟩, Subtype.ext rfl⟩
  have hfin := PositivityTheory.HtPt.Mf.coordTie_comp (o := o) U.ι hξ2 hsurj hct
  rw [hfac] at hfin
  exact ⟨N + 1, t, hfin⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverCoordsExistStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_over_coords_exist : ∀ (o : Type) [CommRing o] [IsNoetherianRing o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → ∀ (Ω : Type) [Field Ω] [Algebra o Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ξ ≫ s = spMap (algebraMap o Ω) → ∃ (n : ℕ) (x : Fin n → Ω), CoordTie o ξ x := by
  first | exact @GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist | exact GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist | (intros; apply GlobalTheory.CompanionTheory.Relay.projective_over_coords_exist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosed
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem exists_lift_of_mem_range {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (x : Sp ℂ ⟶ X)
    (p : Sp ℂ) (hp : x p ∈ Set.range i) : ∃ t : Sp ℂ ⟶ Z, t ≫ i = x := by
  obtain ⟨z, hz⟩ := hp
  obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback z p hz
  have hsub : Subsingleton (Sp ℂ) := inferInstanceAs (Subsingleton (PrimeSpectrum ℂ))
  have hs : Surjective (pullback.snd i x) :=
    ⟨fun q => ⟨w, by rw [hw]; exact Subsingleton.elim _ _⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i x)
  exact ⟨inv (pullback.snd i x) ≫ pullback.fst i x, by simp [pullback.condition]⟩

theorem one_left_eq {S : Scheme.{0}} (G : Over S) [GrpObj G] (X : Over S) :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, Over.toUnit_left]

theorem mem_per_of_frequently : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSeparated G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∀ (s : (Fin n → ℂ) → (Fin g → ℂ)), ContinuousAt s b₀ → (∃ᶠ b in 𝓝 b₀, b ∈ B ∧ s b ∈ e.per b) → s b₀ ∈ e.per b₀ := by
  intro R _ G _ _ g n M B ψ e hsep hψ b₀ hb₀ s hs hfr
  haveI := hsep
  by_contra hne
  have hid : η[G].left ≫ G.hom = 𝟙 _ := Over.w _
  have hη : IsClosedImmersion η[G].left := by
    have : IsClosedImmersion (η[G].left ≫ G.hom) := by rw [hid]; infer_instance
    exact IsClosedImmersion.of_comp _ G.hom
  let V : G.left.Opens := ⟨(Set.range η[G].left)ᶜ, by
    letI := hη
    exact η[G].left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV₀ : ⊤ ≤ (e.ex b₀ (s b₀)).left ⁻¹ᵁ V := by
    intro p _
    show (e.ex b₀ (s b₀)).left p ∉ Set.range η[G].left
    intro hp
    obtain ⟨t, ht⟩ := exists_lift_of_mem_range η[G].left (e.ex b₀ (s b₀)).left p hp
    apply hne
    show e.ex b₀ (s b₀) = 1
    apply Over.OverMorphism.ext
    have h1 : t = spMap (ψ b₀) := by
      have h2 := Over.w (e.ex b₀ (s b₀))
      have h4 : (t ≫ η[G].left) ≫ G.hom = spMap (ψ b₀) := by rw [ht]; exact h2
      rw [Category.assoc, hid] at h4
      exact h4
    rw [one_left_eq, ← ht, h1]
    rfl
  have hopen := (e.hol V 0).1
  have hmem : (b₀, s b₀) ∈ {bz : (Fin n → ℂ) × (Fin g → ℂ) | bz ∈ B ×ˢ Set.univ ∧ ⊤ ≤ (e.ex bz.1 bz.2).left ⁻¹ᵁ V} :=
    ⟨⟨hb₀, trivial⟩, hV₀⟩
  have hcont : ContinuousAt (fun b => (b, s b)) b₀ := continuousAt_id.prodMk hs
  have hev := hcont.eventually (hopen.mem_nhds hmem)
  obtain ⟨b, ⟨-, hper⟩, -, hb⟩ := (hfr.and_eventually hev).exists
  have hper' : e.ex b (s b) = 1 := hper
  have hb' : ⊤ ≤ (e.ex b (s b)).left ⁻¹ᵁ V := hb
  rw [hper'] at hb'
  let p : Sp ℂ := (⊥ : PrimeSpectrum ℂ)
  have hp : (1 : Over.mk (spMap (ψ b)) ⟶ G).left p ∉ Set.range η[G].left := hb' (show p ∈ ⊤ from trivial)
  apply hp
  rw [one_left_eq]
  exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodSetClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_set_closed : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsSeparated G.hom → IsHolPts B ψ → ∀ b₀ ∈ B, ∀ (s : (Fin n → ℂ) → (Fin g → ℂ)), ContinuousAt s b₀ → (∃ᶠ b in 𝓝 b₀, b ∈ B ∧ s b ∈ e.per b) → s b₀ ∈ e.per b₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.mem_per_of_frequently | exact GlobalTheory.CompanionTheory.Ar.Flat.mem_per_of_frequently | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.mem_per_of_frequently <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapTangentCoordinates
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapTangentCoordinates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PeriodCoord

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {A R : Type} [CommRing A] [CommRing R]

theorem dualMap_comp_base (i : Sp A ⟶ X) (θ : A →+* R) :
    spMap (dualMap θ) ≫ (epsAt i).hom = (epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i)).hom := by
  have e : (CommRingCat.ofHom (algebraMap A (DualNumber A))) ≫ CommRingCat.ofHom (dualMap θ) =
      CommRingCat.ofHom θ ≫ CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    show dualMap θ (algebraMap A (DualNumber A) a) = algebraMap R (DualNumber R) (θ a)
    rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl]
    ext <;> simp [dualMap]
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp] at e'
  show spMap (dualMap θ) ≫ Spec.map _ ≫ i = Spec.map _ ≫ 𝟙 (Sp R) ≫ spMap θ ≫ i
  rw [Category.id_comp, ← Category.assoc, e', Category.assoc]

def pushEps (i : Sp A ⟶ X) (θ : A →+* R) (v : epsAt i ⟶ G) : epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i) ⟶ G :=
  Over.homMk (spMap (dualMap θ) ≫ v.left) (by
    have e : (spMap (dualMap θ) ≫ v.left) ≫ G.hom = (epsAt (𝟙 (Sp R) ≫ spMap θ ≫ i)).hom := by
      rw [Category.assoc, Over.w v, dualMap_comp_base]
    exact e)

theorem isTanAt_pushEps (i : Sp A ⟶ X) (θ : A →+* R) {v : epsAt i ⟶ G} (h : IsTanAt G i v) :
    IsTanAt G (𝟙 (Sp R) ≫ spMap θ ≫ i) (pushEps i θ v) := by
  unfold IsTanAt at h ⊢
  have key : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap θ)) =
      Spec.map (CommRingCat.ofHom θ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp [dualMap]
  let s : Over.mk (𝟙 (Sp R) ≫ spMap θ ≫ i) ⟶ Over.mk i :=
    Over.homMk (spMap θ) (by simp)
  have h1 : s ≫ (1 : Over.mk i ⟶ G) = 1 := MonObj.comp_one s
  have h2 := congrArg CommaMorphism.left h1
  refine Eq.trans ?_ h2
  change _ = spMap θ ≫ (1 : Over.mk i ⟶ G).left
  rw [← h]
  change Spec.map _ ≫ spMap (dualMap θ) ≫ v.left = _
  rw [← Category.assoc, key, Category.assoc]

theorem exists_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (i : Sp A ⟶ X) (N : ℕ) (v : Fin N → (epsAt i ⟶ t.G)) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (θ : A →+* R) (m : SABMap t' t (spMap θ ≫ i)) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)), (∀ k, IsTanAt t.G i (v k)) → ∃ x : Fin N → Fin g → R, ∀ k, (M.pt (x k)).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := by
  intro E _ _ _ H X t A _ i N v R _ t' θ m g M hv
  have hx : ∀ k, ∃ e : Fin g → R, (M.pt e).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := fun k => by
    have ht : IsTanAt t'.G (𝟙 (Sp R)) ((LiePull.tanPts m.cart (𝟙 (Sp R))).symm (pushEps i θ (v k))) :=
      (LiePull.isTan_iff m.cart (𝟙 (Sp R)) _).1 (by
        rw [MulEquiv.apply_symm_apply]
        exact isTanAt_pushEps i θ (hv k))
    obtain ⟨e, he⟩ := M.onto _ ht
    refine ⟨e, ?_⟩
    rw [he, ← LiePull.pts_left m.cart (LiePull.eps_assoc (𝟙 (Sp R))), MulEquiv.apply_symm_apply]
    rfl
  choose x hx using hx
  exact ⟨x, hx⟩

end GlobalTheory.CompanionTheory.Ar.PeriodCoord
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapTangentCoordinatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_map_tangent_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (A : Type) [CommRing A] (i : Sp A ⟶ X) (N : ℕ) (v : Fin N → (epsAt i ⟶ t.G)) (R : Type) [CommRing R] (t' : SAB H (Sp R)) (θ : A →+* R) (m : SABMap t' t (spMap θ ≫ i)) (g : ℕ) (M : LieModel t'.G (𝟙 (Sp R)) (Fin g → R)), (∀ k, IsTanAt t.G i (v k)) → ∃ x : Fin N → Fin g → R, ∀ k, (M.pt (x k)).left ≫ m.φ = spMap (dualMap θ) ≫ (v k).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords | exact GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.PeriodCoord.exists_coords <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OneLeftSpMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.ExpChart

open GlobalTheory.HolHom

variable {R : Type} [CommRing R]

def cst {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (p.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem valR_cst {C : Type} [CommRing C] {X : Scheme.{0}} (p : X ⟶ Sp R) (U : X.Opens) (θ : R →+* C)
    (y : Sp C ⟶ X) (hy : y ≫ p = spMap θ) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : R) : evalHom y U h (cst p U a) = θ a := by
  have e := GlobalTheory.TangentOrigin.evalPt_constFn p y U h a
  have e2 := GlobalTheory.TangentOrigin.evalPt_spMap θ a
  rw [hy] at e
  exact e.trans e2

theorem exists_pt {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) (θ : R →+* ℂ)
    (χ : Γ(G.left, V) →+* ℂ) (hχ : ∀ r, χ (cst G.hom V r) = θ r) :
    ∃ x : Over.mk (spMap θ) ⟶ G, ⊤ ≤ x.left ⁻¹ᵁ V ∧ ∀ a, valAt' x.left V a = χ a := by
  obtain ⟨y, hy, he⟩ := GlobalTheory.TangentOrigin.exists_evalPt_eq hV χ
  have hy' : y ≫ G.hom = spMap θ := GlobalTheory.TangentOrigin.eq_spMap_of_evalPt _ θ (fun a => by
    rw [← GlobalTheory.TangentOrigin.evalPt_constFn G.hom y V hy a, he]; exact hχ a)
  refine ⟨Over.homMk y hy', hy, fun a => ?_⟩
  show valAt' y V a = χ a
  rw [GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hy, he]

theorem val_cst {G : Over (Sp R)} (V : G.left.Opens) {θ : R →+* ℂ} (x : Over.mk (spMap θ) ⟶ G)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (r : R) : valAt' x.left V (cst G.hom V r) = θ r :=
  (GlobalTheory.TangentOrigin.valAt'_eq_evalPt _ _ hx _).trans (valR_cst G.hom V θ x.left (Over.w x) hx r)

theorem pt_ext {G : Over (Sp R)} {V : G.left.Opens} (hV : IsAffineOpen V) {θ : R →+* ℂ}
    {x y : Over.mk (spMap θ) ⟶ G} (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V)
    (h : ∀ a, valAt' x.left V a = valAt' y.left V a) : x = y :=
  Over.OverMorphism.ext (point_ext hV hx hy h)

theorem tan_der {X : Scheme.{0}} {x : Sp ℂ ⟶ X} {v : Sp (DualNumber ℂ) ⟶ X}
    (h : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = x) {V : X.Opens} (hx : ⊤ ≤ x ⁻¹ᵁ V) :
    ∃ D : Γ(X, V) →+ ℂ, (∀ f, D f = TrivSqZeroExt.snd (valR v V f)) ∧
      ∀ f f', D (f * f') = valAt' x V f * D f' + valAt' x V f' * D f := by
  have hv := (le_preimage_dual_iff h V).2 hx
  refine ⟨AddMonoidHom.mk' (fun f => TrivSqZeroExt.snd (valR v V f)) fun a b => ?_, fun _ => rfl, fun f f' => ?_⟩
  · simp only [valR_eq _ _ hv, map_add (f := _), TrivSqZeroExt.snd_add]
  · have e1 := fst_valR h hx f
    have e2 := fst_valR h hx f'
    simp only [AddMonoidHom.mk'_apply]
    rw [← e1, ← e2]
    simp only [valR_eq _ _ hv, map_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
    ring

theorem one_left_spMap {G : Over (Sp R)} [GrpObj G] (θ : R →+* ℂ) :
    (1 : Over.mk (spMap θ) ⟶ G).left = spMap θ ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left := by
  have e : (Over.homMk (spMap θ) (by simp) : Over.mk (spMap θ) ⟶ Over.mk (𝟙 (Sp R))) ≫ (1 : Over.mk (𝟙 (Sp R)) ⟶ G) = 1 := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
  exact (congrArg (fun q => Over.Hom.left q) e).symm

theorem tan_base {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ (spMap (dualMap θ) ≫ (M.pt w).left) =
      (1 : Over.mk (spMap θ) ⟶ G).left := by
  rw [one_left_spMap, ← M.tan w, ← Category.assoc, ← Category.assoc]
  congr 1
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun x => ?_
  show TrivSqZeroExt.fst (dualMap θ x) = θ (TrivSqZeroExt.fst x)
  simp [dualMap]

theorem tan_over {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (𝟙 (Sp R)) E) (θ : R →+* ℂ) (w : E) :
    (spMap (dualMap θ) ≫ (M.pt w).left) ≫ G.hom = spMap ((algebraMap ℂ (DualNumber ℂ)).comp θ) := by
  have e : (M.pt w).left ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ 𝟙 (Sp R) := Over.w (M.pt w)
  rw [Category.assoc, e, Category.comp_id]
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory.CompanionTheory.Ar.Flat.ExpChart
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixConjugation
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixConjugation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem dualMap_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (φ : R →+* R') (ψ : R' →+* R'') :
    dualMap (ψ.comp φ) = (dualMap ψ).comp (dualMap φ) :=
  RingHom.ext fun a => TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem dualMap_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (a : R) :
    dualMap φ (algebraMap R (DualNumber R) a) = algebraMap R' (DualNumber R') (φ a) := by
  change dualMap φ (TrivSqZeroExt.inl a) = TrivSqZeroExt.inl (φ a)
  exact TrivSqZeroExt.ext (by simp [dualMap]) (by simp [dualMap])

theorem centre_conj (z : Spec (CommRingCat.of ℂ) ⟶ X) : centre (spMap (starRingEnd ℂ) ≫ z) = centre z := by
  have h : (spMap (starRingEnd ℂ)) (IsLocalRing.closedPoint ℂ) = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact congrArg (fun p => z p) h

theorem extends_conj (M : LieModel G ξ E) {x x' : X} (hx : x = x') (h : genPt ξ ⤳ x) (h' : genPt ξ ⤳ x') (e : E)
    (v : epsAt (X.fromSpecStalk x) ⟶ G) (hv : M.Extends ⟨x, h⟩ e v)
    (φ : X.presheaf.stalk x ⟶ CommRingCat.of ℂ) (φ' : X.presheaf.stalk x' ⟶ CommRingCat.of ℂ)
    (H : Spec.map φ' ≫ X.fromSpecStalk x' = spMap (starRingEnd ℂ) ≫ Spec.map φ ≫ X.fromSpecStalk x) :
    ∃ v' : epsAt (X.fromSpecStalk x') ⟶ G, M.Extends ⟨x', h'⟩ e v' ∧
      Spec.map (CommRingCat.ofHom (dualMap φ'.hom)) ≫ v'.left =
        spMap (dualMap (starRingEnd ℂ)) ≫ Spec.map (CommRingCat.ofHom (dualMap φ.hom)) ≫ v.left := by
  subst hx
  refine ⟨v, hv, ?_⟩
  have h1 : Spec.map φ' = Spec.map (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)) := by
    rw [← cancel_mono (X.fromSpecStalk x), H, Spec.map_comp, Category.assoc]
  have h2 : φ' = φ ≫ CommRingCat.ofHom (starRingEnd ℂ) := Spec.map_injective h1
  subst h2
  have h3 : dualMap (φ ≫ CommRingCat.ofHom (starRingEnd ℂ)).hom =
      (dualMap (starRingEnd ℂ)).comp (dualMap φ.hom) := dualMap_comp _ _
  rw [h3, CommRingCat.ofHom_comp, Spec.map_comp]
  exact Category.assoc _ _ _

def conjVec (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : epsAt z ⟶ G) : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G :=
  Over.homMk (spMap (dualMap (starRingEnd ℂ)) ≫ w.left) (by
    have h1 : w.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫ z := Over.w w
    have h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) =
        CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) :=
      CommRingCat.hom_ext (RingHom.ext fun a => dualMap_algebraMap (starRingEnd ℂ) a)
    have h3 := congrArg Spec.map h2
    simp only [Spec.map_comp] at h3
    simp only [Over.mk_hom, Category.assoc, h1]
    rw [← Category.assoc, h3, Category.assoc])

theorem valAt_conj (M : LieModel G ξ E) (z : Spec (CommRingCat.of ℂ) ⟶ X) (e : E) (w : epsAt z ⟶ G)
    (hw : M.ValAt z e w) : M.ValAt (spMap (starRingEnd ℂ) ≫ z) e (conjVec z w) := by
  obtain ⟨h, v, hv, hl⟩ := hw
  have hc := centre_conj z
  have h' : genPt ξ ⤳ centre (spMap (starRingEnd ℂ) ≫ z) := hc ▸ h
  obtain ⟨v', hv', hl'⟩ := extends_conj M hc.symm h h' e v hv (Scheme.stalkClosedPointTo z)
    (Scheme.stalkClosedPointTo (spMap (starRingEnd ℂ) ≫ z)) (by
      refine (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (spMap (starRingEnd ℂ) ≫ z)).trans ?_
      exact congrArg (spMap (starRingEnd ℂ) ≫ ·) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z).symm)
  refine ⟨h', v', hv', ?_⟩
  have : (conjVec z w).left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left := rfl
  rw [this, hl]
  exact hl'.symm

theorem gramAt_conj_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L (spMap (starRingEnd ℂ) ≫ z) b (Γ.map (starRingEnd ℂ)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J _ y 𝔐 z r b Γ ⟨v, hv, hG⟩
  refine ⟨fun i => conjVec z (v i), fun i => valAt_conj 𝔐.M z (b i) (v i) (hv i), fun p q => ?_⟩
  exact GlobalTheory.T.hodge_inner_product_conjugate E H 𝔐.X 𝔐.t z (v p) (v q) (conjVec z (v p)) (conjVec z (v q)) (Γ p q) rfl rfl (hG p q)

end GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixConjugationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramAt_conj_point_map_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (r : ℕ) (b : Fin r → 𝔐.Li) (Γ : Matrix (Fin r) (Fin r) ℂ), 𝔐.M.GramAt 𝔐.t.PP.L z b Γ → 𝔐.M.GramAt 𝔐.t.PP.L (spMap (starRingEnd ℂ) ≫ z) b (Γ.map (starRingEnd ℂ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point | exact GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.gramAt_conj_point <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuation
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuation
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem spread_slice {n g N : ℕ} {W : Set ((Fin n → ℂ) × (Fin g → ℂ))} (hW : IsOpen W)
    {Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin N → ℂ)} (hΦ : ∀ j, DifferentiableOn ℂ (fun bz => Φ bz j) W)
    {b₀ : Fin n → ℂ} {x : Fin g → ℂ} (hmem : (b₀, x) ∈ W)
    {L : (Fin n → ℂ) × (Fin N → ℂ) → (Fin g → ℂ)} (hL : AnalyticAt ℂ L (b₀, Φ (b₀, x)))
    {Q : (Fin n → ℂ) × (Fin N → ℂ) → Prop} (hQ : ∀ᶠ p in 𝓝 (b₀, Φ (b₀, x)), Q p) :
    ∃ ε : ℝ, 0 < ε ∧ DifferentiableOn ℂ (fun b => L (b, Φ (b, x))) (ball b₀ ε) ∧
      ∀ b ∈ ball b₀ ε, (b, x) ∈ W ∧ Q (b, Φ (b, x)) := by
  have hcont : Continuous (fun b : Fin n → ℂ => (b, x)) := continuous_id.prodMk continuous_const
  have hUo : IsOpen ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) := hW.preimage hcont
  have hΦd : DifferentiableOn ℂ (fun b => Φ (b, x)) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) := by
    rw [differentiableOn_pi]
    intro j
    exact (hΦ j).comp (differentiable_id.prodMk (differentiable_const x)).differentiableOn
      (fun b hb => hb)
  have hFd : DifferentiableOn ℂ (fun b => (b, Φ (b, x))) ((fun b : Fin n → ℂ => (b, x)) ⁻¹' W) :=
    differentiableOn_id.prodMk hΦd
  have hb₀ : b₀ ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W := hmem
  have hFc : ContinuousAt (fun b => (b, Φ (b, x))) b₀ :=
    (hFd.differentiableAt (hUo.mem_nhds hb₀)).continuousAt
  have hU' : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W := hUo.mem_nhds hb₀
  have hev : ∀ᶠ b in 𝓝 b₀, b ∈ (fun b : Fin n → ℂ => (b, x)) ⁻¹' W ∧
      AnalyticAt ℂ L (b, Φ (b, x)) ∧ Q (b, Φ (b, x)) :=
    hU'.and (Filter.Tendsto.eventually hFc (hL.eventually_analyticAt.and hQ))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨ε, hε, fun b hb => ?_, fun b hb => ⟨(hball b hb).1, (hball b hb).2.2⟩⟩
  exact ((hball b hb).2.1.differentiableAt.comp b
    (hFd.differentiableAt (hUo.mem_nhds (hball b hb).1))).differentiableWithinAt

theorem per_spreads : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsOpen B → ∀ b₀ ∈ B, ∀ x ∈ e.per b₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ s (ball b₀ ε) ∧ s b₀ = x ∧ ∀ b ∈ ball b₀ ε, s b ∈ e.per b := by
  intro R _ G _ _ g n M B ψ e _ b₀ hb₀ x hx
  have hx1 : e.ex b₀ x = 1 := hx
  have h01 : e.ex b₀ 0 = 1 := by
    have h := e.add b₀ hb₀ 0 0
    rw [add_zero] at h
    exact mul_right_cancel (h.symm.trans (_root_.one_mul _).symm)
  have hx0 : e.ex b₀ x = e.ex b₀ 0 := hx1.trans h01.symm
  obtain ⟨V, N, f, L, hV, hLan, hinv, huniq⟩ := e.log b₀ hb₀
  let W : Set ((Fin n → ℂ) × (Fin g → ℂ)) := {bz | bz ∈ B ×ˢ Set.univ ∧
    ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex bz.1 bz.2)).base).obj V}
  have hWo : IsOpen W := (e.hol V 0).1
  let Φ : (Fin n → ℂ) × (Fin g → ℂ) → (Fin N → ℂ) :=
    fun bz j => valAt' (Over.Hom.left (e.ex bz.1 bz.2)) V (f j)
  have hΦ : ∀ j, DifferentiableOn ℂ (fun bz => Φ bz j) W := fun j => (e.hol V (f j)).2
  have hmemW : (b₀, x) ∈ W := by
    refine ⟨⟨hb₀, Set.mem_univ _⟩, ?_⟩
    show ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b₀ x)).base).obj V
    rw [hx0]
    exact hV
  have hΦx : Φ (b₀, x) = fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j) := by
    show (fun j => valAt' (Over.Hom.left (e.ex b₀ x)) V (f j)) = _
    rw [hx0]
  have hL' : AnalyticAt ℂ L (b₀, Φ (b₀, x)) := by
    rw [hΦx]
    exact hLan
  let Q : (Fin n → ℂ) × (Fin N → ℂ) → Prop := fun p =>
    ∀ y : Over.mk (spMap (ψ p.1)) ⟶ G,
      ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left y).base).obj V →
        (∀ j, valAt' (Over.Hom.left y) V (f j) = p.2 j) → y = e.ex p.1 (L p)
  have hQ : ∀ᶠ p in 𝓝 (b₀, Φ (b₀, x)), Q p := by
    rw [hΦx]
    exact huniq
  obtain ⟨ε, hε, hdiff, hprop⟩ := spread_slice hWo hΦ hmemW hL' hQ
  have hWmem : ∀ b ∈ ball b₀ ε, b ∈ B ∧
      ⊤ ≤ (TopologicalSpace.Opens.map (Over.Hom.left (e.ex b x)).base).obj V := by
    intro b hb
    obtain ⟨⟨hbB, -⟩, hcov⟩ := (hprop b hb).1
    exact ⟨hbB, hcov⟩
  refine ⟨ε, fun b => x - L (b, Φ (b, x)), hε, fun b hb => (hWmem b hb).1,
    (differentiableOn_const x).sub hdiff, ?_, ?_⟩
  · show x - L (b₀, Φ (b₀, x)) = x
    have h0 : L (b₀, fun j => valAt' (Over.Hom.left (e.ex b₀ 0)) V (f j)) = 0 :=
      hinv.self_of_nhds
    rw [hΦx, h0, sub_zero]
  · intro b hb
    obtain ⟨hbB, hcov⟩ := hWmem b hb
    have hyx : e.ex b x = e.ex b (L (b, Φ (b, x))) :=
      (hprop b hb).2 (e.ex b x) hcov (fun j => rfl)
    show e.ex b (x - L (b, Φ (b, x))) = 1
    have hadd := e.add b hbB (x - L (b, Φ (b, x))) (L (b, Φ (b, x)))
    rw [sub_add_cancel, hyx] at hadd
    exact mul_right_cancel (hadd.symm.trans (_root_.one_mul _).symm)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodHolomorphicContinuationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_holomorphic_continuation : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g n : ℕ) (M : LieModel G (𝟙 (Sp R)) (Fin g → R)) (B : Set (Fin n → ℂ)) (ψ : (Fin n → ℂ) → (R →+* ℂ)) (e : FamExp G M B ψ), IsOpen B → ∀ b₀ ∈ B, ∀ x ∈ e.per b₀, ∃ (ε : ℝ) (s : (Fin n → ℂ) → (Fin g → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ s (ball b₀ ε) ∧ s b₀ = x ∧ ∀ b ∈ ball b₀ ε, s b ∈ e.per b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.per_spreads | exact GlobalTheory.CompanionTheory.Ar.Flat.per_spreads | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.per_spreads <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFieldExtension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
open TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.EigBase

section Linear

variable {O F F' V T : Type} [CommRing O] [Field F] [Field F'] [Algebra F F'] [AddCommGroup V] [Module F V]
  [AddCommGroup T] [Module F' T] [Module F T] [IsScalarTower F F' T]

theorem mem_eigSp {R E : Type} [CommRing R] [AddCommGroup E] [Module R E] (ρ : O →+* Module.End R E) (σ : O →+* R)
    (u : E) : u ∈ eigSp ρ σ ↔ ∀ a, ρ a u = σ a • u := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem linearIndependent_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) : LinearIndependent F' fun i => j (u i) := by
  have hs : LinearIndepOn F id (Set.range u) := hu.linearIndepOn_id
  let b := Module.Basis.extend hs
  let g : Fin n → (hs.extend (Set.subset_univ _)) := fun i => ⟨u i, hs.subset_extend _ ⟨i, rfl⟩⟩
  have hg : Function.Injective g := fun a c e => hu.injective (congrArg Subtype.val e)
  have e : (fun i => j (u i)) = (hj.basis b) ∘ g := by
    funext i
    simp [IsBaseChange.basis_apply, b, g]
  rw [e]
  exact (hj.basis b).linearIndependent.comp g hg

theorem equiv_baseChange {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) (a : O) (y : F' ⊗[F] V) :
    hj.equiv (LinearMap.baseChange F' (ρ a - σ a • LinearMap.id) y) =
      ρ' a (hj.equiv y) - algebraMap F F' (σ a) • hj.equiv y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul c w =>
    rw [LinearMap.baseChange_tmul, hj.equiv_tmul, hj.equiv_tmul, map_smul, hact, smul_comm (algebraMap F F' (σ a)) c,
      ← smul_sub]
    congr 1
    simp [algebraMap_smul]
  | add y z hy hz =>
    simp only [map_add (f := _), hy, hz, smul_add]
    abel

theorem exists_sum_of_mem_eigSp {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {t : T}
    (ht : t ∈ eigSp ρ' ((algebraMap F F').comp σ)) :
    ∃ (J : Type) (B : J → F') (b : J →₀ V), (∀ k, b k ∈ eigSp ρ σ) ∧ t = b.sum fun k w => B k • j w := by
  classical
  let B := Module.Basis.ofVectorSpace F F'
  obtain ⟨b, hb⟩ := TensorProduct.eq_repr_basis_left B (hj.equiv.symm t)
  refine ⟨_, B, b, fun k => (mem_eigSp ρ σ _).2 fun a => ?_, ?_⟩
  · obtain ⟨A, hA⟩ : ∃ A : V →ₗ[F] V, A = ρ a - σ a • LinearMap.id := ⟨_, rfl⟩
    have h0 : LinearMap.baseChange F' A (hj.equiv.symm t) = 0 := by
      apply hj.equiv.injective
      rw [hA, equiv_baseChange hj σ hact, LinearEquiv.apply_symm_apply, map_zero]
      exact sub_eq_zero.2 ((mem_eigSp ρ' _ t).1 ht a)
    rw [← hb, map_finsuppSum] at h0
    simp only [LinearMap.baseChange_tmul] at h0
    have h1 : (b.mapRange A (map_zero A)).sum (fun i n => B i ⊗ₜ[F] n) = 0 := by
      rw [Finsupp.sum_mapRange_index (by simp)]
      exact h0
    have h2 := TensorProduct.sum_tmul_basis_left_eq_zero B _ h1
    have h3 := DFunLike.congr_fun h2 k
    simpa [hA, sub_eq_zero] using h3
  · rw [← hj.equiv.apply_symm_apply t, ← hb, map_finsuppSum]
    simp [hj.equiv_tmul]

theorem frame_base {j : V →ₗ[F] T} (hj : IsBaseChange F' j) {ρ : O →+* Module.End F V}
    {ρ' : O →+* Module.End F' T} (σ : O →+* F) (hact : ∀ a e, ρ' a (j e) = j (ρ a e)) {n : ℕ} {u : Fin n → V}
    (hu : LinearIndependent F u) (hs : Submodule.span F (Set.range u) = eigSp ρ σ) :
    LinearIndependent F' (fun i => j (u i)) ∧
      Submodule.span F' (Set.range fun i => j (u i)) = eigSp ρ' ((algebraMap F F').comp σ) := by
  refine ⟨linearIndependent_base hj hu, le_antisymm (Submodule.span_le.2 ?_) fun t ht => ?_⟩
  · rintro _ ⟨i, rfl⟩
    have hi : u i ∈ eigSp ρ σ := hs ▸ Submodule.subset_span ⟨i, rfl⟩
    refine (mem_eigSp ρ' _ _).2 fun a => ?_
    rw [hact, (mem_eigSp ρ σ _).1 hi a, map_smul]
    simp [algebraMap_smul]
  · obtain ⟨J, B, b, hb, rfl⟩ := exists_sum_of_mem_eigSp hj σ hact ht
    have key : ∀ w ∈ Submodule.span F (Set.range u),
        j w ∈ Submodule.span F' (Set.range fun i => j (u i)) := fun w hw => by
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i, rfl⟩ := hw
        exact Submodule.subset_span ⟨i, rfl⟩
      | zero => simp
      | add w z _ _ hw hz =>
        rw [map_add (f := _)]
        exact Submodule.add_mem _ hw hz
      | smul c w _ hw =>
        rw [map_smul, ← algebraMap_smul F' c]
        exact Submodule.smul_mem _ _ hw
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (key _ (hs ▸ hb k))

end Linear

theorem eigFrame_base {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {F F' : Type} [Field F]
    [Field F'] [Algebra F F'] (x : Sp F ⟶ S) {P : Type} [CommRing P] (act : OAct P G) (σ : P →+* F) {n : ℕ}
    (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt (spMap (algebraMap F F') ≫ x) ⟶ G))
    (hv : ∀ i, (v' i).left = spMap (dualMap (algebraMap F F')) ≫ (v i).left) (h : IsEigFrame act x σ v) :
    IsEigFrame act (spMap (algebraMap F F') ≫ x) ((algebraMap F F').comp σ) v' := by
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  obtain ⟨T, _, _, _, _, M', j, hl, hj⟩ := GlobalTheory.T.exists_lie_model_base_change S G F F' x V M
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G F x V M P act.act act.hom act.one act.mul act.add
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act S G F' _ T M' P act.act act.hom act.one act.mul act.add
  have hl' : ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap F F')) ≫ (M.pt e).left := fun e => by
    have := hl e
    simpa using this
  have hact : ∀ a e, ρ' a (j e) = j (ρ a e) := fun a e => M'.inj (Over.OverMorphism.ext (by
    rw [hρ' a (j e), Over.comp_left, hl', hl', hρ a e, Over.comp_left, Category.assoc]))
  choose u hu using fun i => M.onto (v i) (h.1 i).1
  obtain rfl : (fun k => M.pt (u k)) = v := funext hu
  obtain ⟨-, hf⟩ := GlobalTheory.T.lie_model_eigenvectors_action S F G x V M
  obtain ⟨hli, hsp⟩ := ((hf P act ρ σ hρ).2 n u).1 h
  have hvv : v' = fun k => M'.pt (j (u k)) := funext fun k => Over.OverMorphism.ext (by rw [hv k, hl'])
  rw [hvv]
  exact (((GlobalTheory.T.lie_model_eigenvectors_action S F' G _ T M').2 P act ρ' _ hρ').2 n _).2 (frame_base hj σ hact hli hsp)

theorem isEigFrame_base : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) [Smooth G.hom] (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (F' : Type) [Field F'] (f : F →+* F') (x' : Sp F' ⟶ S), spMap f ≫ x = x' → ∀ (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (v' : Fin n → (epsAt x' ⟶ G)), (∀ i, (v' i).left = spMap (dualMap f) ≫ (v i).left) → IsEigFrame act x σ v → IsEigFrame act x' (f.comp σ) v' := by
  intro S G _ _ F _ x _ P _ act σ F' _ f x' hx n v v' hv h
  letI := f.toAlgebra
  subst hx
  exact eigFrame_base x act σ v v' hv h

end GlobalTheory.CompanionTheory.Ar.EigBase
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open GlobalTheory.CompanionTheory.Ar.LocFn.Transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem isEigFrame_of_sameVec (Y : Model Xo c β) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) (κ : 𝓞 E →+* F) {n : ℕ}
    (v : Fin n → (epsAt (under y) ⟶ Xo.univ.t.G)) (v₀ : Fin n → (epsAt (y ≫ Y.j) ⟶ Y.t.G))
    (hs : ∀ i, SameVec Y y (v i) (v₀ i)) (hf : IsEigFrame Y.t.act (y ≫ Y.j) κ v₀) :
    IsEigFrame Xo.univ.t.act (under y) κ v := by
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  choose u hu₀ hu₁ hu₂ using hs
  let a : Fin n → (epsAt y ⟶ Y.oF.t.G) := fun i => Over.homMk (u i) (hu₀ i)
  have e₀ : (fun i => tanMap hq y (a i)) = v₀ := funext fun i => Over.OverMorphism.ext (hu₂ i)
  have e₁ : (fun i => tanMap hp y (a i)) = v := funext fun i => Over.OverMorphism.ext (hu₁ i)
  have h₁ : IsEigFrame Y.oF.t.act y κ a :=
    (isEigFrame_iff hq Y.oF.t.act Y.t.act Y.m.act y κ a).1 (by rw [e₀]; exact hf)
  have h₂ := (isEigFrame_iff hp Y.oF.t.act Xo.univ.t.act Y.m0.act y κ a).2 h₁
  rw [e₁] at h₂
  exact h₂

theorem isFramed_of_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (v₀ : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)), y ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y y (v i) (v₀ i)) → (∀ j, SameVec Y y (w j) (w₀ j)) → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c τ)) v₀ → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w₀ → IsFramed Set.univ τ σ y v w := by
  intro E _ _ _ H D l Xo c O _ β Y τ σ y v w v₀ w₀ hy hv hw fv fw
  exact ⟨hy, Set.subset_univ _, isEigFrame_of_sameVec Y y _ v v₀ hv fv, isEigFrame_of_sameVec Y y _ w w₀ hw fw⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.VectorsAtComplexPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectors_at_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (y : Sp ℂ ⟶ Xo.XF c) (v : Vecs y D.p) (w : Vecs y D.q) (v₀ : Fin D.p → (epsAt (y ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (y ≫ Y.j) ⟶ Y.t.G)), y ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y y (v i) (v₀ i)) → (∀ j, SameVec Y y (w j) (w₀ j)) → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c τ)) v₀ → IsEigFrame Y.t.act (y ≫ Y.j) (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w₀ → IsFramed Set.univ τ σ y v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model | exact GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isFramed_of_model <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueLocallyRegularFunction
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueLocallyRegularFunction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SectionNear

theorem germ_closedPoint {Y : Scheme.{0}} {R : CommRingCat.{0}} [IsLocalRing R] (f : Spec R ⟶ Y) (U : Y.Opens)
    (hU : f (IsLocalRing.closedPoint R) ∈ U) (h : ⊤ ≤ f ⁻¹ᵁ U) :
    Y.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo f =
      f.appLE U ⊤ h ≫ (Scheme.ΓSpecIso R).hom := by
  rw [Scheme.germ_stalkClosedPointTo]
  simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]

theorem fromSpec_appLE_self {T : Scheme.{0}} {V : T.Opens} (hV : IsAffineOpen V) (h : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V) :
    hV.fromSpec.appLE V ⊤ h ≫ (Scheme.ΓSpecIso Γ(T, V)).hom = 𝟙 _ := by
  have e : (Spec Γ(T, V)).presheaf.map (eqToHom hV.fromSpec_preimage_self).op ≫
      (Spec Γ(T, V)).presheaf.map (homOfLE h).op = 𝟙 _ := by
    have e₀ : (eqToHom hV.fromSpec_preimage_self).op ≫ (homOfLE h).op = 𝟙 _ :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [← Functor.map_comp, e₀, CategoryTheory.Functor.map_id]
  rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, Category.assoc,
    reassoc_of% e]
  simp

theorem spMap_fromSpec_appLE {T : Scheme.{0}} {V : T.Opens} (hV : IsAffineOpen V) (χ : Γ(T, V) →+* ℂ)
    (h : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V) :
    (spMap χ ≫ hV.fromSpec).appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = CommRingCat.ofHom χ := by
  have h₁ : ⊤ ≤ hV.fromSpec ⁻¹ᵁ V := hV.fromSpec_preimage_self.ge
  have n := Scheme.ΓSpecIso_naturality (R := Γ(T, V)) (S := CommRingCat.of ℂ) (CommRingCat.ofHom χ)
  have a : (spMap χ).appLE ⊤ ⊤ le_top = Scheme.Hom.appTop (spMap χ) := by
    simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    exact Category.comp_id _
  rw [← Scheme.Hom.appLE_comp_appLE (spMap χ) hV.fromSpec V ⊤ ⊤ h₁ le_top, a, Category.assoc, n,
    reassoc_of% (fromSpec_appLE_self hV h₁)]

theorem section_near : ∀ (X T : Scheme.{0}) (j : T ⟶ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (y₀ : Sp ℂ ⟶ T) (t : Ω) (r₀ : ℂ), ValAt ξ (y₀ ≫ j) t r₀ → ∃ W₁ : T.Opens, ⊤ ≤ y₀ ⁻¹ᵁ W₁ ∧ ∀ (V : T.Opens) (hV : IsAffineOpen V), V ≤ W₁ → ∃ g : Γ(T, V), ∀ (χ : Γ(T, V) →+* ℂ) (r : ℂ), ValAt ξ ((spMap χ ≫ hV.fromSpec) ≫ j) t r → r = χ g := by
  intro X T j Ω _ ξ hξ y₀ t r₀ h₀
  obtain ⟨h, s, hs, -⟩ := h₀
  obtain ⟨N, hp, G, rfl⟩ := TopCat.Presheaf.germ_exist X.presheaf s
  have hgen : genPt ξ ∈ N := h.mem_open N.2 hp
  have hgerm : ∀ (p : Cpt ξ) (hp : p.1 ∈ N), genMap ξ p (X.presheaf.germ N p.1 hp G) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ N (genPt ξ) hgen G) := by
    intro p hp
    have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hp p.2
    have e' : (X.presheaf.stalkSpecializes p.2).hom (X.presheaf.germ N p.1 hp G) =
        X.presheaf.germ N (genPt ξ) hgen G := by
      rw [← e]; rfl
    exact congrArg (Scheme.stalkClosedPointTo ξ).hom e'
  refine ⟨j ⁻¹ᵁ N, ?_, fun V hV hVN => ⟨j.appLE N V hVN G, fun χ r hr => ?_⟩⟩
  · intro x _
    have hx : x = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    subst hx
    exact hp
  · obtain ⟨h', s', hs', rfl⟩ := hr
    have hcV : (spMap χ ≫ hV.fromSpec) (IsLocalRing.closedPoint ℂ) ∈ V := by
      have : hV.fromSpec ((spMap χ) (IsLocalRing.closedPoint ℂ)) ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
      rw [hV.range_fromSpec] at this
      exact this
    have hq : centre ((spMap χ ≫ hV.fromSpec) ≫ j) ∈ N := hVN hcV
    have e : s' = X.presheaf.germ N _ hq G :=
      hξ.inj ⟨_, h'⟩ (hs'.trans ((hs.symm.trans (hgerm ⟨_, h⟩ hp)).trans (hgerm ⟨_, h'⟩ hq).symm))
    subst e
    have e₂ : ⊤ ≤ (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V :=
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hcV).ge
    have k := germ_closedPoint (R := CommRingCat.of ℂ) ((spMap χ ≫ hV.fromSpec) ≫ j) N hq
      (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hq).ge
    have d : ((spMap χ ≫ hV.fromSpec) ≫ j).appLE N ⊤
        (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of ℂ) _ hq).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = j.appLE N V hVN ≫ CommRingCat.ofHom χ := by
      rw [← Scheme.Hom.appLE_comp_appLE (spMap χ ≫ hV.fromSpec) j N V ⊤ hVN e₂, Category.assoc,
        spMap_fromSpec_appLE hV χ e₂]
    exact congrArg (fun φ => φ.hom G) (k.trans d)

end GlobalTheory.CompanionTheory.Ar.SectionNear
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueLocallyRegularFunctionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.value_locally_regular_function : ∀ (X T : Scheme.{0}) (j : T ⟶ X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (y₀ : Sp ℂ ⟶ T) (t : Ω) (r₀ : ℂ), ValAt ξ (y₀ ≫ j) t r₀ → ∃ W₁ : T.Opens, ⊤ ≤ y₀ ⁻¹ᵁ W₁ ∧ ∀ (V : T.Opens) (hV : IsAffineOpen V), V ≤ W₁ → ∃ g : Γ(T, V), ∀ (χ : Γ(T, V) →+* ℂ) (r : ℂ), ValAt ξ ((spMap χ ≫ hV.fromSpec) ≫ j) t r → r = χ g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SectionNear.section_near | exact GlobalTheory.CompanionTheory.Ar.SectionNear.section_near | (intros; apply GlobalTheory.CompanionTheory.Ar.SectionNear.section_near <;> assumption)
end
end
