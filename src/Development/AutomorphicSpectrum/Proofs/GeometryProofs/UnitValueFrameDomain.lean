module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitValueFrameDomain
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitValueFrameDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.UnitValue

theorem mem_regAt_of_pow_mul {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ}
    {f u : Ω} (hf : f ≠ 0) (hf' : f⁻¹ ∈ regAt ξ p) {n : ℕ} (h : f ^ n * u ∈ regAt ξ p) : u ∈ regAt ξ p := by
  have hu : u = f⁻¹ ^ n * (f ^ n * u) := by
    rw [← _root_.mul_assoc, ← _root_.mul_pow, inv_mul_cancel₀ hf, _root_.one_pow, _root_.one_mul]
  rw [hu]
  exact mul_mem (pow_mem hf' n) h

private theorem valAt_unique_lemma {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (hg : GlobalTheory.CompanionTheory.Ar.IsCptGen ξ) {z : Spec (CommRingCat.of ℂ) ⟶ X} {a : Ω} {r r' : ℂ}
    (h1 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a r) (h2 : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a r') : r = r' := by
  obtain ⟨h, s, hs, rfl⟩ := h1
  obtain ⟨h', s', hs', rfl⟩ := h2
  have hss : s = s' := hg.inj ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ (hs.trans hs'.symm)
  rw [hss]

private theorem ne_zero_and_inv_mem_regAt_of_valAt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {z : Spec (CommRingCat.of ℂ) ⟶ X} (hz : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ GlobalTheory.CompanionTheory.Ar.centre z) {a : Ω} {v : ℂ}
    (hv : v ≠ 0) (h : GlobalTheory.CompanionTheory.Ar.ValAt ξ z a v) :
    a ≠ 0 ∧ a⁻¹ ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ := by
  obtain ⟨h', s, hs, hsv⟩ := h
  have hsu : IsUnit s := by
    have hi : IsUnit ((Scheme.stalkClosedPointTo z).hom s) := by
      rw [hsv]; exact hv.isUnit
    have hloc : IsLocalHom (Scheme.stalkClosedPointTo z).hom := by infer_instance
    exact hloc.map_nonunit s hi
  refine ⟨?_, ?_⟩
  · rw [← hs]
    exact (hsu.map (GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h'⟩)).ne_zero
  · have hva : ∃ r : ℂ, GlobalTheory.CompanionTheory.Ar.ValAt ξ z a⁻¹ r := by
      refine ⟨_, h', ↑hsu.unit⁻¹, ?_, rfl⟩
      rw [map_units_inv, IsUnit.unit_spec, hs]
    obtain ⟨r, hr⟩ := hva
    exact GlobalTheory.CompanionTheory.Ar.ChgUnit.mem_regAt_of_valAt hr _ rfl

theorem valAt_ne_zero_of_isUnitOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f u : Ω), CoordTie ℤ ξ (segreCoord y) → genPt ξ ⤳ centre z → CoordsAt ξ y z w → InFrameDomain y cc f w → IsUnitOn y cc f u → valAt y u w ≠ 0 ∧ ValAt ξ z u (valAt y u w) := by
  intro X Ω _ ξ K _ J _ y z w cc f u hT hz hC hF hU
  have hequiv := GlobalTheory.T.valAt_iff_value_at X Ω ξ K J y hT z w hz hC
  have hch := GlobalTheory.CompanionTheory.Ar.ChgUnit.inChart_of_coordsAt hC cc (fun k => (hF.1 k).isUnit)
    ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ rfl
  have hreg : ∀ a, a ∈ ReciprocityTheory.ChartRestriction.G.Geo.chartRing ℤ (GroundTheory.Heights₂.Heights.LowerBoundFree.segreCoord y) cc →
      a ∈ GlobalTheory.CompanionTheory.Ar.regAt ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, hz⟩ :=
    fun a ha => (hT.ring cc hch.1 a).1 ha _ hch
  obtain ⟨v, hv, hv0⟩ := hF.2
  obtain ⟨hf0, hfi⟩ := ne_zero_and_inv_mem_regAt_of_valAt hz hv0 ((hequiv f v).2 hv)
  obtain ⟨hu0, ⟨n, hn⟩, ⟨m, hm⟩⟩ := hU
  have hu := mem_regAt_of_pow_mul hf0 hfi (hreg _ hn)
  have hui := mem_regAt_of_pow_mul hf0 hfi (hreg _ hm)
  obtain ⟨r, hr0, hr⟩ := GlobalTheory.CompanionTheory.Ar.ChgUnit.exists_value_of_unit hT.gen z hz hu0 hu hui
  have hex : ∃ v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsValueAt y u w v := ⟨r, (hequiv u r).1 hr⟩
  have hval : GroundTheory.Heights₂.Heights.LowerBoundFree.valAt y u w = hex.choose := by
    rw [GroundTheory.Heights₂.Heights.LowerBoundFree.valAt, dite_eq_left hex]
  have hc : GlobalTheory.CompanionTheory.Ar.ValAt ξ z u hex.choose := (hequiv u _).2 hex.choose_spec
  have heq : hex.choose = r := valAt_unique_lemma hT.gen hc hr
  rw [hval, heq]
  exact ⟨hr0, hr⟩

end GlobalTheory.CompanionTheory.Ar.UnitValue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitValueFrameDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_value_frame_domain : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (z : Spec (CommRingCat.of ℂ) ⟶ X) (w : (Σ k, J k) → ℂ) (cc : (k : K) → J k) (f u : Ω), CoordTie ℤ ξ (segreCoord y) → genPt ξ ⤳ centre z → CoordsAt ξ y z w → InFrameDomain y cc f w → IsUnitOn y cc f u → valAt y u w ≠ 0 ∧ ValAt ξ z u (valAt y u w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn | exact GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn | (intros; apply GlobalTheory.CompanionTheory.Ar.UnitValue.valAt_ne_zero_of_isUnitOn <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleComponentClopen
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleComponentClopen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_ringEquiv_of_genPt_eq {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X)
    (ξ' : Sp Ω' ⟶ X) (h : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom)
    (h' : Function.Bijective (Scheme.stalkClosedPointTo ξ').hom) (he : genPt ξ = genPt ξ') :
    ∃ e : Ω ≃+* Ω', spMap e.toRingHom ≫ ξ = ξ' := by
  haveI : IsIso (Scheme.stalkClosedPointTo ξ) := (ConcreteCategory.isIso_iff_bijective _).2 h
  haveI : IsIso (Scheme.stalkClosedPointTo ξ') := (ConcreteCategory.isIso_iff_bijective _).2 h'
  have hi : Inseparable (ξ (IsLocalRing.closedPoint Ω)) (ξ' (IsLocalRing.closedPoint Ω')) := .of_eq he
  let i : CommRingCat.of Ω ≅ CommRingCat.of Ω' :=
    (asIso (Scheme.stalkClosedPointTo ξ)).symm ≪≫ X.presheaf.stalkCongr hi ≪≫
      asIso (Scheme.stalkClosedPointTo ξ')
  refine ⟨i.commRingCatIsoToRingEquiv, ?_⟩
  have e1 : Scheme.stalkClosedPointTo ξ ≫ i.hom =
      (X.presheaf.stalkCongr hi).hom ≫ Scheme.stalkClosedPointTo ξ' := by simp [i]
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ'
  have h3 : Spec.map (X.presheaf.stalkCongr hi).hom ≫ X.fromSpecStalk _ = X.fromSpecStalk _ :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hi.symm.specializes
  show Spec.map i.hom ≫ ξ = ξ'
  conv_lhs => rw [← h1]
  conv_rhs => rw [← h2]
  rw [← Category.assoc, ← Spec.map_comp, e1, Spec.map_comp, Category.assoc, h3]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem bijective_stalk_of_cptOver {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}
    (Z : CptOver Y U) (hβ : FracBase β) : Function.Bijective (Scheme.stalkClosedPointTo Z.ξ₀).hom := by
  obtain ⟨h1, h2⟩ := j_flat_preimmersion Y hβ.1 hβ.2.2
  have hb := stalkMap_bijective_of_flat_preimmersion Y.j (Z.ξ₀ (IsLocalRing.closedPoint Z.Ω))
  have hg := Z.gen.bij
  rw [Scheme.stalkClosedPointTo_comp] at hg
  exact (Function.Bijective.of_comp_iff _ hb).1 hg

theorem genPt_eq_of_cptOver {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}
    {Y : Model Xo c β} {Y' : Model Xo c β'} {U : Set (Xo.XF c)} (Z : CptOver Y U) (Z' : CptOver Y' U) :
    genPt Z.ξ₀ = genPt Z'.ξ₀ :=
  (((Z.closure _).1 Z'.genPt_mem).antisymm ((Z'.closure _).1 Z.genPt_mem)).eq

theorem cptOver_any : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), U ∈ irreducibleComponents (Xo.XF c) → IsClopen U ∧ (∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), FracBase β → Nonempty (CptOver Y U)) ∧ ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (Z : CptOver Y U) (Z' : CptOver Y' U), FracBase β → FracBase β' → Z.IsGeom → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c U hU
  refine ⟨Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj Xo c) ⟨U, hU⟩,
    fun O _ β Y hβ => nonempty_cptOver_of_fraction hβ.1 hβ.2.2 Y U hU, ?_⟩
  intro O _ β Y O' _ β' Y' Z Z' hβ hβ' hg
  obtain ⟨e, he⟩ := exists_ringEquiv_of_genPt_eq Z.ξ₀ Z'.ξ₀ (bijective_stalk_of_cptOver Z hβ)
    (bijective_stalk_of_cptOver Z' hβ') (genPt_eq_of_cptOver Z Z')
  have h2 : spMap e.toRingHom ≫ spMap Z.inc = spMap Z'.inc := by
    rw [← Z.over_inc, ← Z'.over_inc, ← he, Category.assoc]
  have h4 : CommRingCat.ofHom Z.inc ≫ CommRingCat.ofHom e.toRingHom = CommRingCat.ofHom Z'.inc :=
    Spec.map_injective (by rw [Spec.map_comp]; exact h2)
  have h3 : e.toRingHom.comp Z.inc = Z'.inc := congrArg CommRingCat.Hom.hom h4
  rintro x ⟨f, hf, hx⟩
  have h5 : f.eval₂ Z.inc (e.symm x) = 0 := by
    apply e.injective
    have := Polynomial.hom_eval₂ f Z.inc e.toRingHom (e.symm x)
    rw [h3] at this
    simpa [hx] using this
  obtain ⟨a, ha⟩ := hg (e.symm x) ⟨f, hf, h5⟩
  refine ⟨a, ?_⟩
  rw [← h3]
  simp [ha]

end GlobalTheory.CompanionTheory.Ar.Br
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IrreducibleComponentClopenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.irreducible_component_clopen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), U ∈ irreducibleComponents (Xo.XF c) → IsClopen U ∧ (∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), FracBase β → Nonempty (CptOver Y U)) ∧ ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (Y' : Model Xo c β') (Z : CptOver Y U) (Z' : CptOver Y' U), FracBase β → FracBase β' → Z.IsGeom → Z'.IsGeom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.cptOver_any | exact GlobalTheory.CompanionTheory.Ar.Br.cptOver_any | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.cptOver_any <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniversalLieModelPullback
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniversalLieModelPullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LieTransport

private theorem mul_left_eq_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : g = T.hom ≫ f) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (hy : y₀.left = y.left ≫ φ) :
    (x₀ * y₀).left = (x * y).left ≫ φ := by
  subst hg
  exact h.2 T x y x₀ y₀ hx hy

private theorem one_left_eq_of_isGrpPullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S')
    (g : T.left ⟶ S) (hg : g = T.hom ≫ f) :
    (1 : Over.mk g ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  subst hg
  let o : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ)
    (by rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
  have hm : (o * o).left = o.left := by
    rw [mul_left_eq_of_isGrpPullback h T _ rfl 1 1 o o rfl rfl, _root_.mul_one]
    rfl
  have ho : o * o = o := Over.OverMorphism.ext hm
  have ho1 : o = 1 := by
    have := congrArg (· * o⁻¹) ho
    simpa [_root_.mul_assoc] using this
  rw [← ho1]
  rfl

private theorem specMap_fstHom_comp_algebraMap_eq_id (R : Type) [CommRing R] :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
  rw [← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of R)
  ext r
  simp

private theorem exists_lieModel_pullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {R : Type} [CommRing R]
    (x : Spec (CommRingCat.of R) ⟶ S') (x' : Spec (CommRingCat.of R) ⟶ S) (hx : x' = x ≫ f)
    {W : Type} [AddCommGroup W] [Module R W] (M : LieModel G' x W) :
    ∃ N : LieModel G x' W, ∀ e, (N.pt e).left = (M.pt e).left ≫ φ := by
  subst hx
  have hw : ∀ e, ((M.pt e).left ≫ φ) ≫ G.hom = (epsAt (x ≫ f)).hom := by
    intro e
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    simp [epsAt]
  let P : W → (epsAt (x ≫ f) ⟶ G) := fun e =>
    Over.homMk (U := epsAt (x ≫ f)) (V := G) ((M.pt e).left ≫ φ) (hw e)
  have hP : ∀ e, (P e).left = (M.pt e).left ≫ φ := fun e => rfl
  have one_eq := one_left_eq_of_isGrpPullback h (Over.mk x) (x ≫ f) rfl
  have hg : Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ x ≫ f =
      (epsAt x).hom ≫ f := by simp [epsAt]
  refine ⟨⟨P, ?_, ?_, ?_, ?_, ?_⟩, hP⟩
  · intro e
    have ht := M.tan e
    unfold IsTanAt at ht ⊢
    rw [hP, ← Category.assoc, ht]
    exact one_eq.symm
  · intro e e' hee
    apply M.inj
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · have := congrArg Over.Hom.left hee
      simpa [P] using this
    · rw [Over.w, Over.w]
  · intro v hv
    have hvw : v.left ≫ G.hom = (epsAt x).hom ≫ f := by
      rw [Over.w]; simp [epsAt]
    let v' : epsAt x ⟶ G' := Over.homMk (h.1.lift v.left (epsAt x).hom hvw) (h.1.lift_snd _ _ _)
    have hv' : IsTanAt G' x v' := by
      unfold IsTanAt at hv ⊢
      apply h.1.hom_ext
      · rw [Category.assoc]
        simp only [v', Over.homMk_left, h.1.lift_fst]
        rw [hv, one_eq]
      · rw [Category.assoc]
        simp only [v', Over.homMk_left, h.1.lift_snd]
        rw [Over.w]
        simp only [epsAt, Over.mk_hom]
        rw [← Category.assoc, specMap_fstHom_comp_algebraMap_eq_id, Category.id_comp]
    obtain ⟨e, he⟩ := M.onto v' hv'
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    show (M.pt e).left ≫ φ = v.left
    rw [he]
    exact h.1.lift_fst _ _ _
  · intro e e'
    apply Over.OverMorphism.ext
    have hm := mul_left_eq_of_isGrpPullback h (epsAt x) _ hg (M.pt e) (M.pt e') (P e) (P e') (hP e) (hP e')
    refine Eq.trans ?_ hm.symm
    rw [hP, M.add]
  · intro c e
    show (M.pt (c • e)).left ≫ φ = _
    rw [M.smul, Category.assoc]
    rfl

private theorem exists_isActOf_geometry {S : Scheme} {G : Over S} [GrpObj G] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {W : Type} [AddCommGroup W] [Module R W]
    (M : LieModel G x W) {O : Type} [CommRing O] (a : OAct O G) :
    ∃ ρ : O →+* Module.End R W, M.IsActOf a.act ρ := by
  have hpt0 : M.pt 0 = 1 := by
    have h0 := M.add 0 0
    rw [add_zero] at h0
    have := congrArg (· * (M.pt 0)⁻¹) h0
    simpa [_root_.mul_assoc] using this.symm
  have tan : ∀ (b : O) (e : W), IsTanAt G x (M.pt e ≫ a.act b) := by
    intro b e
    have ht := M.tan e
    have hh := a.hom b
    unfold IsTanAt at ht ⊢
    rw [Over.comp_left, ← Category.assoc, ht, ← Over.comp_left, MonObj.one_comp]
  choose A hA using fun (b : O) (e : W) => M.onto (M.pt e ≫ a.act b) (tan b e)
  have hadd : ∀ b e e', A b (e + e') = A b e + A b e' := by
    intro b e e'
    have hh := a.hom b
    apply M.inj
    rw [hA, M.add, M.add, hA, hA, MonObj.mul_comp]
  have hsmul : ∀ b (c : R) e, A b (c • e) = c • A b e := by
    intro b c e
    apply M.inj
    apply Over.OverMorphism.ext
    rw [hA, Over.comp_left, M.smul, M.smul, hA, Over.comp_left, Category.assoc]
  let L : O → Module.End R W := fun b =>
    { toFun := A b, map_add' := hadd b, map_smul' := fun c e => by simpa using hsmul b c e }
  have hL : ∀ b e, L b e = A b e := fun _ _ => rfl
  have hone : L 1 = 1 := by
    ext e
    apply M.inj
    rw [hL, hA, a.one, Category.comp_id]
    rfl
  have hmul : ∀ b b', L (b * b') = L b * L b' := by
    intro b b'
    ext e
    apply M.inj
    rw [Module.End.mul_apply, hL, hL, hL, hA, hA, hA, mul_comm, a.mul, Category.assoc]
  have haddL : ∀ b b', L (b + b') = L b + L b' := by
    intro b b'
    ext e
    apply M.inj
    rw [LinearMap.add_apply, hL, hL, hL, hA, M.add, hA, hA, a.add, MonObj.comp_mul]
  let ρ : O →+* Module.End R W := RingHom.mk' ⟨⟨L, hone⟩, hmul⟩ haddL
  exact ⟨ρ, fun b e => hA b e⟩

private theorem isActOf_of_pullback {S S' : Scheme} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {φ : G'.left ⟶ G.left} {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S'} {x' : Spec (CommRingCat.of R) ⟶ S}
    {W : Type} [AddCommGroup W] [Module R W] (M : LieModel G' x W) (N : LieModel G x' W)
    (hN : ∀ e, (N.pt e).left = (M.pt e).left ≫ φ) {O : Type} [CommRing O]
    (act' : O → (G' ⟶ G')) (act : O → (G ⟶ G))
    (hact : ∀ b, (act' b).left ≫ φ = φ ≫ (act b).left)
    (ρ : O →+* Module.End R W) (hM : M.IsActOf act' ρ) : N.IsActOf act ρ := by
  intro b e
  apply Over.OverMorphism.ext
  have h1 := hM b e
  rw [hN, h1, Over.comp_left, Over.comp_left, hN, Category.assoc, hact, Category.assoc]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module F W) (Mu : LieModel Xo.univ.t.G (under y) W) (Mz : LieModel Y.t.G (y ≫ Y.j) W) (ρ : 𝓞 E →+* Module.End F W), Mu.IsActOf Xo.univ.t.act.act ρ ∧ Mz.IsActOf Y.t.act.act ρ ∧ ∀ e, SameVec Y y (Mu.pt e) (Mz.pt e) := by
  intro E _ _ _ H D l Xo c O _ β Y F _ y
  obtain ⟨W, i1, i2, ⟨M0⟩⟩ := lieModel_exists _ Y.oF.t.G F y
  obtain ⟨ρ, hρ⟩ := exists_isActOf_geometry M0 Y.oF.t.act
  obtain ⟨Mu, hMu⟩ := exists_lieModel_pullback Y.m0.toSABMap.cart y (under y) rfl M0
  obtain ⟨Mz, hMz⟩ := exists_lieModel_pullback Y.m.cart y (y ≫ Y.j) rfl M0
  refine ⟨W, i1, i2, Mu, Mz, ρ, ?_, ?_, ?_⟩
  · exact isActOf_of_pullback M0 Mu hMu _ _ (fun b => Y.m0.toSABMap.act b) ρ hρ
  · exact isActOf_of_pullback M0 Mz hMz _ _ (fun b => Y.m.act b) ρ hρ
  · intro e
    unfold SameVec
    exact ⟨(M0.pt e).left, Over.w (M0.pt e), (hMu e).symm, (hMz e).symm⟩

end GlobalTheory.CompanionTheory.Ar.LieTransport
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.UniversalLieModelPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universal_lie_model_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (F : Type) [Field F] (y : Sp F ⟶ Xo.XF c), ∃ (W : Type) (_ : AddCommGroup W) (_ : Module F W) (Mu : LieModel Xo.univ.t.G (under y) W) (Mz : LieModel Y.t.G (y ≫ Y.j) W) (ρ : 𝓞 E →+* Module.End F W), Mu.IsActOf Xo.univ.t.act.act ρ ∧ Mz.IsActOf Y.t.act.act ρ ∧ ∀ e, SameVec Y y (Mu.pt e) (Mz.pt e) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieTransport.main | exact GlobalTheory.CompanionTheory.Ar.LieTransport.main | (intros; apply GlobalTheory.CompanionTheory.Ar.LieTransport.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsModuleStructure
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsModuleStructure
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction

open GroundTheory.Heights₂.Heights.Regular

theorem exists_eventually_int_eq_zero {X V J : Type*} [TopologicalSpace X] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [Fintype J] (v : X → J → V) (x₀ : X)
    (hv : ∀ i, ContinuousAt (fun x => v x i) x₀)
    (hind : ∀ r : J → ℝ, ∑ i, r i • v x₀ i = 0 → r = 0) :
    ∃ ε > (0 : ℝ), ∀ᶠ x in 𝓝 x₀, ∀ m : J → ℤ, ‖∑ i, (m i : ℝ) • v x i‖ < ε → m = 0 := by
  classical
  let T : (J → ℝ) →ₗ[ℝ] V := ∑ i, (LinearMap.proj i : (J → ℝ) →ₗ[ℝ] ℝ).smulRight (v x₀ i)
  have hT : ∀ r, T r = ∑ i, r i • v x₀ i := fun r => by simp [T, LinearMap.sum_apply]
  have hker : LinearMap.ker T = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro r hr
    exact hind r (by rw [← hT]; exact hr)
  obtain ⟨K, hK0, hK⟩ := T.exists_antilipschitzWith hker
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hb : ∀ r, ‖r‖ ≤ K * ‖T r‖ := fun r => by
    simpa [dist_zero_right] using hK.le_mul_dist r 0
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = Fintype.card J + 1 := ⟨_, rfl⟩
  have hN : 0 < N := by rw [hNdef]; positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 1 / (2 * K * N) := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  have hev : ∀ᶠ x in 𝓝 x₀, ∀ i, ‖v x i - v x₀ i‖ < δ := by
    refine eventually_all.2 fun i => ?_
    have := (Metric.tendsto_nhds.1 (hv i).tendsto) δ hδ
    simpa [dist_eq_norm] using this
  filter_upwards [hev] with x hx m hm
  obtain ⟨r, hr⟩ : ∃ r : J → ℝ, r = fun i => (m i : ℝ) := ⟨_, rfl⟩
  have hm' : ‖∑ i, r i • v x i‖ < 1 / (2 * K) := by rw [hr]; exact hm
  have hsplit : T r = ∑ i, r i • v x i - ∑ i, r i • (v x i - v x₀ i) := by
    rw [hT, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sub]; abel
  have herr : ‖∑ i, r i • (v x i - v x₀ i)‖ ≤ N * (‖r‖ * δ) := by
    calc ‖∑ i, r i • (v x i - v x₀ i)‖ ≤ ∑ i, ‖r i • (v x i - v x₀ i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : J, ‖r‖ * δ := Finset.sum_le_sum fun i _ => by
          rw [norm_smul]
          exact mul_le_mul (norm_le_pi_norm r i) (hx i).le (norm_nonneg _) (norm_nonneg _)
      _ = (Fintype.card J : ℝ) * (‖r‖ * δ) := by simp
      _ ≤ N * (‖r‖ * δ) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hNdef]; linarith
  have h1 : ‖r‖ ≤ K * (‖∑ i, r i • v x i‖ + N * (‖r‖ * δ)) := by
    refine (hb r).trans (mul_le_mul_of_nonneg_left ?_ hKpos.le)
    rw [hsplit]
    exact (norm_sub_le _ _).trans (by linarith)
  have h2 : K * (N * (‖r‖ * δ)) = ‖r‖ / 2 := by
    rw [hδdef]; field_simp
  have h3 : K * ‖∑ i, r i • v x i‖ < 1 / 2 := by
    have := mul_lt_mul_of_pos_left hm' hKpos
    have h4 : K * (1 / (2 * K)) = 1 / 2 := by field_simp
    linarith
  have h5 : ‖r‖ < 1 := by
    rw [mul_add, h2] at h1
    linarith
  funext i
  have h6 : |(m i : ℝ)| < 1 := by
    have := (norm_le_pi_norm r i).trans_lt h5
    rw [hr] at this
    simpa [Real.norm_eq_abs] using this
  have h7 : |m i| < 1 := by exact_mod_cast h6
  simpa using Int.abs_lt_one_iff.1 h7

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ)

theorem P_injective {w : Fin n → ℂ} (hw : w ∈ logCover L.a_le) : Function.Injective (L.P w) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  apply L.unimod.1
  rw [map_zero]
  refine LinearMap.ext fun y => ?_
  have h := L.im w hw x y
  rw [hx] at h
  simp at h
  exact_mod_cast h.symm

theorem real_indep {J : Type*} [Fintype J] (b : Module.Basis J ℤ Λ) {w : Fin n → ℂ}
    (hw : w ∈ logCover L.a_le) (r : J → ℝ) (h : ∑ i, r i • L.P w (b i) = 0) : r = 0 := by
  classical
  funext j
  obtain ⟨u, hu⟩ := L.unimod.2 (b.coord j)
  let ψ : (Fin g → ℂ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => (L.P w u ⬝ᵥ L.H (expCover a w) *ᵥ star v).im
      map_add' := fun v v' => by simp [star_add, mulVec_add, dotProduct_add]
      map_smul' := fun t v => by simp [star_smul, mulVec_smul, dotProduct_smul] }
  have h1 : ∀ i, ψ (L.P w (b i)) = if i = j then 1 else 0 := fun i => by
    have h2 := L.im w hw u (b i)
    change (L.P w u ⬝ᵥ L.H (expCover a w) *ᵥ star (L.P w (b i))).im = _
    rw [h2, hu]
    simp [Module.Basis.coord_apply, Finsupp.single_apply]
  have h2 := congrArg ψ h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, h1, map_zero, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h2
  simpa using h2

theorem continuousAt_P (x : Λ) {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le) :
    ContinuousAt (fun w => L.P w x) w₀ :=
  (L.hol x).continuousOn.continuousAt ((isOpen_logCover L.a_le).mem_nhds hw)

theorem continuousAt_apply (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1)) (x : Λ)
    {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le) :
    ContinuousAt (fun w => A (expCover a w) (L.P w x)) w₀ := by
  classical
  have hP := continuousAt_P L x hw
  have hexp : ContinuousAt (expCover (n := n) a) w₀ := (continuous_expCover a).continuousAt
  have hAe : ∀ v, ContinuousAt (fun w => A (expCover a w) v) w₀ := fun v =>
    ContinuousAt.comp (f := expCover a) (g := fun z => A z v)
      ((hA v).continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (expCover_mem_ball L.a_le hw))) hexp
  have h1 : (fun w => A (expCover a w) (L.P w x)) = fun w =>
      ∑ i, (L.P w x i) • A (expCover a w) (fun j => if i = j then 1 else 0) := by
    funext w
    exact LinearMap.pi_apply_eq_sum_univ _ _
  rw [h1]
  exact tendsto_finsetSum _ fun i _ =>
    (((continuous_apply i).continuousAt.comp hP).smul (hAe _))

theorem eventually_eq (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1))
    (hex : ∀ w ∈ logCover L.a_le, ∀ x, ∃ y, L.P w y = A (expCover a w) (L.P w x))
    (x y : Λ) {w₀ : Fin n → ℂ} (hw : w₀ ∈ logCover L.a_le)
    (h : L.P w₀ y = A (expCover a w₀) (L.P w₀ x)) :
    ∀ᶠ w in 𝓝 w₀, L.P w y = A (expCover a w) (L.P w x) := by
  haveI := L.free
  haveI := L.fin
  obtain ⟨b⟩ : Nonempty (Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℤ Λ) :=
    ⟨Module.Free.chooseBasis ℤ Λ⟩
  obtain ⟨ε, hε, hev⟩ := exists_eventually_int_eq_zero (fun w i => L.P w (b i)) w₀
    (fun i => continuousAt_P L (b i) hw) (real_indep L b hw)
  have hD : ContinuousAt (fun w => A (expCover a w) (L.P w x) - L.P w y) w₀ :=
    (continuousAt_apply L A hA x hw).sub (continuousAt_P L y hw)
  have hsmall : ∀ᶠ w in 𝓝 w₀, ‖A (expCover a w) (L.P w x) - L.P w y‖ < ε := by
    have h0 := (Metric.tendsto_nhds.1 hD.tendsto) ε hε
    simpa [h, dist_eq_norm] using h0
  filter_upwards [hev, hsmall, (isOpen_logCover L.a_le).mem_nhds hw] with w h1 h2 hwC
  obtain ⟨y', hy'⟩ := hex w hwC x
  have hk : L.P w (y' - y) = ∑ i, ((b.repr (y' - y) i : ℤ) : ℝ) • L.P w (b i) := by
    conv_lhs => rw [← b.sum_repr (y' - y)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul]
    exact (Int.cast_smul_eq_zsmul ℝ _ _).symm
  have hm := h1 (fun i => b.repr (y' - y) i) (by rw [← hk, map_sub, hy']; exact h2)
  have h0 : y' - y = 0 := b.repr.map_eq_zero_iff.1 (Finsupp.ext fun i => congrFun hm i)
  rw [← sub_eq_zero.1 h0, hy']

theorem eq_of_mem (A : (Fin n → ℂ) → Module.End ℂ (Fin g → ℂ))
    (hA : ∀ x, DifferentiableOn ℂ (fun z => A z x) (Metric.ball 0 1))
    (hex : ∀ w ∈ logCover L.a_le, ∀ x, ∃ y, L.P w y = A (expCover a w) (L.P w x))
    (x y : Λ) {w₀ w₁ : Fin n → ℂ} (h0 : w₀ ∈ logCover L.a_le) (h1 : w₁ ∈ logCover L.a_le)
    (h : L.P w₀ y = A (expCover a w₀) (L.P w₀ x)) :
    L.P w₁ y = A (expCover a w₁) (L.P w₁ x) := by
  classical
  choose φ hφ using fun w : logCover L.a_le => hex w.1 w.2 x
  have hlc : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro w
    have h2 := (continuous_subtype_val.continuousAt (x := w)).eventually
      (eventually_eq L A hA hex x (φ w) w.2 (hφ w))
    filter_upwards [h2] with w' hw'
    exact P_injective L w'.2 ((hφ w').trans hw'.symm)
  haveI : PreconnectedSpace (logCover L.a_le) :=
    Subtype.preconnectedSpace (convex_logCover L.a_le).isPreconnected
  have h2 := hlc.apply_eq_of_preconnectedSpace ⟨w₀, h0⟩ ⟨w₁, h1⟩
  have hy : φ ⟨w₀, h0⟩ = y := P_injective L h0 ((hφ ⟨w₀, h0⟩).trans h.symm)
  rw [← hy, h2]
  exact hφ ⟨w₁, h1⟩

theorem exists_module_of_period_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ))), (∀ c x, DifferentiableOn ℂ (fun z => B z c x) (Metric.ball 0 1)) → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ c x, ∃ y, L.P w y = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x)) → ∃ _ : Module (𝓞 E) Λ, ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ (c : 𝓞 E) x, L.P w (c • x) = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x) := by
  intro E _ _ _ n a g Λ _ L B hB hex
  obtain ⟨w₀, hw₀⟩ := logCover_nonempty L.a_le
  choose f hf using fun c x => hex w₀ hw₀ c x
  have key : ∀ w ∈ logCover L.a_le, ∀ c x, L.P w (f c x) = B (expCover a w) c (L.P w x) :=
    fun w hw c x => eq_of_mem L (fun z => B z c) (fun x => hB c x)
      (fun w hw x => hex w hw c x) x (f c x) hw₀ hw (hf c x)
  have inj := P_injective L hw₀
  have e1 : ∀ x, f 1 x = x := fun x => inj (by rw [hf]; simp)
  have e2 : ∀ c d x, f (c * d) x = f c (f d x) := fun c d x => inj (by
    rw [hf, hf, hf, map_mul, Module.End.mul_apply])
  have e3 : ∀ c, f c 0 = 0 := fun c => inj (by rw [hf]; simp)
  have e4 : ∀ c x y, f c (x + y) = f c x + f c y := fun c x y => inj (by
    rw [map_add (f := _), hf, hf, hf, map_add (f := _), map_add (f := _)])
  have e5 : ∀ c d x, f (c + d) x = f c x + f d x := fun c d x => inj (by
    rw [map_add (f := _), hf, hf, hf, map_add (f := _), LinearMap.add_apply])
  have e6 : ∀ x, f 0 x = 0 := fun x => inj (by rw [hf]; simp)
  exact ⟨{ smul := f, one_smul := e1, mul_smul := e2, smul_zero := e3, smul_add := e4,
           add_smul := e5, zero_smul := e6 }, key⟩

end GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsModuleStructureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_periods_module_structure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ))), (∀ c x, DifferentiableOn ℂ (fun z => B z c x) (Metric.ball 0 1)) → (∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ c x, ∃ y, L.P w y = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x)) → ∃ _ : Module (𝓞 E) Λ, ∀ w ∈ GroundTheory.Heights₂.Heights.Regular.logCover L.a_le, ∀ (c : 𝓞 E) x, L.P w (c • x) = B (GroundTheory.Heights₂.Heights.Regular.expCover a w) c (L.P w x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction.exists_module_of_period_action | exact GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction.exists_module_of_period_action | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PeriodAction.exists_module_of_period_action <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeIsoCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeIsoCompat
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open MonoidalCategory CartesianMonoidalCategory MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GMove

section Ring

variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem dualMap_algebraMap (f : R →+* S) :
    (dualMap f).comp (algebraMap R (DualNumber R)) = (algebraMap S (DualNumber S)).comp f := by
  ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_dualMap (f : R →+* S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (dualMap f) = f.comp (TrivSqZeroExt.fstHom R R R).toRingHom :=
  RingHom.ext fun x => by simp [dualMap]

theorem dualMap_comp (f : R →+* S) (g : S →+* T) : dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  ext x <;> simp [dualMap]

theorem specMap_comp (f : R →+* S) (g : S →+* T) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) = Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]; rfl

end Ring

section Scheme

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem specializes_of_iso (e : X' ≅ X) {a b : X'} (h : e.hom a ⤳ e.hom b) : a ⤳ b := by
  have := h.map e.inv.continuous
  simpa using this

theorem genMap_stalkMap_eq (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (g : X' ⟶ X) (q : Cpt ξ')
    (h : genPt (ξ' ≫ g) ⤳ g q.1) (s : X.presheaf.stalk (g q.1)) :
    genMap ξ' q ((g.stalkMap q.1).hom s) = genMap (ξ' ≫ g) ⟨g q.1, h⟩ s := by
  have e := Scheme.Hom.stalkSpecializes_stalkMap g _ _ q.2
  have e2 := congrArg (fun t => (t ≫ Scheme.stalkClosedPointTo ξ').hom s) e
  have e3 := Scheme.stalkClosedPointTo_comp ξ' g
  have e4 := congrArg (fun t => (X.presheaf.stalkSpecializes h ≫ t).hom s) e3
  exact e2.symm.trans e4.symm

theorem eta_comp {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (f : X' ⟶ X) (φ : G'.left ⟶ G.left)
    (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have hw := h.1.w
  let x₀ : Over.mk ((Over.mk (𝟙 X')).hom ≫ f) ⟶ G :=
    Over.homMk ((1 : Over.mk (𝟙 X') ⟶ G').left ≫ φ) (by
      rw [Category.assoc, hw, ← Category.assoc, Over.w]; simp)
  have hm := h.2 (Over.mk (𝟙 X')) 1 1 x₀ x₀ rfl rfl
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hm, _root_.mul_one]
    rfl
  have h1 : x₀ = 1 := by simpa using hx
  have h2 := congrArg (fun u => u.left) h1
  simpa [x₀, Hom.one_def] using h2

end Scheme

section Move

variable {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]

theorem valAt_up (e : X' ≅ X) {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] (φ : G'.left ≅ G.left)
    (hw : φ.hom ≫ G.hom = G'.hom ≫ e.hom) (hη : η[G'].left ≫ φ.hom = e.hom ≫ η[G].left)
    {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} (M : LieModel G ξ V) (M' : LieModel G' ξ' V) (hξ : ξ' ≫ e.hom = ξ)
    (hpt : ∀ v, (M'.pt v).left ≫ φ.hom = (M.pt v).left)
    {z : Sp ℂ ⟶ X'} {z₀ : Sp ℂ ⟶ X} (hz : z ≫ e.hom = z₀) {b : V} {w : epsAt z₀ ⟶ G} {w' : epsAt z ⟶ G'}
    (hww : w'.left ≫ φ.hom = w.left) : M.ValAt z₀ b w → M'.ValAt z b w' := by
  subst hξ hz
  rintro ⟨h, v, ⟨hvt, hve⟩, hvw⟩
  have h' : genPt ξ' ⤳ centre z := specializes_of_iso e h
  change e.hom (genPt ξ') ⤳ e.hom (centre z) at h
  change epsAt (R := X.presheaf.stalk (e.hom (centre z))) (X.fromSpecStalk (e.hom (centre z))) ⟶ G at v
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
      (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
      (1 : Over.mk (X.fromSpecStalk (e.hom (centre z))) ⟶ G).left at hvt
  change (M.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) ≫
      v.left at hve
  change w.left = Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) ≫ v.left at hvw
  have hφ : φ.inv ≫ G'.hom = G.hom ≫ e.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : e.hom ≫ η[G].left ≫ φ.inv = η[G'].left := by
    rw [← Category.assoc, ← hη, Category.assoc, φ.hom_inv_id, Category.comp_id]
  have hv : v.left ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
      (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z)) := Over.w v
  have hσ : Spec.map (e.hom.stalkMap (centre z)) ≫ X.fromSpecStalk (e.hom (centre z)) =
      X'.fromSpecStalk (centre z) ≫ e.hom := Scheme.SpecMap_stalkMap_fromSpecStalk e.hom
  have k1 : Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ Spec.map (e.hom.stalkMap (centre z)) := by
    rw [specMap_comp, dualMap_algebraMap, ← specMap_comp]
    rfl
  let v' : epsAt (R := X'.presheaf.stalk (centre z)) (X'.fromSpecStalk (centre z)) ⟶ G' :=
    Over.homMk (Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv) (by
      show _ ≫ (v.left ≫ φ.inv) ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (centre z))
        (DualNumber (X'.presheaf.stalk (centre z))))) ≫ X'.fromSpecStalk (centre z)
      rw [Category.assoc, hφ, reassoc_of% hv]
      show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk (e.hom (centre z)))
        (DualNumber (X.presheaf.stalk (e.hom (centre z)))))) ≫ X.fromSpecStalk (e.hom (centre z))) ≫ e.inv = _
      rw [← Category.assoc, ← Category.assoc]
      erw [k1]
      erw [Category.assoc, Category.assoc, reassoc_of% hσ, e.hom_inv_id, Category.comp_id]
      rfl)
  have hv' : v'.left = Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) ≫ v.left ≫ φ.inv := rfl
  refine ⟨h', v', ⟨?_, ?_⟩, ?_⟩
  · have e1 : (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left = X'.fromSpecStalk (centre z) ≫ η[G'].left := by
      simp [Hom.one_def]
    have e2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))).toRingHom) ≫ v.left =
        X.fromSpecStalk (e.hom (centre z)) ≫ η[G].left := by
      rw [hvt]
      simp [Hom.one_def]
    have k2 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (e.hom.stalkMap (centre z)) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom
        (X.presheaf.stalk (e.hom (centre z))) (X.presheaf.stalk (e.hom (centre z)))
        (X.presheaf.stalk (e.hom (centre z)))).toRingHom) := by
      rw [specMap_comp, fstHom_dualMap, ← specMap_comp]
      rfl
    show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom (X'.presheaf.stalk (centre z))
        (X'.presheaf.stalk (centre z)) (X'.presheaf.stalk (centre z))).toRingHom) ≫ v'.left =
        (1 : Over.mk (X'.fromSpecStalk (centre z)) ⟶ G').left
    rw [hv', e1, ← hη', ← reassoc_of% hσ, ← reassoc_of% e2, reassoc_of% k2]
    rfl
  · have k3 : Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩))) := by
      have hg : (genMap ξ' ⟨centre z, h'⟩).comp (e.hom.stalkMap (centre z)).hom =
          genMap (ξ' ≫ e.hom) ⟨e.hom (centre z), h⟩ :=
        RingHom.ext (genMap_stalkMap_eq ξ' e.hom ⟨centre z, h'⟩ h)
      rw [specMap_comp, ← dualMap_comp, hg]
    show (M'.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (genMap ξ' ⟨centre z, h'⟩))) ≫ v'.left
    rw [(Iso.eq_comp_inv φ).2 (hpt b), hve, hv', reassoc_of% k3]
    exact Category.assoc _ _ _
  · have k4 : Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo z).hom)) ≫
        Spec.map (CommRingCat.ofHom (dualMap (e.hom.stalkMap (centre z)).hom)) =
        Spec.map (CommRingCat.ofHom (dualMap (Scheme.stalkClosedPointTo (z ≫ e.hom)).hom)) := by
      refine (specMap_comp (dualMap (e.hom.stalkMap (centre z)).hom) (dualMap (Scheme.stalkClosedPointTo z).hom)).trans ?_
      rw [Scheme.stalkClosedPointTo_comp]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (dualMap_comp _ _).symm
    rw [(Iso.eq_comp_inv φ).2 hww, hvw, hv', ← k4]
    erw [Category.assoc, Category.assoc]

end Move

theorem gramAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X)
    (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (k : SABMap t' t e.hom)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V),
    ξ' ≫ e.hom = ξ → (∀ v, (M'.pt v).left ≫ k.φ = (M.pt v).left) →
    ∀ (z : Sp ℂ ⟶ X') (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ),
      M'.GramAt t'.PP.L z b Γ ↔ M.GramAt t.PP.L (z ≫ e.hom) b Γ := by
  intro E _ _ _ H X X' e Ω _ ξ ξ' t t' k V _ _ M M' hξ hpt z r b Γ
  haveI : IsIso k.φ := k.cart.1.isIso_fst_of_isIso
  let φ : t'.G.left ≅ t.G.left := asIso k.φ
  have hw : φ.hom ≫ t.G.hom = t'.G.hom ≫ e.hom := k.cart.1.w
  have hη : η[t'.G].left ≫ φ.hom = e.hom ≫ η[t.G].left := eta_comp e.hom k.φ k.cart
  have hw' : φ.symm.hom ≫ t'.G.hom = t.G.hom ≫ e.symm.hom := by
    show φ.inv ≫ _ = _ ≫ e.inv
    rw [Iso.inv_comp_eq, ← Category.assoc, hw, Category.assoc, e.hom_inv_id, Category.comp_id]
  have hη' : η[t.G].left ≫ φ.symm.hom = e.symm.hom ≫ η[t'.G].left := by
    show _ ≫ φ.inv = e.inv ≫ _
    rw [Iso.eq_inv_comp, ← reassoc_of% hη, φ.hom_inv_id, Category.comp_id]
  have hpt' : ∀ v, (M.pt v).left ≫ φ.symm.hom = (M'.pt v).left := fun v => by
    show _ ≫ φ.inv = _
    rw [← hpt v, Category.assoc]
    erw [φ.hom_inv_id]
    exact Category.comp_id _
  have hξ' : ξ ≫ e.symm.hom = ξ' := by rw [← hξ]; simp
  constructor
  · rintro ⟨v', hval, hip⟩
    let v : Fin r → (epsAt (z ≫ e.hom) ⟶ t.G) := fun i => Over.homMk ((v' i).left ≫ k.φ) (by
      have h1 := Over.w (v' i)
      rw [Category.assoc, k.cart.1.w, ← Category.assoc, h1]
      simp [epsAt])
    refine ⟨v, fun i => ?_, fun p q => ?_⟩
    · refine valAt_up e.symm φ.symm hw' hη' M' M hξ' hpt' (z := z ≫ e.hom) (z₀ := z) (by simp) ?_ (hval i)
      show ((v' i).left ≫ k.φ) ≫ φ.inv = _
      simp [φ]
    · exact (GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) rfl rfl).1 (hip p q)
  · rintro ⟨v, hval, hip⟩
    let v' : Fin r → (epsAt z ⟶ t'.G) := fun i => Over.homMk ((v i).left ≫ φ.inv) (by
      have h1 := Over.w (v i)
      rw [Category.assoc, ← Iso.symm_hom, hw', ← Category.assoc, h1]
      simp [epsAt])
    have hv' : ∀ i, (v' i).left ≫ k.φ = (v i).left := fun i => by
      show ((v i).left ≫ φ.inv) ≫ φ.hom = _
      simp
    refine ⟨v', fun i => ?_, fun p q => ?_⟩
    · exact valAt_up e φ hw hη M M' hξ hpt (z := z) (z₀ := z ≫ e.hom) rfl (hv' i) (hval i)
    · exact (GlobalTheory.T.hodge_inner_product_pullback_iff E H X X' t t' e.hom k z (v' p) (v' q) (v p) (v q) (Γ p q) (hv' p) (hv' q)).2 (hip p q)

end GlobalTheory.CompanionTheory.Ar.GMove
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeIsoCompatStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_base_change_iso_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (e : X' ≅ X)
    (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω ⟶ X') (t : SAB H X) (t' : SAB H X') (k : SABMap t' t e.hom)
    (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V),
    ξ' ≫ e.hom = ξ → (∀ v, (M'.pt v).left ≫ k.φ = (M.pt v).left) →
    ∀ (z : Sp ℂ ⟶ X') (r : ℕ) (b : Fin r → V) (Γ : Matrix (Fin r) (Fin r) ℂ),
      M'.GramAt t'.PP.L z b Γ ↔ M.GramAt t.PP.L (z ≫ e.hom) b Γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move | exact GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move | (intros; apply GlobalTheory.CompanionTheory.Ar.GMove.gramAt_move <;> assumption)
end
end
