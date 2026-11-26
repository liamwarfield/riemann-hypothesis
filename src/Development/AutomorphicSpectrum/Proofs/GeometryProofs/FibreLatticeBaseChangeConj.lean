module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarised

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove

def chartPullComp {X Y Z : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (h : Z ⟶ Y) :
    ChartPull (L.pull (h ≫ F)) (L.pull F) h where
  idx J := J
  le J y hy := mem_pull.2 (by simpa using mem_pull.1 hy)
  g y i j hi hj := by
    have hi' : h y ∈ (L.pull F).U i := mem_pull.2 (by simpa using mem_pull.1 hi)
    have hj' : h y ∈ (L.pull F).U j := mem_pull.2 (by simpa using mem_pull.1 hj)
    refine (gm_pull_g L (h ≫ F) (𝟙 Z) y i j hi hj).trans ?_
    refine Eq.trans ?_ (gm_pull_g L F h y i j hi' hj').symm
    rw [Category.id_comp]

theorem lbIso_pull {X Y Z : Scheme.{0}} {L' : LB Y} {L : LB X} {F : Y ⟶ X} (H : LBIso L' (L.pull F)) (h : Z ⟶ Y) :
    LBIso (L'.pull h) (L.pull (h ≫ F)) :=
  LBIso.chartPull (chartPullPull L' h) (chartPullComp L F h) H

theorem fibreLat_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (z : Sp ℂ ⟶ X'), (Nonempty (SABMap t' t f) → (FibreLat t' z R ↔ FibreLat t (z ≫ f) R)) ∧ ((∀ x, R'.P x = star (R.P x)) → R'.Hm = R.Hm.map (starRingEnd ℂ) → (∀ a x, R'.B a x = star (R.B a (star x))) → FibreLat t' z R → FibreLat t' (spMap (starRingEnd ℂ) ≫ z) R') := by
  intro E _ _ _ H X X' t t' f g Λ _ _ R R' z
  refine ⟨fun ⟨m⟩ => ⟨?_, ?_⟩, fun hP hH hB => ?_⟩
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, -⟩
    obtain ⟨w, hw, -⟩ := m.lin
    obtain ⟨v, hv⟩ := lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw⟩ φ
    have h₁ := pull_isLB t'.PP.isLB φ
    have h₂ := pull_isLB t.PP.isLB (φ ≫ m.cm.F)
    refine ⟨A, inferInstance, φ ≫ m.cm.F, GlobalTheory.ArchMetricCompare.carry u h₁ h₂ hv, χ, hpb.comp m.cart,
      GlobalTheory.ArchMetricCompare.carry_isAH h₁ h₂ hv hAH, fun a p => ?_, hinj, hmem, fun i => i.elim⟩
    show (u.ex (R.B a p)).left ≫ φ ≫ m.cm.F = (u.ex p).left ≫ (φ ≫ m.cm.F) ≫ (t.act.act a).left
    rw [← Category.assoc, hact a p, Category.assoc, Category.assoc, Category.assoc, m.act a]
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, -⟩
    have hp := m.cart.1
    obtain ⟨F, rfl, hw⟩ : ∃ F : A.left ⟶ t'.G.left, F ≫ m.cm.F = φ ∧ F ≫ t'.G.hom = A.hom ≫ z :=
      ⟨hp.lift φ (A.hom ≫ z) (by rw [hpb.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
    obtain ⟨w, hw', -⟩ := m.lin
    obtain ⟨v, hv⟩ := (lbIso_pull (L' := t'.PP.L) (L := t.PP.L) ⟨w, hw'⟩ F).symm
    have h₁ := pull_isLB t'.PP.isLB F
    have h₂ := pull_isLB t.PP.isLB (F ≫ m.cm.F)
    refine ⟨A, inferInstance, F, GlobalTheory.ArchMetricCompare.carry u h₂ h₁ hv, χ, m.cart.cancel hpb hw,
      GlobalTheory.ArchMetricCompare.carry_isAH h₂ h₁ hv hAH, fun a p => ?_, hinj, hmem, fun i => i.elim⟩
    show (u.ex (R.B a p)).left ≫ F = (u.ex p).left ≫ F ≫ (t'.act.act a).left
    apply hp.hom_ext
    · have e := hact a p
      simp only [Category.assoc] at e ⊢
      rw [m.act a]
      exact e
    · simp only [Category.assoc]
      rw [Over.w (t'.act.act a), hw, ← Category.assoc, ← Category.assoc, Over.w (u.ex _), Over.w (u.ex _)]
  · rintro ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, -⟩
    have h := isGrpPullback_pullback A (spMap (starRingEnd ℂ))
    refine ⟨(Over.pullback (spMap (starRingEnd ℂ))).obj A, inferInstance, pullback.fst _ _ ≫ φ,
      GlobalTheory.ArchMetricCompare.cjUnif h u, fun l => star (χ ⟨star l.1, l.2⟩), h.comp hpb, ?_, fun a p => ?_, ?_,
      fun p => ?_, fun i => i.elim⟩
    · rw [hH]
      exact GlobalTheory.ArchMetricCompare.cj_isAH h u hAH
    · show (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star (R'.B a p)))).left ≫ pullback.fst _ _ ≫ φ =
        (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star p))).left ≫ (pullback.fst _ _ ≫ φ) ≫ (t'.act.act a).left
      rw [hB a p, star_star, GlobalTheory.ArchMetricCompare.cjPt_comp' h, Category.assoc, ← Category.assoc _ φ,
        ← Category.assoc _ (pullback.fst _ _ ≫ φ), GlobalTheory.ArchMetricCompare.cjPt_comp', hact a (star p)]
      simp only [Category.assoc]
    · intro x y e
      rw [hP, hP] at e
      exact hinj (star_injective e)
    · show star p ∈ u.Λ ↔ _
      rw [hmem]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨x, by rw [hP, hx, star_star]⟩
      · rintro ⟨x, rfl⟩
        exact ⟨x, by rw [hP, star_star]⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_lattice_base_change_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (z : Sp ℂ ⟶ X'), (Nonempty (SABMap t' t f) → (FibreLat t' z R ↔ FibreLat t (z ≫ f) R)) ∧ ((∀ x, R'.P x = star (R.P x)) → R'.Hm = R.Hm.map (starRingEnd ℂ) → (∀ a x, R'.B a x = star (R.B a (star x))) → FibreLat t' z R → FibreLat t' (spMap (starRingEnd ℂ) ≫ z) R') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move | exact GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FibreMove.fibreLat_move <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowFnsOfAbelianGeneric
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.BasicOpenEqBotOfField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace PositivityTheory.HtPt.Cf

theorem basicOpen_eq_bot_of_field {K : Type} [Field K] {Y : Scheme.{0}} (π : Y ⟶ Sp K) [UniversallyClosed π]
    [ConnectedSpace Y] (f : Γ(Y, ⊤)) (y₀ : Y) (h₀ : y₀ ∉ Y.basicOpen f) : Y.basicOpen f = ⊥ := by
  let φ : K →+* Γ(Y, ⊤) := π.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hφ : φ.IsIntegral := RingHom.IsIntegral.trans _ _
    (RingHom.isIntegral_of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective)
    (isIntegral_appTop_of_universallyClosed π)
  obtain ⟨p, hp, hpf⟩ := hφ f
  obtain ⟨q, hq, hn⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  have hc : q.coeff 0 ≠ 0 := fun h => hn (by simpa using Polynomial.X_dvd_iff.2 h)
  let g := Polynomial.eval₂ φ f q
  have h1 : f ^ p.rootMultiplicity 0 * g = 0 := by
    rw [hq, Polynomial.eval₂_mul, Polynomial.eval₂_pow] at hpf
    simpa using hpf
  have h2 : g = f * Polynomial.eval₂ φ f q.divX + φ (q.coeff 0) := by
    show Polynomial.eval₂ φ f q = _
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
  have key : ∀ y : Y, y ∉ Y.basicOpen f ↔ y ∈ Y.basicOpen g := fun y => by
    rw [← Y.evaluation_eq_zero_iff_notMem_basicOpen (U := ⊤) y trivial,
      ← Y.evaluation_ne_zero_iff_mem_basicOpen (U := ⊤) y trivial]
    let v := (Y.evaluation ⊤ y trivial).hom
    show v f = 0 ↔ v g ≠ 0
    constructor
    · intro h
      rw [h2, map_add (f := _), map_mul, h, zero_mul, zero_add]
      exact (map_ne_zero (v.comp φ)).2 hc
    · intro h
      have := congrArg v h1
      rw [map_mul, map_pow, map_zero] at this
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.1 this).resolve_right h)
  have hcl : IsClopen (Y.basicOpen f : Set Y) := by
    refine ⟨⟨?_⟩, (Y.basicOpen f).isOpen⟩
    have : (Y.basicOpen f : Set Y)ᶜ = Y.basicOpen g := Set.ext key
    rw [this]; exact (Y.basicOpen g).isOpen
  rcases isClopen_iff.1 hcl with h | h
  · exact TopologicalSpace.Opens.ext h
  · exact absurd (show y₀ ∈ (Y.basicOpen f : Set Y) from h ▸ trivial) h₀

theorem geomReduced_of_smooth {X S : Scheme.{0}} (π : X ⟶ S) [Smooth π] : GeometricallyReduced π :=
  ⟨fun K _ y Z fst snd h => by
    have : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h ‹_›
    exact isReduced_of_smooth snd⟩

theorem exists_generic {S : Scheme.{0}} (s : S) : ∃ z : S, z ⤳ s ∧ ∀ z' : S, z' ⤳ z → z' = z := by
  have hi := isIrreducible_irreducibleComponent (x := s)
  have hg := hi.isGenericPoint_genericPoint isClosed_irreducibleComponent
  refine ⟨_, hg.specializes mem_irreducibleComponent, fun z' hz => ?_⟩
  have hsub : irreducibleComponent s ⊆ closure {z'} := by
    rw [← hg.def]
    exact closure_minimal (Set.singleton_subset_iff.2 hz.mem_closure) isClosed_closure
  have he : closure {z'} = irreducibleComponent s :=
    eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub
  exact (IsGenericPoint.eq (show IsGenericPoint z' _ from he) hg)

theorem bijective_of_generic {X S : Scheme.{0}} (π : X ⟶ S) (e : S ⟶ X) (he : e ≫ π = 𝟙 S) [Smooth π]
    [GeometricallyConnected π] [IsReduced S] [IsLocallyNoetherian S]
    (h : ∀ z : S, (∀ z' : S, z' ⤳ z → z' = z) →
      ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ S), z ∈ Set.range t ∧ IsProper (pullback.snd π t)) :
    Function.Bijective π.appTop.hom := by
  have hret : ∀ a, e.appTop (π.appTop a) = a := fun a => by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he, Scheme.Hom.id_appTop]; rfl
  refine ⟨Function.LeftInverse.injective hret, fun f => ⟨e.appTop f, ?_⟩⟩
  have := geomReduced_of_smooth π
  have : IsReduced X := GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian π
  symm
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
  set f' := f - π.appTop.hom (e.appTop f) with hf'
  have h0 : e.appTop f' = 0 := by
    rw [hf', map_sub]; exact sub_eq_zero.2 (hret _).symm
  have hout : ∀ s, e s ∉ X.basicOpen f' := fun s hs => by
    have : s ∈ e ⁻¹ᵁ X.basicOpen f' := hs
    rw [Scheme.preimage_basicOpen_top, h0, Scheme.basicOpen_zero] at this
    exact this
  by_contra hne
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hne
  obtain ⟨z, hz, hgen⟩ := exists_generic (π x)
  obtain ⟨x', hx', hxz⟩ : z ∈ π '' (X.basicOpen f' : Set X) :=
    hz.mem_open (π.isOpenMap _ (X.basicOpen f').isOpen) ⟨x, hx, rfl⟩
  obtain ⟨K, _, t, ⟨w, hw⟩, hp⟩ := h z hgen
  have : ConnectedSpace ↥(pullback π t) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback π t)
  obtain ⟨y, hy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := t) x' w (hxz.trans hw.symm)
  obtain ⟨y₀, hy₀, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := t) (e z) w
    (((Scheme.Hom.comp_apply e π z).symm.trans (by rw [he]; rfl)).trans hw.symm)
  have hb := basicOpen_eq_bot_of_field (pullback.snd π t) ((pullback.fst π t).appTop f') y₀ (by
    rw [← Scheme.preimage_basicOpen_top]
    show pullback.fst π t y₀ ∉ X.basicOpen f'
    rw [hy₀]; exact hout z)
  have : y ∈ pullback.fst π t ⁻¹ᵁ X.basicOpen f' := by
    show pullback.fst π t y ∈ X.basicOpen f'
    rw [hy]; exact hx'
  rw [Scheme.preimage_basicOpen_top, hb] at this
  exact this

theorem pow_smooth_conn {S : Scheme.{0}} (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom] :
    ∀ n : ℕ, Smooth (Out.powObj G n).hom ∧ GeometricallyConnected (Out.powObj G n).hom := by
  intro n
  induction n with
  | zero =>
    exact ⟨inferInstanceAs (Smooth (𝟙 S)), ⟨fun K _ y Z fst snd h => by
      have : IsIso snd := h.isIso_snd_of_isIso (f := 𝟙 S)
      have : ConnectedSpace (Spec (CommRingCat.of K)) := inferInstanceAs (ConnectedSpace (PrimeSpectrum K))
      exact snd.homeomorph.connectedSpace_iff.2 this⟩⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [show Out.powObj G (n + 1) = G ⊗ Out.powObj G n from rfl, Over.tensorObj_hom, pullback.condition]
    exact ⟨inferInstance, GeometricallyConnected.comp _ _⟩

theorem pow_proper {S : Scheme.{0}} (G : Over S) [IsProper G.hom] : ∀ n : ℕ, IsProper (Out.powObj G n).hom
  | 0 => inferInstanceAs (IsProper (𝟙 S))
  | n + 1 => by
    have := pow_proper G n
    rw [show Out.powObj G (n + 1) = G ⊗ Out.powObj G n from rfl, Over.tensorObj_hom, pullback.condition]
    infer_instance

theorem pow_fns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsReduced X0 → IsLocallyNoetherian X0 → (∀ z : X0, (∀ z' : X0, z' ⤳ z → z' = z) → z ∈ abLocus t.G) → PowFns t := by
  intro E _ _ _ H X0 t _ _ h n
  have := t.semi.smooth
  have := t.semi.geomConnected
  obtain ⟨h1, h2⟩ := pow_smooth_conn t.G n
  refine bijective_of_generic (Out.powObj t.G n).hom (η[Out.powObj t.G n]).left (Over.w (η[Out.powObj t.G n]))
    fun z hz => ?_
  let K := AlgebraicClosure (X0.residueField z)
  let x : Sp K ⟶ X0 := spMap (algebraMap (X0.residueField z) K) ≫ X0.fromSpecResidueField z
  have hx : z ∈ Set.range x := ⟨IsLocalRing.closedPoint K, Scheme.fromSpecResidueField_apply z _⟩
  refine ⟨K, inferInstance, x, hx, ?_⟩
  have : IsProper ((Over.pullback x).obj t.G).hom := h z hz K x hx
  have := pow_proper ((Over.pullback x).obj t.G) n
  let e := GlobalFunctionsDvrPowers.pullPowIso x t.G n
  have : IsIso e.hom.left := isIso_inv_left e.symm
  show IsProper ((Over.pullback x).obj (Out.powObj t.G n)).hom
  rw [← Over.w e.hom]
  infer_instance

end PositivityTheory.HtPt.Cf
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowFnsOfAbelianGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.PowFn

theorem powFns_of_generic_abelian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsReduced X0 → IsLocallyNoetherian X0 → (∀ z : X0, (∀ z' : X0, z' ⤳ z → z' = z) → z ∈ abLocus t.G) → PowFns t :=
  @PositivityTheory.HtPt.Cf.pow_fns

end GlobalTheory.CompanionTheory.Ar.PowFn
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PowFnsOfAbelianGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powFns_of_abelian_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsReduced X0 → IsLocallyNoetherian X0 → (∀ z : X0, (∀ z' : X0, z' ⤳ z → z' = z) → z ∈ abLocus t.G) → PowFns t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PowFn.powFns_of_generic_abelian | exact GlobalTheory.CompanionTheory.Ar.PowFn.powFns_of_generic_abelian | (intros; apply GlobalTheory.CompanionTheory.Ar.PowFn.powFns_of_generic_abelian <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationLatticeBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationLatticeBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

open GlobalTheory.CompanionTheory.Ar.LieTangent GlobalTheory.CompanionTheory.Ar.LieVB

section Frame

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type} [AddCommGroup V]
  [Module Ω V] {K : Type} [Field K]

theorem valAt_of_isDiffOf {M : LieModel G ξ V} {z : Sp K ⟶ X} (f : G ⟶ G) [IsMonHom f] (A : V →ₗ[Ω] V)
    (hf : M.IsDiffOf f A) {e : V} {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  obtain ⟨hs, v, hv, hw⟩ := h
  refine ⟨hs, v ≫ f, ⟨?_, ?_⟩, ?_⟩
  · change _ ≫ (v ≫ f).left = _
    rw [Over.comp_left, ← Category.assoc, hv.1]
    exact congrArg Over.Hom.left (one_comp f)
  · change (M.pt (A e)).left = _
    rw [hf e, Over.comp_left, hv.2, Over.comp_left, Category.assoc]
  · change (w ≫ f).left = _
    rw [Over.comp_left, hw, Over.comp_left, Category.assoc]

theorem exists_model_of_frame [IsCommMonObj G] [Smooth G.hom] (hξ : IsCptGen ξ) (M : LieModel G ξ V) (z : Sp K ⟶ X)
    (h : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h⟩ →+* K) (hψ : ∀ a : regAt ξ ⟨_, h⟩, ValAt ξ z (a : Ω) (ψ a)) {g : ℕ}
    (ℓ : Fin g → V) (hℓ : M.lat.IsFrameAt ℓ ⟨_, h⟩) :
    ∃ MY : LieModel G z (Fin g → K), ∀ x : Fin g → regAt ξ ⟨_, h⟩,
      M.ValAt z (comb ℓ x) (MY.pt fun i => ψ (x i)) := by
  obtain ⟨F, _, _, ⟨MF⟩⟩ := lieModel_exists X G K z
  obtain ⟨ev, hev, hsm, hsp⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ V M K z h F MF hξ inferInstance
  have hmem : ∀ i, ℓ i ∈ M.lat ⟨_, h⟩ := fun i => by
    rw [hℓ.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  let u : Fin g → F := fun i => ev ⟨ℓ i, hmem i⟩
  have hcomb : ∀ x : Fin g → regAt ξ ⟨_, h⟩, comb ℓ x ∈ M.lat ⟨_, h⟩ := fun x =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ (x i) (hmem i)
  have hevc : ∀ x : Fin g → regAt ξ ⟨_, h⟩, ev ⟨comb ℓ x, hcomb x⟩ = ∑ i, ψ (x i) • u i := by
    intro x
    have e1 : (⟨comb ℓ x, hcomb x⟩ : M.lat ⟨_, h⟩) = ∑ i, x i • (⟨ℓ i, hmem i⟩ : M.lat ⟨_, h⟩) := by
      apply Subtype.ext
      simp [comb]
      rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    exact Finset.sum_congr rfl fun i _ => hsm (x i) (ψ (x i)) _ (hψ (x i))
  have hle : ⊤ ≤ Submodule.span K (Set.range u) := by
    have hr : Set.range ev ⊆ (Submodule.span K (Set.range u) : Set F) := by
      rintro _ ⟨⟨e, he⟩, rfl⟩
      have he' := he
      rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at he'
      obtain ⟨x, rfl⟩ := he'
      have e2 : (∑ i, x i • ℓ i) = comb ℓ x := rfl
      simp only [e2]
      rw [hevc x]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    rw [← hsp]
    exact Submodule.span_le.2 hr
  have hcard : Fintype.card (Fin g) = Module.finrank K F := by
    obtain ⟨_, hU, b', hb'sp, hb'⟩ := (lieLat_isVB_of_smooth X Ω ξ G V M hξ inferInstance).1 ⟨_, h⟩ trivial
    have hfr := hb' ⟨_, h⟩ trivial hU
    have htop : Submodule.span Ω (Set.range ℓ) = ⊤ := by
      rw [eq_top_iff, ← hb'sp, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h3 : b' i ∈ M.lat ⟨_, h⟩ := by
        rw [hfr.2]
        exact Submodule.subset_span ⟨i, rfl⟩
      rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at h3
      obtain ⟨x, hx⟩ := h3
      rw [← hx]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hg : Module.finrank Ω V = g := by
      rw [← finrank_top, ← htop, finrank_span_eq_card hℓ.1, Fintype.card_fin]
    obtain ⟨R', _, x, hx, F', _, _, MR, n, b, hp⟩ := exists_chart G (centre z)
    have hgen : genPt ξ ∈ x.opensRange := h.mem_open x.opensRange.isOpen hp
    obtain ⟨φ, hφ⟩ := exists_lift x ξ hgen
    obtain ⟨a, ha⟩ := exists_lift x z hp
    obtain ⟨β, B, -, -⟩ := basis_tr a x z ha MR MF b
    obtain ⟨c, hli, hsp', -⟩ := frame_of_basis x MR b ξ M φ hφ
    have hn : n = Module.finrank Ω V := by
      rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp'.ge), Fintype.card_fin]
    rw [Module.finrank_eq_card_basis B, Fintype.card_fin, Fintype.card_fin]
    omega
  let bb : Module.Basis (Fin g) K F := basisOfTopLeSpanOfCardEqFinrank u hle hcard
  refine ⟨lieModelOfEquiv MF bb.equivFun.symm, fun x => ?_⟩
  have e3 : bb.equivFun.symm (fun i => ψ (x i)) = ev ⟨comb ℓ x, hcomb x⟩ := by
    rw [hevc, Module.Basis.equivFun_symm_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [bb]
  change M.ValAt z (comb ℓ x) (MF.pt (bb.equivFun.symm fun i => ψ (x i)))
  rw [e3]
  exact (hev _ _).2 ⟨hcomb x, rfl⟩

theorem isActOf_of_frame {E : Type} [Field E] [NumberField E] (hξ : IsCptGen ξ) {M : LieModel G ξ V} {z : Sp K ⟶ X}
    {h : genPt ξ ⤳ centre z} {ψ : regAt ξ ⟨_, h⟩ →+* K} {g : ℕ} {ℓ : Fin g → V}
    (hℓ : M.lat.IsFrameAt ℓ ⟨_, h⟩) (act : OAct (𝓞 E) G) {ρ : 𝓞 E →+* Module.End Ω V}
    (hact : M.IsActOf act.act ρ) {ρK : 𝓞 E →+* Module.End K (Fin g → K)} (hT : Tied ℓ ψ ρ ρK)
    {MY : LieModel G z (Fin g → K)}
    (hY : ∀ x : Fin g → regAt ξ ⟨_, h⟩, M.ValAt z (comb ℓ x) (MY.pt fun i => ψ (x i))) :
    MY.IsActOf act.act ρK := by
  obtain ⟨ρ', hρ', -⟩ := lieModel_exists_unique_act _ G K z _ MY (𝓞 E) act.act act.hom act.one act.mul act.add
  suffices hq : ρ' = ρK from hq ▸ hρ'
  refine RingHom.ext fun a => (Pi.basisFun K (Fin g)).ext fun i => ?_
  let x : Fin g → regAt ξ ⟨_, h⟩ := Pi.single i 1
  have hx : (fun j => ψ (x j)) = Pi.basisFun K (Fin g) i := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [x]
    · simp [x, hj]
  have hmem : ρ a (comb ℓ x) ∈ M.lat ⟨_, h⟩ := by
    refine GlobalTheory.T.lie_lattice_stable_under_action X Ω ξ G V M (𝓞 E) act ρ hact ⟨_, h⟩ a _ ?_
    rw [hℓ.2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  rw [hℓ.2, Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨x', hx'⟩ := hmem
  have hc : comb ℓ x' = ρ a (comb ℓ x) := hx'
  have := act.hom a
  have h1 : M.ValAt z (ρ a (comb ℓ x)) (MY.pt (fun j => ψ (x j)) ≫ act.act a) :=
    valAt_of_isDiffOf (act.act a) (ρ a) (hact a) (hY x)
  have h2 := hY x'
  rw [hc] at h2
  have h3 := h2.unique hξ h1
  rw [← hρ' a] at h3
  have h4 := MY.inj h3
  rw [← hx, ← h4]
  exact (hT a x x' hc.symm).symm

end Frame

theorem tangent_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K)),
    (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → Tied ℓ ψ Z.ρ ρK →
    ∃ (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K)),
      (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) ∧
      (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) ∧
      MU.IsActOf Xo.univ.t.act.act ρK ∧ MY.IsActOf Y.t.act.act ρK := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z K _ y h₁ ψ g ℓ ρK hψ hℓ hT
  have : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨MY, hMY⟩ := exists_model_of_frame Z.gen Z.M (y ≫ Y.j) h₁ ψ hψ ℓ hℓ
  have hY : MY.IsActOf Y.t.act.act ρK := isActOf_of_frame Z.gen hℓ Y.t.act Z.act hT hMY
  have hp : IsGrpPullback Y.oF.t.G Xo.univ.t.G (pullback.fst _ _) Y.m0.toSABMap.φ := Y.m0.cart
  have hq : IsGrpPullback Y.oF.t.G Y.t.G Y.j Y.m.φ := Y.m.cart
  obtain ⟨Mo, hMo⟩ := (LiePull.lieModel_pullback _ _ Y.t.G Y.oF.t.G Y.j Y.m.φ hq K y (Fin g → K)).1 MY
  obtain ⟨MU, hMU⟩ := (LiePull.lieModel_pullback _ _ Xo.univ.t.G Y.oF.t.G (pullback.fst _ _) Y.m0.toSABMap.φ hp
    K y (Fin g → K)).2 Mo
  have hMoAct : ∀ (a : 𝓞 E) (e : Fin g → K), Mo.pt (ρK a e) = Mo.pt e ≫ Y.oF.t.act.act a := by
    intro a e
    apply Over.OverMorphism.ext
    apply hq.1.hom_ext
    · rw [hMo, hY a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m.act, ← Category.assoc, hMo]
    · rw [Over.w, Over.comp_left, Category.assoc, Over.w, Over.w]
  refine ⟨MU, MY, fun e => ⟨(Mo.pt e).left, Over.w (Mo.pt e), hMU e, hMo e⟩, hMY, fun a e => ?_, hY⟩
  apply Over.OverMorphism.ext
  rw [← hMU, hMoAct a e, Over.comp_left, Over.comp_left, Category.assoc, Y.m0.act, ← Category.assoc, hMU]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentSpecializationLatticeBasisStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_specialization_lattice_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (K : Type) [Field K] (y : Sp K ⟶ Xo.XF c) (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j))
    (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K) (g : ℕ) (ℓ : Fin g → Z.V) (ρK : 𝓞 E →+* Module.End K (Fin g → K)),
    (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) → Z.M.lat.IsFrameAt ℓ ⟨_, h₁⟩ → Tied ℓ ψ Z.ρ ρK →
    ∃ (MU : LieModel Xo.univ.t.G (under y) (Fin g → K)) (MY : LieModel Y.t.G (y ≫ Y.j) (Fin g → K)),
      (∀ e, SameVec Y y (MU.pt e) (MY.pt e)) ∧
      (∀ x : Fin g → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, Z.M.ValAt (y ≫ Y.j) (comb ℓ x) (MY.pt (fun i => ψ (x i)))) ∧
      MU.IsActOf Xo.univ.t.act.act ρK ∧ MY.IsActOf Y.t.act.act ρK := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CPoint.tangent_coords | exact GlobalTheory.CompanionTheory.Ar.Flat.CPoint.tangent_coords | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CPoint.tangent_coords <;> assumption)
end
end
