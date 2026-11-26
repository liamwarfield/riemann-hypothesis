module

public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsNoetherianRingOfIsAdicComplete
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CbBase

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.Imports
namespace PositivityTheory.HtPt.Ktw

theorem a1 :
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.Statement.{0, 0} :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Swarm.GradedCech.proof).mpr
    GroundTheory.Heights₂.Heights.KeyFormula.serreVanishing_graded_holds

theorem a2 :
    GroundTheory.Heights₂.Heights.Kleiman.TildeVanish.Statement.{0, 0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.TildeVanish.proof a1

theorem a3 :
    GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.SurjectiveClosed.proof
    GroundTheory.Heights₂.Heights.Kleiman.Extension.proof
    GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily.proof a2

theorem a4 :
    GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.RestrLenRestrict.proof a3
    GroundTheory.Heights₂.Heights.Kleiman.PrimeFiltration.RestrictQuot.proof

theorem a5 :
    GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict.Statement.{0, 0} :=
  GroundTheory.Heights₂.Heights.Kleiman.InterNumRestrict.proof a4

end PositivityTheory.HtPt.Ktw
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MgLevel
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace PositivityTheory.HtPt.Mg

abbrev extPt {X : Scheme.{0}} {k K : Type} [Field k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) :
    Over.mk (spMap i ≫ x) ⟶ Over.mk x := Over.homMk (spMap i) rfl

theorem epi_spMap {k K : Type} [Field k] [Field K] (i : k →+* K) : Epi (spMap i) := by
  have : Surjective (spMap i) :=
    ⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem extPt_inj {X : Scheme.{0}} {k K : Type} [Field k] [Field K] (i : k →+* K) (x : Sp k ⟶ X) {G : Over X}
    {a b : Over.mk x ⟶ G} (h : extPt i x ≫ a = extPt i x ≫ b) : a = b := by
  have := epi_spMap i
  have h' : spMap i ≫ a.left = spMap i ≫ b.left := congrArg (fun q => q.left) h
  exact Over.OverMorphism.ext ((cancel_epi (spMap i)).1 h')

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {X : Scheme.{0}}
  {t : SAB H X} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {N : ℕ} {z : Ωˣ} {ev : D.La → (Over.mk ξ ⟶ t.G)}

theorem full_iso (h : IsFullLevelAt D t ξ N z ev) (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) :
    ∃ I : TateIsoAt D t (spMap i ≫ ξ), I.ζ N = Units.map i.toMonoidHom z ∧ ∀ a, I.ev N a = extPt i ξ ≫ ev a := by
  obtain ⟨I, h1, h2⟩ := h k i
  exact ⟨I, Units.ext h1, fun a => Over.OverMorphism.ext (h2 a)⟩

theorem full_desc (hN : 0 < N) (h : IsFullLevelAt D t ξ N z ev) (k : Type) [Field k] (i : Ω →+* k)
    (g : Over.mk (spMap i ≫ ξ) ⟶ t.G) (hg : g ^ N = 1) : ∃ a, g.left = spMap i ≫ (ev a).left := by
  let j : k →+* AlgebraicClosure k := algebraMap _ _
  obtain ⟨I, -, h2⟩ := h (AlgebraicClosure k) (j.comp i)
  let u : Over.mk (spMap (j.comp i) ≫ ξ) ⟶ Over.mk (spMap i ≫ ξ) :=
    Over.homMk (spMap j) (by simp [spMap_comp])
  obtain ⟨a, ha⟩ := (I.onto N hN (u ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])
  refine ⟨a, ?_⟩
  have := epi_spMap j
  have e : spMap j ≫ g.left = (I.ev N a).left := by rw [ha]; rfl
  rw [← cancel_epi (spMap j), e, h2, spMap_comp, Category.assoc]

theorem level_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X : Scheme.{0}) (t : SAB H X) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (N : ℕ), 0 < N → ∀ (z : Ωˣ) (ev : D.La → (Over.mk ξ ⟶ t.G)), IsFullLevelAt D t ξ N z ev → IsPrimitiveRoot z N ∧ (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (r : 𝓞 E) a, ev (r • a) = ev a ≫ t.act.act r) ∧ (∀ a, ev a = 1 ↔ ∃ b, a = N • b) ∧ (∀ g : Over.mk ξ ⟶ t.G, g ^ N = 1 ↔ ∃ a, ev a = g) ∧ FullTorsion t.G ξ N ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (i : Ω →+* k) (a b : D.La) (g g' : Over.mk (spMap i ≫ ξ) ⟶ t.G), g.left = spMap i ≫ (ev a).left → g'.left = spMap i ≫ (ev b).left → Out.WeilIs t.G t.PP.L N g g' (unitOn (Units.map i.toMonoidHom z ^ D.EF a b)) := by
  intro E _ _ _ H D X t Ω _ ξ N hN z ev h
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  obtain ⟨I, h1, h2⟩ := full_iso h (AlgebraicClosure Ω) j
  refine ⟨?_, fun a b => ?_, fun r a => ?_, fun a => ?_, fun g => ?_, fun k _ i g hg => ?_,
    fun k _ _ i a b g g' hg hg' => ?_⟩
  · refine IsPrimitiveRoot.of_map_of_injective (f := Units.map j.toMonoidHom) ?_ (Units.map_injective j.injective)
    rw [← h1]
    exact I.ζ_prim N hN
  · apply extPt_inj j
    rw [MonObj.comp_mul, ← h2, ← h2, ← h2, I.add]
  · apply extPt_inj j
    rw [← h2, I.lin, h2, Category.assoc]
  · rw [← I.ker N hN a, h2]
    exact ⟨fun e => by rw [e, MonObj.comp_one], fun e => extPt_inj j ξ (by rw [e, MonObj.comp_one])⟩
  · constructor
    · intro hg
      obtain ⟨a, ha⟩ := (I.onto N hN (extPt j ξ ≫ g)).1 (by rw [← MonObj.comp_pow, hg, MonObj.comp_one])
      exact ⟨a, extPt_inj j ξ (by rw [← h2, ha])⟩
    · rintro ⟨a, rfl⟩
      apply extPt_inj j
      rw [MonObj.comp_pow, ← h2, MonObj.comp_one]
      exact (I.onto N hN _).2 ⟨a, rfl⟩
  · obtain ⟨a, ha⟩ := full_desc hN h k i g hg
    exact ⟨ev a, ha⟩
  · obtain ⟨J, e1, e2⟩ := full_iso h k i
    have hg1 : g = J.ev N a := by rw [e2]; exact Over.OverMorphism.ext hg
    have hg2 : g' = J.ev N b := by rw [e2]; exact Over.OverMorphism.ext hg'
    rw [hg1, hg2, ← e1]
    exact J.isom N hN a b

theorem finrank_La (D : Datum H) : Module.Free ℤ D.La ∧ Module.Finite ℤ D.La ∧
    Module.finrank ℤ D.La = Module.finrank ℚ E * (D.p + D.q) := by
  have := D.fin
  refine ⟨GlobalTheory.datum_free_int D, Module.Finite.trans (𝓞 E) D.La, ?_⟩
  rw [GlobalTheory.finrank_int_eq_mul_of_finite (O := 𝓞 E), D.rank, RingOfIntegers.rank]

end PositivityTheory.HtPt.Mg
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MfBase
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

noncomputable section

namespace PositivityTheory.HtPt.Mf


set_option maxHeartbeats 1000000 in
theorem xr_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → (∀ q : X, GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ q) → IsIntegral X ∧ (Flat.NormalCpt ξ ↔ IsNormalScheme X) := by
  intro X Ω _ ξ hgen hall
  have hdom : ∀ x : X, IsDomain (X.presheaf.stalk x) := fun x =>
    Function.Injective.isDomain (genMap ξ ⟨x, hall x⟩) (hgen.inj ⟨x, hall x⟩)
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := hdom x
    infer_instance
  haveI : AlgebraicGeometry.IsReduced X := isReduced_of_isReduced_stalk X
  haveI : IrreducibleSpace X := by
    rw [irreducibleSpace_def]
    have hcl : closure {GlobalTheory.CompanionTheory.Ar.genPt ξ} = (Set.univ : Set X) :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.mp (hall q)
    rw [Set.top_eq_univ, ← hcl]
    exact isIrreducible_singleton.closure
  haveI hI : AlgebraicGeometry.IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  refine ⟨hI, ?_⟩
  have key : ∀ p : Cpt ξ, IsIntegrallyClosedIn (regAt ξ p) Ω ↔ IsIntegrallyClosed (X.presheaf.stalk p.1) := by
    intro p
    let ψ : X.functionField →+* Ω :=
      (X.presheaf.stalkSpecializes (hall (genericPoint X)) ≫ Scheme.stalkClosedPointTo ξ).hom
    letI : Algebra (X.presheaf.stalk p.1) Ω := (genMap ξ p).toAlgebra
    have hcomm : ∀ r : X.presheaf.stalk p.1, ψ (algebraMap _ X.functionField r) = algebraMap _ Ω r := by
      intro r
      have hc : X.presheaf.stalkSpecializes (genericPoint_specializes p.1) ≫
          X.presheaf.stalkSpecializes (hall (genericPoint X)) = X.presheaf.stalkSpecializes p.2 :=
        TopCat.Presheaf.stalkSpecializes_comp _ _ _
      have h1 : algebraMap (X.presheaf.stalk p.1) X.functionField r =
          (X.presheaf.stalkSpecializes (genericPoint_specializes p.1)).hom r := rfl
      have h2 : algebraMap (X.presheaf.stalk p.1) Ω r =
          (X.presheaf.stalkSpecializes p.2 ≫ Scheme.stalkClosedPointTo ξ).hom r := rfl
      rw [h1, h2]
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom r) hc
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h3
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3
    have hsurj : Function.Surjective ψ := by
      intro a
      obtain ⟨g, rfl⟩ := hgen.bij.2 a
      refine ⟨(X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ))).hom g, ?_⟩
      have hc2 : X.presheaf.stalkSpecializes (genericPoint_specializes (GlobalTheory.CompanionTheory.Ar.genPt ξ)) ≫
          X.presheaf.stalkSpecializes (hall (genericPoint X)) = 𝟙 _ :=
        (TopCat.Presheaf.stalkSpecializes_comp _ _ _).trans (TopCat.Presheaf.stalkSpecializes_refl _ _)
      have h3 := congrArg (fun φ => (φ ≫ Scheme.stalkClosedPointTo ξ).hom g) hc2
      simp only [Category.id_comp, CommRingCat.hom_comp, RingHom.comp_apply] at h3
      simp only [ψ, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h3
    let e : X.functionField ≃ₐ[X.presheaf.stalk p.1] Ω :=
      AlgEquiv.ofBijective { ψ with commutes' := hcomm } ⟨ψ.injective, hsurj⟩
    rw [isIntegrallyClosed_iff_isIntegrallyClosedIn X.functionField, e.isIntegrallyClosedIn]
    letI : Algebra (X.presheaf.stalk p.1) (regAt ξ p) := (genMap ξ p).rangeRestrict.toAlgebra
    haveI : IsScalarTower (X.presheaf.stalk p.1) (regAt ξ p) Ω :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Algebra.IsIntegral (X.presheaf.stalk p.1) (regAt ξ p) :=
      Algebra.isIntegral_of_surjective (genMap ξ p).rangeRestrict_surjective
    rw [Subring.isIntegrallyClosedIn_iff, isIntegrallyClosedIn_iff]
    constructor
    · intro h
      refine ⟨hgen.inj p, fun {x} hx => ?_⟩
      exact RingHom.mem_range.mp (h hx.tower_top)
    · rintro ⟨-, h⟩ x hx
      exact RingHom.mem_range.mpr (h (isIntegral_trans x hx))
  constructor
  · intro h x
    exact ⟨inferInstance, (key ⟨x, hall x⟩).mp
      (Subring.isIntegrallyClosedIn_iff.mpr (fun a ha => h ⟨x, hall x⟩ a ha))⟩
  · intro h p a ha
    exact Subring.isIntegrallyClosedIn_iff.mp ((key p).mpr (h p.1).2) ha

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem bijective_iff_isIso_stalkMap (ξ : Sp Ω ⟶ X) (x : Sp Ω) :
    Function.Bijective (Scheme.stalkClosedPointTo ξ).hom ↔ IsIso (ξ.stalkMap x) := by
  obtain rfl : x = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
  rw [← isIso_comp_right_iff (ξ.stalkMap _) (AlgebraicGeometry.stalkClosedPointIso (CommRingCat.of Ω)).hom]
  exact (ConcreteCategory.isIso_iff_bijective _).symm

def push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) (q : Cpt ξ) : Cpt (ξ ≫ f) :=
  ⟨f q.1, q.2.map f.continuous⟩

theorem genMap_push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) (q : Cpt ξ) :
    genMap (ξ ≫ f) (push ξ f q) = (genMap ξ q).comp (f.stalkMap q.1).hom := by
  show (X.presheaf.stalkSpecializes _ ≫ Scheme.stalkClosedPointTo (ξ ≫ f)).hom =
    (W.presheaf.stalkSpecializes q.2 ≫ Scheme.stalkClosedPointTo ξ).hom.comp (f.stalkMap q.1).hom
  rw [← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.stalkClosedPointTo_comp]
  exact Scheme.Hom.stalkSpecializes_stalkMap_assoc f _ q.1 q.2 _

theorem regAt_push {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) [SurjectiveOnStalks f] (q : Cpt ξ) :
    regAt (ξ ≫ f) (push ξ f q) = regAt ξ q := by
  ext a
  simp only [regAt, genMap_push, RingHom.mem_range, RingHom.comp_apply]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := f.stalkMap_surjective q.1 y
    exact ⟨x, rfl⟩

theorem isCptGen_of_comp {W : Scheme.{0}} (ξ : Sp Ω ⟶ W) (f : W ⟶ X) [SurjectiveOnStalks f]
    (h : IsCptGen (ξ ≫ f)) : IsCptGen ξ := by
  have key : ∀ {A B C : Type} (g : B → C) (s : A → B), Function.Injective (g ∘ s) →
      Function.Surjective s → Function.Injective g := by
    intro A B C g s hi hs y y' hy
    obtain ⟨x, rfl⟩ := hs y
    obtain ⟨x', rfl⟩ := hs y'
    exact congrArg s (hi hy)
  have hb : Function.Bijective ((Scheme.stalkClosedPointTo ξ).hom ∘ (f.stalkMap (ξ (closedPoint Ω))).hom) := by
    have hb0 := h.bij
    rw [Scheme.stalkClosedPointTo_comp] at hb0
    exact hb0
  refine ⟨⟨key _ _ hb.1 (f.stalkMap_surjective _), Function.Surjective.of_comp hb.2⟩, fun p => ?_⟩
  have hi : Function.Injective ((genMap ξ p) ∘ (f.stalkMap p.1).hom) := by
    have hi0 := h.inj (push ξ f p)
    rw [genMap_push] at hi0
    exact hi0
  exact key _ _ hi (f.stalkMap_surjective p.1)

end PositivityTheory.HtPt.Mf
end
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.CoeffEvPowOne
noncomputable section

namespace PositivityTheory.HtPt.Cb

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open ReciprocityTheory.ChartRestriction.G.TB

section

variable {R : Type} [CommRing R] {σ : Type} [Finite σ]

def scl (w : σ → ℕ) (m : σ →₀ ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun s => w s * m s

theorem scl_inj {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) : Function.Injective (scl w) := fun m m' h => by
  ext s
  have := congrArg (fun f => f s) h
  simpa [scl, hw s] using this

theorem hasSubst_w {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) :
    HasSubst (fun s => (X s : MvPowerSeries σ R) ^ w s) :=
  hasSubst_of_constantCoeff_zero fun s => by simp [hw s]

theorem prod_w (w : σ → ℕ) (m : σ →₀ ℕ) :
    (m.prod fun s e => ((X s : MvPowerSeries σ R) ^ w s) ^ e) = monomial (scl w m) 1 := by
  classical
  have := Fintype.ofFinite σ
  rw [monomial_eq', Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  simp [scl, pow_mul]

theorem coeff_scl {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) (g : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    coeff (scl w m) (subst (fun s => (X s : MvPowerSeries σ R) ^ w s) g) = coeff m g := by
  classical
  rw [coeff_subst (hasSubst_w hw), finsum_eq_single _ m]
  · simp [prod_w]
  · intro m' h
    rw [prod_w, coeff_monomial, ite_eq_right ((scl_inj hw).ne h.symm), smul_zero]

theorem coeff_not_scl {w : σ → ℕ} (hw : ∀ s, w s ≠ 0) (g : MvPowerSeries σ R) (e : σ →₀ ℕ)
    (he : ∀ m, e ≠ scl w m) :
    coeff e (subst (fun s => (X s : MvPowerSeries σ R) ^ w s) g) = 0 := by
  classical
  rw [coeff_subst (hasSubst_w hw)]
  refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
  rw [prod_w, coeff_monomial, ite_eq_right (he m), smul_zero]

theorem exists_scl (p : ℕ) [hp : Fact p.Prime] [CharP R p] (S : σ → Prop) [DecidablePred S]
    (f : MvPowerSeries σ R) (hf : ∀ s, S s → pderiv s f = 0) :
    ∃ g : MvPowerSeries σ R, f = subst (fun s => (X s : MvPowerSeries σ R) ^ (if S s then p else 1)) g := by
  classical
  have hw : ∀ s, (if S s then p else 1) ≠ 0 := fun s => by split_ifs <;> simp [hp.out.ne_zero]
  obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries σ R, ∀ m, coeff m g = coeff (scl (fun s => if S s then p else 1) m) f :=
    ⟨fun m => coeff (scl (fun s => if S s then p else 1) m) f, fun _ => rfl⟩
  refine ⟨g, ?_⟩
  ext e
  by_cases he : ∃ m, e = scl (fun s => if S s then p else 1) m
  · obtain ⟨m, rfl⟩ := he
    rw [coeff_scl hw, hg]
  · rw [coeff_not_scl hw _ _ (not_exists.1 he)]
    obtain ⟨s, hS, hs⟩ : ∃ s, S s ∧ ¬ p ∣ e s := by
      by_contra hc
      push Not at hc
      refine he ⟨Finsupp.equivFunOnFinite.symm fun s => if S s then e s / p else e s, ?_⟩
      ext s
      by_cases h : S s
      · simp [scl, h, Nat.mul_div_cancel' (hc s h)]
      · simp [scl, h]
    have h0 : e s ≠ 0 := fun h => hs (h ▸ dvd_zero p)
    have h1 := congrArg (coeff (e - Finsupp.single s 1)) (hf s hS)
    rw [coeff_pderiv, tsub_add_cancel_of_le (by simpa [Finsupp.single_le_iff] using Nat.one_le_iff_ne_zero.2 h0),
      map_zero] at h1
    have h2 : (((e - Finsupp.single s 1 : σ →₀ ℕ) s : ℕ) : R) + 1 = (e s : R) := by
      rw [← Nat.cast_succ]; congr 1; simp; omega
    rw [h2] at h1
    have hu : IsUnit (e s : R) := (CharP.isUnit_natCast_iff hp.out).2 hs
    exact hu.mul_left_eq_zero.1 h1

end

section

variable {R : Type} [CommRing R] {d : ℕ} (p : ℕ)

theorem ev_pow_one_eq (g : PS R 1 d) : ev (n := 1) ![ptPow R d p 0] g =
    subst (fun s : Fin 1 × Fin d => (X s : PS R 1 d) ^ (if s.1 = 0 then p else 1)) g := by
  unfold ev; congr 1; funext ⟨j, i⟩; fin_cases j; simp [ptPow]

theorem ev_pow_two_eq (g : PS R 2 d) : ev (n := 2) ![ptPow R d p 0, pt R d 1] g =
    subst (fun s : Fin 2 × Fin d => (X s : PS R 2 d) ^ (if s.1 = 0 then p else 1)) g := by
  unfold ev; congr 1; funext ⟨j, i⟩; fin_cases j <;> simp [ptPow, pt]

variable [hp : Fact p.Prime]

theorem w_ne {n : ℕ} [NeZero n] (s : Fin n × Fin d) : (if s.1 = 0 then p else 1) ≠ 0 := by
  split_ifs <;> simp [hp.out.ne_zero]

theorem ev_pow_inj {f g : PS R 1 d} (h : ev (n := 1) ![ptPow R d p 0] f = ev ![ptPow R d p 0] g) : f = g := by
  ext m
  rw [← coeff_scl (w_ne p) f, ← coeff_scl (w_ne p) g, ← ev_pow_one_eq, ← ev_pow_one_eq, h]

theorem coeff_ev_pow_one (g : PS R 1 d) (j : Fin d) :
    coeff (Finsupp.single ((0 : Fin 1), j) p) (ev (n := 1) ![ptPow R d p 0] g) =
      coeff (Finsupp.single ((0 : Fin 1), j) 1) g := by
  rw [← coeff_scl (w_ne p) g, ev_pow_one_eq]
  congr 2
  ext s
  by_cases h : s = (0, j)
  · simp [scl, h]
  · simp [scl, Finsupp.single_eq_of_ne h]

theorem bil_ev_pow_two (g : PS R 2 d) : bil (ev (n := 2) ![ptPow R d p 0, pt R d 1] g) p 1 = bil g 1 1 := by
  ext i j
  rw [bil, bil, ← coeff_scl (w_ne p) g, ev_pow_two_eq]
  congr 2
  ext ⟨s, t⟩
  fin_cases s <;> simp [scl, Finsupp.single_apply]

end

theorem series_in_p : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ), (∀ f : PS R 1 d, (∀ j, pderiv ((0 : Fin 1), j) f = 0) → ∃ g : PS R 1 d, f = ev (n := 1) ![ptPow R d p 0] g) ∧ ∀ f : PS R 2 d, (∀ j, pderiv ((0 : Fin 2), j) f = 0) → ∃ g : PS R 2 d, f = ev (n := 2) ![ptPow R d p 0, pt R d 1] g := by
  intro R _ p _ _ d
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · simp only [ev_pow_one_eq]
    exact exists_scl p (fun s : Fin 1 × Fin d => s.1 = 0) f fun ⟨s, t⟩ h => by
      obtain rfl : s = 0 := h
      exact hf t
  · simp only [ev_pow_two_eq]
    exact exists_scl p (fun s : Fin 2 × Fin d => s.1 = 0) f fun ⟨s, t⟩ h => by
      obtain rfl : s = 0 := h
      exact hf t

theorem frob_subst : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d), f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) := by
  intro R _ p hp _ d n f
  rw [← map_frobenius_expand p hp.out.ne_zero, map_expand, expand, substAlgHom_apply]
  rfl

end PositivityTheory.HtPt.Cb
end
end
