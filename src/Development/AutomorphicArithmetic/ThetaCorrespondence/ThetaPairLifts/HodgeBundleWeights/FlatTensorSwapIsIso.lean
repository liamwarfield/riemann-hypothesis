module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGaga
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatDegreeHolds
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LocallyQuasiFiniteSpMap
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LeadMinorSmulOne
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLineIdempotentSections
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.LineFunctionPlaceValuation
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocalValuationLogNormsExistence
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameFunctionFiniteNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteNormLocalBound
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GagaSections
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDifferentFromIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGramRelationsBlocksOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineDegreeEqEigenLatticeDegreeSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSectionFlatWeight
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.ComplexPeriods.FlatDegreeResidues.FlatSlim
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatDegreeStOfResKGaga
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterFrameBound
section -- merged from Development.WeilBound.CoreStatements.ComplexPeriods.ComplexPointPeriods.PeriodIn
section -- merged from Development.WeilBound.CoreStatements.ComplexPeriods.ComplexPointPeriods.PeriodPos
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace PositivityTheory.Xj6.PeriodIn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem exists_complex_point {U : Set (Xo.XF c)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) ∧ ∀ z, y z ∈ U := by
  haveI := Xo.smooth
  haveI hs0 : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  let s : Xo.XF c ⟶ Sp c.F := pullback.snd _ _
  haveI hs : Smooth s := inferInstanceAs (Smooth (pullback.snd _ _))
  obtain ⟨L, _, j, g, hj, hg, hZ⟩ := GlobalTheory.FlatLine.exists_finite_point s hU hne
  letI : Algebra c.F L := j.toAlgebra
  haveI : Module.Finite c.F L := hj
  let e : L →ₐ[c.F] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨spMap e.toRingHom ≫ g, ?_, fun z => ?_⟩
  · change (spMap e.toRingHom ≫ g) ≫ s = _
    rw [Category.assoc, hg, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact e.comp_algebraMap
  · rw [Scheme.Hom.comp_apply]; exact hZ _

theorem exists_period {U : Set (Xo.XF c)} (hU : IsClopen U) (hne : U.Nonempty) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (hty : IsTypeFn H D.p D.q ty) :
    ∃ i : Fin FU.n, ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  obtain ⟨y₀, hy₀, hU₀⟩ := exists_complex_point hU.isOpen hne
  have hs : under y₀ ≫ Xo.s = spMap (algebraMap (KA l) ℂ) := by
    rw [under, Category.assoc, pullback.condition, ← Category.assoc, hy₀, ← Spec.map_comp]; rfl
  obtain ⟨i, P₀, hP₀, hu₀⟩ := FU.onto _ hs
  refine ⟨i, fun P y hP hu hy => ?_⟩
  rintro _ ⟨z, rfl⟩
  have h := PositivityTheory.Xgn.GeometricOfPeriods.sameComp_periods FU i hty hP hP₀
  rw [← hu, hu₀] at h
  obtain ⟨hp, hq, h⟩ := PositivityTheory.Xgn.GeometricOfPeriods.sameComp_baseChange _ _ Xo.s y y₀ hy hy₀ h
  let π : pullback (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
      (spMap (algebraMap c.F ℂ)) ⟶ Xo.XF c := pullback.fst _ _
  have h1 := π.continuous.image_connectedComponent_subset _ ⟨_, h z, rfl⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst] at h1
  exact hU.connectedComponent_subset (hU₀ z) h1

theorem period_in_pos (hr : 1 ≤ D.p + D.q) {U : Set (Xo.XF c)} (hU : IsClopen U) (hne : U.Nonempty) :
    ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n),
      IsTypeFn H D.p D.q ty ∧ ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
        y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.CompanionTheory.Ar.Top.complex_uniformisation_holds E H D l Xo (algebraMap (KA l) ℂ) g ty hr rfl hty
  obtain ⟨i, hi⟩ := exists_period hU hne FU hty
  exact ⟨g, ty, FU, i, hty, hi⟩

end PositivityTheory.Xj6.PeriodIn
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

theorem PositivityTheory.Xj6.period_in : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), 1 ≤ D.p + D.q → IsClopen U → U.Nonempty → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U :=
  fun _ _ _ _ _ _ _ _ _ _ hr hU hne => PositivityTheory.Xj6.PeriodIn.period_in_pos hr hU hne
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformizationTypeRelay
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformizationTypeRelay
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.family_uniformization_type_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), 1 ≤ D.p + D.q → IsClopen U → U.Nonempty → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  first | exact @PositivityTheory.Xj6.period_in | exact PositivityTheory.Xj6.period_in
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyUniformizationTypeRelayStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_uniformization_type_relay : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)), 1 ≤ D.p + D.q → IsClopen U → U.Nonempty → ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n), IsTypeFn H D.p D.q ty ∧ ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.Relay.family_uniformization_type_relay | exact GlobalTheory.CompanionTheory.Relay.family_uniformization_type_relay | (intros; apply GlobalTheory.CompanionTheory.Relay.family_uniformization_type_relay <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterFrameBound
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem degree_of_flatOnModel : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [NumberField c.F] (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → IsClopen U → Z.IsGeom → FlatOnModel Z τ φ → (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) → N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hres hgaga E _ _ _ H D l Xo c O _ β Y _ U Z τ φ N _ χ hχ hO hpq hτ hcl hZ hflat hinf hfin
  obtain ⟨g, ty, FU, i, hty, hin⟩ := GlobalTheory.T.family_uniformization_type_relay E H D l Xo c U hpq hcl ⟨_, Z.genPt_mem⟩
  have hA := GlobalTheory.T.flat_first_from_resolution_and_gaga hres hgaga E H D l Xo c O β Y U Z τ φ hO hpq hτ hZ hflat.isLineFn hflat
  exact GlobalTheory.CompanionTheory.Ar.Fl.TopLL.degree_frames GlobalTheory.T.FlatDegree_holds E H D l Xo c g ty FU i U τ φ N χ hχ hty hτ
    (hA.2 g ty FU i hty hin) hinf hfin

end GlobalTheory.CompanionTheory.Ar.Br
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterFrameBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kronecker_character_frame_bound : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [NumberField c.F] (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (φ : FrameFn Xo c) (N : LogNorms c.F) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → FracBase β → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → IsClopen U → Z.IsGeom → FlatOnModel Z τ φ → (∀ s, HasInfNorm U τ φ s (N.inf s)) → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm U τ φ p κ (N.fin p κ)) → N.IsAdelic ∧ N.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.degree_of_flatOnModel | exact GlobalTheory.CompanionTheory.Ar.Br.degree_of_flatOnModel | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.degree_of_flatOnModel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Foundations.NotFlatExistsOfIsEmpty
noncomputable section

namespace GlobalTheory.FlatLine.Model

open NumberField IsDedekindDomain Module AlgebraicGeometry CategoryTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions _root_.Formalism.L2.Pj GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem sum_flatWt (τ : Psi H) :
    ∑ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) = Dw.q - Dw.p := by
  classical
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have key : ∀ ρ : E →+* ℂ, ∑ i : Fin (Dw.mult ρ), (((wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) : ℤ) : ℝ) =
      (if ρ = conjEmb τ.1 then (Dw.q : ℝ) else 0) - if ρ = τ.1 then (Dw.p : ℝ) else 0 := fun ρ => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hm : Dw.mult ρ = Dw.p := by simp [Datum.mult, h]
      have h1 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = τ.1 then -1 else 0 :=
        fun i => by
          have := wtOf_big (flatWt Dw τ) 0 ⟨ρ, h⟩ i (hm ▸ i.2)
          rw [this]
          simp [flatWt, parWt, Subtype.ext_iff]
      simp only [h2]
      split_ifs <;> simp_all
    · have hm : Dw.mult ρ = Dw.q := by simp [Datum.mult, h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      have h2 : ∀ i : Fin (Dw.mult ρ), (wtOf Dw (flatWt Dw τ) 0).1 (ρ, i) = if ρ = conjEmb τ.1 then 1 else 0 :=
        fun i => by
          have := wtOf_small (flatWt Dw τ) 0 ⟨_, conj_mem h⟩ i (hm ▸ i.2)
          simp only [AllWt.conjEmb_conjEmb] at this
          rw [this]
          by_cases e : ρ = conjEmb τ.1
          · simp [flatWt, parWt, Subtype.ext_iff, e, AllWt.conjEmb_conjEmb]
          · have : conjEmb ρ ≠ τ.1 := fun e' => e (by rw [← e', AllWt.conjEmb_conjEmb])
            simp [flatWt, parWt, Subtype.ext_iff, e, this]
      simp only [h2]
      split_ifs <;> simp_all
  simp [key]

end GlobalTheory.FlatLine.Model
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem exists_fieldMap_of_surjective {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (h : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) (z : X) (hz : ξ (IsLocalRing.closedPoint Ω) = z) :
    ∃ i : Ω →+* X.residueField z, spMap i ≫ ξ = X.fromSpecResidueField z := by
  subst hz
  let g := X.descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ)
  have hsurj : Function.Surjective g.hom := by
    intro a
    obtain ⟨b, hb⟩ := h a
    refine ⟨(X.residue _).hom b, ?_⟩
    have e := congrArg CommRingCat.Hom.hom
      (X.residue_descResidueField (Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) ξ))
    exact (congrArg (fun φ => φ b) e).trans hb
  let e : X.residueField (ξ (IsLocalRing.closedPoint Ω)) ≃+* Ω :=
    RingEquiv.ofBijective g.hom ⟨g.hom.injective, hsurj⟩
  refine ⟨e.symm.toRingHom, ?_⟩
  have h1 : Spec.map g ≫ X.fromSpecResidueField (ξ (IsLocalRing.closedPoint Ω)) = ξ :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X ξ
  have h2 : spMap e.symm.toRingHom ≫ Spec.map g = 𝟙 _ := by
    have h3 : g ≫ CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := by
      ext a
      exact e.symm_apply_apply a
    exact (Spec.map_comp _ _).symm.trans ((congrArg Spec.map h3).trans (Spec.map_id _))
  refine (congrArg (spMap e.symm.toRingHom ≫ ·) h1).symm.trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ X.fromSpecResidueField _) h2).trans (Category.id_comp _))

theorem isGeom_of_fnAlgClosed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))), FracBase β → Formalism.L2.Pj.FnAlgClosed (Xo := Xo) (c := c) → Z'.IsGeom := by
  intro E _ _ _ H D l Xo c O _ β Y Z Z' _ hc x ⟨f, hf0, hf⟩
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo Z'.ξ₀).hom := by
    have h := Z'.gen.bij.2
    rw [Scheme.stalkClosedPointTo_comp] at h
    intro a
    obtain ⟨b, hb⟩ := h a
    exact ⟨_, hb⟩
  have hgp : genPt Z'.ξ₀ = Formalism.L2.Pj.genPt Z := by
    have hg := Z.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ Z.2)
    have h2 : Formalism.L2.Pj.genPt Z ⤳ genPt Z'.ξ₀ := hg.specializes Z'.genPt_mem
    have h3 : genPt Z'.ξ₀ ⤳ Formalism.L2.Pj.genPt Z := (Z'.closure _).1 hg.mem
    exact (h3.antisymm h2).eq
  obtain ⟨i, hi⟩ := exists_fieldMap_of_surjective Z'.ξ₀ hsurj _ hgp
  have hcomp : i.comp Z'.inc = algebraMap c.F (Formalism.L2.Pj.kap Z) := by
    have h1 : Formalism.L2.Pj.genSp Z ≫ Formalism.L2.Pj.strK = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) :=
      (Spec.map_preimage _).symm
    have h2 : spMap (i.comp Z'.inc) = spMap (algebraMap c.F (Formalism.L2.Pj.kap Z)) := by
      rw [← h1]
      have e : spMap (i.comp Z'.inc) = spMap i ≫ spMap Z'.inc := by
        rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl
      rw [e, ← Z'.over_inc, ← Category.assoc, hi]
      rfl
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h2)
  have hb : IsAlgebraic c.F (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z) (i x)) := by
    refine ⟨f, hf0, ?_⟩
    have h3 := Polynomial.hom_eval₂ f Z'.inc ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i) x
    rw [hf, map_zero] at h3
    rw [Polynomial.aeval_def]
    refine Eq.trans ?_ h3.symm
    have e : algebraMap c.F (Formalism.L2.Pj.Om Z) =
        ((algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).comp i).comp Z'.inc := by
      rw [RingHom.comp_assoc, hcomp]
      exact IsScalarTower.algebraMap_eq _ _ _
    rw [e]
    rfl
  obtain ⟨k, hk⟩ := hc Z _ hb
  refine ⟨k, i.injective ?_⟩
  have h2 : algebraMap c.F (Formalism.L2.Pj.kap Z) k = i x := by
    apply (algebraMap (Formalism.L2.Pj.kap Z) (Formalism.L2.Pj.Om Z)).injective
    rw [← hk, ← IsScalarTower.algebraMap_apply]
  rw [← h2, ← hcomp]
  rfl

end GlobalTheory.CompanionTheory.Ar.Br
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricComponentAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_component_alg_closed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))), FracBase β → Formalism.L2.Pj.FnAlgClosed (Xo := Xo) (c := c) → Z'.IsGeom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed | exact GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.isGeom_of_fnAlgClosed <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsConstSectionKroneckerChar
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UnfSectionNormBoundAtHeight
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UnfSectionNormBoundAtHeight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.FlatNorm

open ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT _root_.Formalism.L2.LamCM
open scoped Matrix ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r}

theorem exists_test (f : Rul Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) :
    ∃ (p : TRing c.F) (ψ : p.R →ₐ[c.F] S) (y₀ : FrPt Xo c p.R), FrMap ψ y₀ y ∧ evR Xo c f y = ψ (f p y₀) := by
  refine ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose, h.choose_spec.choose_spec.choose_spec, ?_⟩
  unfold evR evalAt
  rw [dif_pos h]

theorem exists_gram_det (hσ : GoodEmb c σ) (hU : IsUnf U) {k : U.Comp} (x : (U.X k).dom)
    (hx : (U.X k).IsOrtho x.1) (y : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ) (ht : FrBor t (U.un k x) y)
    (τ : E →+* ℂ) (n : ℕ) (hn : Dw.mult τ = n) (z : Sp ℂ ⟶ Xo.X) (hz : z = y.x)
    (v : Fin n → (GlobalTheory.CompanionTheory.Ar.epsAt z ⟶ Xo.univ.t.G)) (hv : ∀ i, (v i).left = y.u τ (Fin.cast hn.symm i)) :
    ∃ Γ : Matrix (Fin n) (Fin n) ℂ, IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L z v Γ ∧
      ‖Γ.det‖ = (Real.pi * (2 * ‖relab c σ τ (U.X k).ξ0‖)) ^ n *
        (∏ i : Fin n, ‖toC (t (some ⟨τ, Fin.cast hn.symm i⟩) : CAt σ)‖) ^ 2 := by
  classical
  subst hn
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := PositivityTheory.UnitarySelfGeneration.GF.hm_diag hσ hU W Wu hx
  choose cf h1 h2 h3 using ht.2.1 τ
  let Y : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := fun j i => toC (cf i j)
  let Dv : Fin (Dw.mult τ) → Fin W.g → ℂ := fun i => ∑ j, Y j i • (Pi.single (W.e.symm ⟨τ, j⟩) 1 : Fin W.g → ℂ)
  have hd : ∀ i, IsDerivAt0 (fun z => (W.F.ex (W.ik k) W.Pm z).left) (Dv i) (v i).left := fun i => by
    rw [hv]
    refine (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm W.per _ ((U.un k x).u τ)
      (fun i => Pi.single (W.e.symm ⟨τ, i⟩) 1) (W.der τ) (fun j => Y j i) _).1 ?_
    have := h3 i
    rw [W.pt] at this
    exact this
  set κ : ℝ := Real.pi * (2 * ‖relab c σ τ (U.X k).ξ0‖) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  let Γ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ := Matrix.of fun a b => Real.pi * hermForm Wu.Hm (Dv a) (Dv b)
  refine ⟨Γ, (hodgeGram_iff_period E H Dw l Xo _ W.g _ W.F (W.ik k) W.Pm Wu.Hm W.per Wu.herm Wu.c1 z
    (hz.trans (ht.1.trans W.pt)) _ v Dv Γ hd).2 fun a b => rfl, ?_⟩
  have hG : Γᵀ = Yᴴ * ((κ : ℂ) • (1 : Matrix _ _ ℂ)) * Y := by
    ext p q
    show (Real.pi : ℂ) * hermForm Wu.Hm (Dv q) (Dv p) = _
    rw [MetricChange.hermForm_sum]
    have hf : ∀ a b : Fin (Dw.mult τ), hermForm Wu.Hm (Pi.single (W.e.symm ⟨τ, a⟩) 1) (Pi.single (W.e.symm ⟨τ, b⟩) 1) =
        if a = b then ((2 * ‖relab c σ τ (U.X k).ξ0‖ : ℝ) : ℂ) else 0 := by
      intro a b
      rw [hH, hermForm, single_dotProduct, Matrix.mulVec_diagonal, _root_.one_mul, Equiv.apply_symm_apply, Pi.star_apply]
      split_ifs with hab
      · subst hab
        simp
      · rw [Pi.single_eq_of_ne (fun hh => hab (eq_of_heq (Sigma.mk.inj (W.e.symm.injective hh)).2))]
        simp
    simp only [hf, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.smul_apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      smul_eq_mul, Finset.mul_sum, hκ]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hdet : Y.det = ∏ i, toC (t (some ⟨τ, i⟩) : CAt σ) := by
    have hb : Y.BlockTriangular id := fun a b h => h2 b a h
    rw [Matrix.det_of_upperTriangular hb]
    exact Finset.prod_congr rfl fun i _ => h1 i
  rw [← Matrix.det_transpose, hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_smul,
    Matrix.det_one, hdet]
  simp only [Fintype.card_fin, _root_.mul_one, norm_mul, norm_star, norm_pow, Complex.norm_real, norm_prod, Fin.cast_eq_self,
    Real.norm_eq_abs, abs_of_nonneg hκ0]
  ring

theorem pnorm_flat (X : Data E r) (τ : X.Ψ) (P : Frame X.Ψ r → ℂ) (y : Frame X.Ψ r) :
    X.pnorm (GlobalTheory.FlatLine.modelFlat r τ) P y =
      ‖P y‖ * ∏ i : Fin r, Real.sqrt ‖dmin X.Gm y τ i.succ / dmin X.Gm y τ i.castSucc‖ := by
  classical
  unfold Data.pnorm
  congr 1
  rw [Fintype.prod_eq_single τ]
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp [GlobalTheory.FlatLine.modelFlat, Real.sqrt_eq_rpow]
  · intro τ' h
    simp [GlobalTheory.FlatLine.modelFlat, h]

theorem prod_split {p q r : ℕ} (hr : r = p + q) (f : Fin r → ℝ) :
    ∏ a, f a = (∏ i : Fin p, f ⟨q + i, by omega⟩) * ∏ j : Fin q, f ⟨q - 1 - j, by omega⟩ := by
  subst hr
  have e : ∏ a, f a = ∏ a : Fin (q + p), f (Fin.cast (by omega) a) :=
    (Fintype.prod_equiv (finCongr (by omega)) _ _ fun a => by simp).symm
  rw [e, Fin.prod_univ_add, mul_comm]
  congr 1
  rw [← Equiv.prod_comp Fin.revPerm]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  ext
  simp [Fin.val_rev]
  omega

end GlobalTheory.CompanionTheory.Ar.Br.FlatNorm

namespace GlobalTheory.CompanionTheory.Ar.Br


open GlobalTheory.CompanionTheory.Ar.Br.FlatNorm ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj in
theorem homN_eq_exp_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ) (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (t : ℝ), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf U → (∀ k (τ' : E →+* ℂ), ‖τ' (U.X k).ξ0‖ = x) → s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) → IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ t → ∀ z ∈ GlobalTheory.AllWt.framesOn U Z, (∀ hz : z.2 ∈ (U.X z.1).dom, GlobalTheory.FlatLine.Tested (U.un z.1 ⟨z.2, hz⟩)) → GlobalTheory.AllWt.homN U x (GlobalTheory.AllWt.wtOf D (GlobalTheory.FlatLine.flatWt D τ) 0) s z = Real.exp t := by
  intro E _ _ _ H D l Xo c r σ U x Z τ s φ t hσ hU hx hs hline hread hinf z hz htest
  classical
  obtain ⟨k, y⟩ := z
  obtain ⟨hy, hlies⟩ := hz
  have ht := htest hy
  dsimp only at hy hlies ht
  obtain ⟨p, ψ, z₀, hmap, hval⟩ := exists_test s (U.un k ⟨y, hy⟩) ht
  have hp : D.mult τ.1 = D.p := by simp [Datum.mult, τ.2]
  have hq : D.mult (ComplexEmbedding.conjugate τ.1) = D.q := by
    have h := GlobalTheory.AllWt.conj_not_mem τ
    have h' : ¬ (ComplexEmbedding.conjugate τ.1) (H.rt : E) = H.rt0 := h
    unfold Datum.mult
    rw [if_neg h']
  let ψ' : p.R →+* ℂ := (ψ : p.R →+* CAt σ)
  let yF : Sp ℂ ⟶ Xo.XF c := GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k ⟨y, hy⟩)
  have hβ : ψ'.comp (algebraMap c.F p.R) = σ := RingHom.ext fun a => ψ.commutes a
  have hu : under yF = spMap ψ' ≫ z₀.x := by
    show GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k ⟨y, hy⟩) ≫ pullback.fst _ _ = _
    rw [GlobalTheory.AllWt.ptF, pullback.lift_fst]
    exact hmap.1
  have hsn : yF ≫ pullback.snd _ _ = spMap (ψ'.comp (algebraMap c.F p.R)) := by
    show GlobalTheory.AllWt.ptF (S := CAt σ) (U.un k ⟨y, hy⟩) ≫ pullback.snd _ _ = _
    rw [GlobalTheory.AllWt.ptF, pullback.lift_snd, hβ]
    rfl
  have hrange : Set.range yF ⊆ (Z : Set (Xo.XF c)) := by
    rintro _ ⟨s', rfl⟩
    exact hlies s'
  obtain ⟨v, w, hv, hw, hfr⟩ := GlobalTheory.CompanionTheory.Ar.FrameEig.isFramed_frPt E H D l Xo c τ.1 p.R z₀ ℂ ψ' yF hp hq hu hsn
  have hfZ := hfr _ hrange
  have hread' := hread p z₀ ℂ ψ' yF hu hsn hrange v w hp hq hv hw
  rw [hβ] at hfZ
  obtain ⟨x₀, tt, ho, hb, hnorm⟩ := PositivityTheory.UnitarySelfGeneration.GF.move hσ hU ⟨y, hy⟩
  have hz' : under yF = (U.un k ⟨y, hy⟩).x := by
    rw [hu]; exact hmap.1.symm
  have hv' : ∀ i, (v i).left = (U.un k ⟨y, hy⟩).u τ.1 (Fin.cast hp.symm i) := fun i => by
    rw [hv i]; exact (hmap.2.1 _ _).symm
  have hw' : ∀ j, (w j).left = (U.un k ⟨y, hy⟩).u (ComplexEmbedding.conjugate τ.1) (Fin.cast hq.symm j) := fun j => by
    rw [hw j]; exact (hmap.2.1 _ _).symm
  obtain ⟨Γ, hΓ, dΓ⟩ := exists_gram_det hσ hU x₀ ho _ tt hb τ.1 D.p hp (under yF) hz' v hv'
  obtain ⟨Δ, hΔ, dΔ⟩ := exists_gram_det hσ hU x₀ ho _ tt hb (ComplexEmbedding.conjugate τ.1) D.q hq (under yF) hz' w hw'
  have hI := hinf yF v w Γ Δ hfZ hΓ hΔ
  have hφ : φ ℂ yF v w ≠ 0 := hline.ne ℂ σ yF v w hfZ
  obtain ⟨-, hrt, -, -⟩ := GlobalTheory.Relab.relab_good E H l c σ hσ
  obtain ⟨hp0, hty⟩ := hU.2.1 k
  have hτ : relab c σ τ.1 ∈ (U.X k).Ψ := (hty _).2 ((hrt τ.1).2 τ.2)
  have hx1 : ‖relab c σ τ.1 (U.X k).ξ0‖ = x := hx k _
  have hx2 : ‖relab c σ (ComplexEmbedding.conjugate τ.1) (U.X k).ξ0‖ = x := hx k _
  have hx0 : 0 < x := hx1 ▸ norm_pos_iff.2 ((map_ne_zero _).2 (U.X k).ξ0_ne)
  rw [hx1] at dΓ
  rw [hx2] at dΔ
  set A : ℝ := ∏ i : Fin D.p, ‖toC (tt (some ⟨τ.1, Fin.cast hp.symm i⟩) : CAt σ)‖ with hA
  set B : ℝ := ∏ j : Fin D.q, ‖toC (tt (some ⟨ComplexEmbedding.conjugate τ.1, Fin.cast hq.symm j⟩) : CAt σ)‖ with hB
  have hA0 : 0 < A := Finset.prod_pos fun i _ => norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) (tt _))
  have hB0 : 0 < B := Finset.prod_pos fun i _ => norm_pos_iff.2 (Units.ne_zero (M₀ := ℂ) (tt _))
  have hprod : ∏ a : Fin r, Real.sqrt ‖dmin (U.X k).Gm y ⟨_, hτ⟩ a.succ / dmin (U.X k).Gm y ⟨_, hτ⟩ a.castSucc‖ =
      A * B⁻¹ := by
    rw [prod_split (p := D.p) (q := D.q) hU.1, hA, hB, ← Finset.prod_inv_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun i _ => ?_
      have h := (hnorm ⟨τ.1, Fin.cast hp.symm i⟩ ⟨_, hτ⟩ ⟨D.q + i, by have := hU.1; omega⟩).1 rfl
        (by show D.q + (i : ℕ) = (U.X k).p0 + (i : ℕ); rw [hp0])
      rw [← h, Real.sqrt_sq (norm_nonneg _)]
    · refine Finset.prod_congr rfl fun j _ => ?_
      have hj := j.2
      have h := (hnorm ⟨ComplexEmbedding.conjugate τ.1, Fin.cast hq.symm j⟩ ⟨_, hτ⟩
        ⟨D.q - 1 - j, by have := hU.1; omega⟩).2 (GlobalTheory.AllWt.relab_conj σ τ.1).symm
        (by show D.q - 1 - (j : ℕ) + (j : ℕ) + 1 = (U.X k).p0; rw [hp0]; omega)
      rw [← inv_eq_iff_eq_inv.2 h, Real.sqrt_inv, Real.sqrt_sq (norm_nonneg _)]
  have hrd : rdU U s k y = φ ℂ yF v w := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hy, dif_pos]
    rw [hval]
    exact hread'
  have hL : GlobalTheory.AllWt.lieFacZ D x (GlobalTheory.AllWt.wtOf D (GlobalTheory.FlatLine.flatWt D τ) 0) =
      Real.exp (-(((D.q : ℝ) - D.p) / 2) * Real.log (2 * Real.pi * x)) := by
    rw [GlobalTheory.AllWt.lieFacZ, GlobalTheory.FlatLine.Model.sum_flatWt]
  rw [GlobalTheory.AllWt.homN, GlobalTheory.AllWt.ptN]
  dsimp only
  rw [GlobalTheory.FlatLine.modelWt_flatWt U hσ hU τ k hτ, pnorm_flat, hrd, hprod, hL, ← hI, dΓ, dΔ]
  have hκ : Real.pi * (2 * x) = 2 * Real.pi * x := by ring
  have hκ0 : 0 < 2 * Real.pi * x := by positivity
  have hP : 0 < ‖φ ℂ yF v w‖ := norm_pos_iff.2 hφ
  rw [hκ, Real.log_mul (pow_pos hκ0 _).ne' (pow_pos hA0 _).ne', Real.log_mul (pow_pos hκ0 _).ne' (pow_pos hB0 _).ne',
    Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]
  conv_lhs => rw [← Real.exp_log hP, ← Real.exp_log hA0, ← Real.exp_log (inv_pos.2 hB0), Real.log_inv]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

end GlobalTheory.CompanionTheory.Ar.Br
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.UnfSectionNormBoundAtHeightStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unf_section_norm_bound_at_height : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (U : Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ) (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (t : ℝ), Formalism.L2.Pj.GoodEmb c σ → Formalism.L2.Pj.IsUnf U → (∀ k (τ' : E →+* ℂ), ‖τ' (U.X k).ξ0‖ = x) → s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) → IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ t → ∀ z ∈ GlobalTheory.AllWt.framesOn U Z, (∀ hz : z.2 ∈ (U.X z.1).dom, GlobalTheory.FlatLine.Tested (U.un z.1 ⟨z.2, hz⟩)) → GlobalTheory.AllWt.homN U x (GlobalTheory.AllWt.wtOf D (GlobalTheory.FlatLine.flatWt D τ) 0) s z = Real.exp t := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.homN_eq_exp_hodge | exact GlobalTheory.CompanionTheory.Ar.Br.homN_eq_exp_hodge | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.homN_eq_exp_hodge <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LineFnReadsLocalHeightSum
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LineFnReadsLocalHeightSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.line_fn_reads_local_height_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (ρ la * Real.log ‖κ π‖)) → ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, v s = (ρ la : EReal) := by
  first | exact @PositivityTheory.Xgn.line_function_place_valuation | exact PositivityTheory.Xgn.line_function_place_valuation
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LineFnReadsLocalHeightSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_fn_reads_local_height_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H) (s : Formalism.L2.Pj.Rul Xo c) (φ : FrameFn Xo c) (ρ : HeightOneSpectrum (𝓞 c.F) → ℝ), IsLineFn (Z : Set (Xo.XF c)) τ.1 φ → Reads (Z : Set (Xo.XF c)) τ.1 s φ → (∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (la : HeightOneSpectrum (𝓞 c.F)) (π : c.F), (∀ a : c.F, la.valuation c.F a ≤ 1 ↔ ‖κ a‖ ≤ 1) → la.valuation c.F π = WithZero.exp (-1 : ℤ) → HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (ρ la * Real.log ‖κ π‖)) → ∀ la, ∀ v ∈ GlobalTheory.FlatLine.valOn Z la, v s = (ρ la : EReal) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.line_fn_reads_local_height_sum | exact GlobalTheory.CompanionTheory.Relay.line_fn_reads_local_height_sum | (intros; apply GlobalTheory.CompanionTheory.Relay.line_fn_reads_local_height_sum <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatOnModelExistsRulSections
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatOnModelExistsRulSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.CvRule

open GlobalTheory.CompanionTheory.Ar.Flat.RuleGlue

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem eq_cspB_rule {C : Set (Xo.XF c)} (hC : IsClopen C) (e : Formalism.L2.Pj.Rul Xo c)
    (he : ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F),
      (¬ Set.range (fpt z ψ) ⊆ C → ψ (e p z) = 0) ∧ (Set.range (fpt z ψ) ⊆ C → ψ (e p z) = 1)) :
    e = Formalism.L2.Pj.CompSplitPfB.cspB_rule Xo c C hC := by
  funext p z
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  refine sub_eq_zero.1 (eq_zero_of_fields _ fun F _ ψ => ?_)
  have hsp := Formalism.L2.Pj.CompSplitPfB.cspB_idem_spec C hC z.x z.x_over (kerPt ψ)
  have hid := Formalism.L2.Pj.CompSplitPfB.cspB_idem_idem C hC z.x z.x_over
  have hl : Formalism.L2.Pj.CompSplitPfB.cspB_lift z.x z.x_over = frPtF z := rfl
  rw [hl, ← range_fpt_subset_iff] at hsp
  have hi : Formalism.L2.Pj.CompSplitPfB.cspB_rule Xo c C hC p z =
      Formalism.L2.Pj.CompSplitPfB.cspB_idem C hC z.x z.x_over := rfl
  rw [hi, ψ.map_sub]
  set i := Formalism.L2.Pj.CompSplitPfB.cspB_idem C hC z.x z.x_over
  have hker : i ∉ (kerPt ψ).asIdeal ↔ ψ i ≠ 0 := Iff.rfl
  rw [hker] at hsp
  have h01 : ψ i = 0 ∨ ψ i = 1 := IsIdempotentElem.iff_eq_zero_or_one.1 (hid.map ψ)
  by_cases hr : Set.range (fpt z ψ) ⊆ C
  · rw [(he p z F ψ).2 hr]
    rcases h01 with h | h
    · exact absurd h (hsp.2 hr)
    · rw [h, sub_self]
  · rw [(he p z F ψ).1 hr]
    rcases h01 with h | h
    · rw [h, sub_self]
    · exact absurd (hsp.1 (by rw [h]; exact one_ne_zero)) hr

theorem exOf_add_detE (τ : GlobalTheory.AllWt.Psi H) (i : Formalism.L2.Pj.Ix D) :
    GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 i + (detE D τ.1 i : ℤ) =
      (detE D (ComplexEmbedding.conjugate τ.1) i : ℤ) := by
  classical
  have f1 : ∀ (τ' : GlobalTheory.AllWt.Psi H) (j : Fin (D.p + D.q)), τ' = τ → GlobalTheory.FlatLine.flatWt D τ τ' j = -1 :=
    fun τ' j h => by simp [GlobalTheory.FlatLine.flatWt, GlobalTheory.FlatLine.parWt, h]
  have f0 : ∀ (τ' : GlobalTheory.AllWt.Psi H) (j : Fin (D.p + D.q)), τ' ≠ τ → GlobalTheory.FlatLine.flatWt D τ τ' j = 0 :=
    fun τ' j h => by simp [GlobalTheory.FlatLine.flatWt, GlobalTheory.FlatLine.parWt, h]
  rcases i with _ | ⟨σ, i⟩
  · have : GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 none = 0 := rfl
    simp [this, detE, Formalism.L2.Pj.ex]
  · have hne : τ.1 ≠ ComplexEmbedding.conjugate τ.1 := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ ((DFunLike.congr_fun h.symm _).trans τ.2)
    have hex : GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 (some ⟨σ, i⟩) =
        (GlobalTheory.AllWt.wtOf D (GlobalTheory.FlatLine.flatWt D τ) 0).1 (σ, i) := rfl
    rw [hex]
    simp only [detE, Formalism.L2.Pj.ex]
    by_cases h : σ (H.rt : E) = H.rt0
    · have hm : D.mult σ = D.p := by rw [Datum.mult, if_pos h]
      have hi : (i : ℕ) < D.p := hm ▸ i.2
      have hw := GlobalTheory.AllWt.wtOf_big (GlobalTheory.FlatLine.flatWt D τ) 0 ⟨σ, h⟩ i hi
      simp only at hw
      rw [hw]
      have hc : σ ≠ ComplexEmbedding.conjugate τ.1 := fun e =>
        GlobalTheory.AllWt.conj_not_mem τ ((DFunLike.congr_fun e.symm _).trans h)
      by_cases e : σ = τ.1
      · rw [f1 _ _ (Subtype.ext e)]
        simp [e, hne]
      · rw [f0 _ _ fun h' => e (congrArg Subtype.val h')]
        simp [e, hc]
    · have h' := GlobalTheory.AllWt.conj_mem h
      have hm : D.mult σ = D.q := by rw [Datum.mult, if_neg h]
      have hi : (i : ℕ) < D.q := hm ▸ i.2
      have hw := GlobalTheory.AllWt.wtOf_small (GlobalTheory.FlatLine.flatWt D τ) 0 ⟨conjEmb σ, h'⟩ i hi
      simp only [GlobalTheory.AllWt.conjEmb_conjEmb] at hw
      rw [hw]
      have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ.1) = τ.1 :=
        GlobalTheory.AllWt.conjEmb_conjEmb τ.1
      have hσ : σ ≠ τ.1 := fun e => h (e ▸ τ.2)
      by_cases e : σ = ComplexEmbedding.conjugate τ.1
      · rw [f1 _ _ (Subtype.ext (by show conjEmb σ = τ.1; rw [e]; exact hcc))]
        simp [e, hne.symm]
      · rw [f0 _ _ fun h2 => e (by
          have h3 : conjEmb σ = τ.1 := congrArg Subtype.val h2
          rw [← h3]
          exact (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm)]
        simp [e, hσ]

theorem wchar_eq_units {S : Type} [CommRing S] (b : Formalism.L2.Pj.Ix D → ℕ) (t : Formalism.L2.Pj.Ix D → Sˣ) :
    Formalism.L2.Pj.wchar b t = ((∏ i, t i ^ (b i : ℤ) : Sˣ) : S) := by
  simp [Formalism.L2.Pj.wchar, Units.coe_prod]

theorem prod_exOf_mul {S : Type} [CommRing S] (τ : GlobalTheory.AllWt.Psi H) (t : Formalism.L2.Pj.Ix D → Sˣ) :
    ((∏ i, t i ^ GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 i : Sˣ) : S) * Formalism.L2.Pj.wchar (detE D τ.1) t =
      Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ.1)) t := by
  rw [wchar_eq_units, wchar_eq_units, ← Units.val_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_add, exOf_add_detE]

end GlobalTheory.CompanionTheory.Ar.Br.CvRule

namespace GlobalTheory.CompanionTheory.Ar.Br

open GlobalTheory.CompanionTheory.Ar.Flat.RuleGlue GlobalTheory.CompanionTheory.Ar.Br.CvRule


set_option maxHeartbeats 1600000 in
theorem exists_flat_sec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))) (τ : GlobalTheory.AllWt.Psi H) (φ : FrameFn Xo c), FlatOnModel Z' τ.1 φ → ∃ s s' : Formalism.L2.Pj.Rul Xo c, s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ s' ∈ GlobalTheory.AllWt.secZ Xo c (-GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * s' = s' ∧ s * s' = GlobalTheory.FlatLine.idem Z ∧ Reads (Z : Set (Xo.XF c)) τ.1 s φ := by
  intro E _ _ _ H D l Xo c O _ β Y Z Z' τ φ hf
  have hτ := τ.2
  have hC : IsClopen (Z : Set (Xo.XF c)) :=
    Formalism.L2.Pj.CompSplitPfB.cspB_isClopen (Formalism.L2.Pj.CompSplitPfD.cspD_comp_disj Xo c) Z
  have hl := hf.1
  obtain ⟨s, s', e, -, hss₀, hsE₀, hs'E₀, -, hval⟩ :=
    GlobalTheory.T.flat_line_idempotent_sections E H D l Xo c (Z : Set (Xo.XF c)) τ.1 O β Y Z' φ hτ hC hl hf
  have hp : D.mult τ.1 = D.p := by rw [Datum.mult, if_pos hτ]
  have hq : D.mult (ComplexEmbedding.conjugate τ.1) = D.q := conj_mult hτ
  have red : ∀ p : Formalism.L2.Pj.TRing c.F, IsReduced p.R := fun p => (Ideal.isRadical_iff_quotient_reduced _).1 p.rad
  have hss : ∀ p z, s p z * s' p z = e p z := fun p z => congrFun (congrFun hss₀ p) z
  have hsE : ∀ p z, s p z * e p z = s p z := fun p z => congrFun (congrFun hsE₀ p) z
  have hs'E : ∀ p z, s' p z * e p z = s' p z := fun p z => congrFun (congrFun hs'E₀ p) z
  have hse : ∀ (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F)
      (y : Sp F ⟶ Xo.XF c), under y = spMap ψ ≫ z.x → y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F p.R)) →
      (¬ Set.range y ⊆ (Z : Set (Xo.XF c)) → ψ (e p z) = 0 ∧ ψ (s p z) = 0) ∧
      (Set.range y ⊆ (Z : Set (Xo.XF c)) → ψ (e p z) = 1 ∧
        ∀ (v : Vecs y D.p) (w : Vecs y D.q) (hp : D.mult τ.1 = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ.1) = D.q),
          (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ.1 (i.cast hp.symm)) →
          (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ.1) (j.cast hq.symm)) →
          ψ (s p z) = φ F y v w) := fun p z F _ ψ y h1 h2 => by
    have Dv := hval p z F ψ y h1 h2
    refine ⟨fun hr => ⟨Dv.1 hr, ?_⟩, Dv.2⟩
    have := congrArg ψ (hsE p z)
    rw [map_mul, Dv.1 hr, mul_zero] at this
    exact this.symm
  have C := fun (p : Formalism.L2.Pj.TRing c.F) (z : Formalism.L2.Pj.FrPt Xo c p.R) (F : Type) [Field F] (ψ : p.R →+* F) =>
    hse p z F ψ (fpt z ψ) (fpt_under z ψ) (fpt_snd z ψ)
  have zero : ∀ (p : Formalism.L2.Pj.TRing c.F) (x : p.R), (∀ (F : Type) [Field F] (ψ : p.R →+* F), ψ x = 0) → x = 0 :=
    fun p x h => by
      haveI := red p
      exact eq_zero_of_fields x h
  have hE : e = GlobalTheory.FlatLine.idem Z := eq_cspB_rule _ e fun p z F _ ψ =>
    ⟨fun hr => ((C p z F ψ).1 hr).1, fun hr => ((C p z F ψ).2 hr).1⟩
  have hnat : ∀ (p q : Formalism.L2.Pj.TRing c.F) (f : p.R →ₐ[c.F] q.R) (y : Formalism.L2.Pj.FrPt Xo c p.R)
      (z : Formalism.L2.Pj.FrPt Xo c q.R), Formalism.L2.Pj.FrMap f y z → e q z = f (e p y) ∧ s q z = f (s p y) := fun p q f y z h => by
    have key : ∀ (F : Type) [Field F] (ψ : q.R →+* F), ψ (e q z) = ψ (f (e p y)) ∧ ψ (s q z) = ψ (f (s p y)) := by
      intro F _ ψ
      let ψ' : p.R →+* F := ψ.comp f.toRingHom
      have h1 : under (fpt z ψ) = spMap ψ' ≫ y.x := by
        rw [fpt_under, h.1, ← Category.assoc, Flat.spMap_comp']
      have h2 : fpt z ψ ≫ pullback.snd _ _ = spMap (ψ'.comp (algebraMap c.F p.R)) := by
        rw [fpt_snd]
        congr 1
        ext a
        simp [ψ']
      have D2 := hse p y F ψ' (fpt z ψ) h1 h2
      have D1 := C q z F ψ
      have e1 : ∀ x : p.R, ψ (f x) = ψ' x := fun _ => rfl
      rw [e1, e1]
      by_cases hr : Set.range (fpt z ψ) ⊆ (Z : Set (Xo.XF c))
      · obtain ⟨v, w, ev, ew, -⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ.1 q.R z F ψ (fpt z ψ) hp hq (fpt_under z ψ) (fpt_snd z ψ)
        refine ⟨by rw [(D1.2 hr).1, (D2.2 hr).1], ?_⟩
        rw [(D1.2 hr).2 v w hp hq ev ew, (D2.2 hr).2 v w hp hq (fun i => ?_) (fun j => ?_)]
        · rw [ev i, h.2.1, ← Category.assoc, dualMap_spMap_comp]
        · rw [ew j, h.2.1, ← Category.assoc, dualMap_spMap_comp]
      · rw [(D1.1 hr).1, (D1.1 hr).2, (D2.1 hr).1, (D2.1 hr).2]
        exact ⟨rfl, rfl⟩
    exact ⟨sub_eq_zero.1 (zero q _ fun F _ ψ => by rw [ψ.map_sub, (key F ψ).1, sub_self]),
      sub_eq_zero.1 (zero q _ fun F _ ψ => by rw [ψ.map_sub, (key F ψ).2, sub_self])⟩
  have hnat' : ∀ (p q : Formalism.L2.Pj.TRing c.F) (f : p.R →ₐ[c.F] q.R) (y : Formalism.L2.Pj.FrPt Xo c p.R)
      (z : Formalism.L2.Pj.FrPt Xo c q.R), Formalism.L2.Pj.FrMap f y z → s' q z = f (s' p y) := fun p q f y z h => by
    obtain ⟨h1, h2⟩ := hnat p q f y z h
    have h3 := hss q z
    have h4 := congrArg f (hss p y)
    have h5 := hs'E q z
    have h6 := congrArg f (hs'E p y)
    rw [map_mul] at h4 h6
    rw [← h2] at h4
    rw [← h1] at h4 h6
    linear_combination (f (s' p y)) * h3 - (s' q z) * h4 - h5 + h6
  have hwt : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ) (y y' : Formalism.L2.Pj.FrPt Xo c p.R),
      Formalism.L2.Pj.FrBor t y y' → e p y' = e p y ∧
        s p y' * Formalism.L2.Pj.wchar (detE D τ.1) t = s p y * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ.1)) t := fun p t y y' h => by
    have key : ∀ (F : Type) [Field F] (ψ : p.R →+* F), ψ (e p y') = ψ (e p y) ∧
        ψ (s p y' * Formalism.L2.Pj.wchar (detE D τ.1) t) = ψ (s p y * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ.1)) t) := by
      intro F _ ψ
      have h1 : under (fpt y ψ) = spMap ψ ≫ y'.x := by rw [fpt_under, h.1]
      have D2 := hse p y' F ψ (fpt y ψ) h1 (fpt_snd y ψ)
      have D1 := C p y F ψ
      rw [map_mul, map_mul]
      by_cases hr : Set.range (fpt y ψ) ⊆ (Z : Set (Xo.XF c))
      · obtain ⟨v, w, ev, ew, hfr⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ.1 p.R y F ψ (fpt y ψ) hp hq (fpt_under y ψ) (fpt_snd y ψ)
        obtain ⟨v', w', ev', ew', hfr'⟩ := GlobalTheory.T.frame_point_vectors E H D l Xo c τ.1 p.R y' F ψ (fpt y ψ) hp hq h1 (fpt_snd y ψ)
        obtain ⟨A, B, hA, hB, dA, dB⟩ := GlobalTheory.T.frame_borel_change_vectors E H D l Xo c τ.1 p.R t y y' h F ψ (fpt y ψ) hp hq v v' w w' (fpt_under y ψ) ev ew ev' ew'
        refine ⟨by rw [(D1.2 hr).1, (D2.2 hr).1], ?_⟩
        rw [(D1.2 hr).2 v w hp hq ev ew, (D2.2 hr).2 v' w' hp hq ev' ew', wchar_detE τ.1 hp, wchar_detE _ hq, map_prod, map_prod,
          ← dA, ← dB]
        exact hl.chg F _ _ v w v' w' A B (hfr _ hr) (hfr' _ hr) hA hB
      · rw [(D1.1 hr).1, (D1.1 hr).2, (D2.1 hr).1, (D2.1 hr).2]
        simp
    have k1 : e p y' - e p y = 0 := zero p _ fun F _ ψ => by rw [ψ.map_sub, (key F ψ).1, sub_self]
    have k2 : s p y' * Formalism.L2.Pj.wchar (detE D τ.1) t - s p y * Formalism.L2.Pj.wchar (detE D (ComplexEmbedding.conjugate τ.1)) t = 0 :=
      zero p _ fun F _ ψ => by
        have := (key F ψ).2
        exact (ψ.map_sub _ _).trans (sub_eq_zero.2 this)
    exact ⟨sub_eq_zero.1 k1, sub_eq_zero.1 k2⟩
  have hunitW : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ) (b : Formalism.L2.Pj.Ix D → ℕ),
      IsUnit (Formalism.L2.Pj.wchar b t) := fun p t b => IsUnit.prod_univ_iff.2 fun i => (t i).isUnit.pow _
  have hS : ∀ (p : Formalism.L2.Pj.TRing c.F) (t : Formalism.L2.Pj.Ix D → (p.R)ˣ) (y y' : Formalism.L2.Pj.FrPt Xo c p.R),
      Formalism.L2.Pj.FrBor t y y' →
        s p y' = ((∏ i, t i ^ GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 i : (p.R)ˣ) : p.R) * s p y := fun p t y y' h => by
    refine (hunitW p t (detE D τ.1)).mul_right_cancel ?_
    have h1 := (hwt p t y y' h).2
    have h2 := prod_exOf_mul τ t
    rw [h1, ← h2]
    ring
  refine ⟨s, s', GlobalTheory.AllWt.mem_secZ.2 ⟨fun p q f y z h => (hnat p q f y z h).2, hS⟩,
    GlobalTheory.AllWt.mem_secZ.2 ⟨hnat', fun p t y y' h => ?_⟩, ?_, ?_, ?_, ?_⟩
  · set T := ((∏ i, t i ^ GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0 i : (p.R)ˣ) : p.R) with hTdef
    set T' := ((∏ i, t i ^ (-GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) i : (p.R)ˣ) : p.R) with hT'def
    have hT : T' * T = 1 := by
      rw [hTdef, hT'def, ← Units.val_mul, ← Finset.prod_mul_distrib]
      simp
    have hw := hS p t y y' h
    have h1 := (hwt p t y y' h).1
    have h3 := hss p y
    have h4 := hss p y'
    have h5 := hs'E p y
    have h6 := hs'E p y'
    rw [h1] at h4 h6
    linear_combination (-1) * h6 + (-(s' p y')) * h3 + (-(s' p y') * s p y * s' p y) * hT +
      (-T' * s' p y' * s' p y) * hw + (T' * s' p y) * h4 + T' * h5
  · rw [← hE, mul_comm]; exact hsE₀
  · rw [← hE, mul_comm]; exact hs'E₀
  · rw [← hE]; exact hss₀
  · exact fun p z F _ ψ y h1 h2 hr v w hp' hq' ev ew => ((hval p z F ψ y h1 h2).2 hr).2 v w hp' hq' ev ew

end GlobalTheory.CompanionTheory.Ar.Br
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlatOnModelExistsRulSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_on_model_exists_rul_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : Formalism.L2.Pj.Comp Xo c) (Z' : CptOver Y (Z : Set (Xo.XF c))) (τ : GlobalTheory.AllWt.Psi H) (φ : FrameFn Xo c), FlatOnModel Z' τ.1 φ → ∃ s s' : Formalism.L2.Pj.Rul Xo c, s ∈ GlobalTheory.AllWt.secZ Xo c (GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ s' ∈ GlobalTheory.AllWt.secZ Xo c (-GlobalTheory.AllWt.exOf D (GlobalTheory.FlatLine.flatWt D τ) 0) ∧ GlobalTheory.FlatLine.idem Z * s = s ∧ GlobalTheory.FlatLine.idem Z * s' = s' ∧ s * s' = GlobalTheory.FlatLine.idem Z ∧ Reads (Z : Set (Xo.XF c)) τ.1 s φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec | exact GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.exists_flat_sec <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsConstSectionKroneckerChar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.CovEx

theorem exists_padic_emb (K : Type) [Field K] [NumberField K] (p : Nat.Primes) : Nonempty (K →+* ℂ_[p]) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  exact ⟨(IsAlgClosed.lift (R := ℚ) (S := K) (M := ℂ_[p]) : K →ₐ[ℚ] ℂ_[p]).toRingHom⟩

theorem goodOf_or {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (σ : c.F →+* ℂ) : Formalism.L2.Pj.goodOf c σ = σ ∨ (starRingEnd ℂ).comp (Formalism.L2.Pj.goodOf c σ) = σ := by
  unfold Formalism.L2.Pj.goodOf
  split_ifs
  · exact Or.inl rfl
  · right; ext x; simp

theorem exists_constSec : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ), GlobalTheory.FlatCore.Laws U x → ∀ [NeZero H.d]
    (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H),
    ∃ s : GlobalTheory.FlatLine.ConstSec U x Z (GlobalTheory.FlatLine.flatWt D τ) 0,
      s.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  intro hR hG E _ _ _ H D l Xo c r U x hL _ χ hχ Z τ
  have hpos := hL.pos
  obtain ⟨κ⟩ := exists_padic_emb c.F (⟨2, Nat.prime_two⟩ : Nat.Primes)
  obtain ⟨O, _, _, _, β, Y, hβ, -, -, -⟩ :=
    GlobalTheory.T.good_reduction_dvr_model_exists E H D l Xo c ⟨2, Nat.prime_two⟩ κ hpos (hL.good 2 Nat.prime_two)
  obtain ⟨hclopen, hcpt, -⟩ := GlobalTheory.T.irreducible_component_clopen E H D l Xo c (Z : Set (Xo.XF c)) Z.2
  obtain ⟨Z'⟩ := hcpt O β Y hβ
  have hgeom : Z'.IsGeom := GlobalTheory.T.geometric_component_alg_closed E H D l Xo c O β Y Z Z' hβ hL.geo
  obtain ⟨φ, hline, hflat, -⟩ := GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 hβ hpos τ.2 hgeom
  obtain ⟨hnorm, -⟩ := GlobalTheory.T.flat_first_from_resolution_and_gaga hR hG E H D l Xo c O β Y Z Z' τ.1 φ hβ hpos τ.2 hgeom hline hflat
  choose t ht ht' using fun σ => hnorm (Formalism.L2.Pj.goodOf c σ)
  have hInf : ∀ σ, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ σ (t σ) := fun σ => by
    rcases goodOf_or c σ with h | h
    · have := ht σ
      rwa [h] at this
    · have := ht' σ
      rwa [h] at this
  have hFinEx : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), ∃ t, HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ t :=
    fun p κ => GlobalTheory.T.frame_function_finite_norm hR hG E H D l Xo c O β Y Z Z' τ.1 φ p κ hβ hpos τ.2 Z.2 hgeom hflat (hL.good p p.2)
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.finite_norm_local_bound E H D l Xo c Z τ.1 φ hFinEx
  obtain ⟨hex, ⟨N, hNinf, hNfin⟩, hdict⟩ := GlobalTheory.T.local_valuation_log_norms_existence c.F (fun σ => Real.exp (t σ)) ρ
  have hinfN : ∀ s, HasInfNorm (Z : Set (Xo.XF c)) τ.1 φ s (N.inf s) := fun s => by
    rw [hNinf s, Real.log_exp]
    exact hInf s
  have hfinN : ∀ (p : Nat.Primes) (κ : c.F →+* ℂ_[p]), HasFinNorm (Z : Set (Xo.XF c)) τ.1 φ p κ (N.fin p κ) :=
    fun p κ => by
      obtain ⟨la, π, h1, h2⟩ := hex p κ
      rw [hNfin p κ la π h1 h2]
      exact hρ p κ la π h1 h2
  obtain ⟨hadel, hdeg⟩ := GlobalTheory.T.kronecker_character_frame_bound hR hG E H D l Xo c O β Y _ Z' τ.1 φ N χ hχ hβ hpos τ.2 hclopen hgeom hflat
    hinfN hfinN
  obtain ⟨hsupp, hline'⟩ := hdict N hNinf hNfin
  obtain ⟨s, s', hs, hs', hi, hi', hm, hread⟩ := GlobalTheory.T.flat_on_model_exists_rul_sections E H D l Xo c O β Y Z Z' τ φ hflat
  have hval := GlobalTheory.T.line_fn_reads_local_height_sum E H D l Xo c Z τ s φ ρ hline hread hρ
  have hPts := GlobalTheory.FlatLine.hasPts U hpos hL.good hL.unf Z
  refine ⟨{ sig := s, inv := s', sig_mem := hs, inv_mem := hs', idem_sig := hi, idem_inv := hi', mul_inv := hm,
            cInf := fun σ => Real.exp (t σ), cInf_pos := fun σ => Real.exp_pos _,
            norm_inf := fun σ => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨(hPts.1 σ).1, fun z hz =>
              GlobalTheory.T.unf_section_norm_bound_at_height E H D l Xo c r (Formalism.L2.Pj.goodOf c σ) (U (Formalism.L2.Pj.goodOf c σ)) x Z τ s φ (t σ)
                (Formalism.L2.Pj.goodEmb_goodOf c σ) (hL.unf _ (Formalism.L2.Pj.goodEmb_goodOf c σ))
                (hL.xi _ (Formalism.L2.Pj.goodEmb_goodOf c σ)) hs hline hread (ht σ) z hz ((hPts.1 σ).2 z hz)⟩,
            rho_vw := ρ,
            val_fin := fun w => GlobalTheory.FlatLine.image_eq_singleton_iff.2 ⟨hPts.2 w, fun v hv => by
              simpa using hval w v hv⟩,
            finite_rho := hsupp.1 hadel }, ?_⟩
  exact (hline' hadel).symm.trans hdeg

end GlobalTheory.CompanionTheory.Ar.Br.CovEx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ExistsConstSectionKroneckerCharStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_section_kronecker_char : Geo.ResK.ResKStatement → GagaSections → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.Pj.Unf Xo c σ r) (x : ℝ), GlobalTheory.FlatCore.Laws U x → ∀ [NeZero H.d] (χ : DirichletCharacter ℂ H.d), GlobalTheory.IsKroneckerChar χ → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (τ : GlobalTheory.AllWt.Psi H), ∃ s : GlobalTheory.FlatLine.ConstSec U x Z (GlobalTheory.FlatLine.flatWt D τ) 0, s.deg = ((D.p : ℝ) - D.q) / 2 * (GlobalTheory.CM.logOm E χ).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Br.CovEx.exists_constSec | exact GlobalTheory.CompanionTheory.Ar.Br.CovEx.exists_constSec | (intros; apply GlobalTheory.CompanionTheory.Ar.Br.CovEx.exists_constSec <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Br

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br

theorem flatDegreeSt_of_resK_gaga : Geo.ResK.ResKStatement → GagaSections → GlobalTheory.FlatCore.FlatDegreeSt := by
  intro hR hG E _ _ _ H _ _ χ hχ Dw l Xo c r U x hL Z τ
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_const_section_kronecker_char hR hG E H Dw l Xo c r U x hL χ hχ Z τ
  let t : GlobalTheory.FlatLine.FlatSec U x Z τ := s.relat (GlobalTheory.FlatLine.flDefect_vw Dw c τ)
    (by simpa using GlobalTheory.FlatLine.finite_flDefect_vw (Dw := Dw) (c := c) τ)
  have ht : t.deg = GlobalTheory.FlatLine.flatDegVal Dw (GlobalTheory.CM.logOm E χ).re := by
    have h2 := GlobalTheory.FlatLine.ConstSec.deg_relat s (GlobalTheory.FlatLine.flDefect_vw Dw c τ)
      (by simpa using GlobalTheory.FlatLine.finite_flDefect_vw (Dw := Dw) (c := c) τ)
    simp only [Pi.zero_apply, zero_sub, neg_mul, finsum_neg_distrib, GlobalTheory.FlatLine.sum_flDefect_vw] at h2
    show (s.relat _ _).deg = _
    rw [h2, hs, GlobalTheory.FlatLine.flatDegVal]; ring
  refine ⟨⟨t⟩, fun s' => ?_⟩
  rw [GlobalTheory.FlatLine.ConstSec.deg_eq hL.unf hL.geo t s', ht, neg_neg]

end GlobalTheory.CompanionTheory.Ar.Br
end
end

theorem FlatDegreeResidue.flatDegreeSt_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → GlobalTheory.FlatCore.FlatDegreeSt :=
  fun h => GlobalTheory.CompanionTheory.Ar.Br.flatDegreeSt_of_resK_gaga h GlobalTheory.CompanionTheory.Gaga.gagaSections
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatDegreeHypotheses
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.FlatDegreeHypotheses : Prop :=  _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.CanonicalExtensionRankOne → GlobalTheory.Published.PrismaticDieudonneHodge → FlatDegreeSt
end
end

section
theorem UpperTheory.Lit.Flat.flat_tensor_swap_isIso : _root_.GlobalTheory.T.FlatDegreeHypotheses :=
  fun _ _ _ => FlatDegreeResidue.flatDegreeSt_of_resK PositivityTheory.ResPlug.FromRes.resK
end
