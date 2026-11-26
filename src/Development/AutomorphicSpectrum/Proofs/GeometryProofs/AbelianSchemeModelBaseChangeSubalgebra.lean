module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TheoremOfCubeTwoProjectiveFactors
public import Development.WeilBound.CoreStatements.SesquilinearFractions.GPureSpan
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsOpenImmersionQuotient
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LevClauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemePointObject
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.ExistsGoodLevel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspCorrespondenceBound
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPowerSectionOfChartFunctions
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperGroupGermFiniteSubscheme

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebra
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebra
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem model_passes_to_subalgebra : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] (A₀ : Over (Sp k)) [GrpObj A₀] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap (algebraMap k V)) φ → ∀ R : Subalgebra k V, ∃ (_ : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R))))) (φ₁ : A.left ⟶ pullback A₀.hom (spMap (algebraMap k R))), IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R)) (pullback.fst _ _) ∧ IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) (spMap R.val.toRingHom) φ₁ ∧ φ₁ ≫ pullback.fst _ _ = φ := by
  intro k V _ _ _ A _ A₀ _ φ h R
  have es : spMap R.val.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k V) := by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  have w : φ ≫ A₀.hom = (A.hom ≫ spMap R.val.toRingHom) ≫ spMap (algebraMap k R) := by
    rw [Category.assoc, es]; exact h.1.w
  let inst : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) :=
    inferInstanceAs (GrpObj ((Over.pullback (spMap (algebraMap k R))).obj A₀))
  have h₁ : IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R))
      (pullback.fst _ _) := isGrpPullback_pullback A₀ (spMap (algebraMap k R))
  have hf : pullback.lift φ (A.hom ≫ spMap R.val.toRingHom) w ≫ pullback.fst _ _ = φ := pullback.lift_fst _ _ _
  refine ⟨inst, pullback.lift φ (A.hom ≫ spMap R.val.toRingHom) w, h₁, ?_, hf⟩
  exact IsGrpPullback.cancel h₁ (h.congr es.symm hf.symm) (pullback.lift_snd _ _ _)

end GlobalTheory.CompanionTheory.Ar.Approx
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebraStatement
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_model_baseChange_subalgebra : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (A : Over (Sp V)) [GrpObj A] (A₀ : Over (Sp k)) [GrpObj A₀] (φ : A.left ⟶ A₀.left), IsGrpPullback A A₀ (spMap (algebraMap k V)) φ → ∀ R : Subalgebra k V, ∃ (_ : GrpObj (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R))))) (φ₁ : A.left ⟶ pullback A₀.hom (spMap (algebraMap k R))), IsGrpPullback (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) A₀ (spMap (algebraMap k R)) (pullback.fst _ _) ∧ IsGrpPullback A (Over.mk (pullback.snd A₀.hom (spMap (algebraMap k R)))) (spMap R.val.toRingHom) φ₁ ∧ φ₁ ≫ pullback.fst _ _ = φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra | exact GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.model_passes_to_subalgebra <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivOfSectionOfLocallyTriv
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem triv_of_section_of_locally_triv : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X), e ≫ p = 𝟙 S → (∀ U : S.Opens, IsIso (p.app U)) → ∀ M : LB X, M.IsLB → GlobalTheory.AbLaw.Triv (M.pull e) → (∀ x : S, ∃ U : S.Opens, x ∈ U ∧ GlobalTheory.AbLaw.Triv (M.pull (p ⁻¹ᵁ U).ι)) → GlobalTheory.AbLaw.Triv M :=
  fun _ _ p e he hp _ hM h₀ loc =>
    GlobalTheory.CubeGlue.triv_of_locally_triv hM p e he (GlobalTheory.CubeGlue.surjective_restrict p hp) h₀ loc

end GlobalTheory.CompanionTheory.Ar.Approx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodsSpanPureDecomposition
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodsSpanPureDecomposition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_pure_vectors_periods_span_of_finite_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (n : ℕ), 0 < n → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ k, s k • P (a k) := by
  exact @PositivityTheory.Xgf.periods_span_pure_decomposition

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodsSpanPureDecompositionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periods_span_pure_decomposition : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P) (n : ℕ), 0 < n → (∀ y : D.La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → g = Module.finrank ℚ E / 2 * (D.p + D.q) ∧ ∃ (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ k, s k • P (a k) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_pure_vectors_periods_span_of_finite_index | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_pure_vectors_periods_span_of_finite_index | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_pure_vectors_periods_span_of_finite_index <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverRestrictInt
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverRestrictInt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem isProjOver_comp_spMap_int : ∀ (o : Type) [CommRing o] [Module.Finite ℤ o] (X : Scheme.{0}) (s : X ⟶ Sp o),
    IsProjOver s → IsProjOver (s ≫ spMap (Int.castRingHom o)) := by
  intro o _ _ X s hs
  have hfin : IsFinite (spMap (Int.castRingHom o)) := by
    have he : Int.castRingHom o = algebraMap ℤ o := RingHom.ext_int _ _
    rw [he]
    show IsFinite (Spec.map (CommRingCat.ofHom (algebraMap ℤ o)))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact GlobalTheory.QuotModel.isProjOver_comp_spMap _ s hfin hs

end GlobalTheory.CompanionTheory.Ar.XR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverRestrictIntStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_over_restrict_int : ∀ (o : Type) [CommRing o] [Module.Finite ℤ o] (X : Scheme.{0}) (s : X ⟶ Sp o), IsProjOver s → IsProjOver (s ≫ spMap (Int.castRingHom o)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int | exact GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.isProjOver_comp_spMap_int <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrincipalDim
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SabModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isPrincipal_dim {K : Type} [Field K] {t : SAB H (Sp K)} (_h : IsPrincipal t) :
    ∃ d, SmoothOfRelativeDimension d t.G.hom := by
  letI := t.grp
  haveI hs : IsSemiAbelian t.G := t.semi
  haveI : Smooth t.G.hom := hs.smooth
  haveI : GeometricallyConnected t.G.hom := hs.geomConnected
  have hc := t.G.hom.isConnected_preimage_singleton (IsLocalRing.closedPoint K)
  have hu : t.G.hom ⁻¹' {IsLocalRing.closedPoint K} = Set.univ := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  haveI : PreconnectedSpace t.G.left := ⟨by rw [← hu]; exact hc.isPreconnected⟩
  exact exists_dim_of_preconnected t.G.hom hc.nonempty.some

def pol {K : Type} [Field K] (t : SAB H (Sp K)) (h : IsPrincipal t) : Out.PolAV (Sp K) where
  A := t.G
  isAb := ⟨inferInstance, t.semi.smooth, h.1, t.semi.geomConnected⟩
  g := (isPrincipal_dim h).choose
  smoothDim := (isPrincipal_dim h).choose_spec
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := h.2.1
  ktriv := h.2.2

end GlobalTheory.CompanionTheory.Ar.SabModel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicPointsOfComponent
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicPointsOfComponent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Flat.LabConst

theorem valAt_const {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (hg : IsCptGen ξ)
    {O : Type} [CommRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O))
    (hs : ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) {R : Type} [CommRing R] [IsLocalRing R]
    (z : Spec (CommRingCat.of R) ⟶ X) (ρ : O →+* R) (hz : z ≫ s = Spec.map (CommRingCat.ofHom ρ)) (o : O) (r : R)
    (h : ValAt ξ z (algebraMap O Ω o) r) : r = ρ o := by
  obtain ⟨hsp, t, ht, rfl⟩ := h
  have hg' := ConstReg.genMap_germ_const ξ s hs ⟨centre z, hsp⟩ o
  have ht' := hg.inj ⟨centre z, hsp⟩ (ht.trans hg'.symm)
  rw [ht']
  have h1 : X.presheaf.germ ⊤ (centre z) trivial ≫ Scheme.stalkClosedPointTo z =
      z.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    refine (Scheme.germ_stalkClosedPointTo z ⊤ trivial).trans ?_
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appTop]
    congr 1
  have h1' := congrArg (fun q => q.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) h1
  refine h1'.trans ?_
  have h2 : z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := by
    rw [← hz]; simp only [Scheme.Hom.comp_appTop]; rfl
  have h3 := congrArg (fun q => q.hom o) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ))
  have h3' : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (ρ o) =
      (Spec.map (CommRingCat.ofHom ρ)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o) := h3
  show (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (z.appTop.hom (s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o))) = ρ o
  rw [h2, ← h3']
  simp

theorem const_of_root {n : ℕ} (f : (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (p : Polynomial ℤ) (hp : p.Monic)
    (hr : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, Polynomial.aeval (f b) p = 0)
    {b b' : Fin n → ℂ} (hb : b ∈ Metric.ball (0 : Fin n → ℂ) 1) (hb' : b' ∈ Metric.ball (0 : Fin n → ℂ) 1) :
    f b = f b' := by
  have hne : p.map (Int.castRingHom ℂ) ≠ 0 := (hp.map _).ne_zero
  have hfin : ((p.map (Int.castRingHom ℂ)).rootSet ℂ).Finite := Polynomial.rootSet_finite _ _
  haveI : Finite ((p.map (Int.castRingHom ℂ)).rootSet ℂ) := hfin
  haveI : DiscreteTopology ((p.map (Int.castRingHom ℂ)).rootSet ℂ) := inferInstance
  refine IsPreconnected.constant_of_mapsTo (convex_ball _ _).isPreconnected
    (T := (p.map (Int.castRingHom ℂ)).rootSet ℂ) ⟨inferInstance⟩ hf.continuousOn (fun x hx => ?_) hb hb'
  rw [Polynomial.mem_rootSet]
  refine ⟨hne, ?_⟩
  have h := hr x hx
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, algebraMap_int_eq] at h
  rw [Polynomial.coe_aeval_eq_eval]
  exact h

theorem labVal_const_of_isHolPts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (R : Type) [CommRing R] (jj : Sp R ⟶ 𝔐.X) (n : ℕ) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Flat.IsHolPts (Metric.ball 0 1) ψ → ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ), (∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.LabVal (spMap (ψ b) ≫ jj) id σ) ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 R _ jj n ψ hψ
  have hB : ∀ b : Fin n → ℂ, ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ),
      𝔐.LabVal (spMap (ψ b) ≫ jj) id σ ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
    intro b
    obtain ⟨σ, h1, -, -, -, -, h6⟩ := GlobalTheory.T.cusp_correspondence_bound E H D l Xo c Y S Ω K J y 𝔐 ℂ (spMap (ψ b) ≫ jj)
    obtain ⟨h7, h8, -⟩ := h6 (RingHom.id ℂ)
    exact ⟨σ, h1, by simpa using h7, by simpa using h8⟩
  choose σ hσ hc1 hc2 using hB
  obtain ⟨ρ, hρ⟩ : ∃ ρ : 𝓞 c.F →+* R, spMap ρ = jj ≫ 𝔐.f ≫ Y.s :=
    ⟨(Spec.preimage (jj ≫ 𝔐.f ≫ Y.s)).hom, by simp [spMap]⟩
  letI : Algebra (𝓞 c.F) Ω := (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)).toAlgebra
  have key : ∀ (s : CMType H ⊕ CMType H) (a : 𝓞 E), ∃ r : R, ∀ b, σ b s a = ψ b r := by
    intro s a
    have hint : IsIntegral ℤ (labelEmb c s a) :=
      (NumberField.RingOfIntegers.isIntegral a).map (labelEmb c s).toIntAlgHom
    refine ⟨ρ (IsIntegralClosure.mk' (𝓞 c.F) _ hint), fun b => ?_⟩
    refine valAt_const 𝔐.ξ 𝔐.tie.gen (𝔐.f ≫ Y.s) 𝔐.cst_over (spMap (ψ b) ≫ jj) ((ψ b).comp ρ) ?_ _ _ ?_
    · rw [Category.assoc, ← hρ]; simp [spMap]
    · have h := hσ b s a
      have he : algebraMap (𝓞 c.F) Ω (IsIntegralClosure.mk' (𝓞 c.F) _ hint) = 𝔐.emb (id s) a := by
        show 𝔐.cst (algebraMap (𝓞 c.F) c.F (IsIntegralClosure.mk' (𝓞 c.F) _ hint)) = 𝔐.cst (labelEmb c s a)
        rw [IsIntegralClosure.algebraMap_mk']
      rw [he]; exact h
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hconst : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, σ b = σ 0 := by
    intro b hb
    funext s
    refine RingHom.ext fun a => ?_
    obtain ⟨r, hr⟩ := key s a
    obtain ⟨p, hpm, hpe⟩ := NumberField.RingOfIntegers.isIntegral a
    refine const_of_root (fun b => σ b s a) ?_ p hpm ?_ hb h0
    · have : (fun b => σ b s a) = fun b => ψ b r := funext hr
      rw [this]; exact hψ.2 r
    · intro x _
      have h1 : Polynomial.aeval a p = 0 := hpe
      have h2 : Polynomial.aeval (σ x s a) p = (σ x s).toIntAlgHom (Polynomial.aeval a p) :=
        Polynomial.aeval_algHom_apply (σ x s).toIntAlgHom a p
      rw [h2, h1, map_zero]
  refine ⟨σ 0, fun b hb => ?_, hc1 0, hc2 0⟩
  rw [← hconst b hb]
  exact hσ b

end GlobalTheory.CompanionTheory.Ar.Flat.LabConst
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicPointsOfComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_points_of_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (R : Type) [CommRing R] (jj : Sp R ⟶ 𝔐.X) (n : ℕ) (ψ : (Fin n → ℂ) → (R →+* ℂ)), Flat.IsHolPts (Metric.ball 0 1) ψ → ∃ σ : CMType H ⊕ CMType H → (𝓞 E →+* ℂ), (∀ b ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.LabVal (spMap (ψ b) ≫ jj) id σ) ∧ IsCMFam (fun τ => σ (.inl τ)) ∧ IsCMFam (fun τ => σ (.inr τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LabConst.labVal_const_of_isHolPts | exact GlobalTheory.CompanionTheory.Ar.Flat.LabConst.labVal_const_of_isHolPts | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LabConst.labVal_const_of_isHolPts <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumMulFG
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

variable {X : Scheme.{0}}

structure FG (M : LB X) (Y : Scheme.{0}) where

  K : Type
  [fin : Fintype K]

  φ : K → (Y ⟶ X)

  ε : K → ℤ

  t : LB.Gen (LB.LinComb M φ ε)
  ht : t.IsGen

attribute [instance] FG.fin

namespace FG

variable {M : LB X} {Y Y' Z : Scheme.{0}}

def sum (a : FG M Y) (U : Type) [CommGroup U] (h : (Y ⟶ X) → U) : U := ∏ k, h (a.φ k) ^ a.ε k

def v (a : FG M Y) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) : (Z.presheaf.stalk z)ˣ := val a.t r z J

def one : FG M Y := ⟨PEmpty, PEmpty.elim, PEmpty.elim, LB.oneGen M, fun _ _ => (map_one _).trans
  ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm⟩

def mul (a b : FG M Y) : FG M Y :=
  ⟨a.K ⊕ b.K, Sum.elim a.φ b.φ, Sum.elim a.ε b.ε, LB.mulGen M _ _ _ _ a.t b.t,
    DVR.mulGen_isGen _ _ _ _ _ _ _ a.ht b.ht⟩

def inv (a : FG M Y) : FG M Y := ⟨a.K, a.φ, fun k => -a.ε k, LB.invGen M _ _ a.t, DVR.invGen_isGen _ _ _ _ a.ht⟩

def pull (a : FG M Y) (h : Y' ⟶ Y) : FG M Y' :=
  ⟨a.K, fun k => h ≫ a.φ k, a.ε, LB.pullGen M _ _ a.t h, DVR.pullGen_isGen _ _ _ _ a.ht h⟩

def pow (a : FG M Y) (n : ℕ) : FG M Y := Nat.rec one (fun _ b => b.mul a) n

theorem pow_zero' (a : FG M Y) : a.pow 0 = one := rfl

theorem pow_succ' (a : FG M Y) (n : ℕ) : a.pow (n + 1) = (a.pow n).mul a := rfl

variable (U : Type) [CommGroup U]

@[simp] theorem sum_one (h : (Y ⟶ X) → U) : (one : FG M Y).sum U h = 1 := by
  show ∏ k : PEmpty, _ = _
  exact Fintype.prod_empty _

@[simp] theorem sum_mul (a b : FG M Y) (h : (Y ⟶ X) → U) : (a.mul b).sum U h = a.sum U h * b.sum U h :=
  Fintype.prod_sum_type _

@[simp] theorem sum_inv (a : FG M Y) (h : (Y ⟶ X) → U) : a.inv.sum U h = (a.sum U h)⁻¹ :=
  (Finset.prod_congr rfl fun k _ => zpow_neg _ _).trans (Finset.prod_inv_distrib _)

@[simp] theorem sum_pull (a : FG M Y) (g : Y' ⟶ Y) (h : (Y' ⟶ X) → U) :
    (a.pull g).sum U h = a.sum U (fun q => h (g ≫ q)) := rfl

@[simp] theorem sum_pow (a : FG M Y) (n : ℕ) (h : (Y ⟶ X) → U) : (a.pow n).sum U h = a.sum U h ^ n := by
  induction n with
  | zero => simp [pow_zero']
  | succ n ih => simp [pow_succ', ih, pow_succ]

variable {z : Z} {J : (Z ⟶ X) → M.ι}

@[simp] theorem v_one (r : Z ⟶ Y) : (one : FG M Y).v r z J = 1 := val_one r

theorem v_mul (hJ : Good M z J) (a b : FG M Y) (r : Z ⟶ Y) : (a.mul b).v r z J = a.v r z J * b.v r z J :=
  val_mul hJ _ _ r

@[simp] theorem v_inv (a : FG M Y) (r : Z ⟶ Y) : a.inv.v r z J = (a.v r z J)⁻¹ := val_inv _ r

theorem v_pull (hJ : Good M z J) (a : FG M Y) (h : Y' ⟶ Y) (r : Z ⟶ Y') : (a.pull h).v r z J = a.v (r ≫ h) z J :=
  val_pull hJ _ h r

theorem v_pow (hJ : Good M z J) (a : FG M Y) (n : ℕ) (r : Z ⟶ Y) : (a.pow n).v r z J = a.v r z J ^ n := by
  induction n with
  | zero => simp [pow_zero']
  | succ n ih => rw [pow_succ', v_mul hJ, ih, pow_succ]

theorem exists_unit (hM : M.IsLB) (a : FG M Y) (h : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), a.sum U h = 1) :
    ∃ e : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J → a.v r z J = gm r z ⊤ e := by
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ := a.φ) (ε := a.ε) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
    (fun U _ k => (h U k).trans (Fintype.prod_empty _).symm) a.t a.ht
  have le : (⊤ : Y.Opens) ≤ LB.wchart M (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s (PEmpty.elim : PEmpty → M.ι)), fun Z r z J hJ => ?_⟩
  exact ((hv Z r z J hJ).symm.trans (val_of t r z J PEmpty.elim (fun k => k.elim))).trans (gm_res r z le trivial _).symm

theorem v_const (hM : M.IsLB) (a : FG M Y) (h : ∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), a.sum U h = 1)
    {S₀ : Scheme.{0}} (p : Y ⟶ S₀) (hp : Function.Surjective p.appTop.hom) {r r' : Z ⟶ Y} (e : r ≫ p = r' ≫ p)
    (hJ : Good M z J) : a.v r z J = a.v r' z J := by
  obtain ⟨c, hc⟩ := exists_unit hM a h
  obtain ⟨b, hb⟩ := hp c.val
  have key : ∀ r : Z ⟶ Y, (a.v r z J).val = gs (r ≫ p) z ⊤ b := fun r => by
    rw [hc Z r z J hJ, ← gs_unit r z ⊤ trivial, ← hb]
    exact gs_pull r p z ⊤ trivial b
  exact Units.ext ((key r).trans (by rw [e]; exact (key r').symm))

end FG

end GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl

section Pts
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem left_pow {T : Over S} (a : T ⟶ G) (N : ℕ) : a.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (a ^ N).left := by
  rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]

theorem one_left (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ eSec G := by
  have e : (1 : T ⟶ G) = toUnit T ≫ η[G] := Hom.one_def
  rw [e, Over.comp_left, eSec]
  congr 1

end Pts

def rigFG {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) : FG P.L (𝟙_ (Over S)).left :=
  ⟨PUnit, fun _ => eSec G, fun _ => 1, P.rig, P.rigGen⟩

@[simp] theorem sum_rigFG {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) (U : Type) [CommGroup U]
    (h : ((𝟙_ (Over S)).left ⟶ G.left) → U) : (rigFG P).sum U h = h (eSec G) := by
  show ∏ _k : PUnit, h (eSec G) ^ (1 : ℤ) = _
  simp

def mulFG {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : LB G.left} {N : ℕ}
    (w : LB.Gen (LB.LinComb M (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen) :
    FG M G.left := ⟨Fin 2, _, _, w, hw⟩

theorem sum_mulFG {S : Scheme.{0}} {G : Over S} [GrpObj G] {M : LB G.left} {N : ℕ}
    (w : LB.Gen (LB.LinComb M (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)])) (hw : w.IsGen)
    (U : Type) [CommGroup U] (h : (G.left ⟶ G.left) → U) :
    (mulFG w hw).sum U h = h ((𝟙 G : G ⟶ G) ^ N).left * (h (𝟙 G.left) ^ (N ^ 2))⁻¹ := by
  show ∏ k : Fin 2, h ((![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) k) ^ (![1, -((N : ℤ) ^ 2)] : Fin 2 → ℤ) k = _
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
  norm_cast

end GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Transl
theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap (f.comp g) = spMap f ≫ spMap g := by
  show Spec.map (CommRingCat.ofHom (f.comp g)) = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem gc_spMap {R : Type} [CommRing R] {F : Type} [Field F] (g : R →+* F) (z : Sp F) (t : R) :
    GlobalTheory.TwistLoc.gc (spMap g) z t = toStk z (g t) := by
  show gs (spMap g) z ⊤ _ = _
  rw [gs_eq _ z ⊤ trivial]
  show _ = ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (g t))
  exact congrArg _ (congrArg (fun φ => φ.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm

end GlobalTheory.CompanionTheory.Ar.Sl.Transl
end
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperGroupGermFiniteSubschemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_group_germ_finite_subscheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left →
    ∃ (A' : Type) (_ : CommRing A') (_ : HopfAlgebra k A') (_ : Coalgebra.IsCocomm k A') (_ : Module.Finite k A'),
      Module.finrank k A' = Module.finrank k A ∧
      ∃ (D : LinearMap.ker (Matrix.toLin' (rho g.B a)) →ₗ[k] (A' →ₗ[k] k))
        (T : LinearMap.ker (Matrix.toLin' (rho g.B (star a))) →ₗ[k] A'),
        Function.Injective D ∧ Function.Injective T ∧
        (∀ u f f', D u (f * f') = D u f * Coalgebra.counit (R := k) f' + Coalgebra.counit (R := k) f * D u f') ∧
        (∀ z, Coalgebra.comul (R := k) (T z) = T z ⊗ₜ[k] (1 : A') + (1 : A') ⊗ₜ[k] T z) ∧
        ∀ (u : LinearMap.ker (Matrix.toLin' (rho g.B a))) (z : LinearMap.ker (Matrix.toLin' (rho g.B (star a)))),
          (z : Fin d → k) ⬝ᵥ (bil (g.B.ad a) 1 1).transpose.mulVec (u : Fin d → k) = 0 → D u (T z) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom | exact GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom <;> assumption)
end
