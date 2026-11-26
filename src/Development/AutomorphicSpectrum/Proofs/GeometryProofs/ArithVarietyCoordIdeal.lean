module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateNormComparison
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLiftClosedImmersionOfDense

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdeal
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdeal
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num.ConstClosure

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type} {x : κ → Ω}

theorem exists_chart_div (h : CoordTie ℤ ξ x) :
    ∃ c, x c ≠ 0 ∧ ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b := by
  let η : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := h.cover η
  refine ⟨c, hc.1, fun ω => ?_⟩
  obtain ⟨U, hU, hmem⟩ := h.affine c hc.1
  have hη : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, hc⟩
  have key : ∀ r : Γ(X, U), (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη r) ∈
      Algebra.adjoin ℤ (Set.range fun j => x j / x c) := by
    intro r
    refine (h.ring c hc.1 _).2 fun p hp => ?_
    have hpU : p.1 ∈ U := (hmem p.1).2 ⟨p.2, hp⟩
    exact ⟨X.presheaf.germ U p.1 hpU r, genMap_germ_eq_stalk_closed ξ p U hpU hη r⟩
  obtain ⟨b, rfl⟩ : ∃ b : X.presheaf.stalk (genPt ξ), (Scheme.stalkClosedPointTo ξ).hom b = ω := h.gen.bij.2 ω
  obtain ⟨r, t, hrt, hunit⟩ := stalk_eq_germ_div_of_affine hU ⟨genPt ξ, hη⟩ b
  replace hrt : b * X.presheaf.germ U (genPt ξ) hη t = X.presheaf.germ U (genPt ξ) hη r := hrt
  replace hunit : IsUnit (X.presheaf.germ U (genPt ξ) hη t) := hunit
  have hne : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hη t) ≠ 0 :=
    (hunit.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨_, _, key r, key t, hne, ?_⟩
  rw [eq_div_iff hne]
  exact ((Scheme.stalkClosedPointTo ξ).hom.map_mul _ _).symm.trans
    (congrArg (Scheme.stalkClosedPointTo ξ).hom hrt)

theorem adjoin_le_subfield (F : Subfield Ω) {c : κ} (h : ∀ j, x j / x c ∈ F) {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c)) : a ∈ F := by
  induction ha using Algebra.adjoin_induction with
  | mem t ht => obtain ⟨j, rfl⟩ := ht; exact h j
  | algebraMap n => simpa using intCast_mem F n
  | add s t _ _ hs ht => exact add_mem hs ht
  | mul s t _ _ hs ht => exact mul_mem hs ht

theorem subfield_eq_top {c : κ} (hc : ∀ ω : Ω, ∃ a b : Ω, a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧
      b ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) ∧ b ≠ 0 ∧ ω = a / b)
    (F : Subfield Ω) (h : ∀ j, x j / x c ∈ F) : F = ⊤ := by
  refine eq_top_iff.2 fun ω _ => ?_
  obtain ⟨a, b, ha, hb, -, rfl⟩ := hc ω
  exact div_mem (adjoin_le_subfield F h ha) (adjoin_le_subfield F h hb)

end Chart

section Field

variable {Ω : Type} [Field Ω]

theorem charZero_of_isArithVar {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
    {y : (Σ k, J k) → Ω} {n : ℕ} (h : IsArithVar (mCoordIdeal y) n) : CharZero Ω := by
  obtain ⟨-, -, hH, -⟩ := h
  refine charZero_of_inj_zero fun n hn => ?_
  have hmem : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing J) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker]
    have e : mConeMap y (C (n : ℤ)) = C (n : Ω) := by
      simp [mConeMap, aeval_C]
    rw [e, hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing J) = ⊥ from hH] at hmem
  simpa using hmem

theorem dedekind_finite_of_finite [CharZero Ω] (hf : FiniteDimensional ℚ (algebraicClosure ℚ Ω))
    (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] :
    IsDedekindDomain A ∧ Module.Finite ℤ A := by
  let L := algebraicClosure ℚ Ω
  have hmem : ∀ a : A, algebraMap A Ω a ∈ L := fun a =>
    mem_algebraicClosure_iff'.2 ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩).tower_top
  letI : Algebra A L := ((algebraMap A Ω).codRestrict L.toSubalgebra.toSubring hmem).toAlgebra
  have hcoe : ∀ a : A, ((algebraMap A L a : L) : Ω) = algebraMap A Ω a := fun _ => rfl
  haveI : IsScalarTower ℤ A L := inferInstance
  haveI : NumberField L := ⟨⟩
  haveI : IsIntegralClosure A ℤ L := by
    refine ⟨fun a b hab => IsIntegralClosure.algebraMap_injective A ℤ Ω ?_, fun {v} => ?_⟩
    · rw [← hcoe, ← hcoe, hab]
    · rw [← isIntegral_algebraMap_iff (A := L) (B := Ω) (R := ℤ) ]
      rw [IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ) (B := Ω)]
      constructor
      · rintro ⟨a, ha⟩
        exact ⟨a, Subtype.ext ha⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, rfl⟩
  haveI : IsDomain A := (IsIntegralClosure.algebraMap_injective A ℤ Ω).isDomain _
  exact ⟨IsIntegralClosure.isDedekindDomain ℤ ℚ L A, IsIntegralClosure.finite ℤ ℚ L A⟩

end Field

section Local

variable {Ω : Type} [Field Ω]

theorem isIntegrallyClosedIn_of_atPrime (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω]
    (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω]
    [IsScalarTower A O Ω] : IsIntegrallyClosedIn O Ω := by
  have hA := IsIntegralClosure.algebraMap_injective A ℤ Ω
  have hs : ∀ s : m.primeCompl, algebraMap A Ω s ≠ 0 := fun s h0 =>
    s.2 (by rw [hA (h0.trans (map_zero _).symm)]; exact m.zero_mem)
  refine isIntegrallyClosedIn_iff.2 ⟨?_, fun {w} hw => ?_⟩
  · refine (injective_iff_map_eq_zero _).2 fun o ho => ?_
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj m.primeCompl o
    have e' := congrArg (algebraMap O Ω) e
    simp only [map_mul, ho, zero_mul, ← IsScalarTower.algebraMap_apply] at e'
    have ha : a = 0 := hA (e'.symm.trans (map_zero _).symm)
    rw [ha, map_zero] at e
    exact (IsLocalization.map_units O s).mul_left_eq_zero.1 e
  · obtain ⟨s, hsw⟩ := IsIntegral.exists_multiple_integral_of_isLocalization m.primeCompl w hw
    haveI : Algebra.IsIntegral ℤ A := IsIntegralClosure.isIntegral_algebra ℤ Ω
    have hz : IsIntegral ℤ (s • w) := isIntegral_trans _ hsw
    obtain ⟨a, ha⟩ := (IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).1 hz
    refine ⟨IsLocalization.mk' O a s, ?_⟩
    have h1 : algebraMap O Ω (IsLocalization.mk' O a s) * algebraMap A Ω s = algebraMap A Ω a := by
      rw [IsScalarTower.algebraMap_apply A O Ω s, ← map_mul, IsLocalization.mk'_spec,
        ← IsScalarTower.algebraMap_apply]
    have h2 : algebraMap A Ω a = algebraMap A Ω s * w := by
      rw [ha, Submonoid.smul_def, Algebra.smul_def]
    exact mul_right_cancel₀ (hs s) (by rw [h1, h2, mul_comm])

end Local

theorem const_closure : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω], IsDedekindDomain A ∧ Module.Finite ℤ A ∧ Function.Injective (algebraMap A Ω) ∧ HasConstants ℤ A y ∧ ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], IsIntegrallyClosedIn O Ω ∧ fnField O y = ⊤ := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hV A _ _ _
  classical
  haveI : CharZero Ω := charZero_of_isArithVar hV
  obtain ⟨c₀, -, hdiv⟩ := exists_chart_div 𝔐.tie
  have hfin : FiniteDimensional ℚ (algebraicClosure ℚ Ω) := by
    refine GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.proof ℚ Ω
      (Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩) ?_
    have htop := subfield_eq_top hdiv (IntermediateField.adjoin ℚ
      ((Finset.univ.image fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c₀ k⟩ : Finset Ω) : Set Ω)).toSubfield
      fun j => IntermediateField.subset_adjoin _ _ (by simp)
    refine eq_top_iff.2 fun ω _ => ?_
    have hω : ω ∈ (⊤ : Subfield Ω) := Subfield.mem_top ω
    rw [← htop] at hω
    exact hω
  have hconst : HasConstants ℤ A y := fun c' hc' a =>
    (𝔐.tie.ring c' hc' _).2 fun p _ =>
      IntReg.mem_regAt_of_isIntegral_of_stalk _ _ _ _ 𝔐.tie.gen (𝔐.normal.isIntegrallyClosed_stalk p.1) _
        ((IsIntegralClosure.isIntegral_iff (A := A) (R := ℤ)).2 ⟨a, rfl⟩)
  obtain ⟨hd, hfA⟩ := dedekind_finite_of_finite hfin A
  refine ⟨hd, hfA, IsIntegralClosure.algebraMap_injective A ℤ Ω, hconst, ?_⟩
  intro m _ O _ _ _ _ _ _ _
  refine ⟨isIntegrallyClosedIn_of_atPrime A m O, subfield_eq_top hdiv _ fun j => ?_⟩
  show (∏ k, y ⟨k, j k⟩) / (∏ k, y ⟨k, c₀ k⟩) ∈ fnField O y
  rw [← Finset.prod_div_distrib]
  exact prod_mem fun k _ => Subfield.subset_closure (Or.inr ⟨⟨k, j k, c₀ k⟩, rfl⟩)

end GlobalTheory.CompanionTheory.Ar.Num.ConstClosure
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArithVarietyCoordIdealStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arith_variety_coord_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω], IsDedekindDomain A ∧ Module.Finite ℤ A ∧ Function.Injective (algebraMap A Ω) ∧ HasConstants ℤ A y ∧ ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], IsIntegrallyClosedIn O Ω ∧ fnField O y = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.const_closure | exact GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.const_closure | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ConstClosure.const_closure <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.StableEig
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def zPt {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) : Sp S ⟶ Xo.XF c :=
  pullback.lift z.x (spMap (algebraMap c.F S)) (by
    rw [z.x_over]
    simp only [Formalism.L2.Pj.sOf, spMap, ← Spec.map_comp]
    rfl)

theorem zPt_fst {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) :
    zPt z ≫ pullback.fst _ _ = z.x := pullback.lift_fst _ _ _

theorem zPt_snd {S : Type} [CommRing S] [Algebra c.F S] (z : Formalism.L2.Pj.FrPt Xo c S) :
    zPt z ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := pullback.lift_snd _ _ _

theorem eq_zPt {S B : Type} [CommRing S] [Algebra c.F S] [CommRing B] (z : Formalism.L2.Pj.FrPt Xo c S)
    (ψ : S →+* B) (y : Sp B ⟶ Xo.XF c) (h₁ : under y = spMap ψ ≫ z.x)
    (h₂ : y ≫ pullback.snd _ _ = spMap (ψ.comp (algebraMap c.F S))) : y = spMap ψ ≫ zPt z := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, zPt_fst]; exact h₁
  · rw [Category.assoc, zPt_snd, h₂]
    simp only [spMap, ← Spec.map_comp]
    rfl

def Tied {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {B : Type} [CommRing B] (y : Sp B ⟶ Xo.XF c)
    (v : Sp (DualNumber B) ⟶ Xo.univ.t.G.left) (v' : Sp (DualNumber B) ⟶ Y.t.G.left) : Prop :=
  ∃ u : Sp (DualNumber B) ⟶ Y.oF.t.G.left, u ≫ Y.oF.t.G.hom = spMap (algebraMap B (DualNumber B)) ≫ y ∧
    u ≫ Y.m0.toSABMap.φ = v ∧ u ≫ Y.m.φ = v'

def StableEig {X : Scheme.{0}} (t : SAB H X) {A : Type} [CommRing A] (x : Sp A ⟶ X) (κ : c.F →+* A) (σ : E →+* ℂ)
    {r : ℕ} (e : Fin r → (epsAt x ⟶ t.G)) : Prop :=
  ∀ (T : Type) [CommRing T] (θ : A →+* T) (x' : Sp T ⟶ X), spMap θ ≫ x = x' →
    ∀ v : Fin r → (epsAt x' ⟶ t.G), (∀ i, (v i).left = spMap (GlobalTheory.CompanionTheory.Ar.dualMap θ) ≫ (e i).left) →
      IsEigFrame t.act x' ((θ.comp κ).comp (tauIn c σ)) v

end GlobalTheory.CompanionTheory.Ar.LocFn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.NonemptyCptOverOfFlatPreimmersion
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem isCptGen_comp_of_flat_preimmersion {A X : Scheme.{0}} (j : A ⟶ X) [IsPreimmersion j] [Flat j]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (w : A) (hw : ∀ y : A, y ⤳ w → y = w) :
    IsCptGen (Ω := A.residueField w) (A.fromSpecResidueField w ≫ j) := by
  have e : genPt (Ω := A.residueField w) (A.fromSpecResidueField w ≫ j) = j w :=
    congrArg j (A.fromSpecResidueField_apply w _)
  refine isCptGen_of_maximal_of_surjective hX _ ?_ ?_
  · rw [e]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := AlgebraicGeometry.Flat.generalizingMap j hy
    rw [hw a ha]
  · unfold Scheme.stalkClosedPointTo
    rw [CommRingCat.hom_comp, RingHom.coe_comp]
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso _).hom).2.comp
      ((A.fromSpecResidueField w ≫ j).stalkMap_surjective _)

theorem eq_genericPoint_of_specializes {A : Type*} [TopologicalSpace A] [T0Space A] {U : Set A}
    (hU : U ∈ irreducibleComponents A) {w : A} (hw : IsGenericPoint w U) (y : A) (hy : y ⤳ w) : y = w := by
  have h1 : U ⊆ closure {y} := by
    rw [← hw.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hy)) isClosed_closure
  have h2 : closure {y} ⊆ U := hU.2 isIrreducible_singleton.closure h1
  have h3 : w ⤳ y := hw.specializes (h2 (subset_closure rfl))
  exact (hy.antisymm h3).eq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem nonempty_cptOver_of_flat_preimmersion {O : Type} [CommRing O] {β : O →+* c.F} [IsPreimmersion (spMap β)]
    [Flat (spMap β)] (Y : Model Xo c β) (U : Set (Xo.XF c)) (hU : U ∈ irreducibleComponents (Xo.XF c)) :
    Nonempty (CptOver Y U) := by
  have := Y.jQ_open
  have : IsPreimmersion Y.j := by unfold Model.j; infer_instance
  have : Flat Y.j := by unfold Model.j; infer_instance
  obtain ⟨w, hw⟩ := QuasiSober.sober hU.1 (isClosed_of_mem_irreducibleComponents U hU)
  let Ω : Type := (Xo.XF c).residueField w
  let ξ₀ : Sp Ω ⟶ Xo.XF c := (Xo.XF c).fromSpecResidueField w
  have e : genPt ξ₀ = w := (Xo.XF c).fromSpecResidueField_apply w _
  obtain ⟨V, _, _, ⟨M⟩⟩ := lieModel_exists Y.X Y.t.G Ω (ξ₀ ≫ Y.j)
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act Y.X Y.t.G Ω (ξ₀ ≫ Y.j) V M (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  exact ⟨{
    Ω := Ω
    ξ₀ := ξ₀
    inc := (Spec.preimage (ξ₀ ≫ pullback.snd _ _)).hom
    over_inc := (Spec.map_preimage _).symm
    gen := isCptGen_comp_of_flat_preimmersion Y.j (fun x => (Y.normal x).1) w
      (eq_genericPoint_of_specializes hU hw)
    closure := fun u => by rw [e]; exact hw.specializes_iff_mem.symm
    V := V
    M := M
    ρ := ρ
    act := hρ }⟩

theorem nonempty_cptOver_of_fraction {O : Type} [CommRing O] {β : O →+* c.F} (hβ : Function.Injective β)
    (hfr : ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) (Y : Model Xo c β) (U : Set (Xo.XF c))
    (hU : U ∈ irreducibleComponents (Xo.XF c)) : Nonempty (CptOver Y U) := by
  letI : Algebra O c.F := β.toAlgebra
  haveI : IsDomain O := hβ.isDomain β
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hβ
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun x => by
    obtain ⟨a, b, hb, h⟩ := hfr x
    exact ⟨a, b, (eq_div_iff hb).2 h⟩
  haveI : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  haveI : Flat (spMap β) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact IsLocalization.flat c.F (nonZeroDivisors O)
  exact nonempty_cptOver_of_flat_preimmersion Y U hU

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsValFam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.Rep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsValFam {Y : Model Xo c β} {U : Set (Xo.XF c)} (Z : CptOver Y U) {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c)
    {n : ℕ} (b : Fin n → Z.V) (v : Vecs y n) : Prop :=
  ∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b i) v' ∧ SameVec Y y (v i) v'

end GlobalTheory.CompanionTheory.Ar.Flat.Rep
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

def FamilyExistsPos : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω]
    (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω)
    (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q →
    ∀ (b : ∀ t, Fin (labelRk D t) → 𝔐.Li), (∀ t, LinearIndependent Ω (b t) ∧ Submodule.span Ω (Set.range (b t)) = 𝔐.Vgen t) →
    ∀ p ∈ S, HT.HTFree 𝔐 p → p ≠ 2 → ¬ (p : ℤ) ∣ NumberField.discr E →
    ∀ φ : Equiv.Perm (CMType H ⊕ CMType H), IsFrobLabels c p φ →
    ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω],
      AtPlacesOver A Ω p fun O _ _ _ _ => ∀ t₀, ∃ (Sg : Type) (_ : Fintype Sg) (e : Sg → CMType H ⊕ CMType H)
        (φ' : Equiv.Perm Sg) (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F p) (w : O)
        (σ : Sg → F →+* IsLocalRing.ResidueField O)
        (Df : (∀ k, J k) → LieLatticeData Ω F (D.p + D.q) Sg (fun τ => labelRk D (e τ)) fun τ => labelRk D (e τ).swap),
        t₀ ∈ Set.range e ∧ (∀ τ, e (φ' τ) = φ (e τ)) ∧ IsPreFamily O y p w σ φ' Df ∧
        IsFamilyOf O y Df (fun τ => 𝔐.dR (e τ)) (fun τ => 𝔐.HT p (e τ)) (fun τ => 𝔐.dR (e τ).swap)
          (fun τ => 𝔐.HT p (e τ).swap) (fun τ => b (e τ)) fun τ => b (e τ).swap

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombIdentityMatrix
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombIdentityMatrix
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

theorem prod_ofFn_lieModel_pt {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R]
    {x : Spec (CommRingCat.of R) ⟶ S} {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) :
    ∀ {n : ℕ} (f : Fin n → E), (List.ofFn fun j => M.pt (f j)).prod = M.pt (∑ j, f j)
  | 0, f => by simp [M.pt_zero]
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_lieModel_pt M, Fin.sum_univ_succ, M.add]

theorem isComb_unit_row : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F]
    (x : Sp F ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)), (∀ i, IsTanAt G x (v i)) →
    ∀ i, IsComb ((1 : Matrix (Fin n) (Fin n) F) i) v (v i) := by
  intro S G _ _ F _ x n v hv i
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  choose e he using fun j => M.onto (v j) (hv j)
  refine ⟨fun j => M.pt ((1 : Matrix (Fin n) (Fin n) F) i j • e j), fun j => ?_, ?_⟩
  · rw [M.smul, he]
  · rw [prod_ofFn_lieModel_pt M, ← he i]
    congr 1
    simp [Matrix.one_apply, ite_smul]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombIdentityMatrixStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_identity_matrix : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)), (∀ i, IsTanAt G x (v i)) → ∀ i, IsComb ((1 : Matrix (Fin n) (Fin n) F) i) v (v i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row | exact GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.isComb_unit_row <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnif
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnif
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HodgeLin

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {z : Spec (CommRingCat.of ℂ) ⟶ X}
  {A : Over (Sp ℂ)} [GrpObj A] {φ : A.left ⟶ G.left}

abbrev tanEquiv (hp : IsGrpPullback A G z φ) : (epsR ℂ ⟶ A) ≃* (epsAt z ⟶ G) :=
  LiePull.pts hp (T := epsR ℂ) (g := (epsAt z).hom) rfl

theorem unit_left (hp : IsGrpPullback A G z φ) : η[A].left ≫ φ = (1 : Over.mk z ⟶ G).left := by
  have e := map_one (LiePull.pts hp (T := 𝟙_ (Over (Sp ℂ))) (g := z) (Category.id_comp z))
  have e' := congrArg (fun q => q.left) e
  have h1 : (1 : 𝟙_ (Over (Sp ℂ)) ⟶ A) = η[A] := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  rw [h1] at e'
  exact e'

theorem isTangent_iff (hp : IsGrpPullback A G z φ) (x : epsR ℂ ⟶ A) :
    IsTangent x ↔ IsTanAt G z (tanEquiv hp x) := by
  unfold IsTangent IsTanAt
  constructor
  · intro t
    rw [← unit_left hp, ← t, Category.assoc]
    rfl
  · intro t
    apply hp.1.hom_ext
    · rw [Category.assoc, unit_left hp, ← t]
      rfl
    · have e : (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫
          CommRingCat.ofHom (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom = 𝟙 _ := by
        ext r
        simp
      have e' := congrArg Spec.map e
      simp only [Spec.map_comp, Spec.map_id] at e'
      have hx : x.left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w x
      have h0 : η[A].left ≫ A.hom = 𝟙 _ := Over.w η[A]
      rw [Category.assoc, hx, h0]
      exact e'

theorem exists_linearEquiv : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type)
    [AddCommGroup V] [Module ℂ V] (M : LieModel G z V) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (L : LB A.left)
    (g : ℕ) (u : HolUnif A L g), IsGrpPullback A G z φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) →
    (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) →
    ∃ D : V ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, ∃ x : epsR ℂ ⟶ A, IsTangent x ∧ x.left ≫ φ = (M.pt v).left ∧ u.IsDiff (D v) x := by
  intro X G _ z V _ _ M A _ φ L g u hp h1 h2
  let Φ := tanEquiv hp
  let x : V → (epsR ℂ ⟶ A) := fun v => Φ.symm (M.pt v)
  have hΦx : ∀ v, Φ (x v) = M.pt v := fun v => Φ.apply_symm_apply _
  have hleft : ∀ v, (x v).left ≫ φ = (M.pt v).left := fun v => congrArg (fun q => q.left) (hΦx v)
  have tx : ∀ v, IsTangent (x v) := fun v => (isTangent_iff hp _).2 (by
    change IsTanAt G z (Φ (x v))
    rw [hΦx]
    exact M.tan v)
  have xadd : ∀ v v', x (v + v') = x v * x v' := fun v v' => by
    simp only [x]
    rw [M.add, map_mul]
  have xsmul : ∀ (c : ℂ) v, x (c • v) = Chart.spMap (Chart.scaleD c) ≫ x v := fun c v => by
    apply Φ.injective
    rw [hΦx]
    apply Over.OverMorphism.ext
    rw [M.smul c v, ← hleft v]
    exact (Category.assoc _ _ _).symm
  have tan' : ∀ {y : epsR ℂ ⟶ A}, IsTangent y → Chart.IsTan y := fun h => (Chart.isTan_iff _).2 h
  choose d hd hu using fun v => h1 (x v) (tx v)
  let Dl : V →ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := d
      map_add' := fun v v' => by
        symm
        apply hu
        rw [xadd]
        exact UnifDifferential.isDiff_mul u (tan' (tx v)) (tan' (tx v')) (hd v) (hd v')
      map_smul' := fun c v => by
        symm
        apply hu
        rw [xsmul]
        exact UnifDifferential.isDiff_scale u (hd v) c }
  have inj : Function.Injective Dl := fun v v' e => by
    have e' : d v = d v' := e
    have h : x v = x v' := (h2 (d v')).unique ⟨tx v, e' ▸ hd v⟩ ⟨tx v', hd v'⟩
    exact M.inj (by rw [← hΦx, ← hΦx, h])
  have surj : Function.Surjective Dl := fun w => by
    obtain ⟨y, ⟨ty, dy⟩, -⟩ := h2 w
    obtain ⟨v, hv⟩ := M.onto _ ((isTangent_iff hp y).1 ty)
    have hy : x v = y := Φ.injective (by rw [hΦx]; exact hv)
    exact ⟨v, (hu v w (hy ▸ dy)).symm⟩
  exact ⟨LinearEquiv.ofBijective Dl ⟨inj, surj⟩, fun v => ⟨x v, tx v, hleft v, hd v⟩⟩

end GlobalTheory.CompanionTheory.Ar.HodgeLin
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentSpaceEquivHolUnifStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_space_equiv_hol_unif : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (z : Spec (CommRingCat.of ℂ) ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (M : LieModel G z V) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ G.left) (L : LB A.left) (g : ℕ) (u : HolUnif A L g), IsGrpPullback A G z φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → ∃ D : V ≃ₗ[ℂ] (Fin g → ℂ), ∀ v, ∃ x : epsR ℂ ⟶ A, IsTangent x ∧ x.left ≫ φ = (M.pt v).left ∧ u.IsDiff (D v) x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv | exact GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeLin.exists_linearEquiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombMatrixMul
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombMatrixMul
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.CombMul

theorem pt_sum_ofFn {S : Scheme.{0}} {G : Over S} [GrpObj G] {F : Type} [Field F] {x : Sp F ⟶ S} {V : Type}
    [AddCommGroup V] [Module F V] (M : LieModel G x V) : ∀ {n : ℕ} (u : Fin n → V),
    M.pt (∑ i, u i) = (List.ofFn fun i => M.pt (u i)).prod
  | 0, u => by simp [M.pt_zero]
  | n + 1, u => by
    rw [Fin.sum_univ_succ, M.add, pt_sum_ofFn M (fun i => u i.succ), List.ofFn_succ, List.prod_cons]

theorem isComb_pt_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] {F : Type} [Field F] {x : Sp F ⟶ S} {V : Type}
    [AddCommGroup V] [Module F V] (M : LieModel G x V) {n : ℕ} (c : Fin n → F) (e : Fin n → V)
    (w : epsAt x ⟶ G) : IsComb c (fun i => M.pt (e i)) w ↔ w = M.pt (∑ i, c i • e i) := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have h : u = fun i => M.pt (c i • e i) :=
      funext fun i => Over.OverMorphism.ext ((hu i).trans (M.smul _ _).symm)
    rw [pt_sum_ofFn, h]
  · rintro rfl
    exact ⟨fun i => M.pt (c i • e i), fun i => M.smul _ _, pt_sum_ofFn M _⟩

theorem isComb_mul : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (m n k : ℕ) (v : Fin n → (epsAt x ⟶ G)) (u : Fin m → (epsAt x ⟶ G)) (w : Fin k → (epsAt x ⟶ G)) (A : Matrix (Fin k) (Fin m) F) (C : Matrix (Fin m) (Fin n) F), (∀ i, IsTanAt G x (v i)) → (∀ i, IsComb (C i) v (u i)) → (∀ i, IsComb (A i) u (w i)) → ∀ i, IsComb ((A * C) i) v (w i) := by
  intro S G _ _ F _ x m n k v u w A C hv hu hw i
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G F x
  obtain ⟨e, rfl⟩ : ∃ e : Fin n → E, v = fun i => M.pt (e i) := by
    choose e he using fun i => M.onto (v i) (hv i)
    exact ⟨e, funext fun i => (he i).symm⟩
  obtain rfl : u = fun j => M.pt (∑ l, C j l • e l) :=
    funext fun j => (isComb_pt_iff M (C j) e (u j)).1 (hu j)
  have hwi := (isComb_pt_iff M (A i) _ (w i)).1 (hw i)
  rw [isComb_pt_iff, hwi]
  congr 1
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

end GlobalTheory.CompanionTheory.Ar.CombMul
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCombMatrixMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_comb_matrix_mul : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (m n k : ℕ) (v : Fin n → (epsAt x ⟶ G)) (u : Fin m → (epsAt x ⟶ G)) (w : Fin k → (epsAt x ⟶ G)) (A : Matrix (Fin k) (Fin m) F) (C : Matrix (Fin m) (Fin n) F), (∀ i, IsTanAt G x (v i)) → (∀ i, IsComb (C i) v (u i)) → (∀ i, IsComb (A i) u (w i)) → ∀ i, IsComb ((A * C) i) v (w i) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul | exact GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.CombMul.isComb_mul <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorLinearCombination
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorLinearCombination
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CombEig

theorem pt_sum {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {V : Type}
    [AddCommGroup V] [Module R V] (M : LieModel G x V) :
    ∀ {n : ℕ} (e : Fin n → V), M.pt (∑ i, e i) = (List.ofFn fun i => M.pt (e i)).prod
  | 0, e => by simpa using M.pt_zero
  | n + 1, e => by
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.prod_cons, M.add, pt_sum M]

theorem isEigVec_comb : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G), (∀ i, IsEigVec act x σ (v i)) → IsComb cf v w → IsEigVec act x σ w := by
  intro S G _ _ F _ x P _ act σ n v cf w hv hc
  have key : ∀ y : epsAt x ⟶ G, IsEigVec act x σ y ↔
      (IsTanAt G x y ∧ ∀ a, y ≫ act.act a = LieTangent.epsScale x (σ a) ≫ y) := by
    intro y
    unfold IsEigVec
    refine and_congr_right fun _ => forall_congr' fun a => ?_
    constructor
    · intro h
      apply Over.OverMorphism.ext
      rw [h]
      rfl
    · intro h
      rw [h]
      rfl
  have hcomm : ∀ c d : F, LieTangent.epsScale x c ≫ LieTangent.epsScale x d =
      LieTangent.epsScale x d ≫ LieTangent.epsScale x c := by
    intro c d
    have hr : (epsMul c).comp (epsMul d) = (epsMul d).comp (epsMul c) := by
      refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
      · simp [LieTangent.epsMul_fst]
      · simp [LieTangent.epsMul_snd, mul_left_comm]
    apply Over.OverMorphism.ext
    show Spec.map (CommRingCat.ofHom (epsMul c)) ≫ Spec.map (CommRingCat.ofHom (epsMul d)) =
      Spec.map (CommRingCat.ofHom (epsMul d)) ≫ Spec.map (CommRingCat.ofHom (epsMul c))
    rw [LieTangent.spec_comp, LieTangent.spec_comp, hr]
  obtain ⟨u, hu, rfl⟩ := hc
  have hu' : ∀ i, u i = LieTangent.epsScale x (cf i) ≫ v i := by
    intro i
    apply Over.OverMorphism.ext
    rw [hu i]
    rfl
  rw [key]
  apply List.prod_induction
    (fun y => IsTanAt G x y ∧ ∀ a, y ≫ act.act a = LieTangent.epsScale x (σ a) ≫ y)
  · rintro y z ⟨hy, hy'⟩ ⟨hz, hz'⟩
    refine ⟨LieTangent.isTanAt_mul hy hz, fun a => ?_⟩
    haveI := act.hom a
    rw [MonObj.mul_comp, hy', hz', MonObj.comp_mul]
  · refine ⟨LieTangent.isTanAt_one, fun a => ?_⟩
    haveI := act.hom a
    rw [MonObj.one_comp, MonObj.comp_one]
  · intro y hy
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
    rw [hu']
    obtain ⟨ht, he⟩ := (key (v i)).mp (hv i)
    refine ⟨LieTangent.isTanAt_scale (cf i) ht, fun a => ?_⟩
    rw [Category.assoc, he a, ← Category.assoc, ← Category.assoc, hcomm]

end GlobalTheory.CompanionTheory.Ar.CombEig
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenvectorLinearCombinationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenvector_linear_combination : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (F : Type) [Field F] (x : Sp F ⟶ S) (P : Type) [CommRing P] (act : OAct P G) (σ : P →+* F) (n : ℕ) (v : Fin n → (epsAt x ⟶ G)) (cf : Fin n → F) (w : epsAt x ⟶ G), (∀ i, IsEigVec act x σ (v i)) → IsComb cf v w → IsEigVec act x σ w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.CombEig.isEigVec_comb | exact GlobalTheory.CompanionTheory.Ar.CombEig.isEigVec_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.CombEig.isEigVec_comb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLocalExtensionExists
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MiOpen
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

namespace PositivityTheory.HtPt.Mi

theorem flat_of_forall {X Z : Scheme.{0}} (f : X ⟶ Z)
    (h : ∀ x : X, ∃ (W : Scheme.{0}) (g : W ⟶ X) (w : W), g w = x ∧ Flat g ∧ Flat (g ≫ f)) : Flat f := by
  refine Flat.of_stalkMap f fun x => ?_
  obtain ⟨W, g, w, rfl, _, _⟩ := h x
  have h := Flat.stalkMap (g ≫ f) w
  rw [Scheme.Hom.stalkMap_comp] at h
  exact GlobalTheory.ringHom_flat_of_comp_faithfullyFlat (GlobalTheory.faithfullyFlat_stalkMap_of_flat g w) h

theorem open_crit : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  intro R _ X Y j q _ H
  have key : ∀ x : X, ∃ (U V : Scheme.{0}) (g : U ⟶ X) (u : U) (δ : U ⟶ V) (m : V ⟶ pullback j j),
      g u = x ∧ Flat g ∧ Flat (g ≫ j) ∧ IsOpenImmersion δ ∧ Flat m ∧ δ ≫ m = g ≫ pullback.diagonal j ∧
      ∀ z, pullback.snd j j z = x → ∃ u', m (δ u') = z := by
    intro x
    obtain ⟨R', _, _, _, X', Y', j', q', a, b, U, hfl, hP, hb, ha, hU, hcl⟩ := @H (q (j x)).asIdeal (q (j x)).isPrime
    have hs : Flat (Spec.map (CommRingCat.ofHom (algebraMap R R'))) :=
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 hfl)
    have hbf : Flat b := MorphismProperty.of_isPullback hb.flip hs
    have haf : Flat a := MorphismProperty.of_isPullback ha.flip hbf
    obtain ⟨x', hx1, hx2⟩ := Scheme.exists_preimage_of_isPullback (ha.paste_vert hb) x
      (IsLocalRing.closedPoint R') (PrimeSpectrum.ext hP.symm)
    have hx2' : q' (j' x') = IsLocalRing.closedPoint R' := by rw [← hx2]; simp
    let u : U.toScheme := ⟨x', hcl x' hx2'⟩
    have hu : U.ι u = x' := rfl
    have hw : (U.ι ≫ a) ≫ j = (U.ι ≫ j') ≫ b := by rw [Category.assoc, ha.w, Category.assoc]
    let δ : U.toScheme ⟶ pullback j' (U.ι ≫ j') := pullback.lift U.ι (𝟙 _) (by simp)
    have hδ : δ ≫ pullback.fst _ _ = U.ι := pullback.lift_fst _ _ _
    have hδ' : δ ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have hV := (IsPullback.of_hasPullback j' (U.ι ≫ j')).paste_horiz ha
    rw [← hw] at hV
    let m : pullback j' (U.ι ≫ j') ⟶ pullback j j :=
      pullback.lift (pullback.fst _ _ ≫ a) (pullback.snd _ _ ≫ U.ι ≫ a) (by rw [hV.w]; simp only [Category.assoc])
    have hm1 : m ≫ pullback.fst j j = pullback.fst _ _ ≫ a := pullback.lift_fst _ _ _
    have hm2 : m ≫ pullback.snd j j = pullback.snd _ _ ≫ U.ι ≫ a := pullback.lift_snd _ _ _
    have hm : IsPullback m (pullback.snd j' (U.ι ≫ j')) (pullback.snd j j) (U.ι ≫ a) :=
      IsPullback.of_right (by rw [hm1]; exact hV) hm2 (IsPullback.of_hasPullback j j)
    have hg : Flat (U.ι ≫ a) := inferInstance
    have hδo : IsOpenImmersion δ := by
      have : IsOpenImmersion (δ ≫ pullback.fst j' (U.ι ≫ j')) := by rw [hδ]; infer_instance
      exact IsOpenImmersion.of_comp δ (pullback.fst j' (U.ι ≫ j'))
    have hgu : (U.ι ≫ a) u = x := by rw [Scheme.Hom.comp_apply, hu]; exact hx1
    refine ⟨U, _, U.ι ≫ a, u, δ, m, hgu, hg, by rw [hw]; infer_instance, hδo,
      MorphismProperty.of_isPullback hm.flip hg, ?_, fun z hz => ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hm1, reassoc_of% hδ]; simp
      · rw [Category.assoc, hm2, reassoc_of% hδ']; simp
    · obtain ⟨v, hv1, hv2⟩ := Scheme.exists_preimage_of_isPullback hm z u (hz.trans hgu.symm)
      have h1 : j' (pullback.fst j' (U.ι ≫ j') v) = j' x' := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
        exact congrArg (fun t => j' (U.ι t)) hv2
      let u' : U.toScheme := ⟨pullback.fst j' (U.ι ≫ j') v, hcl _ (by rw [h1, hx2'])⟩
      have h2 : δ u' = v := by
        apply (pullback.fst j' (U.ι ≫ j')).isOpenEmbedding.injective
        rw [← Scheme.Hom.comp_apply, hδ]
        rfl
      exact ⟨u', by rw [h2]; exact hv1⟩
  have : Flat j := flat_of_forall j fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, h3, -⟩ := key x
    exact ⟨U, g, u, h1, h2, h3⟩
  have : Flat (pullback.diagonal j) := flat_of_forall _ fun x => by
    obtain ⟨U, V, g, u, δ, m, h1, h2, -, h4, h5, h6, -⟩ := key x
    exact ⟨U, g, u, h1, h2, by rw [← h6]; infer_instance⟩
  have : Surjective (pullback.diagonal j) := ⟨fun z => by
    obtain ⟨U, V, g, u, δ, m, -, -, -, -, -, h6, h7⟩ := key (pullback.snd j j z)
    obtain ⟨u', hu'⟩ := h7 z rfl
    exact ⟨g u', by rw [← hu', ← Scheme.Hom.comp_apply, ← h6, Scheme.Hom.comp_apply]⟩⟩
  have : IsClosedImmersion (pullback.diagonal j) :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [(pullback.diagonal j).surjective.range_eq]; exact isClosed_univ)
  have : IsIso (pullback.diagonal j) := Flat.isIso_of_surjective_of_mono _
  have : Mono j := (pullback.isIso_diagonal_iff j).1 this
  exact IsOpenImmersion.of_flat_of_mono j

end PositivityTheory.HtPt.Mi
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLocalExtensionExists
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  first | exact @PositivityTheory.HtPt.Mi.open_crit | exact PositivityTheory.HtPt.Mi.open_crit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatLocalExtensionExistsStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_local_extension_exists : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists | exact GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists | (intros; apply GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameBorelChangeVectors
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameBorelChangeVectors
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.FrameTri

open MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem comp_list_prod {B : Scheme.{0}} {G T T' : Over B} [GrpObj G] (f : T' ⟶ T) (L : List (T ⟶ G)) :
    f ≫ L.prod = (L.map fun a => f ≫ a).prod := by
  induction L with
  | nil => simpa using MonObj.comp_one f
  | cons a L ih => rw [List.prod_cons, List.map_cons, List.prod_cons, MonObj.comp_mul, ih]

theorem dualMap_comp_algebraMap {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F) :
    (Formalism.L2.Pj.dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap F (DualNumber F)).comp ψ := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul' {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F) (a : S) :
    (Formalism.L2.Pj.dualMap ψ).comp (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) =
      (GlobalTheory.CompanionTheory.Ar.epsMul (ψ a)).comp (Formalism.L2.Pj.dualMap ψ) := by
  ext s <;> simp [Formalism.L2.Pj.dualMap, ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, GlobalTheory.CompanionTheory.Ar.epsMul,
    TrivSqZeroExt.algebraMap_eq_inl]

theorem isComb_of_isCombAt {Xo : Moduli D l} {S F : Type} [CommRing S] [CommRing F] (ψ : S →+* F)
    {x : Sp S ⟶ Xo.X} {x' : Sp F ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) {m : ℕ}
    {vS : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {cf : Fin m → S}
    {wS : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : Formalism.L2.Pj.IsCombAt x vS cf wS)
    {v : Fin m → (epsAt x' ⟶ Xo.univ.t.G)} {w : epsAt x' ⟶ Xo.univ.t.G}
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ vS i)
    (hw : w.left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ wS) :
    Fl.IsComb (fun i => ψ (cf i)) v w := by
  subst hx
  obtain ⟨u, hu, hp⟩ := h
  have hf : spMap (Formalism.L2.Pj.dualMap ψ) ≫ (Formalism.L2.Pj.tEps x).hom = (epsAt (spMap ψ ≫ x)).hom := by
    show spMap (Formalism.L2.Pj.dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      Spec.map (CommRingCat.ofHom (algebraMap F (DualNumber F))) ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_algebraMap]
  let f : epsAt (spMap ψ ≫ x) ⟶ Formalism.L2.Pj.tEps x := Over.homMk (spMap (Formalism.L2.Pj.dualMap ψ)) hf
  refine ⟨fun i => f ≫ u i, fun i => ?_, ?_⟩
  · show spMap (Formalism.L2.Pj.dualMap ψ) ≫ (u i).left = _
    rw [hu i, hv i, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      dualMap_comp_epsMul']
  · have e : (List.ofFn fun i => f ≫ u i) = (List.ofFn u).map fun a => f ≫ a := by
      rw [List.map_ofFn]; rfl
    rw [e, ← comp_list_prod]
    apply Over.OverMorphism.ext
    rw [hw, ← hp]
    rfl

theorem exists_matrix {Xo : Moduli D l} {S F : Type} [CommRing S] [Field F] (ψ : S →+* F)
    {x : Sp S ⟶ Xo.X} {x' : Sp F ⟶ Xo.X} (hx : x' = spMap ψ ≫ x) {m n : ℕ} (hn : n = m)
    {u u' : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (d : Fin m → S)
    (h : ∀ i, ∃ cf : Fin m → S, cf i = d i ∧ (∀ j, i < j → cf j = 0) ∧ Formalism.L2.Pj.IsCombAt x u cf (u' i))
    {v v' : Fin n → (epsAt x' ⟶ Xo.univ.t.G)}
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ u (i.cast hn))
    (hv' : ∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ u' (i.cast hn)) :
    ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, Fl.IsComb (A i) v (v' i)) ∧
      A.det = ∏ i : Fin n, ψ (d (i.cast hn)) := by
  subst hn
  choose cf h1 h2 h3 using h
  refine ⟨Matrix.of fun i j => ψ (cf i j), fun i => ?_, ?_⟩
  · exact isComb_of_isCombAt ψ hx (h3 i) hv (hv' i)
  · rw [Matrix.det_of_lowerTriangular]
    · exact Finset.prod_congr rfl fun i _ => by simp [h1]
    · intro i j hij
      have : i < j := hij
      simp [h2 i j this]

theorem exists_triangular_at_field (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S]
    (t : Formalism.L2.Pj.Ix D → Sˣ) (z z' : Formalism.L2.Pj.FrPt Xo c S) (hb : Formalism.L2.Pj.FrBor t z z')
    (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p)
    (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (v v' : Vecs y D.p) (w w' : Vecs y D.q)
    (hy : under y = spMap ψ ≫ z.x)
    (hv : ∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm))
    (hw : ∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm))
    (hv' : ∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u τ (i.cast hp.symm))
    (hw' : ∀ j, (w' j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) :
    ∃ (A : Matrix (Fin D.p) (Fin D.p) F) (B : Matrix (Fin D.q) (Fin D.q) F),
      (∀ i, Fl.IsComb (A i) v (v' i)) ∧ (∀ j, Fl.IsComb (B j) w (w' j)) ∧
      A.det = ∏ i : Fin D.p, ψ (t (some ⟨τ, i.cast hp.symm⟩) : Sˣ) ∧
      B.det = ∏ j : Fin D.q, ψ (t (some ⟨ComplexEmbedding.conjugate τ, j.cast hq.symm⟩) : Sˣ) := by
  obtain ⟨-, hc, -⟩ := hb
  obtain ⟨A, hA, dA⟩ := exists_matrix ψ hy hp.symm (fun i => (t (some ⟨τ, i⟩) : S)) (hc τ) hv hv'
  obtain ⟨B, hB, dB⟩ := exists_matrix ψ hy hq.symm
    (fun i => (t (some ⟨ComplexEmbedding.conjugate τ, i⟩) : S)) (hc (ComplexEmbedding.conjugate τ)) hw hw'
  exact ⟨A, B, hA, hB, dA, dB⟩

end GlobalTheory.CompanionTheory.Ar.Flat.FrameTri
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameBorelChangeVectorsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_borel_change_vectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (τ : E →+* ℂ) (S : Type) [CommRing S] [Algebra c.F S] (t : Formalism.L2.Pj.Ix D → Sˣ) (z z' : Formalism.L2.Pj.FrPt Xo c S), Formalism.L2.Pj.FrBor t z z' → ∀ (F : Type) [Field F] (ψ : S →+* F) (y : Sp F ⟶ Xo.XF c) (hp : D.mult τ = D.p) (hq : D.mult (ComplexEmbedding.conjugate τ) = D.q) (v v' : Vecs y D.p) (w w' : Vecs y D.q), under y = spMap ψ ≫ z.x → (∀ i, (v i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u τ (i.cast hp.symm)) → (∀ j, (w j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → (∀ i, (v' i).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u τ (i.cast hp.symm)) → (∀ j, (w' j).left = spMap (Formalism.L2.Pj.dualMap ψ) ≫ z'.u (ComplexEmbedding.conjugate τ) (j.cast hq.symm)) → ∃ (A : Matrix (Fin D.p) (Fin D.p) F) (B : Matrix (Fin D.q) (Fin D.q) F), (∀ i, Fl.IsComb (A i) v (v' i)) ∧ (∀ j, Fl.IsComb (B j) w (w' j)) ∧ A.det = ∏ i : Fin D.p, ψ (t (some ⟨τ, i.cast hp.symm⟩) : Sˣ) ∧ B.det = ∏ j : Fin D.q, ψ (t (some ⟨ComplexEmbedding.conjugate τ, j.cast hq.symm⟩) : Sˣ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FrameTri.exists_triangular_at_field | exact GlobalTheory.CompanionTheory.Ar.Flat.FrameTri.exists_triangular_at_field | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FrameTri.exists_triangular_at_field <;> assumption)
end
end
