module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtChartLocalization
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralMultilinearExpansion
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsStokesGeo
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ThetaUnifAVOfLaws
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FromNAdd
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt

open GlobalTheory.CompanionTheory.Ar.BT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O₀ : Type} [CommRing O₀] {β : O₀ →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
  {F : Type} [Field F]

abbrev NAdd (E : Type) [Field E] [NumberField E] (n p : ℕ) : Type := Fin n → (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})

def toNAdd {n p : ℕ} (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) : (Fin n → F) →+ NAdd E n p where
  toFun a i := sc (a i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def fromNAdd {n p : ℕ} (pq : (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)}) →+* F) : NAdd E n p →+ (Fin n → F) where
  toFun t i := pq (t i)
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

def bcLin (C : Type) [Field C] [Algebra Ω C] {m n : ℕ} (f : (Fin m → Ω) →ₗ[Ω] (Fin n → Ω)) :
    (Fin m → C) →ₗ[C] (Fin n → C) :=
  Matrix.toLin' ((LinearMap.toMatrix' f).map (algebraMap Ω C))

variable {𝔐 : HodgeCpt Y S y} {p : ℕ} {G : GenTors 𝔐 p} {O : Type} [CommRing O] [Algebra O Ω] {c' : ∀ k, J k}

def testOrd (P : ChartPack G O c') {C : Type} [Field C] [Algebra O C] [Algebra Ω C] (RC : Subalgebra O C) :
    Submodule RC (NAdd E (D.p + D.q) p → C) :=
  Submodule.span RC {f | ∃ g ∈ P.Γ₁.btOrder ⊤, f = fun x =>
    algebraMap Ω C ((g (Multiplicative.ofAdd x) : CR O y c') : Ω)}

def testOrdW (P : ChartPack G O c') (sc : F →+ (𝓞 E ⧸ Ideal.span {(p : 𝓞 E)})) {C : Type} [Field C] [Algebra O C]
    [Algebra Ω C] (RC : Subalgebra O C) : Submodule RC ((Fin (D.p + D.q) → F) → C) :=
  (testOrd P RC).map (LinearMap.funLeft RC C (toNAdd sc : (Fin (D.p + D.q) → F) → NAdd E (D.p + D.q) p))

end GlobalTheory.CompanionTheory.Ar.Num.FamEx.TestPt
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegree
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TieArith

open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar ReciprocityTheory.ChartRestriction.G.AI.I4

section Forms

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem aeval_eq_ratioPt (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    MvPolynomial.aeval y g = MvPolynomial.aeval (ratioPt y c) g * ∏ k, y ⟨k, c k⟩ ^ d k := by
  have h1 := mConeMap_eq_scale y c hc g
  rw [ConeTrdeg.mConeMap_of_isMultiHomog y hg, ConeTrdeg.mConeMap_of_isMultiHomog (ratioPt y c) hg] at h1
  have h2 : scaleT (fun k ↦ y ⟨k, c k⟩)
      (MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g) * ∏ k, MvPolynomial.X k ^ d k) =
      MvPolynomial.C (MvPolynomial.aeval (ratioPt y c) g * ∏ k, y ⟨k, c k⟩ ^ d k) *
        ∏ k, MvPolynomial.X k ^ d k := by
    simp only [scaleT, map_mul, map_prod, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      MvPolynomial.algebraMap_eq, mul_pow, Finset.prod_mul_distrib]
    ring
  rw [h2] at h1
  have h3 : (∏ k, MvPolynomial.X k ^ d k : MvPolynomial K Ω) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k)
  exact MvPolynomial.C_injective _ _ (mul_right_cancel₀ h3 h1)

theorem birational_of_ratioField_eq_top [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) : Birational y := by
  intro s
  obtain ⟨d, g, h, hg, hh, n, e⟩ := rep_of_mem y c hc (x := s) (by rw [htop]; trivial)
  have hU : (∏ k, y ⟨k, c k⟩ ^ d k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hc k)
  refine ⟨d, g, h, hg, hh, ?_, ?_⟩
  · rw [aeval_eq_ratioPt y c hc hh]
    exact mul_ne_zero n hU
  · rw [aeval_eq_ratioPt y c hc hg, aeval_eq_ratioPt y c hc hh, e, _root_.mul_assoc]

theorem isArithVar_of_ratioField_eq_top [Nonempty K] [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (htop : ratioField y c = ⊤) (d : ℕ)
    (hd : Algebra.trdeg ℤ Ω = d) : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) := by
  refine ⟨‹_›, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y c hc⟩, horizontal y, ?_⟩
  have hb : blockFnField y = ⊤ := by rw [← Cmp.ratioField_eq_blockFnField y c hc, htop]
  have htr : Algebra.trdeg ℤ (blockFnField y) = d := by
    rw [hb, ← hd]
    exact (IntermediateField.topEquiv (F := ℚ) (E := Ω)).toRingEquiv.toIntAlgEquiv.trdeg_eq
  rw [Cmp.ringKrullDim_coord y c hc, htr]
  have h4 : (((d : Cardinal) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) =
      ((d + 1 + Fintype.card K : ℕ) : ℕ∞) := by
    rw [map_add (f := _), Cardinal.toENat_nat, Cardinal.toENat_nat]
    push_cast
    ring
  rw [h4]
  rfl

end Forms

section Chart

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)

def genCpt : Cpt ξ := ⟨genPt ξ, specializes_rfl⟩

theorem mem_regAt_genCpt (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ (genCpt ξ) := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  show (X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫
    Scheme.stalkClosedPointTo ξ).hom s = a
  rw [e]
  exact hs

variable {K : Type} [Fintype K] {J : K → Type} [CharZero Ω] (y : (Σ k, J k) → Ω) (c : ∀ k, J k)

theorem adjoin_le_ratioField {a : Ω}
    (ha : a ∈ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩)) : a ∈ ratioField y c := by
  have hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k =>
      (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ (ratioField y c).toSubalgebra.restrictScalars ℤ := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show _ ∈ ratioField y c
    simp only [← Finset.prod_div_distrib]
    exact prod_mem fun k _ ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k, j k⟩, rfl⟩
  exact hle ha

end Chart

end GlobalTheory.CompanionTheory.Ar.TieArith

namespace GlobalTheory.CompanionTheory.Ar


open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar TieArith in
theorem coordTie_birational_isArithVar (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [Nonempty K] [CharZero Ω] (d : ℕ)
    (h : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩))
    (hd : Algebra.trdeg ℤ Ω = d) : Birational y ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (d + 1) := by
  obtain ⟨c, hchart⟩ := h.cover (TieArith.genCpt ξ)
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦
    (Finset.prod_ne_zero_iff.mp hchart.1) k (Finset.mem_univ k)
  have htop : GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField y c = ⊤ := by
    rw [eq_top_iff]
    intro a _
    obtain ⟨s, hs, hu, hsa⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ _ h c (TieArith.genCpt ξ) hchart a).mp
      (TieArith.mem_regAt_genCpt ξ h.gen a)
    have h1 := TieArith.adjoin_le_ratioField y c hs
    have h2 := TieArith.adjoin_le_ratioField y c hsa
    have h3 := div_mem h2 h1
    rwa [mul_div_cancel_left₀ _ hu.1] at h3
  exact ⟨TieArith.birational_of_ratioField_eq_top y c hc htop,
    TieArith.isArithVar_of_ratioField_eq_top y c hc htop d hd⟩

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BirationalOfTranscendenceDegreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birational_of_transcendence_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) [Nonempty K] [CharZero Ω] (d : ℕ), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → Algebra.trdeg ℤ Ω = d → Birational y ∧ IsArithVar (mCoordIdeal y) (d + 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar | exact GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar | (intros; apply GlobalTheory.CompanionTheory.Ar.coordTie_birational_isArithVar <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModel
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModel
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartFType

theorem finiteType_of_equiv {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra ℤ C]
    [Algebra.FiniteType ℤ C] (E : B ≃+* C) (g : ℤ →+* A) (f : A →+* B) : f.FiniteType := by
  have hC : (algebraMap ℤ C).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have hE : (E.symm.toRingHom).FiniteType := RingHom.FiniteType.of_surjective _ E.symm.surjective
  have h1 : ((E.symm.toRingHom).comp (algebraMap ℤ C)).FiniteType := hE.comp hC
  have h2 : f.comp (Int.castRingHom A) = (E.symm.toRingHom).comp (algebraMap ℤ C) := RingHom.ext_int _ _
  rw [← h2] at h1
  exact RingHom.FiniteType.of_comp_finiteType h1

theorem main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → ∃ s : X ⟶ Spec (CommRingCat.of ℤ), LocallyOfFiniteType s ∧ QuasiCompact s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := by
  intro X Ω _ ξ κ _ x hall T
  refine ⟨specZIsTerminal.from X, ?_, ?_, specZIsTerminal.hom_ext _ _⟩
  · have hQ := (RingHom.finiteType_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finiteType_holdsForLocalizationAway).1
    rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFiniteType) hQ]
    intro q
    obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
    obtain ⟨U, hUa, hU⟩ := T.affine c hcq.1
    have hqU : q ∈ U := (hU q).2 ⟨hall q, hcq⟩
    have hg : genPt ξ ∈ U := (hall q).mem_open U.isOpen hqU
    obtain ⟨E, -⟩ := GlobalTheory.CompanionTheory.Ar.ChartSmooth.exists_secEquiv hall T hcq.1 hU hg
    haveI : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range fun j => x j / x c)) :=
      (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩)
    exact ⟨⟨⊤, isAffineOpen_top _⟩, ⟨U, hUa⟩, hqU, by simp, finiteType_of_equiv E (Int.castRingHom _) _⟩
  · rw [quasiCompact_iff_compactSpace]
    choose U hUa hU using T.affine
    refine ⟨?_⟩
    have hcov : (Set.univ : Set X) = ⋃ (c : κ) (hc : x c ≠ 0), (U c hc : Set X) := by
      ext q
      simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
      obtain ⟨c, hcq⟩ := T.cover ⟨q, hall q⟩
      exact ⟨c, hcq.1, (hU c hcq.1 q).2 ⟨hall q, hcq⟩⟩
    rw [hcov]
    exact isCompact_iUnion fun c => isCompact_iUnion fun hc => (hUa c hc).isCompact

end GlobalTheory.CompanionTheory.Ar.ChartFType
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteTypeOverIntegersModelStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_type_over_integers_model : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) [Finite κ] (x : κ → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → ∃ s : X ⟶ Spec (CommRingCat.of ℤ), LocallyOfFiniteType s ∧ QuasiCompact s ∧ ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap ℤ Ω)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartFType.main | exact GlobalTheory.CompanionTheory.Ar.ChartFType.main | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartFType.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompat
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LinePull

theorem wedge_eq_span_pull {X₀ X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {f : X ⟶ X₀} {i : Ω₀ →+* Ω}
    {V₀ V : Type} [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] {j : V₀ →+ V}
    (hD : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) (hE : IsExtOver i j) {L₀ : Lat ξ₀ V₀} {L : Lat ξ V} {n : ℕ}
    {a₀ : ⋀[Ω₀]^n V₀} {a : ⋀[Ω]^n V} (x : Cpt ξ) (h : genPt ξ₀ ⤳ f x.1) {u : Fin n → V₀} {α : Ω₀} (hα : α ≠ 0)
    (hF : L₀.IsFrameAt u ⟨f x.1, h⟩) (hL : L x = L₀.pull ξ f j x)
    (hW : L₀.wedge n ⟨f x.1, h⟩ = Submodule.span (regAt ξ₀ ⟨f x.1, h⟩) {α • a₀})
    (hP : CptIn.IsPullWedge i j a₀ a) :
    L.wedge n x = Submodule.span (regAt ξ x) {i α • a} := by
  obtain ⟨_, hreg, -⟩ := pull_reg_and_gen X₀ Ω₀ ξ₀ X Ω ξ f i hD x
  have hF' := FlagPull.pull_isFrameAt hD hE x h hF
  have hFr : L.IsFrameAt (fun k => j (u k)) x := ⟨hF'.1, hL.trans hF'.2⟩
  obtain ⟨hw, -⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L n _ x hFr
  obtain ⟨hw₀, hne⟩ := WedgeFrame.wedge_eq_span_ιMulti _ _ _ _ L₀ n u _ hF
  obtain ⟨ε, hε, e⟩ := ZUnit.exists_of_span_eq hne (hw₀.symm.trans hW)
  have hεα : ε * α ≠ 0 := mul_ne_zero hε.1 hα
  have ha₀ : a₀ = (ε * α)⁻¹ • exteriorPower.ιMulti Ω₀ n u := by
    rw [e, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ hεα, one_smul]
  have ha := hP u _ ha₀
  have hne' : i ε ≠ 0 := (map_ne_zero i).2 hε.1
  have hiα : i α ≠ 0 := (map_ne_zero i).2 hα
  have e2 : exteriorPower.ιMulti Ω n (fun k => j (u k)) = i ε • i α • a := by
    rw [ha, smul_smul, smul_smul, ← map_mul, ← map_mul, mul_inv_cancel₀ hεα, map_one, one_smul]
  rw [hw, e2]
  have hu : i ε ∈ regAt ξ x := hreg _ hε.2.1
  have hv : (i ε)⁻¹ ∈ regAt ξ x := by
    rw [← map_inv₀]
    exact hreg _ hε.2.2
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨i ε, hu⟩, rfl⟩
  · refine ⟨⟨(i ε)⁻¹, hv⟩, ?_⟩
    show (i ε)⁻¹ • i ε • i α • a = i α • a
    rw [inv_smul_smul₀ hne']

theorem isCoeffAt_pull : ∀ (X₀ X : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ X₀) (i : Ω₀ →+* Ω) (V₀ V : Type) [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] (j : V₀ →+ V) (A₀ B₀ : Lat ξ₀ V₀) (A B : Lat ξ V) (p q : ℕ) (a₀ : ⋀[Ω₀]^p V₀) (b₀ : ⋀[Ω₀]^q V₀) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (x₀ : Cpt ξ₀) (u₁ : Fin p → V₀) (u₂ : Fin q → V₀), IsCptGen ξ₀ → IsCptGen ξ → Dominates ξ ξ₀ f i → IsExtOver i j → x₀.1 = f x.1 → A₀.IsFrameAt u₁ x₀ → B₀.IsFrameAt u₂ x₀ → A x = A₀.pull ξ f j x → B x = B₀.pull ξ f j x → IsCoeffAt A₀ B₀ p q a₀ b₀ x₀ 1 → CptIn.IsPullWedge i j a₀ a → CptIn.IsPullWedge i j b₀ b → IsCoeffAt A B p q a b x 1 := by
  intro X₀ X Ω₀ Ω _ _ ξ₀ ξ f i V₀ V _ _ _ _ j A₀ B₀ A B p q a₀ b₀ a b x x₀ u₁ u₂ _ _ hD hE hx hF₁ hF₂ hA hB hC hPa hPb
  obtain ⟨α, β, hα, -, hAw, hBw, hαβ⟩ := hC
  rw [one_mul] at hαβ
  subst hαβ
  obtain ⟨y, hy⟩ := x₀
  obtain rfl : y = f x.1 := hx
  exact ⟨i α, i α, (map_ne_zero i).2 hα, (map_ne_zero i).2 hα,
    wedge_eq_span_pull hD hE x hy hα hF₁ hA hAw hPa, wedge_eq_span_pull hD hE x hy hα hF₂ hB hBw hPb, one_mul _⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LinePull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExteriorCoeffBaseChangeCompatStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exterior_coeff_base_change_compat : ∀ (X₀ X : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ X₀) (ξ : Spec (CommRingCat.of Ω) ⟶ X) (f : X ⟶ X₀) (i : Ω₀ →+* Ω) (V₀ V : Type) [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V] (j : V₀ →+ V) (A₀ B₀ : Lat ξ₀ V₀) (A B : Lat ξ V) (p q : ℕ) (a₀ : ⋀[Ω₀]^p V₀) (b₀ : ⋀[Ω₀]^q V₀) (a : ⋀[Ω]^p V) (b : ⋀[Ω]^q V) (x : Cpt ξ) (x₀ : Cpt ξ₀) (u₁ : Fin p → V₀) (u₂ : Fin q → V₀), IsCptGen ξ₀ → IsCptGen ξ → Dominates ξ ξ₀ f i → IsExtOver i j → x₀.1 = f x.1 → A₀.IsFrameAt u₁ x₀ → B₀.IsFrameAt u₂ x₀ → A x = A₀.pull ξ f j x → B x = B₀.pull ξ f j x → IsCoeffAt A₀ B₀ p q a₀ b₀ x₀ 1 → CptIn.IsPullWedge i j a₀ a → CptIn.IsPullWedge i j b₀ b → IsCoeffAt A B p q a b x 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull | exact GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LinePull.isCoeffAt_pull <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsC2AtOfIsPotential
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm
  ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo
  GlobalTheory.CompanionTheory.Ar.PB

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isSmoothHerm_combLine {σ : Type} [Fintype σ] {A : σ → HermLine ι} (hA : ∀ a, IsSmoothHerm (A a))
    (n : σ → ℤ) : IsSmoothHerm (GlobalTheory.CompanionTheory.Ar.PB.combLine A n) := by
  refine contDiffOn_prod fun a _ => ?_
  intro z hz
  have h0 : (A a).h z ≠ 0 := ((A a).pos z hz).ne'
  have hf := hA a z hz
  have key : ∀ m : ℤ, ContDiffWithinAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (A a).h z ^ m)
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} z := by
    intro m
    cases m with
    | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hf.pow k
    | negSucc k =>
      simp only [zpow_negSucc]
      exact (hf.pow (k + 1)).inv (pow_ne_zero _ h0)
  exact key _

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {P : LocPot X}
    (hP : IsPotential A P) (x : X) : IsTwiceDifferentiableAt A P x := by
  intro j hj
  have hm : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' P.U x :=
    ⟨(A.chart j).map_source hj, by
      rw [Set.mem_preimage, (A.chart j).left_inv hj]; exact P.mem_U x⟩
  exact (contDiffAt_of_isPotential A P hP x j hm).of_le (by
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))

theorem mInt_potOf_eq_of_deg {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) {L L' : Fin e → HermLine ι}
    (hL : ∀ j, IsSmoothHerm (L j)) (hL' : ∀ j, IsSmoothHerm (L' j)) (ha : ∀ j, (L j).a = (L' j).a) :
    mInt R.A (fun j => potOf R (L j)) (fun _ => 1) = mInt R.A (fun j => potOf R (L' j)) (fun _ => 1) := by
  let B : Fin e → HermLine ι := fun j => GlobalTheory.CompanionTheory.Ar.PB.combLine ![L j, L' j] ![1, -1]
  have hB0 : ∀ j, (B j).a = 0 := fun j => by
    rw [(combLine_div (L j) (L' j)).1, ha j, sub_self]
  have hBs : ∀ j, IsSmoothHerm (B j) := fun j =>
    isSmoothHerm_combLine (fun a => by
      fin_cases a
      · exact hL j
      · exact hL' j) _
  let u : Fin e → R.X → ℝ := fun j x => Real.log ((B j).h (R.lift x x))
  have hu : ∀ j, R.A.Smooth (u j) := fun j => smooth_diag R (hBs j) (hB0 j)
  have h1 : mInt R.A (fun j => potOf R (L j)) (fun _ => 1) =
      mInt R.A (fun j => potOf R (L' j) + LocPot.ofFun (u j)) (fun _ => 1) := by
    refine mInt_congr _ (locDens_congr_of_eqOn R fun i x y hy => ?_) fun _ => rfl
    show Real.log ((L i).h (R.lift x y)) = Real.log ((L' i).h (R.lift x y)) + Real.log ((B i).h (R.lift y y))
    have hm := (R.mem x y hy).1
    rw [← h_eq_of_sameOrbit (hB0 i) (R.compat x y y ⟨hy, R.mem_U y⟩), (combLine_div (L i) (L' i)).2,
      Real.log_div ((L i).pos _ hm).ne' ((L' i).pos _ hm).ne']
    ring
  rw [h1]
  exact massIndep R.A _ u (fun i => isPotential_potOf R (hL' i)) hu

end Lines

section Coef

variable {Ψ : Type} [DecidableEq Ψ] {N : ℕ}

def rootCoef (r p : Ψ × Fin N) : ℤ :=
  (if p.1 = r.1 ∧ (p.2 : ℕ) + 1 = r.2 then 1 else 0) - (if p = r then 1 else 0)

theorem sum_rootCoef_mul [Fintype Ψ] (r : Ψ × Fin N) (f : Ψ × Fin N → ℤ) :
    ∑ p, rootCoef r p * f p =
      (if h : 0 < (r.2 : ℕ) then f (r.1, ⟨(r.2 : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) r.2.isLt⟩) else 0) - f r := by
  obtain ⟨τ, i⟩ := r
  simp only [rootCoef, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul]
  congr 1
  · split_ifs with h
    · rw [Finset.sum_eq_single (τ, ⟨(i : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩)]
      · rw [if_pos ⟨rfl, by simp only; omega⟩]
      · rintro ⟨τ', l⟩ - hne
        rw [if_neg]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        subst h1
        exact hne (by simp only [Prod.mk.injEq, true_and]; ext; simp only; omega)
      · simp
    · refine Finset.sum_eq_zero fun p _ => if_neg ?_
      rintro ⟨-, h2⟩
      have h2' : (p.2 : ℕ) + 1 = i := h2
      omega
  · simp

theorem sum_neg_mul_rootCoef [Fintype Ψ] (lam : Ψ × Fin N → ℝ) (p : Ψ × Fin N) :
    ∑ r, -lam r * (rootCoef r p : ℝ) = GlobalTheory.CompanionTheory.Ar.PB.gap lam p := by
  obtain ⟨τ, l⟩ := p
  have h2 : ∑ r : Ψ × Fin N, lam r * (if (τ, l) = r then (1 : ℝ) else 0) = lam (τ, l) := by simp
  have h1 : ∑ r : Ψ × Fin N, lam r * (if (τ, l).1 = r.1 ∧ (((τ, l).2 : Fin N) : ℕ) + 1 = r.2 then (1 : ℝ) else 0) =
      if h : (l : ℕ) + 1 < N then lam (τ, ⟨(l : ℕ) + 1, h⟩) else 0 := by
    split_ifs with h
    · rw [Finset.sum_eq_single (τ, ⟨(l : ℕ) + 1, h⟩)]
      · simp
      · rintro ⟨τ', m⟩ - hne
        rw [if_neg, mul_zero]
        rintro ⟨h1, h2⟩
        simp only at h1 h2
        subst h1
        exact hne (by simp only [Prod.mk.injEq, true_and]; ext; simp only; omega)
      · simp
    · refine Finset.sum_eq_zero fun r _ => ?_
      rw [if_neg, mul_zero]
      rintro ⟨-, h2⟩
      have := r.2.isLt
      simp only at h2
      omega
  have h3 : GlobalTheory.CompanionTheory.Ar.PB.gap lam (τ, l) =
      lam (τ, l) - if h : (l : ℕ) + 1 < N then lam (τ, ⟨(l : ℕ) + 1, h⟩) else 0 := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.gap gapX
    split_ifs with h <;> simp [h]
  rw [h3, ← h1, ← h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [rootCoef]
  push_cast
  ring

end Coef

section Real

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mInt_ref_eq {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (w : Fin D → σ) :
    mInt Re.R.A (fun j => potOf Re.R (Re.ref (w j))) (fun _ => 1) = Re.deg * S.degNum w := by
  have hth : ∀ a, IsPotential S.A (S.th a) := fun a => (S.sing a).1
  have hpb : ∀ a, IsPotential Re.R.A ((S.th a).pullback Re.π Re.holo.1) := fun a =>
    isPotentialPullback S.A Re.R.A Re.π Re.holo (S.th a) (hth a)
  have h1 := (GlobalTheory.T.monge_ampere_integral_congr_potentials D Re.R.X Re.R.A Set.univ (fun j => potOf Re.R (Re.ref (w j)))
    (fun j => (S.th (w j)).pullback Re.π Re.holo.1) (fun _ => 1) (fun _ => 1)
    (fun j => by simp) (fun i => Re.ref_pot (w i)) (fun i x _ => isC2At_of_isPotential _ (hpb _) x)
    (fun _ _ => rfl)).1
  rw [h1]
  exact (degreeFormulaInt S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree (fun j => S.th (w j)) (fun i => hth _)
    (fun _ => 1) (mIntegrableCont S.A _ (fun i => hth _) _ continuous_const)).2

theorem mInt_combLine_eq {D : ℕ} {σ : Type} [Fintype σ] {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P)
    (n : Fin D → σ → ℤ) :
    mInt Re.R.A (fun j => potOf Re.R (GlobalTheory.CompanionTheory.Ar.PB.combLine Re.ref (n j))) (fun _ => 1) =
      ∑ w : Fin D → σ, (∏ i, (n i (w i) : ℝ)) * (Re.deg * S.degNum w) := by
  have hP : ∀ a, IsPotential Re.R.A (potOf Re.R (Re.ref a)) := fun a => isPotential_potOf Re.R (Re.ref_smooth a)
  have h1 : mInt Re.R.A (fun j => potOf Re.R (GlobalTheory.CompanionTheory.Ar.PB.combLine Re.ref (n j))) (fun _ => 1) =
      mInt Re.R.A (fun j => sumPot (fun a => (n j a : ℝ)) fun a => potOf Re.R (Re.ref a)) (fun _ => 1) := by
    refine mInt_congr _ (fun j y hy => ?_) fun _ => rfl
    refine ReciprocityTheory.ChartRestriction.G.Geo.maDens_congr fun i => ?_
    filter_upwards [((Re.R.A.chart j).isOpen_inter_preimage_symm (Re.R.isOpen_U ((Re.R.A.chart j).symm y))).mem_nhds
      ⟨hy, Re.R.mem_U _⟩] with y' hy'
    have hm := (Re.R.mem _ _ hy'.2).1
    show Real.log (∏ a, (Re.ref a).h _ ^ n i a) = ∑ a, (n i a : ℝ) * Real.log ((Re.ref a).h _)
    rw [Real.log_prod fun a _ => (zpow_pos ((Re.ref a).pos _ hm) _).ne']
    exact Finset.sum_congr rfl fun a _ => Real.log_zpow _ _
  rw [h1, (GlobalTheory.T.monge_ampere_integral_multilinear_expansion D Re.R.X Re.R.A σ Set.univ (fun a => potOf Re.R (Re.ref a)) (fun j a => (n j a : ℝ))
    (fun _ => 1) (fun j => by simp) (fun a x _ => isC2At_of_isPotential _ (hP a) x)
    (fun w => mIntegrableCont _ _ (fun i => hP _) _ continuous_const)).2]
  exact Finset.sum_congr rfl fun w _ => by rw [mInt_ref_eq Re w]

end Real

section Main

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

end Main

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalForm
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem exists_appellHumbert_frame_of_cubical :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (Lr : RigLB A) (_ : CubicalStr A Lr) (g : ℕ) (u₀ : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g), ∃ (u : HolUnif A Lr.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.ex = u₀.ex ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Lr.L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l) := by
  intro A _ _ Lr cs g u₀
  have hval := @valAt'_rules
  have hholprod := @holFamily_lift hval
  have hT := @cube_trivialisation_on_uniformising_space hval hholprod
  have hdbl := @exists_doubling_solution_pi
  have hdblu := @eventually_eq_zero_of_isBigO_cube_of_doubling
  have hlock := @LocalCube.exists_third_difference hdbl hdblu
  have hface := @cube_section_faces_and_doubling
  have hloc := @exists_localFrame_compatible_cube @hface hlock
  have hglob := @CubeFrame.exists_global_frame
  have hfac := @automorphyFactor_exp_linear_of_cube
  have hnf := @appellHumbert_normal_form_of_linear_exponent
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7⟩, T, hT1, hT2, hT3, hT4⟩ :=
    hT A _ Lr.L g u₀ Lr.isLB cs.t cs.isGen _ _ rfl rfl
  obtain ⟨fr, κ, hfr, hκ⟩ := hglob g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3
    (hloc g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full h6 h7 hT4)
  obtain ⟨a, B, ha, hab, hfa⟩ := hfac g _ _ h1 h2 h3 h4 h5 T hT1 hT2 hT3 u₀.Λ u₀.discrete u₀.full
    h6 h7 hT4 fr κ hfr hκ
  obtain ⟨Hm, χ, Ef, Q, hH, hχ, hE, hQ, hQ0, hQn⟩ := hnf g u₀.Λ u₀.discrete u₀.full a B ha hab
  obtain ⟨f1, f2, f3⟩ := hfr
  refine ⟨{ ex := u₀.ex, ex_add := u₀.ex_add, ex_onto := u₀.ex_onto, Λ := u₀.Λ, ker := u₀.ker,
            discrete := u₀.discrete, full := u₀.full, hol := u₀.hol,
            fr := fun i z => fr i z * Complex.exp (Q z),
            fr_hol := fun i => ?_, fr_ne := fun i z hz => ?_, fr_compat := fun i j z hz => ?_ },
    Hm, χ, rfl, hH, hχ, ?_⟩
  · have := f1 i
    rw [Set.inter_univ] at this
    exact this.mul hQ.cexp.differentiableOn
  · exact mul_ne_zero (f2 i z hz trivial) (Complex.exp_ne_zero _)
  · have := f3 i j z (le_trans hz (fun _ h => h.1)) (le_trans hz (fun _ h => h.2)) trivial
    rw [this]
    ring
  · intro l i z hz
    show fr i z * Complex.exp (Q z) = _ * (fr i (z + l) * Complex.exp (Q (z + l)))
    rw [← hQn l z, hfa l i z hz, Complex.exp_sub]
    have := Complex.exp_ne_zero (Q (z + l))
    field_simp

end GlobalTheory.CompanionTheory.Ar
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThetaMultiplierNormalFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_multiplier_normal_form : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (Lr : RigLB A) (_ : CubicalStr A Lr) (g : ℕ) (u₀ : HolUnif A (⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩ : LB A.left) g), ∃ (u : HolUnif A Lr.L g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), u.ex = u₀.ex ∧ Hm.IsHermitian ∧ (∀ l, ‖χ l‖ = 1) ∧ ∀ (l : u.Λ) i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ Lr.L.U i → u.fr i z = χ l * Complex.exp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)))) * u.fr i (z + l) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical | exact GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical | (intros; apply GlobalTheory.CompanionTheory.Ar.exists_appellHumbert_frame_of_cubical <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TopLeOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

def sc {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

def valR {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U) : Γ(X, U) →+* O :=
  (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom.comp (a.appLE U ⊤ h).hom

theorem top_le_of_closedPoint {O : Type} [CommRing O] [IsLocalRing O] (V : (Sp O).Opens)
    (h : IsLocalRing.closedPoint O ∈ V) : ⊤ ≤ V := by
  intro x _
  have hs : (x : Sp O) ⤳ IsLocalRing.closedPoint O :=
    (PrimeSpectrum.le_iff_specializes _ _).mp (IsLocalRing.le_maximalIdeal (x : PrimeSpectrum O).2.ne_top)
  exact hs.mem_open V.2 h

theorem valR_isUnit_iff {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ U) (b : Γ(X, U)) :
    IsUnit (valR a U h b) ↔ a (IsLocalRing.closedPoint O) ∈ X.basicOpen b := by
  have e : (a.appLE U ⊤ h).hom b = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (valR a U h b) := by
    simp [valR]
  have e2 := Scheme.basicOpen_appLE a ⊤ U h b
  rw [e, basicOpen_eq_of_affine] at e2
  have : a (IsLocalRing.closedPoint O) ∈ X.basicOpen b ↔ IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b := Iff.rfl
  rw [this]
  have e3 : (IsLocalRing.closedPoint O ∈ a ⁻¹ᵁ X.basicOpen b) ↔ (IsLocalRing.closedPoint O ∈ (PrimeSpectrum.basicOpen (valR a U h b))) := by
    rw [e2]; exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [e3]
  change _ ↔ (valR a U h b) ∉ IsLocalRing.maximalIdeal O
  simp [IsLocalRing.mem_maximalIdeal]

theorem valR_res {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ a ⁻¹ᵁ V) (h' : ⊤ ≤ a ⁻¹ᵁ U) (f : Γ(X, U)) :
    valR a V h ((X.presheaf.map (homOfLE hVU).op).hom f) = valR a U h' f := by
  simp only [valR, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_sc {O R : Type} [CommRing O] [CommRing R] {X : Scheme.{0}} (a : Sp O ⟶ X) (π : X ⟶ Sp R) (ρ : R →+* O)
    (hρ : a ≫ π = spMap ρ) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U) (r : R) : valR a U h (sc π U r) = ρ r := by
  have key : ∀ (g : Sp O ⟶ Sp R) (_ : g = spMap ρ) (e : ⊤ ≤ g ⁻¹ᵁ ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom ((g.appLE ⊤ ⊤ e).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) = ρ r := by
    rintro _ rfl e
    have e1 : (spMap ρ).appLE ⊤ ⊤ e = (spMap ρ).appTop := Scheme.Hom.appLE_eq_app (f := spMap ρ) (U := ⊤)
    have e2 := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ρ)
    rw [e1]
    have e3 : ((spMap ρ).appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) = (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom (ρ r) :=
      (congrArg (fun q => q.hom r) e2).symm
    rw [e3]
    simp
  have e1 := Scheme.Hom.appLE_comp_appLE a π ⊤ U ⊤ (fun _ _ => trivial) h
  rw [← key (a ≫ π) hρ (by simpa using fun _ _ => trivial)]
  simp only [valR, sc, RingHom.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, e1]

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeGivesComponent
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeGivesComponent
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase.Mdl

section Alg

variable {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] {κ : Type}

abbrev chartZ (x : κ → Ω) (c : κ) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun j => x j / x c)

theorem chartZ_le (x : κ → Ω) (c : κ) {t : Ω} (ht : t ∈ chartZ x c) : t ∈ chartQ x c := by
  induction ht using Algebra.adjoin_induction with
  | mem a ha => exact Algebra.subset_adjoin ha
  | algebraMap r => simpa using intCast_mem (chartQ x c) r
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem exists_natCast_mul_mem (x : κ → Ω) (c : κ) {s : Ω} (hs : s ∈ chartQ x c) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : Ω) * s ∈ chartZ x c := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha => exact ⟨1, one_ne_zero, by simpa using Algebra.subset_adjoin ha⟩
  | algebraMap r =>
    refine ⟨r.den, r.den_nz, ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.2 r.den_nz
    have e : (r.den : Ω) * algebraMap ℚ Ω r = (r.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def]
      field_simp
    rw [e]
    exact intCast_mem _ _
  | add a b _ _ ha hb =>
    obtain ⟨k, hk0, hk⟩ := ha
    obtain ⟨l, hl0, hl⟩ := hb
    refine ⟨k * l, mul_ne_zero hk0 hl0, ?_⟩
    have e : ((k * l : ℕ) : Ω) * (a + b) = (l : Ω) * ((k : Ω) * a) + (k : Ω) * ((l : Ω) * b) := by
      push_cast
      ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hk) (mul_mem (natCast_mem _ _) hl)
  | mul a b _ _ ha hb =>
    obtain ⟨k, hk0, hk⟩ := ha
    obtain ⟨l, hl0, hl⟩ := hb
    refine ⟨k * l, mul_ne_zero hk0 hl0, ?_⟩
    have e : ((k * l : ℕ) : Ω) * (a * b) = ((k : Ω) * a) * ((l : Ω) * b) := by
      push_cast
      ring
    rw [e]
    exact mul_mem hk hl

def chartIncl (x : κ → Ω) (c : κ) : chartZ x c →+* chartQ x c :=
  ((chartZ x c).val : chartZ x c →+* Ω).codRestrict (chartQ x c) fun t => chartZ_le x c t.2

theorem natCast_notMem_chartQ (x : κ → Ω) (c : κ) {I : Ideal (chartQ x c)} (hI : I.IsPrime) {m : ℕ}
    (hm : m ≠ 0) : (m : chartQ x c) ∉ I := by
  intro h
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one]
  have hd : (m : Ω) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hi : (m : Ω)⁻¹ ∈ chartQ x c := by
    have := (chartQ x c).algebraMap_mem ((m : ℚ)⁻¹)
    simpa using this
  have e : (⟨(m : Ω)⁻¹, hi⟩ : chartQ x c) * (m : chartQ x c) = 1 :=
    Subtype.ext (by simp [hd])
  rw [← e]
  exact I.mul_mem_left _ h

theorem natCast_mul_notMem_iff (x : κ → Ω) (c : κ) {I : Ideal (chartQ x c)} (hI : I.IsPrime) {m : ℕ}
    (hm : m ≠ 0) (s : chartQ x c) : (m : chartQ x c) * s ∉ I ↔ s ∉ I := by
  refine not_congr ⟨fun h => ?_, fun h => I.mul_mem_left _ h⟩
  exact (hI.mem_or_mem h).resolve_left (natCast_notMem_chartQ x c hI hm)

end Alg

section Pts

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] [CharZero Ω] [Algebra ℚ Ω] {κ : Type}

theorem notMem_comap_iff {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal B) (P : A → Prop)
    (h : ∀ t, t ∉ I.comap f ↔ P t) (t : A) : f t ∉ I ↔ P t := by
  rw [← h t, Ideal.mem_comap]

theorem algebraMap_mem_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} (hp : Char0 ξ p) (r : ℚ) :
    algebraMap ℚ Ω r ∈ regAt ξ p := by
  have e : algebraMap ℚ Ω r = (r.num : Ω) * ((r.den : Ω))⁻¹ := by
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
  rw [e]
  exact (regAt ξ p).mul_mem (intCast_mem _ _) (Char0.unitAt_natCast hp r.den_nz).2.2

theorem chartQ_le_regAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {p : Cpt ξ} (hp : Char0 ξ p)
    (hc : InChart ξ x c p) {s : Ω} (hs : s ∈ chartQ x c) : s ∈ regAt ξ p := by
  induction hs using Algebra.adjoin_induction with
  | mem a ha => obtain ⟨j, rfl⟩ := ha; exact hc.2 j
  | algebraMap r => exact algebraMap_mem_regAt hp r
  | add a b _ _ ha hb => exact (regAt ξ p).add_mem ha hb
  | mul a b _ _ ha hb => exact (regAt ξ p).mul_mem ha hb

theorem char_zero_of_chart_inclusion {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {I : Ideal (chartQ x c)}
    (hI : I.IsPrime) {p : Cpt ξ} (hp : ∀ t : chartZ x c, chartIncl x c t ∉ I ↔ unitAt ξ p (t : Ω)) :
    Char0 ξ p := by
  intro r hr hF
  apply hF
  have h := (hp ⟨(r : Ω), natCast_mem _ r⟩).1
  apply h
  have e : chartIncl x c ⟨(r : Ω), natCast_mem _ r⟩ = (r : chartQ x c) := Subtype.ext (by simp [chartIncl])
  rw [e]
  exact natCast_notMem_chartQ x c hI hr.ne_zero

theorem notMem_iff_unitAt {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {I : Ideal (chartQ x c)}
    (hI : I.IsPrime) {p : Cpt ξ} (hchar : Char0 ξ p) (hc : InChart ξ x c p)
    (hp : ∀ t : chartZ x c, chartIncl x c t ∉ I ↔ unitAt ξ p (t : Ω)) (s : chartQ x c) :
    s ∉ I ↔ unitAt ξ p (s : Ω) := by
  obtain ⟨m, hm, hms⟩ := exists_natCast_mul_mem x c s.2
  have e : chartIncl x c ⟨_, hms⟩ = (m : chartQ x c) * s := Subtype.ext (by simp [chartIncl])
  have h1 := hp ⟨_, hms⟩
  rw [e, natCast_mul_notMem_iff x c hI hm] at h1
  rw [h1]
  constructor
  · intro h
    exact unitAt_of_mul_right h (natCast_mem _ m) (chartQ_le_regAt hchar hc s.2)
  · intro h
    exact unitAt_mul (Char0.unitAt_natCast hchar hm) h

theorem isLocAt_of_unit {ξ : Spec (CommRingCat.of Ω) ⟶ X} {x : κ → Ω} {c : κ} {I : Ideal (chartQ x c)}
    {p : Cpt ξ} (hchar : Char0 ξ p) (hc : InChart ξ x c p)
    (hreg : ∀ a : Ω, a ∈ regAt ξ p ↔ ∃ s ∈ chartZ x c, unitAt ξ p s ∧ s * a ∈ chartZ x c)
    (hunit : ∀ s : chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) : IsLocAt (chartQ x c) I (regAt ξ p) := by
  refine fun a => ⟨fun ha => ?_, ?_⟩
  · obtain ⟨s, hs, hsu, hsa⟩ := (hreg a).1 ha
    exact ⟨⟨s, chartZ_le x c hs⟩, (hunit _).2 hsu, chartZ_le x c hsa⟩
  · rintro ⟨s, hs, hsa⟩
    have hu := (hunit s).1 hs
    have e : a = (s : Ω)⁻¹ * ((s : Ω) * a) := by
      rw [inv_mul_cancel_left₀ hu.1]
    rw [e]
    exact (regAt ξ p).mul_mem hu.2.2 (chartQ_le_regAt hchar hc hsa)

theorem chart_prime_component_point (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : κ → Ω) (c : κ)
    (hT : CoordTie ℤ ξ x) (hc0 : x c ≠ 0) (I : Ideal (chartQ x c)) (hI : I.IsPrime) :
    ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧
      IsLocAt (chartQ x c) I (regAt ξ p) := by
  have hJ : (I.comap (chartIncl x c)).IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨p, ⟨hc, hp⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ κ x hT c hc0 _ hJ
  have hp' := notMem_comap_iff (chartIncl x c) I (fun t => unitAt ξ p (t : Ω)) hp
  have hchar : Char0 ξ p := char_zero_of_chart_inclusion hI hp'
  have hunit := notMem_iff_unitAt hI hchar hc hp'
  exact ⟨p, hchar, hc, hunit, isLocAt_of_unit hchar hc (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ κ x hT c p hc) hunit⟩

end Pts

theorem chartPrime_point : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) :=
  fun _ _ _ _ ξ _ x c hT hc0 I hI => chart_prime_component_point ξ x c hT hc0 I hI

end GlobalTheory.CompanionTheory.Ar.SncBase.Mdl
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartPrimeGivesComponentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_prime_gives_component : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ I : Ideal (Mdl.chartQ x c), I.IsPrime → ∃ p : Cpt ξ, Char0 ξ p ∧ InChart ξ x c p ∧ (∀ s : Mdl.chartQ x c, s ∉ I ↔ unitAt ξ p (s : Ω)) ∧ IsLocAt (Mdl.chartQ x c) I (regAt ξ p) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point | exact GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.Mdl.chartPrime_point <;> assumption)
end
end
