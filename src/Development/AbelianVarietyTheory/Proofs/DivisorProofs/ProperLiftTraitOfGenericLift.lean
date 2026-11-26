module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerBoundaryEtaleCohomology
public import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentPicardGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLift
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem proper_lift_trait : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), IsProper π → ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (f : V →+* V') (fK : FractionRing V →+* FractionRing V'), (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) → ∀ (ξ : Sp V ⟶ X) (y : Sp (FractionRing V') ⟶ Y), y ≫ π = spMap fK ≫ jK V ≫ ξ → ∃ ξ' : Sp V' ⟶ Y, ξ' ≫ π = spMap f ≫ ξ ∧ jK V' ≫ ξ' = y := by
  intro X Y π hπ V V' _ _ _ _ _ f fK hf ξ y hy
  have hsq : jK V' ≫ spMap f = spMap fK ≫ jK V := by
    have e : fK.comp (algebraMap V (FractionRing V)) = (algebraMap V' (FractionRing V')).comp f :=
      RingHom.ext hf
    exact (spMap_comp f (algebraMap V' (FractionRing V'))).symm.trans
      ((congrArg spMap e.symm).trans (spMap_comp (algebraMap V (FractionRing V)) fK))
  have h : y ≫ π = jK V' ≫ (spMap f ≫ ξ) := by
    rw [hy, ← Category.assoc, ← hsq, Category.assoc]
  obtain ⟨x, hx1, hx2⟩ := val_exists (R := V') π y (spMap f ≫ ξ) h
  exact ⟨x, hx2, hx1⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperLiftTraitOfGenericLiftStatement
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_lift_trait_of_generic_lift : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), IsProper π → ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] (f : V →+* V') (fK : FractionRing V →+* FractionRing V'), (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) → ∀ (ξ : Sp V ⟶ X) (y : Sp (FractionRing V') ⟶ Y), y ≫ π = spMap fK ≫ jK V ≫ ξ → ∃ ξ' : Sp V' ⟶ Y, ξ' ≫ π = spMap f ≫ ξ ∧ jK V' ≫ ξ' = y := by
  first | exact @GlobalTheory.proper_lift_trait | exact GlobalTheory.proper_lift_trait | (intros; apply GlobalTheory.proper_lift_trait <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalVectorFieldOfOneFormFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalVectorFieldOfOneFormFunctional
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem exists_vectorField_of_functional : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ l : Glob1 F →ₗ[R] R, ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T, (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧ ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  intro R _ C _ F hF h0 l
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨c, hc, hsum⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  refine ⟨fun T ↦ ∑ i, algebraMap R (F.obj T) (l (Φ.w i)) • Φ.δ i T, ?_, ?_⟩
  · intro T T' φ ω
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, map_sum, map_mul,
      AlgHom.commutes, Φ.nat]
  · intro w T
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hc, ← map_mul, ← map_sum]
    have hw : l w = l (∑ i, c i w • Φ.w i) := congrArg l (hsum w)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sum]
    simp [mul_comm]

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalVectorFieldOfOneFormFunctionalStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_globalVectorField_of_oneForm_functional : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ l : Glob1 F →ₗ[R] R, ∃ δ : ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T, (∀ ⦃T T' : C⦄ (φ : T ⟶ T') (ω : Ω[F.obj T⁄R]), δ T' (p1 F φ ω) = mp F φ (δ T ω)) ∧ ∀ (w : Glob1 F) T, δ T (w.1 T) = algebraMap R (F.obj T) (l w) := by
  first | exact @GlobalTheory.AbCoh.exists_vectorField_of_functional | exact GlobalTheory.AbCoh.exists_vectorField_of_functional | (intros; apply GlobalTheory.AbCoh.exists_vectorField_of_functional <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseChangeCompatibleGlobalOneForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseChangeCompatibleGlobalOneForms
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem isBaseChange_glob1 (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
    (hF : HasFrame F) (h0 : CohomZeroIsConstants F) (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]) (he : ∀ w, e w = w.1 T) :
    IsBaseChange (F.obj T) e := by
  obtain ⟨n, ⟨Φ⟩⟩ := hF
  obtain ⟨l, hl, hsum⟩ := GlobalTheory.T.globalOneFormFrame_coordinates_constant R C F h0 n Φ
  let S := F.obj T
  let fwd : S ⊗[R] Glob1 F →ₗ[S] Ω[F.obj T⁄R] := e.liftBaseChange S
  let inv : Ω[F.obj T⁄R] →ₗ[S] S ⊗[R] Glob1 F :=
    ∑ i, (Φ.δ i T).smulRight ((1 : S) ⊗ₜ[R] Φ.w i)
  have hinv : ∀ ω, inv ω = ∑ i, Φ.δ i T ω ⊗ₜ[R] Φ.w i := by
    intro ω
    simp only [inv, LinearMap.sum_apply, LinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  have h1 : ∀ ω, fwd (inv ω) = ω := by
    intro ω
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hinv, map_sum]
    simp only [fwd, LinearMap.liftBaseChange_tmul, he]
    exact (Φ.sum T ω).symm
  have h2 : ∀ x, inv (fwd x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | tmul b w =>
      have : ∑ i, Φ.δ i T (w.1 T) ⊗ₜ[R] Φ.w i = (1 : S) ⊗ₜ[R] w := by
        conv_rhs => rw [hsum w]
        rw [TensorProduct.tmul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hl, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      show inv (e.liftBaseChange S (b ⊗ₜ[R] w)) = _
      rw [LinearMap.liftBaseChange_tmul, map_smul, he, hinv, this, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
  exact IsBaseChange.of_equiv (LinearEquiv.ofLinear fwd inv (LinearMap.ext h1) (LinearMap.ext h2))
    (fun w ↦ by simp [fwd])

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseChangeCompatibleGlobalOneFormsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBaseChange_compatibleGlobalOneForms : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → ∀ (T : C) (e : Glob1 F →ₗ[R] Ω[F.obj T⁄R]), (∀ w, e w = w.1 T) → IsBaseChange (F.obj T) e := by
  first | exact @GlobalTheory.AbCoh.isBaseChange_glob1 | exact GlobalTheory.AbCoh.isBaseChange_glob1 | (intros; apply GlobalTheory.AbCoh.isBaseChange_glob1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
namespace GlobalTheory.OTY.TwEst

open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def wt (A : WeightedAtlas n Y ι La) (E : La) (β : ι → Y → ℂ) (z : Y → V n) (y : Y) : ℝ :=
  -Real.log (A.nsq (A.kap + E) β y) + Real.log (A.nsq A.kap (jdet A z) y)

def quot (A : WeightedAtlas n Y ι La) (h β : ι → Y → ℂ) (y : Y) : ℂ :=
  h (A.pick y) y / β (A.pick y) y


open scoped Classical in
def ext0 {Y : Type*} (U : Set Y) (f : U → ℂ) (y : Y) : ℂ :=
  if hy : y ∈ U then f ⟨y, hy⟩ else 0

theorem extendByZeroOnSubset_apply_coe {Y : Type*} (U : Set Y) (f : U → ℂ) (y : U) : ext0 U f y = f y := by
  simp [ext0, y.2]

end

end GlobalTheory.OTY.TwEst

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.nz_facts {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] (A : WeightedAtlas n Y ι La)
    (L Λ : La) (s : Fin n → ι → Y → ℂ) (τ : ι → Y → ℂ) (C : ℝ) (hC0 : 0 < C)
    (hsq : ∀ y, A.sqn L s y ≤ 1) (hC : ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y) (y : Y) (hy : y ∈ nz A τ) :
    y ∉ A.zeroSet s ∧ psi A L s y ≤ 0 ∧
      -psi A L s y ≤ (n : ℝ) * (-Real.log (A.nsq Λ τ y)) + (n : ℝ) * Real.log C := by
  have hτy : τ (A.pick y) y ≠ 0 := hy
  have hτ0 : 0 < A.nsq Λ τ y := by
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr hτy) 2) (Real.exp_pos _)
  have hs0 : 0 < A.sqn L s y := by
    by_contra hle
    push_neg at hle
    have := hC y
    nlinarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hz' : ∀ k, s k (A.pick y) y = 0 := hz
    have : A.sqn L s y = 0 := by
      unfold WeightedAtlas.sqn WeightedAtlas.nsq
      simp [hz']
    linarith
  · unfold psi
    have := Real.log_nonpos hs0.le (hsq y)
    nlinarith
  · unfold psi
    have h1 : Real.log (A.nsq Λ τ y) ≤ Real.log C + Real.log (A.sqn L s y) := by
      rw [← Real.log_mul hC0.ne' hs0.ne']
      exact Real.log_le_log hτ0 (hC y)
    have := mul_le_mul_of_nonneg_left h1 hn
    nlinarith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfKummerClassOfUnitEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfKummerClassOfUnitEqZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.KumZero

theorem isUnit_top {A : Type} [CommRing A] {q : ℕ} (h : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem inv_sch {q : ℕ} {X : Scheme.{0}} (hX : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  rintro U ⟨x⟩
  have x' : U ⟶ X := x
  simpa using hX.map x'.appTop.hom

theorem unitSec_injective {X : Scheme.{0}} : Function.Injective (unitSec (U := X)) := by
  intro a b h
  have := (GlobalTheory.EtC.GmSec.gm_sec_bijective X).1 h
  simpa using congrArg (fun z => Additive.toMul z.down) this

theorem unitSec_surjective {X : Scheme.{0}} (b : Sec Gm X) : ∃ v, unitSec v = b := by
  obtain ⟨w, hw⟩ := (GlobalTheory.EtC.GmSec.gm_sec_bijective X).2 b
  exact ⟨Additive.toMul w.down, hw⟩

theorem sec_map_zsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) (n : ℤ) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (n • φ) x = n • Sec.map φ x := by
  have h : (n • φ).hom = n • φ.hom := (sheafToPresheaf _ _).map_zsmul (X := F) (Y := G) (f := φ) (r := n)
  unfold Sec.map
  rw [h, NatTrans.app_zsmul, ModuleCat.hom_zsmul, LinearMap.smul_apply]

theorem smul_unitSec (n : ℕ) {X : Scheme.{0}} (v : (Γ(X, ⊤))ˣ) : (n : ℤ) • unitSec v = unitSec (v ^ n) := by
  unfold unitSec ofRings.sec
  refine (map_zsmul (ModuleCat.Hom.hom ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op X))) (n : ℤ)
    (show (Scheme.Γ ⋙ unitsF).obj (op X) from ⟨Additive.ofMul v⟩)).symm.trans ?_
  congr 1

theorem map_q_unitSec (q : ℕ) {X : Scheme.{0}} (v : (Γ(X, ⊤))ˣ) :
    Sec.map ((q : ℤ) • 𝟙 Gm) (unitSec v) = unitSec (v ^ q) := by
  rw [sec_map_zsmul, ← smul_unitSec]
  rfl

theorem _root_.GlobalTheory.EtC.eq_pow_of_kum_eq_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) →
    ∀ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = 0 → ∃ v, u = v ^ q := by
  intro q _ A _ hq u hu
  have hX := isUnit_top hq
  obtain ⟨κ, -, bd, -, hex, ⟨s, hs⟩, -⟩ := GlobalTheory.T.exists_kummer_boundary_etale_cohomology q
  have h1 : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0 := by
    rw [hs _ u hX, hu, smul_zero]
  obtain ⟨y, hy⟩ := ((hex _ (inv_sch hX) 0).1 _).1 h1
  have hsc := GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))
  obtain ⟨b, rfl⟩ := hsc.2.1.2 y
  rw [hsc.2.2.2.2] at hy
  have hb := hsc.2.1.1 hy
  obtain ⟨v, rfl⟩ := unitSec_surjective b
  rw [map_q_unitSec] at hb
  exact ⟨v, (unitSec_injective hb).symm⟩

end GlobalTheory.EtC.KumZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowOfKummerClassOfUnitEqZeroStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_pow_of_kummerClassOfUnit_eq_zero : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → ∀ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = 0 → ∃ v, u = v ^ q := by
  first | (exact @GlobalTheory.EtC.eq_pow_of_kum_eq_zero) | (exact GlobalTheory.EtC.eq_pow_of_kum_eq_zero) | (intros; apply GlobalTheory.EtC.eq_pow_of_kum_eq_zero  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullback
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AbCoh

theorem prod_pullback_sq : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap σ) φ → ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left, IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) ∧ μ[A'].left ≫ φ = Φ ≫ μ[A].left ∧ (fst A' A').left ≫ φ = Φ ≫ (fst A A).left ∧ (snd A' A').left ≫ φ = Φ ≫ (snd A A).left ∧ (lift (𝟙 A') (toUnit A' ≫ η[A'])).left ≫ Φ = φ ≫ (lift (𝟙 A) (toUnit A ≫ η[A])).left ∧ (lift (toUnit A' ≫ η[A']) (𝟙 A')).left ≫ Φ = φ ≫ (lift (toUnit A ≫ η[A]) (𝟙 A)).left := by
  intro R R' _ _ σ A _ A' _ φ h
  have pA : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  have pA' : IsPullback (fst A' A').left (snd A' A').left A'.hom A'.hom := IsPullback.of_hasPullback _ _
  obtain ⟨Φ, h₁, h₂⟩ : ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left,
      Φ ≫ (fst A A).left = (fst A' A').left ≫ φ ∧ Φ ≫ (snd A A).left = (snd A' A').left ≫ φ :=
    ⟨pA.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ) (by
      rw [Category.assoc, Category.assoc, h.1.w, ← Category.assoc, ← Category.assoc, pA'.w]),
      pA.lift_fst _ _ _, pA.lift_snd _ _ _⟩
  have hP : IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) := by
    have q := pA'.paste_horiz h.1
    rw [← h₁, ← h.1.w] at q
    have r := (IsPullback.of_right q h₂ pA).paste_vert h.1
    rwa [Over.w, Over.w] at r
  have one : ∀ T : Over (Sp R'), (toUnit T ≫ η[A']).left ≫ φ = (T.hom ≫ spMap σ) ≫ η[A].left := by
    intro T
    let x₀ : Over.mk (T.hom ≫ spMap σ) ⟶ A := Over.homMk ((toUnit T ≫ η[A']).left ≫ φ) (by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]; rfl)
    have hx : x₀ * x₀ = x₀ := by
      apply Over.OverMorphism.ext
      rw [h.2 T 1 1 x₀ x₀ rfl rfl, _root_.mul_one]
      rfl
    have e : x₀ = 1 := mul_eq_left.1 hx
    have e' := congrArg (fun q => q.left) e
    refine e'.trans ?_
    show (toUnit _ ≫ η[A]).left = _
    rw [Over.comp_left, Over.toUnit_left]
    rfl
  let Ψ : Over.mk ((A' ⊗ A').hom ≫ spMap σ) ⟶ A ⊗ A := Over.homMk Φ hP.w
  have hm := h.2 (A' ⊗ A') (fst A' A') (snd A' A') (Ψ ≫ fst A A) (Ψ ≫ snd A A) h₁ h₂
  rw [← MonObj.comp_mul, Hom.mul_def, Hom.mul_def, lift_fst_snd, lift_fst_snd, Category.id_comp, Category.id_comp,
    Over.comp_left] at hm
  refine ⟨Φ, hP, hm.symm, h₁.symm, h₂.symm, ?_, ?_⟩
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
  · refine pA.hom_ext ?_ ?_
    · rw [Category.assoc, h₁, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst, one, Over.comp_left, Over.toUnit_left, ← Category.assoc, h.1.w]
    · rw [Category.assoc, h₂, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd, Over.id_left, Over.id_left, Category.id_comp, Category.comp_id]

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullbackStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpPullback_prod_self_isPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsGrpPullback A' A (spMap σ) φ → ∃ Φ : (A' ⊗ A').left ⟶ (A ⊗ A).left, IsPullback Φ (A' ⊗ A').hom (A ⊗ A).hom (spMap σ) ∧ μ[A'].left ≫ φ = Φ ≫ μ[A].left ∧ (fst A' A').left ≫ φ = Φ ≫ (fst A A).left ∧ (snd A' A').left ≫ φ = Φ ≫ (snd A A).left ∧ (lift (𝟙 A') (toUnit A' ≫ η[A'])).left ≫ Φ = φ ≫ (lift (𝟙 A) (toUnit A ≫ η[A])).left ∧ (lift (toUnit A' ≫ η[A']) (𝟙 A')).left ≫ Φ = φ ≫ (lift (toUnit A ≫ η[A]) (𝟙 A)).left := by
  first | exact @GlobalTheory.AbCoh.prod_pullback_sq | exact GlobalTheory.AbCoh.prod_pullback_sq | (intros; apply GlobalTheory.AbCoh.prod_pullback_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalInverse
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem Etale.contDiffAt_chart {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
    {A : WeightedAtlas n Y ι La} {U : Set Y} {z : Y → V n} (hE : Etale A U z) {x : Y} (hx : x ∈ U)
    {i : ι} (hi : x ∈ (A.chart i).source) :
    ContDiffAt ℂ ∞ (z ∘ (A.chart i).symm) (A.chart i x) := by
  have hS : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (A.chart i).isOpen_inter_preimage_symm hE.isOpen
  have hmem : A.chart i x ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U :=
    ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hx]⟩
  rw [contDiffAt_euclidean]
  intro k
  have hk : DifferentiableOn ℂ (fun w => (z ∘ (A.chart i).symm) w k)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) :=
    (EuclideanSpace.proj (𝕜 := ℂ) k).differentiable.comp_differentiableOn (hE.holo i)
  exact (contDiffOn_of_differentiableOn n _ _ hS hk).contDiffAt (hS.mem_nhds hmem)

theorem etale_local_inverse : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → ∀ v ∈ e.target, ∀ i, ((e.symm v : U) : Y) ∈ (A.chart i).source → ContDiffAt ℂ ∞ (fun v' => A.chart i (e.symm v' : U)) v ∧ (∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source) ∧ ∀ ξ : V n, fderiv ℂ (fun v' => A.chart i (e.symm v' : U)) v (jz A z i (e.symm v : U) ξ) = ξ := by
  intro n Y _ _ _ _ _ ι La _ A U z hE e he v hv i hi
  set g : V n → V n := z ∘ (A.chart i).symm with hg_def
  have hg : ContDiffAt ℂ ∞ g (A.chart i (e.symm v : U)) := hE.contDiffAt_chart (e.symm v).2 hi
  have hdet : (jz A z i (e.symm v : U)).det ≠ 0 := hE.det_ne i _ (e.symm v).2 hi
  set f' : V n ≃L[ℂ] V n :=
    (jz A z i (e.symm v : U)).toContinuousLinearEquivOfDetNeZero hdet with hf'_def
  have hf'coe : (f' : V n →L[ℂ] V n) = fderiv ℂ g (A.chart i (e.symm v : U)) := by
    ext w; rfl
  have hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) (A.chart i (e.symm v : U)) := by
    rw [hf'coe]; exact (hg.differentiableAt (by simp)).hasFDerivAt
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hstrict := hg.hasStrictFDerivAt' hf' hn

  have hgv : g (A.chart i (e.symm v : U)) = v := by
    have h1 : z (e.symm v : U) = e (e.symm v) := he (e.map_target hv)
    show z ((A.chart i).symm (A.chart i (e.symm v : U))) = v
    rw [(A.chart i).left_inv hi, h1, e.right_inv hv]

  set h : V n → V n := fun v' => A.chart i (e.symm v' : U) with hh_def
  have hcoe : ContinuousAt (fun v' => ((e.symm v' : U) : Y)) v :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt_symm hv)
  have hhc : ContinuousAt h v :=
    ContinuousAt.comp (g := A.chart i) (f := fun v' => ((e.symm v' : U) : Y)) (x := v)
      ((A.chart i).continuousAt hi) hcoe
  have hsrc : ∀ᶠ v' in 𝓝 v, ((e.symm v' : U) : Y) ∈ (A.chart i).source :=
    hcoe.preimage_mem_nhds ((A.chart i).open_source.mem_nhds hi)
  have htgt : ∀ᶠ v' in 𝓝 v, v' ∈ e.target := e.open_target.mem_nhds hv

  have hright : ∀ᶠ v' in 𝓝 v, g (h v') = v' := by
    filter_upwards [hsrc, htgt] with v' h1 h2
    have h3 : z (e.symm v') = e (e.symm v') := he (e.map_target h2)
    show z ((A.chart i).symm (A.chart i (e.symm v' : U))) = v'
    rw [(A.chart i).left_inv h1, h3, e.right_inv h2]

  have hleft : ∀ᶠ v' in 𝓝 v,
      hstrict.localInverse g f' (A.chart i (e.symm v : U)) (g (h v')) = h v' :=
    hhc.tendsto.eventually hstrict.eventually_left_inverse
  have heq : h =ᶠ[𝓝 v] hstrict.localInverse g f' (A.chart i (e.symm v : U)) := by
    filter_upwards [hleft, hright] with v' h1 h2
    rw [← h1, h2]
  have hinv := hstrict.to_localInverse
  rw [hgv] at hinv
  have hGc : ContDiffAt ℂ ∞ (hstrict.localInverse g f' (A.chart i (e.symm v : U))) v := by
    have := hg.to_localInverse hf' hn
    rw [hgv] at this
    exact this
  refine ⟨hGc.congr_of_eventuallyEq heq, hsrc, fun ξ => ?_⟩
  have hfd : fderiv ℂ h v = (f'.symm : V n →L[ℂ] V n) :=
    heq.fderiv_eq.trans hinv.hasFDerivAt.fderiv
  change fderiv ℂ h v (jz A z i (e.symm v : U) ξ) = ξ
  rw [hfd]
  exact f'.symm_apply_apply ξ

end GlobalTheory.OTY
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFree
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.KumSurj

theorem unitSec_mul' {U : Scheme.{0}} (u v : (Γ(U, ⊤))ˣ) : unitSec (u * v) = unitSec u + unitSec v := by
  unfold unitSec
  exact map_add ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op U)).hom
    (ULift.up (Additive.ofMul u)) (ULift.up (Additive.ofMul v))

theorem unitSec_surj {U : Scheme.{0}} (b : Sec Gm U) : ∃ u : (Γ(U, ⊤))ˣ, unitSec u = b := by
  obtain ⟨y, hy⟩ := (GlobalTheory.EtC.GmSec.gm_sec_bijective U).2 b
  exact ⟨Additive.toMul y.down, hy⟩

theorem inv_sp (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) : Inv q (sp A) := by
  intro U ⟨x⟩
  have h1 : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  simpa using h1.map (show U ⟶ Spec (CommRingCat.of A) from x).appTop.hom

end GlobalTheory.EtC.KumSurj


open GlobalTheory.EtC.KumSurj in
theorem GlobalTheory.EtC.kum_surjective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x := by
  intro q _ A _ hq hp x
  obtain ⟨κ, hκ, bd, hbd, hex, ⟨s, hs⟩, hlast⟩ := GlobalTheory.T.exists_kummer_boundary_etale_cohomology q
  have hE : Inv q (sp A) := inv_sp q A hq
  have hqX : IsUnit (q : Γ(Spec (CommRingCat.of A), ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  obtain ⟨_, h2, h3⟩ := hex (sp A) hE 0
  obtain ⟨_, _, _, hpc, _⟩ := GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)
  obtain ⟨hpid, _⟩ := GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive ℤ ((chains ℤ).obj (sp A)) (0 + 1)
  set y := HK.post ℤ ((chains ℤ).obj (sp A)) κ (0 + 1) (restrH (Int.castRingHom (ZMod q)) (sp A) (tw q 1) (0 + 1) x) with hy
  have hqy : (q : ℤ) • y = 0 := by
    have := (h3 y).2 ⟨x, rfl⟩
    rw [hpc, hpid] at this
    exact this
  have hy0 : y = 0 := by
    obtain ⟨e⟩ := GlobalTheory.T.etale_descent_picard_group A
    have h1 : (q : ℤ) • e y = 0 := by rw [← map_zsmul, hqy, map_zero]
    have h2' : (Additive.toMul (e y)) ^ q = 1 := by
      have := congrArg Additive.toMul h1
      rw [natCast_zsmul, toMul_nsmul] at this
      exact this
    have := hp _ h2'
    apply e.injective
    rw [map_zero]
    exact congrArg Additive.ofMul this
  obtain ⟨g, hg⟩ := (h2 x).1 hy0
  obtain ⟨-, hbij, hadd, -, -⟩ := GlobalTheory.T.degreeZeroSectionClass_properties ℤ Gm (Spec (CommRingCat.of A))
  obtain ⟨b, rfl⟩ := hbij.2 g
  obtain ⟨u, rfl⟩ := unitSec_surj b
  have hsu := hs _ u hqX
  rcases Int.units_eq_one_or s with rfl | rfl
  · exact ⟨u, by rw [← hg, hsu, one_smul]⟩
  · refine ⟨u⁻¹, ?_⟩
    have hsi := hs _ u⁻¹ hqX
    have hsum : bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u⁻¹)) +
        bd (sch.obj (Spec (CommRingCat.of A))) 0 (secClass Gm (unitSec u)) = 0 := by
      rw [← map_add (f := _), ← hadd, ← unitSec_mul', inv_mul_cancel]
      have h0 : unitSec (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) = 0 := by
        have := unitSec_mul' (1 : (Γ(Spec (CommRingCat.of A), ⊤))ˣ) 1
        rw [mul_one] at this
        exact (left_eq_add.1 this)
      have h00 : secClass Gm (0 : Sec Gm (Spec (CommRingCat.of A))) = 0 := by
        have := hadd 0 0
        rw [add_zero] at this
        exact left_eq_add.1 this
      rw [h0, h00, map_zero]
    rw [hsi, hsu, Units.neg_smul, Units.neg_smul, one_smul, one_smul] at hsum
    rw [← hg, hsu, Units.neg_smul, one_smul]
    rw [← neg_add] at hsum
    exact eq_neg_of_add_eq_zero_left (neg_eq_zero.1 hsum)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitKummerEqOfPicardTorsionFreeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_kummer_eq_of_picard_torsionFree : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], IsUnit (q : A) → (∀ c : CommRing.Pic A, c ^ q = 1 → c = 1) → ∀ x : Ht q (sp A) 1 1, ∃ u : (Γ(Spec (CommRingCat.of A), ⊤))ˣ, kum q u = x := by
  first | (exact @GlobalTheory.EtC.kum_surjective) | (exact GlobalTheory.EtC.kum_surjective) | (intros; apply GlobalTheory.EtC.kum_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem mem_map_of_smul_eq_zero_of_flat {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) (hb : t • b = 0) :
    b ∈ J.map (algebraMap R S) := by
  let f : J →ₗ[R] R := J.subtype
  let g : R →ₗ[R] R := LinearMap.mulLeft R t
  have ex : Function.Exact f g := by
    intro y
    change t * y = 0 ↔ y ∈ Set.range f
    rw [_root_.mul_comm, ← hJ]
    exact ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.2⟩
  have ex' := Module.Flat.lTensor_exact S ex
  have h0 : g.lTensor S (b ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    change b ⊗ₜ[R] (t * 1) = 0
    rw [_root_.mul_one, ← _root_.mul_one t, ← smul_eq_mul, ← TensorProduct.smul_tmul, hb,
      TensorProduct.zero_tmul]
  obtain ⟨y, hy⟩ := (ex' _).1 h0
  have key : ∀ y : S ⊗[R] J, TensorProduct.rid R S (f.lTensor S y) ∈ J.map (algebraMap R S) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s j =>
      rw [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, Algebra.smul_def]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ j.2)
    | add x z hx hz => rw [map_add (f := _), map_add (f := _)]; exact add_mem hx hz
  have := key y
  rwa [hy, TensorProduct.rid_tmul, _root_.one_smul] at this

theorem mem_map_ann_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (t : R) (J : Ideal R) (hJ : ∀ a, a ∈ J ↔ a * t = 0) (b : S) :
    b ∈ J.map (algebraMap R S) ↔ t • b = 0 := by
  refine ⟨fun hb ↦ ?_, mem_map_of_smul_eq_zero_of_flat t J hJ b⟩
  rw [Algebra.smul_def]
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_mul, _root_.mul_comm, (hJ a).1 ha, map_zero]
  | zero => exact MulZeroClass.mul_zero _
  | add x y _ _ hx hy => rw [_root_.mul_add, hx, hy, _root_.add_zero]
  | smul a x _ hx => rw [smul_eq_mul, _root_.mul_left_comm, hx, MulZeroClass.mul_zero]

theorem mem_map_span_singleton_iff {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (t : R) (b : S) :
    b ∈ (Ideal.span {t}).map (algebraMap R S) ↔ ∃ c : S, b = t • c := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, rfl⟩; exact ⟨a, by rw [Algebra.smul_def, _root_.mul_comm]⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, by rw [Algebra.smul_def, _root_.mul_comm]⟩

end GlobalTheory.AbCoh

namespace GlobalTheory.AbCoh

theorem preα_surjective_and_ker : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ _ _ hE hF U
  obtain ⟨hσ, hk, hσ₀, hk₀⟩ := hE
  have A := secPull_surjective_and_ker R R' (Ideal.span {t}) σ hσ hk X' X s' s φ h (prePair φ U.unop) rfl
  have B := secPull_surjective_and_ker R R₀ (RingHom.ker σ₀) σ₀ hσ₀ rfl X₀ X s₀ s φ₀ h₀
    (prePair φ₀ U.unop) rfl
  haveI : Flat s := hF
  have hfl : (algebraMap R (Sec s U.unop.1)).Flat := by
    change ((s.appLE ⊤ U.unop.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Flat
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv))
      (Flat.flat_appLE s (isAffineOpen_top _) U.unop.2 le_top)
  haveI : Module.Flat R (Sec s U.unop.1) := hfl
  exact ⟨A.1, fun b ↦ (A.2 b).trans (mem_map_span_singleton_iff t b), B.1,
    fun b ↦ (B.2 b).trans (mem_map_ann_iff t _ (fun a ↦ RingHom.mem_ker.trans (hk₀ a)) b)⟩

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSectionsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.surjective_deformation_affine_sections : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) [IsAffineHom φ] [IsAffineHom φ₀], SmallExt t σ σ₀ → Flat s → ∀ U : AffOp X, Function.Surjective (preα φ s s' U) ∧ (∀ b, preα φ s s' U b = 0 ↔ ∃ c, b = t • c) ∧ Function.Surjective (preα φ₀ s s₀ U) ∧ ∀ b : (OAff s).obj U, preα φ₀ s s₀ U b = 0 ↔ t • b = 0 := by
  first | exact @GlobalTheory.AbCoh.preα_surjective_and_ker | exact GlobalTheory.AbCoh.preα_surjective_and_ker | (intros; apply GlobalTheory.AbCoh.preα_surjective_and_ker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormula
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
namespace GlobalTheory.L2Cutoff

theorem cutoff_smooth_dbar : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ b : ℝ) (θ : ℝ → ℝ), SmoothR n X.z ψ → ContDiff ℝ ∞ θ → (∀ t, b ≤ t → θ t = 0) → IsOpen Ω → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ b → x ∈ Ω) → Smooth n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n X.z (fun y => (θ (δ * ψ y) : ℂ) * G y) x ξ = ((deriv θ (δ * ψ x) * δ : ℝ) : ℂ) * G x * dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ := by
  intro n M _ _ _ _ _ X ψ G Ω δ b θ hψ hθ hθ0 hΩ hG hsub
  have hψe : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e →
      ContDiffOn ℝ ∞ (fun v => ψ (e.symm v)) e.target := by
    intro e he
    have h1 := (Complex.reCLM.contDiff (n := ∞)).comp_contDiffOn (hψ e he)
    refine h1.congr fun v _ => ?_
    simp
  have hθd : ∀ t, DifferentiableAt ℝ θ t := fun t => (hθ.differentiable (by simp)) t
  have hθzero : ∀ t, b < t → θ =ᶠ[𝓝 t] fun _ => 0 := by
    intro t ht
    filter_upwards [lt_mem_nhds ht] with s hs
    exact hθ0 s hs.le
  have hloc : ∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → ∀ v ∈ e.target,
      (e.symm v ∈ Ω → DifferentiableAt ℂ (G ∘ e.symm) v) ∧
      (e.symm v ∉ Ω → ((fun x => (θ (δ * ψ x) : ℂ) * G x) ∘ e.symm) =ᶠ[𝓝 v] fun _ => 0) := by
    intro e he v hv
    constructor
    · intro hvΩ
      exact (hG e he).differentiableAt
        ((e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩)
    · intro hvΩ
      have hb : b < δ * ψ (e.symm v) := by
        by_contra h
        exact hvΩ (hsub _ (not_lt.1 h))
      have hc : ContinuousAt (fun w => δ * ψ (e.symm w)) v :=
        continuousAt_const.mul ((hψe e he).continuousOn.continuousAt (e.open_target.mem_nhds hv))
      filter_upwards [hc.eventually (lt_mem_nhds hb)] with w hw
      simp [hθ0 _ hw.le]
  refine ⟨?_, ?_⟩
  · intro e he v hv
    apply ContDiffAt.contDiffWithinAt
    by_cases hvΩ : e.symm v ∈ Ω
    · have hU := (e.isOpen_inter_preimage_symm hΩ).mem_nhds ⟨hv, hvΩ⟩
      have hGc : ContDiffAt ℝ ∞ (G ∘ e.symm) v :=
        ((contDiffOn_of_differentiableOn n _ _ (e.isOpen_inter_preimage_symm hΩ) (hG e he)).contDiffAt
          hU).restrict_scalars ℝ
      have hk : ContDiffAt ℝ ∞ (fun w => ((θ (δ * ψ (e.symm w)) : ℝ) : ℂ)) v :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp v
          (hθ.contDiffAt.comp v (contDiffAt_const.mul
            ((hψe e he).contDiffAt (e.open_target.mem_nhds hv))))
      exact hk.mul hGc
    · exact contDiffAt_const.congr_of_eventuallyEq ((hloc e he v hv).2 hvΩ)
  · intro x ξ
    obtain ⟨e, he, hx⟩ := exists_chart n X.z X.isLocalHomeomorph x
    have hzx : X.z x = e x := he hx
    have hv : X.z x ∈ e.target := by rw [hzx]; exact e.map_source hx
    have hsx : e.symm (X.z x) = x := by rw [hzx]; exact e.left_inv hx
    unfold dbarDot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [db_eq_wdb n X.z e he j _ x hx, db_eq_wdb n X.z e he j _ x hx]
    by_cases hxΩ : x ∈ Ω
    · have hGd := (hloc e he _ hv).1 (by rw [hsx]; exact hxΩ)
      have hψd : DifferentiableAt ℝ (fun w => ψ (e.symm w)) (X.z x) :=
        ((hψe e he).contDiffAt (e.open_target.mem_nhds hv)).differentiableAt (by simp)
      have hkd : DifferentiableAt ℝ (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) :=
        (hθd _).comp _ ((differentiableAt_id).const_mul δ)
      have hderiv : deriv (fun t => θ (δ * t)) (ψ (e.symm (X.z x))) =
          deriv θ (δ * ψ (e.symm (X.z x))) * δ := by
        have h1 : HasDerivAt (fun t : ℝ => δ * t) δ (ψ (e.symm (X.z x))) := by
          simpa using (hasDerivAt_id (ψ (e.symm (X.z x)))).const_mul δ
        exact ((hθd _).hasDerivAt.comp _ h1).deriv
      have h1 : ((fun y => (θ (δ * ψ y) : ℂ) * G y) ∘ e.symm) =
          fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ) * (G ∘ e.symm) w := rfl
      have hkd' : DifferentiableAt ℝ (fun w => (((fun t => θ (δ * t)) (ψ (e.symm w)) : ℝ) : ℂ))
          (X.z x) := differentiableAt_ofReal (DifferentiableAt.comp (f := fun w => ψ (e.symm w)) (X.z x) hkd hψd)
      rw [h1, wdb_mul hkd' (hGd.restrictScalars ℝ), wdb_of_differentiableAt hGd,
        wdb_ofReal_comp (k := fun t => θ (δ * t)) (v := fun w => ψ (e.symm w)) hkd hψd, hderiv]
      have h2 : ((fun y => (ψ y : ℂ)) ∘ e.symm) = fun w => ((ψ (e.symm w) : ℝ) : ℂ) := rfl
      rw [h2]
      simp only [Function.comp_apply, hsx]
      push_cast
      ring
    · have hb : b < δ * ψ x := by
        by_contra h
        exact hxΩ (hsub _ (not_lt.1 h))
      rw [ReciprocityTheory.L2DbarEstimates.wdb_congr n j _ _ _ ((hloc e he _ hv).2 (by rw [hsx]; exact hxΩ)),
        ((hθzero _ hb).deriv_eq)]
      simp [wdb]

end GlobalTheory.L2Cutoff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffHoloSmoothDbarFormulaStatement
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutoff_holo_smooth_dbar_formula : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (ψ : M → ℝ) (G : M → ℂ) (Ω : Set M) (δ b : ℝ) (θ : ℝ → ℝ), SmoothR n X.z ψ → ContDiff ℝ ∞ θ → (∀ t, b ≤ t → θ t = 0) → IsOpen Ω → (∀ e : OpenPartialHomeomorph M (V n), IsChart n X.z e → DifferentiableOn ℂ (G ∘ e.symm) (e.target ∩ e.symm ⁻¹' Ω)) → (∀ x, δ * ψ x ≤ b → x ∈ Ω) → Smooth n X.z (fun x => (θ (δ * ψ x) : ℂ) * G x) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n X.z (fun y => (θ (δ * ψ y) : ℂ) * G y) x ξ = ((deriv θ (δ * ψ x) * δ : ℝ) : ℂ) * G x * dbarDot n X.z (fun y => (ψ y : ℂ)) x ξ := by
  first | exact @GlobalTheory.L2Cutoff.cutoff_smooth_dbar | exact GlobalTheory.L2Cutoff.cutoff_smooth_dbar | (intros; apply GlobalTheory.L2Cutoff.cutoff_smooth_dbar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem exists_fin_span_of_cover {X : Scheme.{0}} (T : X.affineOpens) (B : Set Γ(X, T.1))
    (hB : ∀ x ∈ T.1, ∃ f ∈ B, x ∈ X.basicOpen f) :
    ∃ (n : ℕ) (b : Fin n → Γ(X, T.1)), Ideal.span (Set.range b) = ⊤ ∧ ∀ i, b i ∈ B := by
  have hsp : Ideal.span B = ⊤ := by
    rw [← T.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, hf, hxf⟩ := hB x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hf⟩, hxf⟩
  obtain ⟨F, hFB, hF⟩ := (Ideal.span_eq_top_iff_finite B).1 hsp
  refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, fun i ↦ hFB (F.equivFin.symm i).2⟩
  rw [eq_top_iff, ← hF]
  exact Ideal.span_mono fun x hx ↦ ⟨F.equivFin ⟨x, hx⟩, by simp⟩

theorem le_basicOpen_of_isUnit_mp {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R)
    {T S : AffOp X} (u : T ⟶ S) (f : (OAff s).obj T) (hu : IsUnit (mp (OAff s) u f)) :
    S.unop.1 ≤ X.basicOpen (show Γ(X, T.unop.1) from f) := by
  change IsUnit (X.presheaf.map (homOfLE (show S.unop.1 ≤ T.unop.1 from leOfHom u.unop)).op
    (show Γ(X, T.unop.1) from f)) at hu
  have h1 := Scheme.basicOpen_of_isUnit X hu
  rw [Scheme.basicOpen_res] at h1
  rw [← h1]; exact inf_le_right

theorem cohO_basis_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (P : Type) [Preorder P] (G : P → X.affineOpens) (hG : Monotone G), (∀ (U : X.affineOpens) (x : X), x ∈ U.1 → ∃ a, x ∈ (G a).1 ∧ (G a).1 ≤ U.1) → (∀ (a b : P) (x : X), x ∈ (G a).1 → x ∈ (G b).1 → ∃ c, c ≤ a ∧ c ≤ b ∧ x ∈ (G c).1) → Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull2 ∧ (CohomZeroIsConstants (OAff s) → CohomZeroIsConstants (hG.functor.op ⋙ OAff s)) := by
  intro R _ X s P _ G hG h1 h2
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s
  have hcov : ∀ T : AffOp X, ∃ (n : ℕ) (b : Fin n → (OAff s).obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp X) (u : T ⟶ S),
        IsUnit (mp (OAff s) u (b i)) →
          ∃ (t : Pᵒᵖ) (v : T ⟶ hG.functor.op.obj t) (w : hG.functor.op.obj t ⟶ S), v ≫ w = u := by
    intro T
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover T.unop
      {f | ∃ a, X.basicOpen f ≤ (G a).1 ∧ (G a).1 ≤ T.unop.1} (fun x hx ↦ by
        obtain ⟨a, hxa, haT⟩ := h1 T.unop x hx
        obtain ⟨f, hf, hxf⟩ := T.unop.2.exists_basicOpen_le (V := (G a).1) ⟨x, hxa⟩ hx
        exact ⟨f, ⟨a, hf, haT⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S u hu ↦ ?_⟩
    obtain ⟨a, hfa, haT⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op a, (homOfLE (show G a ≤ T.unop from haT)).op,
      (homOfLE (show S.unop ≤ G a from hS.trans hfa)).op, Quiver.Hom.unop_inj (Subsingleton.elim _ _)⟩
  have hdir : ∀ (t₁ t₂ : Pᵒᵖ) (S : AffOp X), (hG.functor.op.obj t₁ ⟶ S) → (hG.functor.op.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s).obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp X) (u : S ⟶ S'), IsUnit (mp (OAff s) u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (hG.functor.op.obj t₃ ⟶ S') := by
    intro t₁ t₂ S a₁ a₂
    have hS₁ : S.unop.1 ≤ (G t₁.unop).1 := leOfHom a₁.unop
    have hS₂ : S.unop.1 ≤ (G t₂.unop).1 := leOfHom a₂.unop
    obtain ⟨n, b, hb, hbB⟩ := exists_fin_span_of_cover S.unop
      {f | ∃ c, c ≤ t₁.unop ∧ c ≤ t₂.unop ∧ X.basicOpen f ≤ (G c).1} (fun x hx ↦ by
        obtain ⟨c, hc₁, hc₂, hxc⟩ := h2 t₁.unop t₂.unop x (hS₁ hx) (hS₂ hx)
        obtain ⟨f, hf, hxf⟩ := S.unop.2.exists_basicOpen_le (V := (G c).1) ⟨x, hxc⟩ hx
        exact ⟨f, ⟨c, hc₁, hc₂, hf⟩, hxf⟩)
    refine ⟨n, b, hb, fun i S' u hu ↦ ?_⟩
    obtain ⟨c, hc₁, hc₂, hfc⟩ := hbB i
    have hS := le_basicOpen_of_isUnit_mp s u (b i) hu
    exact ⟨Opposite.op c, ⟨(homOfLE hc₁).op⟩, ⟨(homOfLE hc₂).op⟩,
      ⟨(homOfLE (show S'.unop ≤ G c from hS.trans hfc)).op⟩⟩
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s) hG.functor.op H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv := _root_.GlobalTheory.CatCoh.Desc.Basis.oneCocycle_vanishing_comma_of_basis (OAff s) hG.functor.op H hcov hdir
  have hv2 := GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor (OAff s) hG.functor.op H hcov hdir
  refine ⟨⟨_root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg,
      _root_.GlobalTheory.CatCoh.pull1_restrict_surjective_of_comma _ _ hs hg hv⟩,
    ⟨GlobalTheory.T.comma_descent_injective _ _ hs hg hv, GlobalTheory.T.comma_descent_restriction_equiv _ _ hs hg hv hv2⟩, ?_⟩
  intro h0 g hg0
  have hcomp : ∀ ⦃t t' : Pᵒᵖ⦄ (a : t ⟶ t'), g t' = mp (OAff s) (hG.functor.op.map a) (g t) := by
    intro t t' a
    have e : d0 (hG.functor.op ⋙ OAff s) g t t' a = 0 := by rw [hg0]; rfl
    rw [amitsur_d0_apply] at e
    exact sub_eq_zero.1 e
  obtain ⟨g1, hg1c, hg1e⟩ := _root_.GlobalTheory.compat_family_extend (OAff s) hG.functor.op hs hg g hcomp
  have hd : d0 (OAff s) g1 = 0 := by
    funext T T' φ
    rw [amitsur_d0_apply, hg1c φ, sub_self]
    rfl
  obtain ⟨r, hr, huniq⟩ := h0 g1 hd
  refine ⟨r, fun t ↦ ?_, fun r' hr' ↦ huniq r' fun T ↦ ?_⟩
  · rw [← hg1e t]; exact hr _
  · refine sub_eq_zero.1 (hs T _ fun t u ↦ ?_)
    rw [map_sub, ← hg1c u, hg1e t, hr' t, AlgHom.commutes]
    exact sub_self _

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyBasisBijectiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structureSheafCohomology_basis_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (P : Type) [Preorder P] (G : P → X.affineOpens) (hG : Monotone G), (∀ (U : X.affineOpens) (x : X), x ∈ U.1 → ∃ a, x ∈ (G a).1 ∧ (G a).1 ≤ U.1) → (∀ (a b : P) (x : X), x ∈ (G a).1 → x ∈ (G b).1 → ∃ c, c ≤ a ∧ c ≤ b ∧ x ∈ (G c).1) → Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull1 ∧ Function.Bijective (CoefMap.restrict (OAff s) hG.functor.op).pull2 ∧ (CohomZeroIsConstants (OAff s) → CohomZeroIsConstants (hG.functor.op ⋙ OAff s)) := by
  first | exact @GlobalTheory.AbCoh.cohO_basis_bijective | exact GlobalTheory.AbCoh.cohO_basis_bijective | (intros; apply GlobalTheory.AbCoh.cohO_basis_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechBijectiveOfAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechBijectiveOfAffine
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

theorem trivCoord_bijective {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (s' : X' ⟶ Sp R') (V : X'.Opens) : Function.Bijective (trivCoord φ s' V) :=
  (GlobalTheory.AbLaw.SecOn.chart (LB.isLB_pull (LB.isLB_triv X) φ) (i0 φ)
    (by rw [triv_pull_U]; exact le_top)).bijective

theorem Φ_bijective_of_affine : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := by
  intro R R' _ _ _ X X' s s' φ h κ _ _ D hD' hD p
  have hB := GlobalTheory.AbLaw.secTermBaseChange_bijective (M := LB.triv X) (D := D) (LB.isLB_triv X) h (p + 1)
    fun t ht => hD t (Finset.card_pos.1 (by omega))
  exact (Function.Bijective.piMap fun t => trivCoord_bijective φ s' _).comp hB

end GlobalTheory.CechPoset
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechBijectiveOfAffineStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChangeTrivialBundleCech_bijective_of_affine : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := by
  first | exact @GlobalTheory.CechPoset.Φ_bijective_of_affine | exact GlobalTheory.CechPoset.Φ_bijective_of_affine | (intros; apply GlobalTheory.CechPoset.Φ_bijective_of_affine <;> assumption)
end
end
