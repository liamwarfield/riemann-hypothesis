module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExistsAfterFiniteExtensionOfCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyMumfordClassBilinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCentralizerOfCommutePadicPointsSpli
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BorelFiniteClassNumberCentraliserTorus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialZeroLocusCoordinates
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteHolds
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtension
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.TraitLift

theorem spMap_comp' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem mem_of_closedPoint {Y : Scheme.{0}} (U : Set Y) (hU : IsOpen U) (V : Type) [CommRing V] [IsLocalRing V]
    (ξ : Sp V ⟶ Y) (h : ξ (closedPoint V) ∈ U) (x : Sp V) : ξ x ∈ U := by
  have hs : x ⤳ closedPoint V := IsLocalRing.specializes_closedPoint x
  exact (hs.map ξ.continuous).mem_open hU h

theorem exists_finite_point {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (K : Type) [Field K] (x : Sp K ⟶ Y)
    (hx : x (closedPoint K) ∈ Set.range π) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (η : Sp L ⟶ X),
      η ≫ π = spMap (algebraMap K L) ≫ x := by
  obtain ⟨p, hp⟩ := hx
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := S) (e.hom ≫ pullback.snd π x)
  letI : Algebra K S := f.hom.toAlgebra
  have hsp : spMap (algebraMap K S) = e.hom ≫ pullback.snd π x := hf
  have hfin : Module.Finite K S := by
    have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (closedPoint K) hp
  haveI : Nontrivial S := (e.inv z).nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (S ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  refine ⟨S ⧸ m, inferInstance, inferInstance, inferInstance, spMap (Ideal.Quotient.mk m) ≫ e.hom ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, ← hsp, ← Category.assoc, spMap_comp']

theorem exists_lift_of_isFinite {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (R : Type) [CommRing R] [IsDomain R]
    [ValuationRing R] (η : Sp (FractionRing R) ⟶ X) (ξ : Sp R ⟶ Y) (h : η ≫ π = jK R ≫ ξ) :
    ∃ l : Sp R ⟶ X, l ≫ π = ξ ∧ jK R ≫ l = η := by
  have hUC : UniversallyClosed π := inferInstance
  have h2 : (ValuativeCriterion.Existence ⊓ @QuasiCompact) π := by
    rw [← UniversallyClosed.eq_valuativeCriterion]; exact hUC
  let S : ValuativeCommSq π :=
    { R := R, K := FractionRing R, i₁ := η, i₂ := ξ, commSq := ⟨h⟩ }
  obtain ⟨l⟩ := (h2.1 S).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩

end GlobalTheory.Poinc.TraitLift

namespace GlobalTheory.Poinc.TraitLift

theorem exists_closure (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (L : Type) [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] :
    ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsLocalRing V₂) (j : V →+* V₂) (e : L →+* FractionRing V₂),
      GlobalTheory.Mum.Base V₂ ∧ IsDiscreteValuationRing V₂ ∧ Function.Injective j ∧ IsLocalHom j ∧
        ∀ a : V, e (algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a)) =
          algebraMap V₂ (FractionRing V₂) (j a) := by
  letI : Algebra V L := ((algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite V (integralClosure V L) := GlobalTheory.FormalIsogeny.finite_integralClosure V (FractionRing V) L
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful V (FractionRing V) L
  haveI hloc : IsLocalRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalRing V L
  haveI hdvr : IsDiscreteValuationRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) L
  haveI : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension (FractionRing V) L
  have hj := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj V L
  haveI : CharZero (integralClosure V L) := charZero_of_injective_algebraMap hj
  refine ⟨integralClosure V L, inferInstance, inferInstance, hloc, algebraMap V (integralClosure V L),
    (FractionRing.algEquiv (integralClosure V L) L).symm.toRingEquiv.toRingHom,
    ⟨⟨inferInstance, inferInstance, inferInstance,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V (integralClosure V L)⟩, inferInstance⟩,
    hdvr, hj, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom V L, fun a => ?_⟩
  have h1 : algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a) =
      algebraMap (integralClosure V L) L (algebraMap V (integralClosure V L) a) := rfl
  rw [h1]
  exact (FractionRing.algEquiv (integralClosure V L) L).symm.commutes _

end GlobalTheory.Poinc.TraitLift

namespace GlobalTheory.Poinc


open GlobalTheory.Poinc.TraitLift in
theorem exists_trait_lift_setup (hExt : TraitExtSt) : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i := by
  intro g n F Z i W8 X₁ hcl T ξ hξ hc
  haveI : IsFinite X₁.π := X₁.fin
  have hgen : (jK T.V ≫ ξ) (closedPoint (FractionRing T.V)) ∈ Set.range X₁.π := by
    exact mem_of_closedPoint _ hcl.isOpen T.V ξ hc _
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point X₁.π (FractionRing T.V) (jK T.V ≫ ξ) hgen
  haveI := T.complete
  obtain ⟨V₂, _, _, _, j, e, hB, hD, hj, hjl, he⟩ := exists_closure T.V L
  have hring : (algebraMap V₂ (FractionRing V₂)).comp j =
      (e.comp (algebraMap (FractionRing T.V) L)).comp (algebraMap T.V (FractionRing T.V)) :=
    RingHom.ext fun a => (he a).symm
  haveI : ValuationRing V₂ := inferInstance
  have hsq : (spMap e ≫ η) ≫ X₁.π = jK V₂ ≫ (spMap j ≫ ξ) := by
    rw [Category.assoc, hη, ← Category.assoc, spMap_comp', ← Category.assoc, ← Category.assoc, spMap_comp',
      show jK V₂ = spMap (algebraMap V₂ (FractionRing V₂)) from rfl, spMap_comp', hring]
  obtain ⟨l, hl1, -⟩ := exists_lift_of_isFinite X₁.π V₂ (spMap e ≫ η) (spMap j ≫ ξ) hsq
  obtain ⟨T', f'', fK'', hinj'', hloc'', -, hc'', hy''⟩ := hExt g n _ (zetaAway n) F V₂ hB hD
    (spMap (e.comp (algebraMap (FractionRing T.V) L)) ≫ T.y)
  have hring2 : (algebraMap T'.V (FractionRing T'.V)).comp (f''.comp j) =
      (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))).comp (algebraMap T.V (FractionRing T.V)) := by
    ext a
    simp only [RingHom.comp_apply]
    rw [← hc'', ← he]
  have key : jK T'.V ≫ spMap (f''.comp j) = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V := by
    rw [show jK T'.V = spMap (algebraMap T'.V (FractionRing T'.V)) from rfl,
      show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl, spMap_comp', spMap_comp', hring2]
  haveI := hloc''
  refine ⟨T', f''.comp j, fK''.comp (e.comp (algebraMap (FractionRing T.V) L)), spMap f'' ≫ l, hinj''.comp hj,
    inferInstance, fun a => (RingHom.congr_fun hring2 a).symm, ?_, ?_, ?_⟩
  · rw [hy'', ← Category.assoc, spMap_comp']
  · rw [Category.assoc, hl1, ← Category.assoc, spMap_comp']
  · calc jK T'.V ≫ (spMap f'' ≫ l) ≫ X₁.π = jK T'.V ≫ spMap (f''.comp j) ≫ ξ := by
          rw [Category.assoc, hl1, ← spMap_comp', Category.assoc]
      _ = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V ≫ ξ := by
          rw [← Category.assoc, key, Category.assoc]
      _ = T'.y ≫ i := by
          rw [hξ, hy'', ← spMap_comp']
          simp only [Category.assoc]

end GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem traitLift_setup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i :=
  exists_trait_lift_setup GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR

end GlobalTheory.Poinc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trait_lift_thetaSetup_model_after_extension : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i := by
  first | exact @GlobalTheory.Poinc.traitLift_setup | exact GlobalTheory.Poinc.traitLift_setup | (intros; apply GlobalTheory.Poinc.traitLift_setup <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartSiegelLevelCoverSharpTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartSiegelLevelCoverSharpTheta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PoincChart
open GlobalTheory.SiegLev GlobalTheory.AbLaw

theorem chartL : ∀ (n N : ℕ) (X Y : Scheme.{0}) (sX : X ⟶ Sp (cycAway n)) (sY : Y ⟶ Sp (cycAway N)) (q : Y ⟶ X), 0 < n → 0 < N → Smooth sX → Smooth sY → IsFinite q → Etale q → Surjective q → ∀ η ∈ genericPoints X, ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (cycAway N) Ω) (_ : ArithBase (cycAway N) Ω) (R : Subalgebra (cycAway N) Ω) (y : Sp R ⟶ Y), R.FG ∧ (∀ z : Ω, ∃ a ∈ R, ∃ c ∈ R, z = a / c) ∧ y ≫ sY = spMap (algebraMap (cycAway N) R) ∧ (∀ w, (spMap R.val.toRingHom ≫ y ≫ q) w = η) ∧ ((spMap R.val.toRingHom ≫ y ≫ q).stalkMap (genericPoint (Sp Ω))).hom.Finite := GlobalTheory.T.exists_chart_finite_etale_cover_generic_point

theorem pullL : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T T' : Scheme.{0}) (P : PolAV T) (P' : PolAV T') (u : T ⟶ F.X) (f : T' ⟶ T) (φ : P'.A.left ⟶ P.A.left), SharpOver F W P u → IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → SharpOver F W P' (f ≫ u) := GlobalTheory.T.sharp_polarization_pullback_stable

theorem exists_isSharpBasis (h : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) :
    ∃ bas : (Fin (2 * (8 * h)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)), IsSharpBasis W bas := by
  have hS : (W + W.transpose).transpose = W + W.transpose := by
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have h1 : (W + W.transpose) * (W + W.transpose).adjugate = 1 := by rw [Matrix.mul_adjugate, hW.2, one_smul]
  have h2 : (W + W.transpose).adjugate * (W + W.transpose) = 1 := by rw [Matrix.adjugate_mul, hW.2, one_smul]
  let e : (Fin 8 → (Fin h ⊕ Fin h → ℤ)) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ)) :=
    { twistSnd (W + W.transpose).adjugate with
      invFun := twistSnd (W + W.transpose)
      left_inv := twistSnd_twistSnd _ _ h1
      right_inv := twistSnd_twistSnd _ _ h2 }
  refine ⟨(sharpReindex h).trans e, fun i j => ?_⟩
  rw [← sum_omegaStd_single h i j]
  exact sum_omegaStd_twistSnd _ _ hS h1 _ _

section
open MonObj

def powBaseR {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) : TBase (cycAway (n * k)) k where
  ζ := (cycBase (mul_ne_zero hn hk)).ζ ^ n
  unit := by
    have h : IsUnit ((n : cycAway (n * k)) * (k : cycAway (n * k))) := by
      rw [← Nat.cast_mul]
      exact isUnit_natCast (mul_ne_zero hn hk)
    exact isUnit_of_mul_isUnit_right h
  prim K _ β := by
    rw [Units.val_pow_eq_pow_val, map_pow, cycBase_ζ]
    exact (isPrimitiveRoot_map (mul_ne_zero hn hk) β).pow (Nat.pos_of_ne_zero (mul_ne_zero hn hk)) rfl

theorem powBaseR_pow {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) : (powBaseR hn hk).ζ ^ k = 1 := by
  show ((cycBase (mul_ne_zero hn hk)).ζ ^ n) ^ k = 1
  rw [← pow_mul]
  exact Units.ext ((Units.val_pow_eq_pow_val _ _).trans
    (Subtype.ext (Complex.isPrimitiveRoot_exp _ (mul_ne_zero hn hk)).pow_eq_one))

def lowerTo {h M N d : ℕ} {B : Type} [CommRing B] {ζ' ζ : B} {S : Scheme.{0}} {s : S ⟶ Sp B}
    (C : SiegPre h M ζ' s) (hM : M = N * d) (h0 : M ≠ 0) (hζ : ζ = ζ' ^ d) : SiegPre h N ζ s where
  A := C.A
  ab := C.ab
  P := C.P
  isLB := C.isLB
  rig₁ := C.rig₁
  rig₂ := C.rig₂
  symm := C.symm
  lev a := C.lev a ^ d
  lev_add := (SiegLower.lower C hM h0 (RingHom.id B) hζ).lev_add
  lev_tors := (SiegLower.lower C hM h0 (RingHom.id B) hζ).lev_tors
  geom K _ _ x β z hx hz := (SiegLower.lower C hM h0 (RingHom.id B) hζ).geom K x β z
    (by rw [show spMap (RingHom.id B) = 𝟙 _ from Spec.map_id _, Category.comp_id]; exact hx) hz

theorem exists_sharpOver_cover (g n k : ℕ) (F : SFam g n (zetaAway n)) (F' : SFam g (n * k) (zetaAway (n * k)))
    (κ : cycAway n →+* cycAway (n * k)) (q : F'.X ⟶ F.X) (hn : 0 < n) (hk3 : 3 ≤ k) (hko : Odd k)
    (hζ : κ (zetaAway n) = zetaAway (n * k) ^ k) (hqs : q ≫ F.s = F'.s ≫ spMap κ)
    (hq : SiegLev.SRel F'.univ F.univ k 1 q) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J]
    (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J)
    (bas : (Fin (2 * (8 * g)) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin g ⊕ Fin g → ℤ))) (hW : IsE8 W) (hb : IsSharpBasis W bas)
    (hw : (W + W.transpose) * a w = W) (hw' : (W + W.transpose) * a w' = W.transpose)
    (hs : ∀ u v, ∃ j, a j = Matrix.single u v 1) :
    ∃ (b : TBase (cycAway (n * k)) k) (t : TObj (8 * g) k J b F'.s), t.Prim w w' ∧ SharpOver F W t.pol q := by
  have hk : k ≠ 0 := by omega
  have hnk : n * k ≠ 0 := mul_ne_zero hn.ne' hk
  let b := powBaseR hn.ne' hk
  have hbζ : (b.ζ : cycAway (n * k)) = zetaAway (n * k) ^ n := Units.val_pow_eq_pow_val _ _
  let c : SiegPre g k (b.ζ : cycAway (n * k)) F'.s := lowerTo F'.univ (mul_comm n k) hnk hbζ
  have hc : c.Principal := F'.princ
  have hd : SmoothOfRelativeDimension g c.A.hom :=
    SiegSharpCover.smoothDim c (by omega) b.ζ.isUnit b.unit
  obtain ⟨L₁, L₂⟩ := abelianSchemeLaws_all
  haveI : IsDedekindDomain (cycAway (n * k)) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsLocallyNoetherian (Sp (cycAway (n * k))) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of _)))
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  haveI : IsLocallyNoetherian F'.X := LocallyOfFiniteType.isLocallyNoetherian F'.s
  obtain ⟨t, ht, hp⟩ := GlobalTheory.exists_isSharp_and_prim L₁ L₂ Moduli.cube_of_isLB g (8 * g) W J a w w' bas hW hb hw hw'
    hs k (cycAway (n * k)) b F'.X F'.s c (powBaseR_pow hn.ne' hk) hko hc hd
  refine ⟨b, t, hp, ?_⟩
  let cT : SiegPre g n (zetaAway n) (F'.s ≫ spMap κ) := SiegLower.lower F'.univ (n := n) (d := k) rfl hnk κ hζ
  have hPB : SiegPB cT F.univ q := by
    obtain ⟨φ, hφ, ⟨φ₂, hsq, hP⟩, hlev⟩ := hq
    exact ⟨φ, φ₂, hφ, hsq, hP, fun a => by have e := hlev a; rw [pow_one] at e; exact e⟩
  obtain ⟨pr, h1, h2, h3, -, -⟩ := ht
  unfold SharpOver
  rw [hqs]
  exact ⟨cT, hPB, pr, h1, h2, h3⟩

end

theorem exists_chart : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ η ∈ genericPoints F.X, ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ ∀ j : ℕ, 1 ≤ j → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (κ : cycAway n →+* o) (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2)) (t : TObj (8 * g) ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J) (x : Sp R ⟶ F.X), R.FG ∧ (∀ y : Ω, ∃ a ∈ R, ∃ c ∈ R, y = a / c) ∧ t.Prim w w' ∧ (∀ (T : Scheme.{0}) (f : T ⟶ Sp R) (P : PolAV T) (φ : P.A.left ⟶ t.A.left), IsGrpPullback P.A t.A f φ → LBIso P.L (t.L.pull φ) → SharpOver F W P (f ≫ x)) ∧ (∀ w, (spMap R.val.toRingHom ≫ x) w = η) ∧ spMap R.val.toRingHom ≫ x ≫ F.s = spMap ((algebraMap o Ω).comp κ) ∧ κ.Finite ∧ ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  intro g n hg hn hodd F W hW η hη
  have hℓ : n.minFac.Prime := Nat.minFac_prime (by omega)
  have hℓn : n.minFac ∣ n := Nat.minFac_dvd n
  have hℓo : Odd n.minFac := Odd.of_dvd_nat hodd hℓn
  refine ⟨n.minFac, hℓ, hℓo, fun j hj => ?_⟩
  have h3 : 3 ≤ n.minFac := by
    have h2 := hℓ.two_le
    have : n.minFac ≠ 2 := fun e => by rw [e] at hℓo; exact absurd hℓo (by decide)
    omega
  have hk3 : 3 ≤ (n.minFac ^ j) ^ 2 :=
    le_trans (le_trans h3 (Nat.le_self_pow (by omega) _)) (Nat.le_self_pow (by omega) _)
  have hko : Odd ((n.minFac ^ j) ^ 2) := hℓo.pow.pow
  obtain ⟨κ, F', q, ⟨-, hζ, hfin, -, -⟩, ⟨hqs, hqfin, hqet, hqsurj, hq⟩, -⟩ :=
    GlobalTheory.SiegLevCover.exists_levelCover g n n.minFac j F hg hn hodd hℓ hℓn hj
  haveI := F.smooth
  haveI : Smooth F.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F.s
  haveI := F'.smooth
  haveI : Smooth F'.s := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) F'.s
  obtain ⟨Ω, _, _, _, R, y, hRfg, hfrac, hys, hpt, hstalk⟩ :=
    chartL n (n * (n.minFac ^ j) ^ 2) F.X F'.X F.s F'.s q (by omega) (Nat.mul_pos (by omega) (pow_pos (pow_pos hℓ.pos _) _)) inferInstance inferInstance
      hqfin hqet hqsurj η hη
  obtain ⟨bas, hbas⟩ := exists_isSharpBasis g W hW
  obtain ⟨a, w, w', hw, hw', hs⟩ := EighthPowerFactor.exists_matrices hW.2
  obtain ⟨b, t', hp', hsh'⟩ := exists_sharpOver_cover g n _ F F' κ q (by omega) hk3 hko hζ hqs hq W _ a w w' bas
    hW hbas hw hw' hs
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull _ (8 * g) _ _ b F'.X (Sp R) F'.s (spMap (algebraMap _ R)) y t' hys
  have hp : t.Prim w w' :=
    (GlobalTheory.shape_prim_pull_and_descend _ _ _ _ b (fun _ => 0) 0 w w' _ _ _ _ y t' t ht).2.1 hp'
  obtain ⟨ψ, hψ, hψL, -, -⟩ := ht
  have hsh : SharpOver F W t.pol (y ≫ q) := pullL _ _ _ _ F W _ _ t'.pol t.pol q y ψ hsh' hψ hψL
  refine ⟨cycAway (n * (n.minFac ^ j) ^ 2), Ω, inferInstance, inferInstance, inferInstance, inferInstance, κ, R, _,
    b, t, w, w', y ≫ q, hRfg, hfrac, hp, fun T f P φ h1 h2 => ?_, hpt, ?_, ((IsFinite.SpecMap_iff _).1 hfin), hstalk⟩
  · have e := pullL _ _ _ _ F W _ _ t.pol P (y ≫ q) f φ hsh h1 h2
    exact e
  · rw [Category.assoc, hqs, ← Category.assoc y, hys]
    simp only [spMap, ← Spec.map_comp]
    rfl

end GlobalTheory.PoincChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartSiegelLevelCoverSharpThetaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chart_siegelLevelCover_sharpTheta : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ η ∈ genericPoints F.X, ∃ ℓ : ℕ, ℓ.Prime ∧ Odd ℓ ∧ ∀ j : ℕ, 1 ≤ j → ∃ (o Ω : Type) (_ : CommRing o) (_ : Field Ω) (_ : Algebra o Ω) (_ : ArithBase o Ω) (κ : cycAway n →+* o) (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2)) (t : TObj (8 * g) ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J) (x : Sp R ⟶ F.X), R.FG ∧ (∀ y : Ω, ∃ a ∈ R, ∃ c ∈ R, y = a / c) ∧ t.Prim w w' ∧ (∀ (T : Scheme.{0}) (f : T ⟶ Sp R) (P : PolAV T) (φ : P.A.left ⟶ t.A.left), IsGrpPullback P.A t.A f φ → LBIso P.L (t.L.pull φ) → SharpOver F W P (f ≫ x)) ∧ (∀ w, (spMap R.val.toRingHom ≫ x) w = η) ∧ spMap R.val.toRingHom ≫ x ≫ F.s = spMap ((algebraMap o Ω).comp κ) ∧ κ.Finite ∧ ((spMap R.val.toRingHom ≫ x).stalkMap (genericPoint (Sp Ω))).hom.Finite := by
  first | exact @GlobalTheory.PoincChart.exists_chart | exact GlobalTheory.PoincChart.exists_chart | (intros; apply GlobalTheory.PoincChart.exists_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrou
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrou
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

noncomputable section

namespace GlobalTheory.HopfQuot

variable {k : Type} [Field k] {A : Type} [CommRing A] [HopfAlgebra k A] [IsCocomm k A]
  [Module.Finite k A] {C : Type} [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C]
  (π : A →ₐc[k] C)

instance isHopfIdeal_dual : (kerIdeal (CartierDual.map π)).IsHopfIdeal k := isHopfIdeal_kerIdeal _

abbrev proj : CartierDual k A →ₐc[k] CartierDual k A ⧸ kerIdeal (CartierDual.map π) :=
  Bialgebra.Quotient.mkBialgHom _

instance isCocomm_quot : IsCocomm k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) :=
  isCocomm_of_surjective (proj π) Ideal.Quotient.mk_surjective

def quotMap : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) →ₐc[k] A :=
  ((CartierDual.bidual k A).symm : _ →ₐc[k] A).comp (CartierDual.map (proj π))

theorem apply_quotMap (y : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)))
    (φ : CartierDual k A) : φ (quotMap π y) = y (proj π φ) := by
  simp [quotMap]

theorem proj_map (ψ : CartierDual k C) :
    proj π (CartierDual.map π ψ) = algebraMap k _ (counit (R := k) ψ) := by
  have hmem : CartierDual.map π ψ - algebraMap k _ (counit (R := k) ψ) ∈
      kerIdeal (CartierDual.map π) := by
    have h : CartierDual.map π ψ - algebraMap k _ (counit (R := k) ψ) =
        CartierDual.map π (ψ - algebraMap k _ (counit (R := k) ψ)) := by
      rw [map_sub, AlgHomClass.commutes]
    rw [h]
    exact Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])
  rw [← sub_eq_zero, ← AlgHomClass.commutes (proj π), ← map_sub]
  exact Ideal.Quotient.eq_zero_iff_mem.2 hmem

theorem quotMap_trivial (y : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π))) :
    π (quotMap π y) = algebraMap k C (counit (R := k) y) := by
  refine CartierDual.eq_of_forall_apply (R := k) fun ψ => ?_
  have h1 : ψ (π (quotMap π y)) = (CartierDual.map π ψ) (quotMap π y) := rfl
  rw [h1, apply_quotMap, proj_map, CartierDual.counit_apply, CartierDual.counit_apply,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul, map_smul]
  simp [mul_comm]

theorem mem_range_quotMap {a : A} (ha : ∀ x ∈ kerIdeal (CartierDual.map π), x a = 0) :
    a ∈ Set.range (quotMap π) := by
  have hann : (CartierDual.bidual k A a).ofConv ∈
      (LinearMap.ker (proj π : CartierDual k A →ₐ[k] CartierDual k A ⧸ kerIdeal (CartierDual.map π)).toLinearMap).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro x hx
    have hx' : x ∈ kerIdeal (CartierDual.map π) :=
      Ideal.Quotient.eq_zero_iff_mem.1 (LinearMap.mem_ker.1 hx)
    exact ha x hx'
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hann
  obtain ⟨y, hy⟩ := hann
  refine ⟨WithConv.toConv y, ?_⟩
  refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
  rw [apply_quotMap]
  exact LinearMap.congr_fun hy φ

theorem mul_map_apply {D : Type} [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A)
    (hf : kerIdeal f ≤ RingHom.ker π) (d : D) (r : CartierDual k A) (ψ : CartierDual k C) :
    (r * CartierDual.map π ψ) (f d) = r (f d) * ψ 1 := by
  have hπf := (kerIdeal_le_ker_iff f (π : A →ₐ[k] C)).1 hf
  have key : ∀ t : D ⊗[k] D, CartierDual.pair k A A (r ⊗ₜ CartierDual.map π ψ)
      (TensorProduct.map (f : D →ₗ[k] A) (f : D →ₗ[k] A) t) =
      r (f (TensorProduct.rid k D (LinearMap.lTensor D (counit (R := k) (A := D)) t))) * ψ 1 := by
    intro t
    induction t with
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_mul]
    | tmul x y =>
      rw [TensorProduct.map_tmul, CartierDual.pair_tmul_tmul, LinearMap.lTensor_tmul,
        TensorProduct.rid_tmul, CartierDual.map_apply]
      have h1 : π (f y) = algebraMap k C (counit (R := k) y) := hπf y
      erw [h1]
      rw [map_smul, map_smul, Algebra.algebraMap_eq_smul_one, map_smul]
      simp only [smul_eq_mul]
      have hfx : (f : D →ₗ[k] A) x = f x := rfl
      rw [hfx]
      ring
  rw [CartierDual.mul_apply]
  have hc : comul (R := k) (f d) = TensorProduct.map (f : D →ₗ[k] A) (f : D →ₗ[k] A) (comul d) :=
    (LinearMap.congr_fun (CoalgHomClass.map_comp_comul f) d).symm
  rw [hc, key, Coalgebra.lTensor_counit_comul, TensorProduct.rid_tmul, one_smul]

theorem ideal_apply_eq_zero {D : Type} [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A)
    (hf : kerIdeal f ≤ RingHom.ker π) (d : D) :
    ∀ x ∈ kerIdeal (CartierDual.map π), x (f d) = 0 := by
  intro x hx
  suffices h : ∀ r : CartierDual k A, (r * x) (f d) = 0 by simpa using h 1
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ψ, hψ, rfl⟩ := hx
    intro r
    have hψ' : ψ 1 = 0 := hψ
    erw [mul_map_apply π f hf d r ψ]
    rw [hψ', mul_zero]
  | zero => intro r; simp
  | add x y _ _ hx hy => intro r; simp [mul_add, hx r, hy r]
  | smul s x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx (r * s)

theorem ideal_eq_of_le_of_finrank_eq {R : Type} [CommRing R] [Algebra k R] [Module.Finite k R]
    {I J : Ideal R} (hIJ : I ≤ J)
    (h : Module.finrank k (R ⧸ I) = Module.finrank k (R ⧸ J)) : I = J := by
  have h1 := Submodule.finrank_quotient_add_finrank (I.restrictScalars k)
  have h2 := Submodule.finrank_quotient_add_finrank (J.restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k I).finrank_eq] at h1
  rw [(Submodule.Quotient.restrictScalarsEquiv k J).finrank_eq] at h2
  have hle : I.restrictScalars k ≤ J.restrictScalars k := hIJ
  exact Submodule.restrictScalars_injective k R R
    (Submodule.eq_of_le_of_finrank_eq hle (by omega))

theorem finrank_cartierDual (M : Type) [AddCommGroup M] [Module k M] [FiniteDimensional k M] :
    Module.finrank k (CartierDual k M) = Module.finrank k M :=
  (CartierDual.toDual k M).finrank_eq.trans Subspace.dual_finrank_eq

theorem quotMap_injective : Function.Injective (quotMap π) := by
  intro x y hxy
  have h := congrArg (CartierDual.bidual k A) hxy
  simp only [quotMap, BialgHom.comp_apply] at h
  erw [BialgEquiv.apply_symm_apply, BialgEquiv.apply_symm_apply] at h
  exact CartierDual.map_injective_of_surjective (f := proj π) Ideal.Quotient.mk_surjective h

theorem exists_quotient : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A]
    [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C]
    [Module.Finite k C] (π : A →ₐc[k] C), Function.Surjective π → ∃ (B : Type) (_ : CommRing B)
    (_ : HopfAlgebra k B) (_ : IsCocomm k B) (_ : Module.Finite k B) (j : B →ₐc[k] A),
    Function.Injective j ∧ kerIdeal j = RingHom.ker π ∧ ∀ (D : Type) [CommRing D]
    [Bialgebra k D] (f : D →ₐc[k] A), kerIdeal f ≤ RingHom.ker π → ∀ d, f d ∈ Set.range j := by
  intro k _ A _ _ _ _ C _ _ _ _ π hπ
  have hinj := quotMap_injective π
  refine ⟨CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)), inferInstance,
    inferInstance, inferInstance, inferInstance, quotMap π, hinj, ?_, ?_⟩
  · have hle : kerIdeal (quotMap π) ≤ RingHom.ker π :=
      (kerIdeal_le_ker_iff _ (π : A →ₐ[k] C)).2 (quotMap_trivial π)
    refine ideal_eq_of_le_of_finrank_eq (k := k) hle ?_
    have hA := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k A _ (quotMap π)
    have hD := GlobalTheory.T.finrank_hopfAlgebra_eq_range_mul_kernel k (CartierDual k A) (CartierDual k C) (CartierDual.map π)
    rw [LinearMap.finrank_range_of_inj (f := ((quotMap π : CartierDual k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) →ₐ[k] A)).toLinearMap)
      (by exact hinj),
      finrank_cartierDual] at hA
    rw [LinearMap.finrank_range_of_inj (f := ((CartierDual.map π : CartierDual k C →ₐ[k] CartierDual k A)).toLinearMap)
      (by exact CartierDual.map_injective_of_surjective hπ), finrank_cartierDual,
      finrank_cartierDual] at hD
    have hC : Module.finrank k (A ⧸ RingHom.ker π) = Module.finrank k C :=
      (Ideal.quotientKerAlgEquivOfSurjective (f := (π : A →ₐ[k] C)) hπ).toLinearEquiv.finrank_eq
    haveI : Nontrivial A := RingHom.domain_nontrivial (counitAlgHom k A : A →+* k)
    have hpos : 0 < Module.finrank k A := Module.finrank_pos
    rw [hC]
    have hQ : 0 < Module.finrank k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)) := by
      rcases Nat.eq_zero_or_pos (Module.finrank k (CartierDual k A ⧸ kerIdeal (CartierDual.map π)))
        with h0 | h0
      · rw [h0, mul_zero] at hD; omega
      · exact h0
    exact Nat.eq_of_mul_eq_mul_left hQ (by rw [← hA, hD, mul_comm])
  · intro D _ _ f hf d
    exact mem_range_quotMap π (ideal_apply_eq_zero π f hf d)

end GlobalTheory.HopfQuot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientFiniteCommGroupSchemeClosedSubgrouStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_finiteCommGroupScheme_closedSubgroup : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [HopfAlgebra k A] [IsCocomm k A] [Module.Finite k A] (C : Type) [CommRing C] [HopfAlgebra k C] [IsCocomm k C] [Module.Finite k C] (π : A →ₐc[k] C), Function.Surjective π → ∃ (B : Type) (_ : CommRing B) (_ : HopfAlgebra k B) (_ : IsCocomm k B) (_ : Module.Finite k B) (j : B →ₐc[k] A), Function.Injective j ∧ kerIdeal j = RingHom.ker π ∧ ∀ (D : Type) [CommRing D] [Bialgebra k D] (f : D →ₐc[k] A), kerIdeal f ≤ RingHom.ker π → ∀ d, f d ∈ Set.range j := by
  first | exact @GlobalTheory.HopfQuot.exists_quotient | exact GlobalTheory.HopfQuot.exists_quotient | (intros; apply GlobalTheory.HopfQuot.exists_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevel
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

open scoped Pointwise

namespace GlobalTheory.DefClassFin

def CCF : Prop :=
  ∀ (D : Type) [Ring D] [Algebra ℚ D] [FiniteDimensional ℚ D] (σ : D →+* Dᵐᵒᵖ) (β y : D) (p : ℕ) [Fact p.Prime],
    letI : TopologicalSpace (AfP p ⊗[ℚ] D) := moduleTopology (AfP p) (AfP p ⊗[ℚ] D)
    letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] D) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] D)
    ∀ U : Subgroup (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)),
      (∃ O : Set (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
        ∀ z ∈ O, TC D σ β y (AfP p) z.1 → TC D σ β y ℚ_[p] z.2 → z ∈ U) →
      ∃ S : Finset (((AfP p ⊗[ℚ] D)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] D)ˣ × ℚ_[p]ˣ)), ∀ z, TC D σ β y (AfP p) z.1 →
        TC D σ β y ℚ_[p] z.2 →
        ∃ γ : Dˣ × ℚˣ, (γ.1 : D) * β * (σ γ.1).unop = algebraMap ℚ D γ.2 * β ∧ Commute (γ.1 : D) y ∧
          ∃ s ∈ S, ∃ u ∈ U, z = dg D p γ * s * u

theorem ccf_holds : CCF :=
  GlobalTheory.T.borel_finite_classNumber_centraliserTorus GlobalTheory.T.exists_polynomialLocus_similitudeCentralizerTorus GlobalTheory.classNumberFinite_holds

theorem finite_of_cover {H : Type} [Group H] (Γ K : Subgroup H) (S : Set H) (hS : S.Finite)
    (h : ∀ g : H, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K, g = γ * s * k) :
    Finite (DoubleCoset.Quotient (Γ : Set H) (K : Set H)) := by
  haveI : Finite S := hS.to_subtype
  refine Finite.of_surjective (fun s : S => DoubleCoset.mk Γ K (s : H)) fun q => ?_
  obtain ⟨γ, hγ, s, hs, k, hk, e⟩ := h q.out
  refine ⟨⟨s, hs⟩, ?_⟩
  change DoubleCoset.mk Γ K s = q
  conv_rhs => rw [← DoubleCoset.out_eq' q]
  exact (@DoubleCoset.eq _ _ Γ K _ _).2 ⟨γ, hγ, k, hk, e⟩

theorem cover_of_relIndex {A B : Type} [Group A] [Group B] (Γ : Subgroup (A × B)) (K₁ : Subgroup A)
    (K₂ K' : Subgroup B) (hK : K'.relIndex K₂ ≠ 0) (S : Set (A × B)) (hS : S.Finite)
    (h : ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S, ∃ k ∈ K₁.prod K₂, g = γ * s * k) :
    ∃ S' : Set (A × B), S'.Finite ∧ ∀ g, ∃ γ ∈ Γ, ∃ s ∈ S', ∃ k ∈ K₁.prod K', g = γ * s * k := by
  haveI : (K'.subgroupOf K₂).FiniteIndex := ⟨hK⟩
  let T : Set (A × B) := Set.range (fun c : K₂ ⧸ K'.subgroupOf K₂ => ((1 : A), ((c.out : K₂) : B)))
  have hT : T.Finite := Set.finite_range _
  refine ⟨S * T, hS.mul hT, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, k, hk, rfl⟩ := h g
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_prod.1 hk
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul (K'.subgroupOf K₂) (⟨k.2, hk2⟩ : K₂)
  refine ⟨γ, hγ, s * (1, ((((⟨k.2, hk2⟩ : K₂) : K₂ ⧸ K'.subgroupOf K₂).out : K₂) : B)),
    Set.mul_mem_mul hs ⟨_, rfl⟩, (k.1, ((u : K₂) : B)⁻¹),
    Subgroup.mem_prod.2 ⟨hk1, K'.inv_mem (Subgroup.mem_subgroupOf.1 u.2)⟩, ?_⟩
  rw [hu]
  ext <;> simp [mul_assoc]

end GlobalTheory.DefClassFin

namespace GlobalTheory.DefClassFin

variable {p : ℕ} [Fact p.Prime]

theorem inT_of_TC (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) (h : TC G.C G.star β 1 R z) : InT G R β 1 z :=
  ⟨h.1, by rw [map_one]; exact Commute.one_right _⟩

theorem TC_of_inT (G : HTGroup p) (R : Type) [CommRing R] [Algebra ℚ R] (β : G.C)
    (z : (R ⊗[ℚ] G.C)ˣ × Rˣ) (h : InT G R β 1 z) : TC G.C G.star β 1 R z :=
  ⟨h.1, by rw [← Algebra.TensorProduct.one_def]; exact Commute.one_right _⟩

theorem psiAway_psiAway_inv (G : HTGroup p) (x : (AfP p ⊗[ℚ] G.C)ˣ)
    (w : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) : psiAway G x (psiAway G x⁻¹ w) = w := by
  simp only [psiAway_apply, inv_inv]
  exact Prod.ext (by group) rfl

theorem cover_KHT (P : CCF) (G : HTGroup p) (L : G.Level) (B : GlobalTheory.LKDef.DForm G) :
    ∃ S : Set (G.GAf × Gr G 1), S.Finite ∧ ∀ g : G.GAf × Gr G 1, ∃ γ ∈ B.emb.range, ∃ s ∈ S,
      ∃ k ∈ L.K.toSubgroup.prod (KHT p G.m G.n 1 G.Fw), g = γ * s * k := by
  set x := B.trivAf.choose with hxdef
  set t := B.trivAf.choose_spec.choose with htdef
  have hx : Triv G (AfP p) B.β x t := B.trivAf.choose_spec.choose_spec
  have hemb : ∀ y, B.emb y = (toAfF G B.β x t hx y, toP1 G B.β y) := fun y => rfl
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  letI : TopologicalSpace (ℚ_[p] ⊗[ℚ] G.C) := moduleTopology ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C)
  let U : Subgroup (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) :=
    (Subgroup.comap (psiAway G x) (L.K.toSubgroup.map (UPts G.star (AfP p)).subtype)).prod
      (Subgroup.comap (psiP G) (KHT p G.m G.n 1 G.Fw))
  obtain ⟨O₁, hO₁, h1O₁, hO₁U⟩ := exists_open_psiAway_mem_conj_level p G L B.β x t hx 1 1
  obtain ⟨O₂, hO₂, h1O₂, hO₂U⟩ := GlobalTheory.TorCls.OpenP.openp p G 1
  have hO : ∃ O : Set (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)), IsOpen O ∧ 1 ∈ O ∧
      ∀ z ∈ O, TC G.C G.star (B.β : G.C) 1 (AfP p) z.1 → TC G.C G.star (B.β : G.C) 1 ℚ_[p] z.2 → z ∈ U := by
    refine ⟨O₁ ×ˢ O₂, hO₁.prod hO₂, ⟨h1O₁, h1O₂⟩, fun z hz h1 _ => Subgroup.mem_prod.2 ⟨?_, ?_⟩⟩
    · obtain ⟨k, hk, e⟩ := hO₁U z.1 hz.1 (inT_of_TC G _ _ _ h1)
      exact ⟨k, hk, by simpa using e⟩
    · have := hO₂U z.2 hz.2
      simpa using this
  obtain ⟨S, hS⟩ := P G.C G.star (B.β : G.C) 1 p U hO

  let Neg : Prop := ∃ γ : G.Cˣ × ℚˣ, (γ.1 : G.C) * (B.β : G.C) * (G.star γ.1).unop =
    algebraMap ℚ G.C γ.2 * (B.β : G.C) ∧ (γ.2 : ℚ) < 0
  let gm : G.Cˣ × ℚˣ := if h : Neg then h.choose else 1
  let S₂ : Set (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) :=
    (S : Set _) ∪ (fun s => dg G.C p gm * s) '' (S : Set _)
  have hS₂ : S₂.Finite := S.finite_toSet.union (S.finite_toSet.image _)
  let Ψ : (((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × ((ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ)) →*
      ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × Gr G 1 := (psiAway G x).prodMap (psiP G)
  let fH : G.GAf × Gr G 1 →* ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) × Gr G 1 :=
    (UPts G.star (AfP p)).subtype.prodMap (MonoidHom.id _)
  have hfH : Function.Injective fH := Prod.map_injective.2 ⟨Subtype.val_injective, Function.injective_id⟩
  refine ⟨fH ⁻¹' (Ψ '' S₂), (hS₂.image Ψ).preimage hfH.injOn, fun g => ?_⟩

  have hz₁ := inT_psiAway_inv_of_commute p G B.β x t hx 1 g.1 (by simp)
  simp only [OneMemClass.coe_one, Prod.fst_one, Units.val_one] at hz₁
  obtain ⟨z₂, hz₂, hψ₂⟩ := GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split p G B.β B.sym 1 g.2 (by simp)
  simp only [OneMemClass.coe_one, Prod.fst_one, Units.val_one] at hz₂
  set z₁ := psiAway G x⁻¹ (g.1 : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) with hz₁def
  obtain ⟨γ, hγ, -, s, hs, u, hu, hz⟩ := hS (z₁, z₂) (TC_of_inT G _ _ _ hz₁) (TC_of_inT G _ _ _ hz₂)

  have key : ∃ δ : grp G B.β, ∃ s' ∈ S₂, (z₁, z₂) = dg G.C p (δ : G.Cˣ × ℚˣ) * s' * u := by
    rcases lt_or_gt_of_ne (Units.ne_zero γ.2) with hneg | hpos
    · have hN : Neg := ⟨γ, hγ, hneg⟩
      have hgm : gm = hN.choose := dif_pos hN
      obtain ⟨hgmf, hgmn⟩ := hN.choose_spec
      rw [← hgm] at hgmf hgmn
      have hδ := form_mul_inv G.star (B.β : G.C) γ.1 gm.1 γ.2 gm.2 hγ hgmf
      have hδpos : (0 : ℚ) < ((γ.2 * gm.2⁻¹ : ℚˣ) : ℚ) := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        exact mul_pos_of_neg_of_neg hneg (inv_lt_zero.2 hgmn)
      refine ⟨⟨γ * gm⁻¹, hδ, hδpos⟩, dg G.C p gm * s, Or.inr ⟨s, hs, rfl⟩, ?_⟩
      rw [hz]
      simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    · exact ⟨⟨γ, hγ, hpos⟩, s, Or.inl hs, hz⟩
  obtain ⟨δ, s', hs', hz'⟩ := key
  obtain ⟨hu1, hu2⟩ := Subgroup.mem_prod.1 hu
  obtain ⟨k₁, hk₁, ek₁⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hu1)
  have hk₂ : psiP G u.2 ∈ KHT p G.m G.n 1 G.Fw := Subgroup.mem_comap.1 hu2
  let k : G.GAf × Gr G 1 := (k₁, psiP G u.2)
  have hk : k ∈ L.K.toSubgroup.prod (KHT p G.m G.n 1 G.Fw) := Subgroup.mem_prod.2 ⟨hk₁, hk₂⟩
  refine ⟨B.emb δ, ⟨δ, rfl⟩, (B.emb δ)⁻¹ * g * k⁻¹, ⟨s', hs', ?_⟩, k, hk, by group⟩
  have hΨz : Ψ (z₁, z₂) = fH g := by
    refine Prod.ext ?_ hψ₂
    exact psiAway_psiAway_inv G x _
  have hΨd : Ψ (dg G.C p (δ : G.Cˣ × ℚˣ)) = fH (B.emb δ) := by
    refine Prod.ext ?_ ?_
    · exact (toAfF_eq_psiAway G B.β x t hx δ).symm
    · exact (formGroupToPadicPointsDegreeOne_eq_unitaryPoints G B.β δ).symm
  have hΨu : Ψ u = fH k := Prod.ext ek₁.symm rfl
  have e := congrArg Ψ hz'
  rw [map_mul, map_mul, hΨz, hΨd, hΨu] at e
  rw [map_mul, map_mul, map_inv, map_inv, e]
  group

end GlobalTheory.DefClassFin

namespace GlobalTheory.DefClassFin

theorem finite_doubleCoset : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level)
    (K' : Subgroup (Gr G 1)), Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ B : GlobalTheory.LKDef.DForm G,
    Finite (DoubleCoset.Quotient (B.emb.range : Set (G.GAf × Gr G 1))
      ((L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))) := by
  intro p _ G _ L K' hK B
  obtain ⟨S, hS, hcov⟩ := cover_KHT ccf_holds G L B
  obtain ⟨S', hS', hcov'⟩ := cover_of_relIndex B.emb.range L.K.toSubgroup _ K' hK.1.relIndex_ne_zero S hS hcov
  exact finite_of_cover _ _ S' hS' hcov'

end GlobalTheory.DefClassFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDoubleCosetDefiniteHermitianFormLevelStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_doubleCoset_definiteHermitianForm_level : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
  Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ B : GlobalTheory.LKDef.DForm G,
    Finite (DoubleCoset.Quotient (B.emb.range : Set (G.GAf × Gr G 1))
      ((L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) : Set (G.GAf × Gr G 1))) := by
  first | (exact @GlobalTheory.DefClassFin.finite_doubleCoset) | (exact GlobalTheory.DefClassFin.finite_doubleCoset) | (intros; apply GlobalTheory.DefClassFin.finite_doubleCoset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDescentEstimate
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun

namespace GlobalTheory.BigTop.Fun.PolBound

theorem log_le_posLog' (y : ℝ) : Real.log y ≤ Real.posLog y := by
  unfold Real.posLog; exact le_max_right _ _

theorem posLog_le_of_log_le {y B : ℝ} (hy : Real.log y ≤ B) (hB : 0 ≤ B) : Real.posLog y ≤ B := by
  unfold Real.posLog; exact max_le hB hy

theorem pol_core {C Q f m k t lb Lb : ℝ} (hC : 1 ≤ C) (hQ : 1 ≤ Q) (hf0 : 0 ≤ f) (hf : f ≤ Q) (hm0 : 0 ≤ m)
    (hm : m ≤ Q) (hk0 : 0 ≤ k) (hk : k ≤ Q) (ht0 : 0 ≤ t) (ht : t ≤ Q) (hlb0 : 0 ≤ lb) (hlb : lb ≤ Q)
    (hLb : Lb ≤ 20 * Q) :
    100000 * C ^ 3 * f * m ^ 2 * (k + m * (t + (k + m + 5) + 1)) ^ 2 *
      ((k + m - 1) * (k + m * (t + (k + m + 5) + 1)) * lb + C * f ^ 2 * (k + m) ^ 6 * Lb) ≤
      13000000000 * C ^ 4 * Q ^ 16 := by
  set N := k + m * (t + (k + m + 5) + 1) with hNdef
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hN0 : 0 ≤ N := by positivity
  have hQ2 : Q ≤ Q ^ 2 := by nlinarith
  have hN : N ≤ 10 * Q ^ 2 := by
    have h1 : t + (k + m + 5) + 1 ≤ 9 * Q := by linarith
    have h2 : m * (t + (k + m + 5) + 1) ≤ Q * (9 * Q) := mul_le_mul hm h1 (by positivity) hQ0
    nlinarith
  have hr : k + m - 1 ≤ 2 * Q := by linarith
  have hnr0 : 0 ≤ k + m := by linarith
  have hnr : k + m ≤ 2 * Q := by linarith
  have i1 : (k + m - 1) * N * lb ≤ (2 * Q) * (10 * Q ^ 2) * Q := by
    have a : (k + m - 1) * (N * lb) ≤ (2 * Q) * (N * lb) := mul_le_mul_of_nonneg_right hr (by positivity)
    have b : N * lb ≤ (10 * Q ^ 2) * Q := mul_le_mul hN hlb hlb0 (by positivity)
    have c : (2 * Q) * (N * lb) ≤ (2 * Q) * ((10 * Q ^ 2) * Q) := mul_le_mul_of_nonneg_left b (by positivity)
    calc (k + m - 1) * N * lb = (k + m - 1) * (N * lb) := by ring
      _ ≤ _ := a.trans c
      _ = _ := by ring
  have i2 : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) := by
    have a : C * f ^ 2 * (k + m) ^ 6 * Lb ≤ C * f ^ 2 * (k + m) ^ 6 * (20 * Q) :=
      mul_le_mul_of_nonneg_left hLb (by positivity)
    have b : C * f ^ 2 * (k + m) ^ 6 ≤ C * Q ^ 2 * (2 * Q) ^ 6 := by gcongr
    exact a.trans (mul_le_mul_of_nonneg_right b (by positivity))
  have hQ4 : Q ^ 4 ≤ Q ^ 9 := pow_le_pow_right₀ hQ (by norm_num)
  have hinner : (k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb ≤ 1300 * C * Q ^ 9 := by
    have e1 : (2 * Q) * (10 * Q ^ 2) * Q = 20 * Q ^ 4 := by ring
    have e2 : C * Q ^ 2 * (2 * Q) ^ 6 * (20 * Q) = 1280 * C * Q ^ 9 := by ring
    have e3 : 20 * Q ^ 4 ≤ 20 * C * Q ^ 9 := by
      have : Q ^ 4 ≤ C * Q ^ 9 := hQ4.trans (le_mul_of_one_le_left (by positivity) hC)
      linarith
    linarith
  have hpre0 : 0 ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 := by positivity
  have hpre : 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 := by gcongr
  calc 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * ((k + m - 1) * N * lb + C * f ^ 2 * (k + m) ^ 6 * Lb)
      ≤ 100000 * C ^ 3 * f * m ^ 2 * N ^ 2 * (1300 * C * Q ^ 9) := mul_le_mul_of_nonneg_left hinner hpre0
    _ ≤ 100000 * C ^ 3 * Q * Q ^ 2 * (10 * Q ^ 2) ^ 2 * (1300 * C * Q ^ 9) :=
        mul_le_mul_of_nonneg_right hpre (by positivity)
    _ = 13000000000 * C ^ 4 * Q ^ 16 := by ring

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun.PolBound

open Formalism.BasicNotions Formalism.MainNotions NumberField

theorem rpow_mono {x a b : ℝ} (hx : 1 ≤ x) (h : a ≤ b) : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx h

theorem factors_le {D : D7} (L : SizeData₂ D) (hS : SizesAt L) (T : ℕ) (hT : L.Ct + 1 ≤ T) :
    (D.R.f : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.m : ℝ) ≤ L.sc.x ^ (T + 9) ∧ (D.R.k : ℝ) ≤ L.sc.x ^ (T + 9) ∧
      (D.R.t : ℝ) ≤ L.sc.x ^ (T + 9) ∧ Real.log L.sc.b ≤ L.sc.x ^ (T + 9) ∧ 0 ≤ Real.log L.sc.b ∧
      Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ 20 * L.sc.x ^ (T + 9) := by
  obtain ⟨hN, hM, hK, hKR, hTt, -, hQD, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, hPde, -⟩ := hS
  set x := L.sc.x with hxdef
  have hx1 : 1 ≤ x := L.sc.one_lt_alt.le
  have hx0 : 0 ≤ x := by linarith
  have he0 : 0 < L.sc.eps := L.sc.eps_pos
  have he1 : L.sc.eps < 1 / 52 := L.sc.eps_lt
  have hth : szTh L = L.sc.eps / 100 := rfl
  have hpow : ∀ j : ℕ, j ≤ T + 9 → x ^ j ≤ x ^ (T + 9) := fun j hj => pow_le_pow_right₀ hx1 hj
  have hrp : ∀ (a : ℝ) (j : ℕ), a ≤ j → x ^ a ≤ x ^ j := fun a j h => by
    rw [← Real.rpow_natCast]; exact rpow_mono hx1 h

  have hLd : L.sc.L = x ^ L.sc.eps := by rw [hxdef]; rfl
  have hlb : Real.log L.sc.b = x ^ L.sc.eps := by
    show Real.log (Real.exp L.sc.L) = _
    rw [Real.log_exp]; exact hLd
  have hLx : x ^ L.sc.eps ≤ x := by
    have := hrp L.sc.eps 1 (by norm_num; linarith); simpa using this

  have hm : (D.R.m : ℝ) ≤ x := by
    have hd1 : L.sc.delta1 ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hd0 : 0 ≤ L.sc.delta1 := Real.rpow_nonneg hx0 _
    have h1 : Real.sqrt (x * L.sc.delta1) ≤ x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]; exact Real.sqrt_le_sqrt (by nlinarith)
    have h2 : x ^ szTh L * Real.sqrt (x * L.sc.delta1) ≤ x ^ szTh L * x ^ (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hx0 _)
    rw [← Real.rpow_add (by linarith)] at h2
    have h3 : x ^ (szTh L + 1 / 2) ≤ x ^ (1 : ℕ) := hrp _ 1 (by rw [hth]; push_cast; linarith)
    linarith [hM.2, pow_one x]
  have hk : (D.R.k : ℝ) ≤ x ^ 5 := hK.2.trans (hrp _ 5 (by rw [hth]; push_cast; linarith))
  have hn : (D.R.n : ℝ) ≤ x ^ 3 := hN.2.trans (hrp _ 3 (by rw [hth]; push_cast; linarith))
  have hm0 : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
  have hf : (D.R.f : ℝ) ≤ x ^ 5 := by
    have h := hKR.2.2.2.2.2.2.2.2.2.2.2.2.1
    have h2 : (D.R.m : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hm0 hm 2
    have h3 : (D.R.m : ℝ) ^ 2 * D.R.n ≤ x ^ 2 * x ^ 3 := mul_le_mul h2 hn (Nat.cast_nonneg _) (by positivity)
    calc (D.R.f : ℝ) ≤ _ := h
      _ ≤ _ := h3
      _ = x ^ 5 := by ring
  have ht : (D.R.t : ℝ) ≤ x ^ T := by
    refine hTt.2.trans (hrp _ T ?_)
    have : L.Ct + szTh L ≤ L.Ct + 1 := by rw [hth]; linarith
    linarith
  have hQ5 : x ^ 5 ≤ x ^ (T + 9) := hpow 5 (by omega)
  have hQ8 : x ^ 8 ≤ x ^ (T + 9) := hpow 8 (by omega)
  have hQ1 : x ≤ x ^ (T + 9) := by simpa using hpow 1 (by omega)
  refine ⟨hf.trans hQ5, hm.trans hQ1, hk.trans hQ5, ht.trans (hpow T (by omega)), by rw [hlb]; linarith,
    by rw [hlb]; positivity, ?_⟩

  have hb : Real.posLog L.sc.b ≤ x := posLog_le_of_log_le (by rw [hlb]; exact hLx) hx0
  have hnr : Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) ≤ 2 * x ^ 5 := by
    refine posLog_le_of_log_le ((Real.log_le_self (Nat.cast_nonneg _)).trans ?_) (by positivity)
    push_cast
    have : (D.R.m : ℝ) ≤ x ^ 5 := hm.trans (by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 5))
    linarith
  have hg : ∀ i : Fin 2, Real.posLog (D.host.g i : ℝ) ≤ x := fun i => by
    refine posLog_le_of_log_le ((hG i i).2.2.trans ?_) hx0
    rw [hLd, ← Real.rpow_add (by linarith)]
    have := hrp (szTh L + L.sc.eps) 1 (by rw [hth]; push_cast; linarith)
    simpa using this
  have hp1 : Real.posLog (D.host.pde : ℝ) ≤ x := posLog_le_of_log_le (hPde.1.trans (hLd ▸ hLx)) hx0
  have hp2 : Real.posLog (D.host.pde' : ℝ) ≤ x := posLog_le_of_log_le (hPde.2.trans (hLd ▸ hLx)) hx0
  have hdE : Real.posLog |((discr D.host.E : ℤ) : ℝ)| ≤ 6 * x ^ 8 := by
    refine posLog_le_of_log_le ?_ (by positivity)
    have e := logdE_eq_rd D
    unfold logdE at e
    rw [e]
    have hlr : Real.log D.host.rdE ≤ 2 * x ^ 3 + x := by
      have h1 := UpperTheory.Ram.Rd.log_rdE_le D.host
      have h2 : Real.log (D.R.n : ℝ) ≤ x ^ 3 := (Real.log_le_self (Nat.cast_nonneg _)).trans hn
      have hq : Real.log D.host.q ≤ x := hQD.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      have hd : Real.log D.host.d ≤ x := hQD.2.2.2.2.1.trans (by
        have := hrp (L.sc.eps / 5 + szTh L) 1 (by rw [hth]; push_cast; linarith); simpa using this)
      linarith
    have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    calc 2 * (D.R.f : ℝ) * Real.log D.host.rdE ≤ 2 * (D.R.f : ℝ) * (2 * x ^ 3 + x) :=
          mul_le_mul_of_nonneg_left hlr (by positivity)
      _ ≤ 2 * x ^ 5 * (2 * x ^ 3 + x) := by gcongr
      _ ≤ 6 * x ^ 8 := by
          have : x ^ 6 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
          nlinarith
  have hprod : Real.log (L.sc.b * ((D.R.k + D.R.m : ℕ) : ℝ) * (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) * (D.host.pde : ℝ) *
        (D.host.pde' : ℝ) * |((discr D.host.E : ℤ) : ℝ)|) ≤ Real.posLog L.sc.b + Real.posLog ((D.R.k + D.R.m : ℕ) : ℝ) +
      Real.posLog (D.host.g 0 : ℝ) + Real.posLog (D.host.g 1 : ℝ) + Real.posLog (D.host.pde : ℝ) +
      Real.posLog (D.host.pde' : ℝ) + Real.posLog |((discr D.host.E : ℤ) : ℝ)| := by
    refine (log_le_posLog' _).trans ?_
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    refine Real.posLog_mul.trans (add_le_add ?_ le_rfl)
    exact Real.posLog_mul
  have h8 : x ^ 5 ≤ x ^ 8 := pow_le_pow_right₀ hx1 (by norm_num)
  have h18 : x ≤ x ^ 8 := by simpa using pow_le_pow_right₀ hx1 (by norm_num : 1 ≤ 8)
  have := hg 0
  have := hg 1
  refine hprod.trans ?_
  linarith

end GlobalTheory.BigTop.Fun.PolBound

namespace GlobalTheory.BigTop.Fun

open Formalism.BasicNotions Formalism.MainNotions NumberField GlobalTheory.BigTop.Fun.PolBound

end GlobalTheory.BigTop.Fun
end
