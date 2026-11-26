module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FormalGroupLawPointMaps
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TangentPow

variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem ptMap_comp_ptMap {A B C : Type} [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    [CommRing C] [Algebra O C] (φ : A →ₐ[O] B) (ψ : B →ₐ[O] C) :
    ptMap ψ ≫ ptMap φ = ptMap (ψ.comp φ) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem ptMap_id' (A : Type) [CommRing A] [Algebra O A] : ptMap (AlgHom.id O A) = 𝟙 _ := by
  ext1
  exact Spec.map_id _


variable (O) in
noncomputable abbrev scale (a : R) : specO O (DualNumber R) ⟶ specO O (DualNumber R) :=
  ptMap ((TrivSqZeroExt.map (a • (LinearMap.id : R →ₗ[R] R))).restrictScalars O)

theorem scale_one : scale O (1 : R) = 𝟙 _ := by
  rw [← ptMap_id', scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp

theorem scale_zero : scale O (0 : R) =
    ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) := by
  rw [ptMap_comp_ptMap, scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp


variable (O) in
noncomputable abbrev toTwo (l : R →ₗ[R] R × R) :
    specO O (TrivSqZeroExt R (R × R)) ⟶ specO O (DualNumber R) :=
  ptMap ((TrivSqZeroExt.map l).restrictScalars O)


variable (O) in
noncomputable abbrev ofTwo (l : R × R →ₗ[R] R) :
    specO O (DualNumber R) ⟶ specO O (TrivSqZeroExt R (R × R)) :=
  ptMap ((TrivSqZeroExt.map l).restrictScalars O)

theorem ofTwo_toTwo (l : R →ₗ[R] R × R) (l' : R × R →ₗ[R] R) :
    ofTwo O l' ≫ toTwo O l = scale O (l' (l 1)) := by
  rw [ofTwo, toTwo, ptMap_comp_ptMap, scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  have : l' (l x.snd) = l' (l 1) * x.snd := by
    rw [mul_comm, ← smul_eq_mul, ← map_smul, ← map_smul, smul_eq_mul, _root_.mul_one]
  ext <;> simp [this]

variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {y : specO O (DualNumber R) ⟶ G}

theorem scale_zero_comp (hy : ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1) :
    scale O (0 : R) ≫ y = 1 := by
  rw [scale_zero, Category.assoc, hy, comp_one]

theorem scale_add_comp (hy : ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1) (a b : R) :
    scale O (a + b) ≫ y = (scale O a ≫ y) * (scale O b ≫ y) := by
  let i₁ := LinearMap.inl R R R
  let i₂ := LinearMap.inr R R R
  have key : toTwo O (i₁ + i₂) ≫ y = (toTwo O i₁ ≫ y) * (toTwo O i₂ ≫ y) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩)
        fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : ofTwo O (LinearMap.fst R R R) ≫ _ = ofTwo O (LinearMap.fst R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, ofTwo_toTwo]
      have e₁ : LinearMap.fst R R R ((i₁ + i₂) 1) = 1 := by simp [i₁, i₂]
      have e₂ : LinearMap.fst R R R (i₁ 1) = 1 := rfl
      have e₃ : LinearMap.fst R R R (i₂ 1) = 0 := rfl
      rw [e₁, e₂, e₃, scale_zero_comp hy, _root_.mul_one]
    · refine congrArg Over.Hom.left
        (?_ : ofTwo O (LinearMap.snd R R R) ≫ _ = ofTwo O (LinearMap.snd R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, ofTwo_toTwo]
      have e₁ : LinearMap.snd R R R ((i₁ + i₂) 1) = 1 := by simp [i₁, i₂]
      have e₂ : LinearMap.snd R R R (i₁ 1) = 0 := rfl
      have e₃ : LinearMap.snd R R R (i₂ 1) = 1 := rfl
      rw [e₁, e₂, e₃, scale_zero_comp hy, _root_.one_mul]
  let l := a • LinearMap.fst R R R + b • LinearMap.snd R R R
  have := congrArg (ofTwo O l ≫ ·) key
  simp only [comp_mul, ← Category.assoc, ofTwo_toTwo] at this
  have e₁ : l ((i₁ + i₂) 1) = a + b := by simp [l, i₁, i₂]
  have e₂ : l (i₁ 1) = a := by simp [l, i₁]
  have e₃ : l (i₂ 1) = b := by simp [l, i₂]
  rwa [e₁, e₂, e₃] at this

theorem pow_eq_scale_comp (hy : ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1) (N : ℕ) :
    y ^ N = scale O (N : R) ≫ y := by
  induction N with
  | zero => rw [pow_zero, Nat.cast_zero, scale_zero_comp hy]
  | succ n ih =>
    rw [pow_succ, Nat.cast_succ, scale_add_comp hy, ih, scale_one, Category.id_comp]

theorem pow_eq_scale_and_existsUnique_torsion :
    ∀ (O : Type) [CommRing O] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] (R : Type)
      [CommRing R] [Algebra O R] (N : ℕ) (y : specO O (DualNumber R) ⟶ G),
      ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1 →
      y ^ N = ptMap ((TrivSqZeroExt.map ((N : R) • (LinearMap.id : R →ₗ[R] R))).restrictScalars O)
          ≫ y ∧
        ((N : R) = 0 → ∃! w : specO O (DualNumber R) ⟶ torsion G N, w ≫ torsion.ι G N = y) := by
  intro O _ G _ R _ _ N y hy
  refine ⟨pow_eq_scale_comp hy N, fun hN => ?_⟩
  have h : y ^ N = 1 := by rw [pow_eq_scale_comp hy, hN, scale_zero_comp hy]
  exact ⟨KernelNoTorsion.torsionLift y h, KernelNoTorsion.torsionLift_ι y h, fun w hw =>
    KernelNoTorsion.torsion_hom_ext (hw.trans (KernelNoTorsion.torsionLift_ι y h).symm)⟩

end GlobalTheory.TangentPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitOfBijectiveMulNatural
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

namespace GmPoints

variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem unitOf_val (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    (unitOf w : R) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
      (w.left.appTop.hom (charUnit (Spec (CommRingCat.of O)) (ULift ℤ) (ULift.up 1)).val) := by
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Spec (CommRingCat.of R)).presheaf.map (𝟙 (Opposite.op ⊤))).hom
      (w.left.appTop.hom (charUnit (Spec (CommRingCat.of O)) (ULift ℤ) (ULift.up 1)).val)) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem evalOne_bijective {M : Type} [Group M] :
    Function.Bijective (fun f : Multiplicative (ULift.{0} ℤ) →* M =>
      f (Multiplicative.ofAdd (ULift.up 1))) := by
  have h : ∀ n : ℤ, (Multiplicative.ofAdd (ULift.up n) : Multiplicative (ULift.{0} ℤ)) =
      (Multiplicative.ofAdd (ULift.up 1)) ^ n := by
    intro n
    rw [← ofAdd_zsmul]
    congr 1
    ext
    simp
  constructor
  · intro f g hfg
    ext ⟨n⟩
    have := h n
    change f (Multiplicative.ofAdd (ULift.up n)) = g (Multiplicative.ofAdd (ULift.up n))
    rw [this, map_zpow, map_zpow]
    exact congrArg (· ^ n) hfg
  · intro m
    exact ⟨{ toFun := fun x => m ^ x.toAdd.down
             map_one' := zpow_zero m
             map_mul' := fun x y => zpow_add m _ _ }, zpow_one m⟩

theorem unitOf_eq (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    unitOf w = Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv
      (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R) w
        (Multiplicative.ofAdd (ULift.up 1))) := by
  ext
  rw [unitOf_val, ← splitTorusPointsEquiv_val]
  rfl

theorem unitOf_bijective :
    Function.Bijective (unitOf : (specO O R ⟶ Gm (Spec (CommRingCat.of O))) → Rˣ) := by
  rw [funext (unitOf_eq (O := O) (R := R))]
  exact (Units.mapEquiv
      (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toMulEquiv).bijective.comp
    (evalOne_bijective.comp
      (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R)).bijective)

theorem unitOf_mul (w w' : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    unitOf (w * w') = unitOf w * unitOf w' := by
  rw [unitOf_eq, unitOf_eq, unitOf_eq]
  refine Eq.trans ?_ (map_mul _ _ _)
  congr 1
  exact DFunLike.congr_fun (map_mul
    (splitTorusPointsEquiv (Spec (CommRingCat.of O)) (ULift ℤ) (specO O R)) w w') _

theorem unitOf_ptMap {R' : Type} [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R')
    (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    (unitOf (ptMap φ ≫ w) : R') = φ (unitOf w : R) := by
  rw [unitOf_val, unitOf_val, Over.comp_left, Scheme.Hom.comp_appTop]
  exact congrArg (fun g : Γ(Spec (CommRingCat.of R), ⊤) ⟶ CommRingCat.of R' => g.hom _)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ.toRingHom))

end GmPoints

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNnrealValuationOfAddValuation
namespace GlobalTheory

open scoped NNReal

noncomputable def expNegTop : WithTop ℚ → ℝ≥0
  | ⊤ => 0
  | (q : ℚ) => ⟨Real.exp (-(q : ℝ)), (Real.exp_pos _).le⟩

@[simp] theorem expNegTop_top : expNegTop ⊤ = 0 := rfl

theorem expNegTop_coe (q : ℚ) : ((expNegTop (q : WithTop ℚ) : ℝ≥0) : ℝ) = Real.exp (-(q : ℝ)) := rfl

theorem expNegTop_zero : expNegTop 0 = 1 := by
  apply NNReal.coe_injective
  have h := expNegTop_coe 0
  simpa using h

theorem expNegTop_add (a b : WithTop ℚ) : expNegTop (a + b) = expNegTop a * expNegTop b := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top => simp
    | coe b =>
      apply NNReal.coe_injective
      rw [← WithTop.coe_add, NNReal.coe_mul, expNegTop_coe, expNegTop_coe, expNegTop_coe,
        ← Real.exp_add]
      push_cast
      ring_nf

theorem expNegTop_le_iff (a b : WithTop ℚ) : expNegTop a ≤ expNegTop b ↔ b ≤ a := by
  induction a using WithTop.recTopCoe with
  | top => simp
  | coe a =>
    induction b using WithTop.recTopCoe with
    | top =>
      rw [← NNReal.coe_le_coe, expNegTop_coe]
      simp only [expNegTop_top, NNReal.coe_zero, top_le_iff, WithTop.coe_ne_top, iff_false, not_le]
      exact Real.exp_pos _
    | coe b =>
      rw [← NNReal.coe_le_coe, expNegTop_coe, expNegTop_coe, Real.exp_le_exp, neg_le_neg_iff,
        Rat.cast_le, WithTop.coe_le_coe]

noncomputable def expNegValuation {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    Valuation F ℝ≥0 where
  toFun x := expNegTop (v x)
  map_zero' := by simp
  map_one' := by simp [expNegTop_zero]
  map_mul' x y := by rw [v.map_mul, expNegTop_add]
  map_add_le_max' x y := by
    rcases min_le_iff.mp (v.map_add x y) with h | h
    · exact le_max_of_le_left ((expNegTop_le_iff _ _).mpr h)
    · exact le_max_of_le_right ((expNegTop_le_iff _ _).mpr h)

theorem expNegValuation_apply {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x = expNegTop (v x) := rfl

theorem expNegValuation_le_one_iff {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) (x : F) :
    expNegValuation v x ≤ 1 ↔ 0 ≤ v x := by
  rw [expNegValuation_apply, ← expNegTop_zero, expNegTop_le_iff]

theorem exists_nnreal_valuation_of_addValuation :
    ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)), ∃ v' : Valuation F NNReal,
      (∀ x y, v' x ≤ v' y ↔ v y ≤ v x) ∧ v'.Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  intro F _ v
  refine ⟨expNegValuation v, fun x y => expNegTop_le_iff _ _, ?_, ?_, ?_⟩
  · exact Subtype.val_injective
  · intro x
    exact (expNegValuation_le_one_iff v _).mpr x.2
  · intro r hr
    exact ⟨⟨r, (expNegValuation_le_one_iff v r).mp hr⟩, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepOnePlusDet
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal ContDiff

noncomputable section

namespace BranchingSupport.TensInh

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem lenA_eq_lA (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin (r + 1)) :
    lenA k r z g a = Formalism.MainNotions.S.lA k r z g a := by
  classical
  let Lm : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    { toFun := fun v => WithLp.toLp 2 (g⁻¹ *ᵥ v)
      map_add' := fun v w => by simp [Matrix.mulVec_add]
      map_smul' := fun c v => by simp [Matrix.mulVec_smul] }
  let S : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) := Submodule.span ℂ
    (Set.range fun b : {b : Fin r // b.val < a.val} => Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1))
  have hlt : ∀ b : Fin (r + 1), b < a → b.val < r :=
    fun b hb => Nat.lt_of_lt_of_le hb (Nat.le_of_lt_succ a.2)
  have hfv : ∀ (b : Fin (r + 1)) (hb : b < a),
      Formalism.QuantumDeterminants.fvec k r z b = Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r ⟨b.val, hlt b hb⟩) := by
    intro b hb
    have hbr : b.val < r := hlt b hb
    simp [Formalism.QuantumDeterminants.fvec, hbr]
  have hspan : Submodule.span ℂ ((fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) '' {b | b < a}) = S.map Lm := by
    rw [Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨_, ⟨⟨⟨b.val, hlt b hb⟩, hb⟩, rfl⟩, ?_⟩
      exact (congrArg (fun v => (WithLp.toLp 2 (g⁻¹ *ᵥ v) : EuclideanSpace ℂ (Fin (2 * r + k + 1))))
        (hfv b hb)).symm
    · rintro ⟨_, ⟨⟨b, hb⟩, rfl⟩, rfl⟩
      refine ⟨⟨b.val, by have := b.2; omega⟩, hb, ?_⟩
      show WithLp.toLp 2 (g⁻¹ *ᵥ _) = _
      rw [hfv _ hb]
      rfl
  have hd : ∀ y, dist (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))
      (WithLp.toLp 2 (g⁻¹ *ᵥ y)) = Formalism.MainNotions.S.eucl (g⁻¹ *ᵥ (Formalism.QuantumDeterminants.fvec k r z a - y)) := by
    intro y
    rw [EuclideanSpace.dist_eq]
    simp [Formalism.MainNotions.S.eucl, Matrix.mulVec_sub, Complex.normSq_eq_norm_sq, dist_eq_norm]
  unfold lenA Formalism.MainNotions.S.lA
  rw [hspan, Metric.infDist_eq_iInf, ← sInf_range]
  congr 1
  ext t
  constructor
  · rintro ⟨⟨_, y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, hd y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨Lm y, y, hy, rfl⟩, hd y⟩

end BranchingSupport.TensInh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PsJetTwistedSeriesOfLeOne
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameTwistCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw FB)
open ReciprocityTheory.ChartRestriction.G.TB (dLin)
open ReciprocityTheory.ChartRestriction.G.TB.LogPf (CZ)
open Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix

attribute [local instance] Over.cartesianMonoidalCategory

section Series

open MvPowerSeries

variable {S : Type} [CommRing S]

variable {n d : ℕ}

variable {c : Fin d → Fin d → S} {P Q : Pt S n d}

variable [Algebra ℚ S]



omit [Algebra ℚ S] in
theorem cc_pt (j : Fin n) (i : Fin d) : constantCoeff (pt S d j i) = 0 := by
  simp [pt]


end Series

section Jets

open MvPolynomial

variable {S : Type} [CommRing S] {d : ℕ}

theorem jetSubstP_psJet {n n' : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    {a : Fin n → Pt S n' d} (ha : CZ a) (hφ : ∀ p, constantCoeff (φ p) = 0)
    (hmk : ∀ p : Fin n × Fin d,
      Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (φ p) = psJet m (a p.1 p.2))
    (f : PS S n d) : jetSubstP m φ (psJet m f) = psJet m (ev a f) := by
  rw [ev, FBIdJet.psJet_subst m _ (fun p => ha p.1 p.2) f]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, hφ p, map_zero, sub_zero]
  rw [hmk p]
  rfl

theorem mk_psIn_psJet {n' : ℕ} (m : ℕ) (k : Fin n') (f : PS S 1 d) :
    Ideal.Quotient.mk (Formalism.L2.Pj.orig S (Fin n' × Fin d) ^ (m + 1)) (psIn d m ![k] f) =
      psJet m (ev ![pt S d k] f) := by
  have e : (![pt S d k] : Fin 1 → Pt S n' d) = fun i => pt S d ((![k] : Fin 1 → Fin n') i) := by
    funext i; fin_cases i; rfl
  rw [e, FBIdPh.psJet_ev_rel, psIn, FBIdPh.mk_rename]
  apply DFunLike.congr_fun
  refine GermD.jet_hom_ext fun p => ?_
  rw [GermD.jetMap_mk, aeval_X]
  simp only [jetSubstP, GermD.jetMap_mk, aeval_X, FBIdPh.rel, constantCoeff_X, map_zero, sub_zero]

theorem cz_left {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    CZ (![comp1 φ (pt S d 0), pt S d 1] : Fin 2 → Pt S 2 d) := by
  intro j i
  fin_cases j
  · exact (TB.LogPf.cc_ev TB.LogPf.czX _).trans (hφ i)
  · exact cc_pt _ i

theorem cz_right {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) :
    CZ (![pt S d 0, comp1 φ (pt S d 1)] : Fin 2 → Pt S 2 d) := by
  intro j i
  fin_cases j
  · exact cc_pt _ i
  · exact (TB.LogPf.cc_ev TB.LogPf.czY _).trans (hφ i)

theorem jetSubstP_left (m : ℕ) {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (f : PS S 2 d) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => psIn d m ![0] (φ j), fun j => X ((1 : Fin 2), j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m f) =
      psJet m (ev (n := 2) ![comp1 φ (pt S d 0), pt S d 1] f) := by
  refine jetSubstP_psJet m _ (cz_left hφ) ?_ ?_ f
  · rintro ⟨i, j⟩
    fin_cases i
    · exact (FBIdPh.cc_psIn d m _ _).trans (hφ j)
    · simp
  · rintro ⟨i, j⟩
    fin_cases i
    · exact mk_psIn_psJet m 0 (φ j)
    · exact (FBIdSy.mk_psTrunc_X m _).symm

theorem jetSubstP_right (m : ℕ) {φ : Pt S 1 d} (hφ : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0) (f : PS S 2 d) :
    jetSubstP m (fun p : Fin 2 × Fin d => (![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (φ j)] :
        Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) p.1 p.2) (psJet m f) =
      psJet m (ev (n := 2) ![pt S d 0, comp1 φ (pt S d 1)] f) := by
  refine jetSubstP_psJet m _ (cz_right hφ) ?_ ?_ f
  · rintro ⟨i, j⟩
    fin_cases i
    · simp
    · exact (FBIdPh.cc_psIn d m _ _).trans (hφ j)
  · rintro ⟨i, j⟩
    fin_cases i
    · exact (FBIdSy.mk_psTrunc_X m _).symm
    · exact mk_psIn_psJet m 1 (φ j)

variable [Algebra ℚ S]

end Jets

section Frames

open MvPolynomial (X)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} {d : ℕ}
variable {x : ∀ m, jO y d m 1 ⟶ Xo.univ.t.G}

variable {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S} {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S}
  {ph1 ph2 : MvPowerSeries (Fin 3 × Fin d) S} {sy : MvPowerSeries (Fin 2 × Fin d) S}
  {ad : 𝓞 E → MvPowerSeries (Fin 2 × Fin d) S} {e e' : ∀ m, FrTy y d x m}

end Frames

section Clauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] [StarRing (𝓞 E)]
variable (y : FrPt Xo c S) (C : ChartAt Xo c y)

end Clauses

end GlobalTheory.FrameTwistCompare
end
end
