module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceRestrictionExistsPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.GrpTangentPt

variable {S : Scheme.{0}} {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)

def sqZeroMapPt {M N : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N] (l : M →ₗ[R'] N) :
    Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' N)) ≫ x) ⟶
      Over.mk (spMap (algebraMap R' (TrivSqZeroExt R' M)) ≫ x) :=
  Over.homMk (spMap (TrivSqZeroExt.map l).toRingHom) (by
    change Spec.map _ ≫ Spec.map _ ≫ x = Spec.map _ ≫ x
    rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    exact CommRingCat.hom_ext (TrivSqZeroExt.map l).comp_algebraMap)

lemma sqZeroMapPt_comp {M N P : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
    [AddCommGroup N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
    [AddCommGroup P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]
    (l : M →ₗ[R'] N) (l' : N →ₗ[R'] P) :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = sqZeroMapPt x (l' ∘ₗ l) := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

abbrev epsScalePt (c : R') : epsPtR x ⟶ epsPtR x := sqZeroMapPt x (c • (LinearMap.id : R' →ₗ[R'] R'))

lemma epsScalePt_left (c : R') : (epsScalePt x c).left = spMap (epsScaleR c) := rfl

lemma sqZeroMapPt_comp_eq {M : Type} [AddCommGroup M] [Module R' M] [Module R'ᵐᵒᵖ M]
    [IsCentralScalar R' M] (l : R' →ₗ[R'] M) (l' : M →ₗ[R'] R') :
    sqZeroMapPt x l' ≫ sqZeroMapPt x l = epsScalePt x (l' (l 1)) := by
  rw [sqZeroMapPt_comp]
  congr 1
  refine LinearMap.ext_ring ?_
  simp

lemma epsScalePt_one : epsScalePt x (1 : R') = 𝟙 _ := by
  ext1
  change Spec.map _ = 𝟙 _
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp

variable {G : Over S} [GrpObj G]

lemma epsScalePt_zero_comp {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x 0 ≫ w = 1 := by
  let π : epsPtR x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R' (DualNumber R'))) rfl
  have e : (1 : epsPtR x ⟶ G) = π ≫ (1 : Over.mk x ⟶ G) := (comp_one π).symm
  rw [e]
  ext1
  rw [Over.comp_left, Over.comp_left, ← hw, ← Category.assoc]
  congr 1
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun z => ?_)
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem epsScalePt_add_comp (a b : R') {w : epsPtR x ⟶ G}
    (hw : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left) :
    epsScalePt x (a + b) ≫ w = (epsScalePt x a ≫ w) * (epsScalePt x b ≫ w) := by
  let i₁ := LinearMap.inl R' R' R'
  let i₂ := LinearMap.inr R' R' R'
  have key : sqZeroMapPt x (i₁ + i₂) ≫ w = (sqZeroMapPt x i₁ ≫ w) * (sqZeroMapPt x i₂ ≫ w) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R' R' R')).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R' R' R')).toRingHom
        (fun z => ⟨1, one_pos, TrivSqZeroExt.map i₁ z, by ext <;> simp [i₁]⟩) fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.fst R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
    · refine congrArg Over.Hom.left
        (?_ : sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _ = sqZeroMapPt x (LinearMap.snd R' R' R') ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, sqZeroMapPt_comp_eq]
      simp [i₁, i₂, epsScalePt_zero_comp x hw, epsScalePt_one]
  have := congrArg (sqZeroMapPt x (a • LinearMap.fst R' R' R' + b • LinearMap.snd R' R' R') ≫ ·) key
  simp only [comp_mul, ← Category.assoc, sqZeroMapPt_comp_eq] at this
  simpa [i₁, i₂] using this

theorem tanadd : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S)
    (w : epsPtR x ⟶ G), spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left →
    ∀ (a b : R') (wa wb : epsPtR x ⟶ G), wa.left = spMap (epsScaleR a) ≫ w.left →
      wb.left = spMap (epsScaleR b) ≫ w.left → (wa * wb).left = spMap (epsScaleR (a + b)) ≫ w.left := by
  intro S G _ R' _ x w hw a b wa wb ha hb
  have ea : wa = epsScalePt x a ≫ w := Over.OverMorphism.ext ha
  have eb : wb = epsScalePt x b ≫ w := Over.OverMorphism.ext hb
  rw [ea, eb, ← epsScalePt_add_comp x a b hw]
  rfl

end GlobalTheory.GrpTangentPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpObj_tangentVector_add_at_point : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S) (w : epsPtR x ⟶ G), spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left → ∀ (a b : R') (wa wb : epsPtR x ⟶ G), wa.left = spMap (epsScaleR a) ≫ w.left → wb.left = spMap (epsScaleR b) ≫ w.left → (wa * wb).left = spMap (epsScaleR (a + b)) ≫ w.left := by
  first | (exact @GlobalTheory.GrpTangentPt.tanadd) | (exact GlobalTheory.GrpTangentPt.tanadd) | (intros; apply GlobalTheory.GrpTangentPt.tanadd  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycle
set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv

namespace GlobalTheory

namespace PDiv

namespace CocycleSum

theorem four {M N : Type} [CommMonoid M] [AddCommGroup N] (c : M → M → N)
    (h : ∀ x y z, c y z - c (x * y) z + c x (y * z) - c x y = 0) (hs : ∀ x y, c x y = c y x)
    (a b a' b' : M) :
    c (a * b) (a' * b') = c a a' + c b b' + (c (a * a') (b * b') - c a b - c a' b') := by
  have h1 := h a b (a' * b')
  have h2 := h a a' (b * b')
  have h3 := h a' b' b
  rw [show b * (a' * b') = a' * (b * b') from mul_left_comm _ _ _] at h1
  rw [show b' * b = b * b' from mul_comm _ _, hs (a' * b') b, hs b' b] at h3
  rw [← sub_eq_zero]
  have e : c (a * b) (a' * b') - (c a a' + c b b' + (c (a * a') (b * b') - c a b - c a' b')) =
      -(c b (a' * b') - c (a * b) (a' * b') + c a (a' * (b * b')) - c a b) +
      (c a' (b * b') - c (a * a') (b * b') + c a (a' * (b * b')) - c a a') -
      (c b b' - c b (a' * b') + c a' (b * b') - c a' b') := by abel
  rw [e, h1, h2, h3]
  simp

variable {R A X : Type} [CommRing R] [CommRing A] [CommRing X] [Bialgebra R A] [Algebra R X]

def val (x y : WithConv (A →ₐ[R] X)) : A ⊗[R] A →ₐ[R] X :=
  Algebra.TensorProduct.lift x.ofConv y.ofConv fun _ _ => .all ..

@[simp] theorem val_tmul (x y : WithConv (A →ₐ[R] X)) (a b : A) :
    val x y (a ⊗ₜ b) = x.ofConv a * y.ofConv b := rfl

theorem mul_apply (x y : WithConv (A →ₐ[R] X)) (a : A) :
    (x * y).ofConv a = val x y (comul a) := by
  rw [val]
  exact AlgHom.convMul_apply x y a

theorem lift_cobTwo (x y z : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    Algebra.TensorProduct.lift x.ofConv (val y z) (fun _ _ => .all ..) (cobTwo R A c) =
      val y z c - val (x * y) z c + val x (y * z) c - val x y c := by
  have hA : ∀ (t : A ⊗[R] A) (b : A),
      Algebra.TensorProduct.lift x.ofConv (val y z) (fun _ _ => .all ..)
        (TensorProduct.assoc R A A A (t ⊗ₜ b)) = val x y t * z.ofConv b := by
    intro t b
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a a' => simp [mul_assoc]
    | add u v hu hv => simp only [TensorProduct.add_tmul, map_add (f := _), hu, hv, add_mul]
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [cobTwo_apply]
    simp only [map_sub, map_add (f := _), TensorProduct.mk_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, LinearMap.flip_apply, Algebra.TensorProduct.lift_tmul, val_tmul, hA,
      mul_apply, map_one, one_mul, mul_one]
  | add u v hu hv =>
    simp only [map_add (f := _), hu, hv]
    abel

theorem val_comm (x y : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    val x y (TensorProduct.comm R A A c) = val y x c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [TensorProduct.comm_tmul, val_tmul, val_tmul, mul_comm]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem val_push {Y : Type} [CommRing Y] [Algebra R Y] (u : X →ₐ[R] Y)
    (x y : WithConv (A →ₐ[R] X)) (c : A ⊗[R] A) :
    val (ptsPush A u x) (ptsPush A u y) c = u (val x y c) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [val_tmul, ptsPush_ofConv, AlgHom.comp_apply, map_mul]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

variable {B : Type} [CommRing B] [Bialgebra R B]

theorem val_include (x y : WithConv (A →ₐ[R] B)) (c : A ⊗[R] A) :
    val (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) x)
      (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) y) c =
      TensorProduct.map x.ofConv.toLinearMap y.ofConv.toLinearMap c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [val_tmul, ptsPush_ofConv, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, TensorProduct.map_tmul, AlgHom.toLinearMap_apply]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]

theorem include_mul (f : A →ₐc[R] B) :
    ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)) *
      ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)) =
      ptsPush A (comulAlgHom R B) (toConv (f : A →ₐ[R] B)) := by
  apply WithConv.ext
  ext a
  rw [mul_apply, val_include]
  simp only [ptsPush_ofConv, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  exact CoalgHomClass.map_comp_comul_apply f a

end CocycleSum


open CocycleSum in
theorem pullTwo_convMul {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A]
    [Bialgebra R B] [IsCocomm R A] (f g : A →ₐc[R] B) (c : A ⊗[R] A) (hc : c ∈ symCocycles R A) :
    pullbackTwo (toConv f * toConv g).ofConv c = pullbackTwo f c + pullbackTwo g c +
      cobOne R B (LinearMap.mul' R B
        (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) := by
  obtain ⟨hc2, hcs⟩ := mem_symCocycles.1 hc
  have hv : ∀ (x y : WithConv (A →ₐ[R] B)) (t : A ⊗[R] A), val x y t =
      LinearMap.mul' R B (TensorProduct.map x.ofConv.toLinearMap y.ofConv.toLinearMap t) := by
    intro x y t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  have key := four (M := WithConv (A →ₐ[R] B ⊗[R] B)) (fun x y => val x y c)
    (fun x y z => (lift_cobTwo x y z c).symm.trans (by rw [hc2, map_zero]))
    (fun x y => by rw [← val_comm, hcs])
    (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B) (toConv (g : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (f : A →ₐ[R] B)))
    (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B) (toConv (g : A →ₐ[R] B)))
  rw [← map_mul (ptsPush A (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] B)),
    ← map_mul (ptsPush A (Algebra.TensorProduct.includeRight : B →ₐ[R] B ⊗[R] B)),
    include_mul f, include_mul g, val_include, val_include, val_include, val_push, val_push,
    val_push] at key
  have hl : ∀ h : A →ₐc[R] B, (h : A →ₗ[R] B) = (h : A →ₐ[R] B).toLinearMap := fun _ => rfl
  have hfg : ((toConv f * toConv g).ofConv : A →ₐ[R] B) =
      (toConv (f : A →ₐ[R] B) * toConv (g : A →ₐ[R] B)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul (toConv f) (toConv g))
  have hv' : LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c) =
      val (toConv (f : A →ₐ[R] B)) (toConv (g : A →ₐ[R] B)) c := by
    rw [hv, hl, hl]
  unfold pullbackTwo
  rw [hl, hfg, key, cobOne_apply, hv', Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, hl, hl]
  rfl

end PDiv

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoConvMulSymmetricCocycleStatement
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bialgebraPullbackTwo_convMul_symmetricCocycle : ∀ {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Bialgebra R A] [Bialgebra R B] [IsCocomm R A] (f g : A →ₐc[R] B) (c : A ⊗[R] A), c ∈ symCocycles R A → pullbackTwo (toConv f * toConv g).ofConv c = pullbackTwo f c + pullbackTwo g c + cobOne R B (LinearMap.mul' R B (TensorProduct.map (f : A →ₗ[R] B) (g : A →ₗ[R] B) c)) := by
  first | exact @GlobalTheory.PDiv.pullTwo_convMul | exact GlobalTheory.PDiv.pullTwo_convMul | (intros; apply GlobalTheory.PDiv.pullTwo_convMul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinates
namespace GlobalTheory.FGDepth.Coord

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

noncomputable section

variable {C : Type} [Field C]

open MvPowerSeries in
private lemma subst_sum_smul_X' {C : Type} [Field C] {σ τ ι : Type} [Fintype ι]
    {b : σ → MvPowerSeries τ C} (hb : HasSubst b) (c : ι → C) (g : ι → σ) :
    subst b (∑ a, c a • (X (g a) : MvPowerSeries σ C)) = ∑ a, c a • b (g a) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← coe_substAlgHom hb, map_sum]
  simp only [map_smul, coe_substAlgHom, subst_X hb]

open MvPowerSeries in
private lemma mvIsInt_X_divisor {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type}
    (s : σ) : _root_.ReciprocityTheory.PGsh.MvIsInt v (X s : MvPowerSeries σ C) := by
  classical
  intro α
  show 0 ≤ v (coeff α (X s : MvPowerSeries σ C))
  rw [coeff_X]
  split_ifs <;> simp


open MvPowerSeries in
variable {C : Type} [Field C] in
theorem _root_.GlobalTheory.FGDepth.Coord.depth_in_coords : ∀ (C : Type) [Field C] [CharZero C]
    (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : _root_.ReciprocityTheory.PGsh.LogFGL v d) (u : Fin i → Fin d → C)
    (Φ Ψ : Fin d → MvPowerSeries (Fin d) C),
    (∀ a, _root_.ReciprocityTheory.PGsh.MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ _root_.ReciprocityTheory.PGsh.MvIsInt v (Ψ a) ∧
      constantCoeff (Ψ a) = 0) →
    (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) →
    ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) →
    (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) →
    _root_.GlobalTheory.FGDepth.detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C //
      _root_.ReciprocityTheory.PGsh.MvIsInt v f}, _root_.GlobalTheory.FGDepth.toE (v (_root_.GlobalTheory.FGDepth.derivAt0
        (_root_.GlobalTheory.FGDepth.detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) =>
          subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2))
            f.1))) := by
  intro C _ _ v i d c G u Φ Ψ hΦΨ hinv t ht0 ht
  have hΦ : HasSubst Φ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.1
  have hΨ : HasSubst Ψ := hasSubst_of_constantCoeff_zero fun a => (hΦΨ a).2.2.2
  have htS : HasSubst t := hasSubst_of_constantCoeff_zero ht0
  have hlg : HasSubst G.lg := hasSubst_of_constantCoeff_zero G.2
  have hex0 : ∀ a, constantCoeff (_root_.GlobalTheory.FGDepth.expOf G a) = 0 := (_root_.GlobalTheory.FGDepth.isExp_expOf G).1
  have hexS : HasSubst (_root_.GlobalTheory.FGDepth.expOf G) := hasSubst_of_constantCoeff_zero hex0
  have hLin0 : ∀ e, constantCoeff (∑ a, u a e • (X a : MvPowerSeries (Fin i) C)) = 0 := by
    intro e
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have hLinS : HasSubst fun e => ∑ a, u a e • (X a : MvPowerSeries (Fin i) C) :=
    hasSubst_of_constantCoeff_zero hLin0
  have hΦtS : HasSubst fun a => subst t (Φ a) :=
    hasSubst_of_constantCoeff_zero fun a => constantCoeff_subst_eq_zero htS ht0 (hΦΨ a).2.1

  have hΦt : ∀ a, subst t (Φ a) =
      subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
        (_root_.GlobalTheory.FGDepth.expOf G a) := by
    intro a
    have h1 : (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C)) =
        fun e => subst (fun a => subst t (Φ a)) (G.lg e) := by
      funext e
      rw [← subst_comp_subst_apply hΦ htS, ht]
    rw [h1, ← subst_comp_subst_apply hlg hΦtS, _root_.GlobalTheory.FGDepth.subst_lg_expOf, subst_X hΦtS]
  have ht_eq : ∀ e, t e = subst (fun e => ∑ b, u b e • (X b : MvPowerSeries (Fin i) C))
      (subst (_root_.GlobalTheory.FGDepth.expOf G) (Ψ e)) := by
    intro e
    rw [subst_comp_subst_apply hexS hLinS]
    calc t e = subst t (X e) := (subst_X htS e).symm
      _ = subst t (subst Φ (Ψ e)) := by rw [(hinv e).2]
      _ = subst (fun a => subst t (Φ a)) (Ψ e) := subst_comp_subst_apply hΦ htS _
      _ = _ := by simp_rw [hΦt]

  have hXb : ∀ b : Fin i, HasSubst fun a : Fin i =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hXd : ∀ b : Fin i, HasSubst fun a : Fin d =>
      (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C) :=
    fun b => hasSubst_of_constantCoeff_zero fun a => constantCoeff_X _
  have hLinB0 : ∀ (b : Fin i) (e : Fin d),
      constantCoeff (∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) = 0 := by
    intro b e
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum]
  have hLinBS : ∀ b : Fin i, HasSubst fun e =>
      ∑ a, u a e • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) :=
    fun b => hasSubst_of_constantCoeff_zero (hLinB0 b)
  have hE0 : ∀ x, constantCoeff
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u) x) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hLinBS x.1) (hLinB0 x.1) (hex0 x.2)
  have hES : HasSubst
      (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u)) :=
    hasSubst_of_constantCoeff_zero hE0
  have hΨ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.2.2
  have hΨS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2) :=
    hasSubst_of_constantCoeff_zero hΨ0
  have hΦ0 : ∀ x : (Σ _ : Fin i, Fin d), constantCoeff
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2)) = 0 :=
    fun x => constantCoeff_subst_eq_zero (hXd x.1) (fun a => constantCoeff_X _) (hΦΨ x.2).2.1
  have hΦS : HasSubst fun x : (Σ _ : Fin i, Fin d) =>
      subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2) :=
    hasSubst_of_constantCoeff_zero hΦ0

  have key : ∀ x : (Σ _ : Fin i, Fin d),
      subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2) =
      subst (_root_.GlobalTheory.FGDepth.expAlong (fun _ : Fin i => G) (fun _ : Fin i => u))
        (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C))
          (Ψ x.2)) := by
    rintro ⟨b, e⟩
    have hlin : (fun e' => subst (fun a : Fin i =>
        (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C))
          (∑ a, u a e' • (X a : MvPowerSeries (Fin i) C))) =
        fun e' => ∑ a, u a e' • (X ⟨b, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C) := by
      funext e'
      exact subst_sum_smul_X' (hXb b) (fun a => u a e') id
    rw [ht_eq e, subst_comp_subst_apply hLinS (hXb b), hlin,
      subst_comp_subst_apply hexS (hLinBS b), subst_comp_subst_apply (hXd b) hES]
    congr 1
    funext a
    rw [subst_X hES]
    rfl

  have hround : (fun x : (Σ _ : Fin i, Fin d) => subst
      (fun x : (Σ _ : Fin i, Fin d) =>
        subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Ψ x.2))
      (subst (fun a : Fin d => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin d) C)) (Φ x.2))) =
      X := by
    funext x
    rw [subst_comp_subst_apply (hXd x.1) hΨS]
    simp_rw [subst_X hΨS]
    rw [← subst_comp_subst_apply hΨ (hXd x.1), (hinv x.2).1, subst_X (hXd x.1)]
  unfold _root_.GlobalTheory.FGDepth.detDepth _root_.GlobalTheory.FGDepth.depth
  simp_rw [key]
  apply le_antisymm
  · refine le_iInf fun f => ?_
    rw [← subst_comp_subst_apply hΨS hES]
    exact iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).2.2.1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΨ0⟩ le_rfl
  · refine le_iInf fun f => ?_
    refine iInf_le_of_le ⟨_, _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2
      (fun x => _root_.ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hΦΨ x.2).1 (fun a => mvIsInt_X_divisor v _) (fun a => constantCoeff_X _))
      hΦ0⟩ ?_
    rw [← subst_comp_subst_apply hΨS hES, subst_comp_subst_apply hΦS hΨS, hround, subst_self]
    rfl

end

end GlobalTheory.FGDepth.Coord
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentialOperatorDepthIntegralCoordinatesStatement
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.differentialOperatorDepth_integral_coordinates : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (i d c : ℕ) (G : LogFGL v d) (u : Fin i → Fin d → C) (Φ Ψ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Φ a) ∧ constantCoeff (Φ a) = 0 ∧ MvIsInt v (Ψ a) ∧ constantCoeff (Ψ a) = 0) → (∀ a, subst Ψ (Φ a) = X a ∧ subst Φ (Ψ a) = X a) → ∀ (t : Fin d → MvPowerSeries (Fin i) C), (∀ a, constantCoeff (t a) = 0) → (∀ e, subst t (subst Φ (G.lg e)) = ∑ a, u a e • X a) → detDepth G u c = ⨅ f : {f : MvPowerSeries (Σ _ : Fin i, Fin d) C // MvIsInt v f}, toE (v (derivAt0 (detPow C i c) (subst (fun x : (Σ _ : Fin i, Fin d) => subst (fun a : Fin i => (X ⟨x.1, a⟩ : MvPowerSeries (Σ _ : Fin i, Fin i) C)) (t x.2)) f.1))) := by
  first | exact @GlobalTheory.FGDepth.Coord.depth_in_coords | exact GlobalTheory.FGDepth.Coord.depth_in_coords | (intros; apply GlobalTheory.FGDepth.Coord.depth_in_coords <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafPresheafOverCoproductEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafPresheafOverCoproductEqSum
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.FreeCofan

theorem pieces {U : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (j : ∀ i, V i ⟶ U)
    (hc : IsColimit (Cofan.mk U j)) :
    (∀ i, IsOpenImmersion (j i)) ∧ (∀ u : U, ∃ i, ∃ v : V i, j i v = u) ∧
      (∀ i k (v : V i) (w : V k), j i v = j k w → i = k) := by
  let e : ∐ V ≅ U := (colimit.isColimit (Discrete.functor V)).coconePointUniqueUpToIso hc
  have he : ∀ i, Sigma.ι V i ≫ e.hom = j i := fun i =>
    (colimit.isColimit (Discrete.functor V)).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have hinv : ∀ u : U, e.hom (e.inv u) = u := fun u => by
    rw [← Scheme.Hom.comp_apply, e.inv_hom_id]; rfl
  have hinv' : ∀ z : (∐ V : Scheme.{0}), e.inv (e.hom z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, e.hom_inv_id]; rfl
  refine ⟨fun i => ?_, fun u => ?_, fun i k v w h => ?_⟩
  · rw [← he i]; infer_instance
  · obtain ⟨⟨i, v⟩, hv⟩ := (sigmaMk V).surjective (e.inv u)
    refine ⟨i, v, ?_⟩
    rw [← he i, Scheme.Hom.comp_apply, ← sigmaMk_mk, hv, hinv]
  · rw [← he i, ← he k, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
    have h2 := congrArg e.inv h
    rw [hinv', hinv'] at h2
    exact congrArg Sigma.fst ((sigmaι_eq_iff V i k v w).1 h2)

theorem pullback_isColimit {U : Scheme.{0}} {ι : Type} {V : ι → Scheme.{0}} (j : ∀ i, V i ⟶ U)
    (hc : IsColimit (Cofan.mk U j)) {T : Scheme.{0}} (y : T ⟶ U) :
    Nonempty (IsColimit (Cofan.mk T (fun i => pullback.fst y (j i)))) := by
  obtain ⟨ho, hcov, hdis⟩ := pieces j hc
  refine nonempty_isColimit_cofanMk_of _ ?_ ?_
  · rw [eq_top_iff]
    rintro z -
    obtain ⟨i, v, hv⟩ := hcov (y z)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := y) (g := j i) z v hv.symm
    exact (TopologicalSpace.Opens.mem_iSup (s := fun i => (pullback.fst y (j i)).opensRange)).2 ⟨i, w, hw⟩
  · intro i k hik
    rw [Function.onFun, disjoint_iff, eq_bot_iff]
    rintro z ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    apply hik
    refine hdis i k (pullback.snd y (j i) p) (pullback.snd y (j k) q) ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, ← pullback.condition,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    change y ((pullback.fst y (j i)) p) = y ((pullback.fst y (j k)) q)
    rw [hp, hq]

theorem sec_subsingleton_of_isEmpty {R : Type} [CommRing R] (G : Shv R) (W : Scheme.{0}) [IsEmpty W] :
    Subsingleton (Sec G W) := by
  haveI : ∀ e : PEmpty.{1}, IsOpenImmersion (PEmpty.elim e : (PEmpty.elim e : Scheme.{0}) ⟶ W) :=
    fun e => e.elim
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (X := fun e : PEmpty.{1} => (PEmpty.elim e : Scheme.{0})) (S := W)
    (fun e => PEmpty.elim e) (by rw [eq_top_iff]; rintro z -; exact isEmptyElim z) (fun e => PEmpty.elim e)
  have hb := GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G W PEmpty.{1} _ _ hc
  exact ⟨fun x y => hb.1 (funext fun e => PEmpty.elim e)⟩

end GlobalTheory.EtC.FreeCofan

namespace GlobalTheory.EtC.FreeCofan

theorem res_res {R : Type} [CommRing R] {G : Shv R} {W W' T : Scheme.{0}} (g : W ⟶ W') (f : W' ⟶ T)
    (z : Sec G T) : Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem main : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ (P : PSh) (t : P ⟶ yoneda.obj U) (Q : ι → PSh) (a : ∀ i, Q i ⟶ P) (b : ∀ i, Q i ⟶ yoneda.obj (V i)), (∀ i, IsPullback (a i) (b i) t (yoneda.map (j i))) → Nonempty (IsColimit (Cofan.mk ((free R).obj P) (fun i ↦ (free R).map (a i)))) := by
  intro R _ U ι V j hc P t Q a b hpb
  obtain ⟨ho, -, hdis⟩ := pieces j hc
  have FH := fun (P' : PSh) (G : Shv R) => GlobalTheory.T.freeEtaleModuleSheaf_hom_equiv_natural_sections R P' G
  let y : ∀ T : Scheme.{0}, P.obj (op T) → (T ⟶ U) := fun T x => t.app (op T) x
  have hy : ∀ (T T' : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)), y T' (P.map g.op x) = g ≫ y T x :=
    fun T T' g x => NatTrans.naturality_apply t g.op x
  have hw : ∀ i (W : Scheme.{0}) (q0 : (Q i).obj (op W)), y W ((a i).app _ q0) = ((b i).app _ q0 : W ⟶ V i) ≫ j i :=
    fun i W q0 => ConcreteCategory.congr_hom (congr_app (hpb i).w (op W)) q0
  have hcol : ∀ (T : Scheme.{0}) (x : P.obj (op T)), IsColimit (Cofan.mk T (fun i => pullback.fst (y T x) (j i))) :=
    fun T x => (pullback_isColimit j hc (y T x)).some
  have SC := fun (G : Shv R) (T : Scheme.{0}) (x : P.obj (op T)) => GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective R G T ι _ _ (hcol T x)
  have hex : ∀ i (W : Scheme.{0}) (x : P.obj (op W)) (σ : W ⟶ V i), y W x = σ ≫ j i →
      ∃ q : (Q i).obj (op W), (a i).app _ q = x ∧ (b i).app _ q = σ := fun i W x σ h =>
    Types.exists_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) x σ h
  have huq : ∀ i (W : Scheme.{0}) (q q' : (Q i).obj (op W)), (a i).app _ q = (a i).app _ q' →
      (b i).app _ q = (b i).app _ q' → q = q' := fun i W q q' h1 h2 =>
    Types.ext_of_isPullback ((hpb i).map ((evaluation _ _).obj (op W))) h1 h2
  have hq : ∀ (T : Scheme.{0}) (x : P.obj (op T)) i, ∃ q : (Q i).obj (op (pullback (y T x) (j i))),
      (a i).app _ q = P.map (pullback.fst (y T x) (j i)).op x ∧ (b i).app _ q = pullback.snd (y T x) (j i) :=
    fun T x i => hex i _ _ _ (by rw [hy]; exact pullback.condition)
  choose q hqa hqb using hq
  have key : ∀ (G : Shv R) (m : (free R).obj P ⟶ G) T x i,
      Sec.res (pullback.fst (y T x) (j i)) (val m T x) = val ((free R).map (a i) ≫ m) _ (q T x i) := by
    intro G m T x i
    rw [(FH P G).2.2.2.1 (Q i) (a i) m, hqa, (FH P G).2.2.1 m]
  let φ : ∀ (G : Shv R) (c : ∀ i, (free R).obj (Q i) ⟶ G) (T : Scheme.{0}), P.obj (op T) → Sec G T :=
    fun G c T x => Function.surjInv (SC G T x).2 (fun i => val (c i) _ (q T x i))
  have hφ : ∀ G c T x i, Sec.res (pullback.fst (y T x) (j i)) (φ G c T x) = val (c i) _ (q T x i) :=
    fun G c T x i => congrFun (Function.surjInv_eq (SC G T x).2 _) i
  have nat : ∀ G c (T' T : Scheme.{0}) (g : T' ⟶ T) (x : P.obj (op T)),
      φ G c T' (P.map g.op x) = Sec.res g (φ G c T x) := by
    intro G c T' T g x
    apply (SC G T' (P.map g.op x)).1
    refine funext fun i => ?_
    dsimp only
    rw [hφ, res_res]
    have hw2 : (pullback.fst (y T' (P.map g.op x)) (j i) ≫ g) ≫ y T x = pullback.snd _ (j i) ≫ j i := by
      rw [Category.assoc, ← hy, pullback.condition]
    have h1 : pullback.lift _ _ hw2 ≫ pullback.fst (y T x) (j i) = pullback.fst (y T' (P.map g.op x)) (j i) ≫ g :=
      pullback.lift_fst _ _ _
    have h2 : pullback.lift _ _ hw2 ≫ pullback.snd (y T x) (j i) = pullback.snd (y T' (P.map g.op x)) (j i) :=
      pullback.lift_snd _ _ _
    rw [← h1, ← res_res, hφ, ← (FH (Q i) G).2.2.1 (c i)]
    congr 1
    apply huq
    · rw [hqa, NatTrans.naturality_apply, hqa, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
        ← op_comp, ← op_comp, h1]
    · rw [hqb, NatTrans.naturality_apply, hqb]
      exact h2.symm
  let d : ∀ s : Cofan (fun i => (free R).obj (Q i)), (free R).obj P ⟶ s.pt := fun s =>
    ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose
  have hd : ∀ s T x, val (d s) T x = φ s.pt s.inj T x := fun s =>
    ((FH P s.pt).2.1 (φ s.pt s.inj) (fun T' T g x => nat s.pt s.inj T' T g x)).choose_spec
  refine ⟨mkCofanColimit _ d ?_ ?_⟩
  · intro s i
    change (free R).map (a i) ≫ d s = s.inj i
    apply (FH (Q i) s.pt).1
    intro W q0
    rw [(FH P s.pt).2.2.2.1 (Q i) (a i), hd]
    obtain ⟨x, hx⟩ : ∃ x, x = (a i).app (op W) q0 := ⟨_, rfl⟩
    have hwx : y W x = ((b i).app _ q0 : W ⟶ V i) ≫ j i := hx ▸ hw i W q0
    rw [← hx]
    apply (SC s.pt W x).1
    refine funext fun k => ?_
    dsimp only
    rw [hφ, ← (FH (Q i) s.pt).2.2.1]
    by_cases hki : k = i
    · subst hki
      congr 1
      apply huq
      · rw [hqa, NatTrans.naturality_apply, ← hx]
      · rw [hqb, NatTrans.naturality_apply]
        change _ = pullback.fst (y W x) (j k) ≫ ((b k).app _ q0 : W ⟶ V k)
        haveI := ho k
        rw [← cancel_mono (j k), Category.assoc, ← pullback.condition, hwx]
    · haveI : IsEmpty ((pullback (y W x) (j k) : Scheme.{0}) : Type) := by
        refine ⟨fun z => hki (hdis k i (pullback.snd (y W x) (j k) z)
          ((pullback.fst (y W x) (j k) ≫ ((b i).app _ q0 : W ⟶ V i)) z) ?_)⟩
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← pullback.condition, Category.assoc, ← hwx]
      exact (sec_subsingleton_of_isEmpty s.pt _).elim _ _
  · intro s m hm
    have hm' : ∀ i, (free R).map (a i) ≫ m = s.inj i := hm
    apply (FH P s.pt).1
    intro T x
    rw [hd]
    apply (SC s.pt T x).1
    refine funext fun i => ?_
    dsimp only
    rw [hφ, key, hm']

end GlobalTheory.EtC.FreeCofan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafPresheafOverCoproductEqSumStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum : ∀ (R : Type) [CommRing R] (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ (P : PSh) (t : P ⟶ yoneda.obj U) (Q : ι → PSh) (a : ∀ i, Q i ⟶ P) (b : ∀ i, Q i ⟶ yoneda.obj (V i)), (∀ i, IsPullback (a i) (b i) t (yoneda.map (j i))) → Nonempty (IsColimit (Cofan.mk ((free R).obj P) (fun i => (free R).map (a i)))) := by
  first | (exact @GlobalTheory.EtC.FreeCofan.main) | (exact GlobalTheory.EtC.FreeCofan.main) | (intros; apply GlobalTheory.EtC.FreeCofan.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossTZeroRight
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.PBFc
open GlobalTheory.EtC GlobalTheory.EtC.CupSpec GlobalTheory.EZ

variable {R : Type} [CommRing R]

abbrev BSx (X : SimplicialObject Spc) (a b : ℕ) (U : Scheme.{0}) : Type :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).obj (op U)

abbrev BSx.res {X : SimplicialObject Spc} {a b : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (y : BSx X a b U) : BSx X a b V :=
  ((X.obj (op (SimplexCategory.mk a))).obj (op (SimplexCategory.mk b))).map g.op y

theorem biChains_isZero (X : SimplicialObject Spc) (c l : ℤ) (h : 0 < c ∨ 0 < l) :
    IsZero (((biChains R X).X c).X l) := by
  rcases h with h | h
  · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
      change -((i : ℕ) : ℤ) = c at hi
      omega))
  · by_cases hc : c ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      refine IsZero.of_iso ?_ ((HomologicalComplex.eval _ _ l).mapIso
        (HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := a) rfl))
      exact HomologicalComplex.isZero_extend_X _ _ l (fun i hi => by
        change -((i : ℕ) : ℤ) = l at hi
        omega)
    · exact (HomologicalComplex.eval _ _ l).map_isZero (HomologicalComplex.isZero_extend_X _ _ c (fun i hi => by
        change -((i : ℕ) : ℤ) = c at hi
        omega))

def evT {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ : Cochain (totChains R X) K n) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + n = s) (U : Scheme.{0}) (y : BSx X a b U) : Sec (K.X s) U :=
  Sec.map ((biChainsXIso R X a b).inv ≫ (biChains R X).ιTotal (ComplexShape.up ℤ) (-(a : ℤ)) (-(b : ℤ))
      (-((a + b : ℕ) : ℤ)) (by simp only [ComplexShape.π_def]; push_cast; ring) ≫ γ.v _ s h) (freeGen R _ U y)

theorem evT_ext {X : SimplicialObject Spc} {K : Cx R} {n : ℤ} (γ γ' : Cochain (totChains R X) K n)
    (h : ∀ a b s h U y, evT γ a b s h U y = evT γ' a b s h U y) : γ = γ' := by
  ext t s hs : 1
  apply HomologicalComplex₂.total.hom_ext
  intro c l hcl
  have hcl' : c + l = t := hcl
  by_cases hc : c ≤ 0 ∧ l ≤ 0
  · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
    obtain rfl : t = -((a + b : ℕ) : ℤ) := by push_cast; omega
    rw [← cancel_epi (biChainsXIso R X a b).inv]
    exact free_ext _ _ fun U y => h a b s hs U y
  · exact (biChains_isZero X c l (by omega)).eq_of_src _ _

theorem evT_exists {X : SimplicialObject Spc} {K : Cx R} {n : ℤ}
    (f : ∀ (a b : ℕ) (s : ℤ), -((a + b : ℕ) : ℤ) + n = s → ∀ U : Scheme.{0}, BSx X a b U → Sec (K.X s) U)
    (hf : ∀ a b s h (V U : Scheme.{0}) (g : V ⟶ U) (y : BSx X a b U), Sec.res g (f a b s h U y) = f a b s h V (y.res g)) :
    ∃ γ : Cochain (totChains R X) K n, ∀ a b s h U y, evT γ a b s h U y = f a b s h U y := by
  have key : ∀ (c l s : ℤ) (hs : c + l + n = s), ∃ ψ : ((biChains R X).X c).X l ⟶ K.X s,
      ∀ (a b : ℕ) (hc : c = -(a : ℤ)) (hl : l = -(b : ℤ)) U y,
        Sec.map ((biChainsXIso R X a b).inv ≫ eqToHom (by rw [hc, hl]) ≫ ψ) (freeGen R _ U y) =
          f a b s (by push_cast; omega) U y := by
    intro c l s hs
    by_cases hc : c ≤ 0 ∧ l ≤ 0
    · obtain ⟨a, rfl⟩ : ∃ a : ℕ, c = -(a : ℤ) := ⟨(-c).toNat, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b : ℕ, l = -(b : ℤ) := ⟨(-l).toNat, by omega⟩
      obtain ⟨φ, hφ⟩ := free_exists (R := R) _ _ (f a b s (by push_cast; omega)) (fun V U g y => hf a b s _ V U g y)
      refine ⟨(biChainsXIso R X a b).hom ≫ φ, fun a' b' hc hl U y => ?_⟩
      obtain rfl : a' = a := by omega
      obtain rfl : b' = b := by omega
      rw [eqToHom_refl, Category.id_comp, Iso.inv_hom_id_assoc]
      exact hφ U y
    · exact ⟨0, fun a b hc' hl' => by omega⟩
  choose ψ hψ using key
  refine ⟨Cochain.mk fun t s h => (biChains R X).totalDesc fun c l hcl => ψ c l s (by
      have : c + l = t := hcl
      omega), fun a b s h U y => ?_⟩
  unfold evT
  rw [Cochain.mk_v, HomologicalComplex₂.ι_totalDesc]
  have := hψ (-(a : ℤ)) (-(b : ℤ)) s (by push_cast at h ⊢; omega) a b rfl rfl U y
  rw [eqToHom_refl, Category.id_comp] at this
  exact this

section Cross
variable {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N))

def baseS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx E a U :=
  (show (E.obj (op (SimplexCategory.mk a))).obj (op U) × ((Fib N).obj (op (SimplexCategory.mk b))).obj (op U) from y).1

variable {B : Spc} (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B)

def vertS {a b : ℕ} {U : Scheme.{0}} (y : BSx (twX E V) a b U) : Sx B b U :=
  ((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).app (op U) y

theorem baseS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    baseS V (y.res g) = (baseS V y).res g := rfl

theorem vertS_res {a b : ℕ} {W U : Scheme.{0}} (g : W ⟶ U) (y : BSx (twX E V) a b U) :
    vertS V ℓ (y.res g) = (vertS V ℓ y).res g :=
  ConcreteCategory.congr_hom (((ℓ.app (op (SimplexCategory.mk a))).app (op (SimplexCategory.mk b))).naturality g.op) y

variable {I J K : Cx R} (μ : Pair I J K) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n)
  (z : Cochain ((chains R).obj B) J m)

def crossVal (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    Sec (K.X s) U :=
  (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
    (_root_.GlobalTheory.EtC.ev (R := R) α a _ rfl U (baseS V y))
    (_root_.GlobalTheory.EtC.ev (R := R) z b _ rfl U (vertS V ℓ y))

theorem crossVal_res (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) {W U : Scheme.{0}} (g : W ⟶ U)
    (y : BSx (twX E V) a b U) :
    Sec.res g (crossVal V ℓ μ hk α z a b s h U y) = crossVal V ℓ μ hk α z a b s h W (y.res g) := by
  unfold crossVal
  rw [Units.smul_def, Units.smul_def, Sec.res, map_zsmul, ← Sec.res, μ.nat, ev_res, ev_res, baseS_res, vertS_res]

def crossT : Cochain (totChains R (twX E V)) K k :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose

theorem evT_crossT (a b : ℕ) (s : ℤ) (h : -((a + b : ℕ) : ℤ) + k = s) (U : Scheme.{0}) (y : BSx (twX E V) a b U) :
    evT (crossT V ℓ μ hk α z) a b s h U y =
      (m * (a : ℤ)).negOnePow • μ.mul U (-(a : ℤ) + n) (-(b : ℤ) + m) s (by push_cast at h; omega)
        (_root_.GlobalTheory.EtC.ev (R := R) α a _ rfl U (baseS V y))
        (_root_.GlobalTheory.EtC.ev (R := R) z b _ rfl U (vertS V ℓ y)) :=
  (evT_exists (crossVal V ℓ μ hk α z) (fun a b s h W U g y => crossVal_res V ℓ μ hk α z a b s h g y)).choose_spec a b s h U y

theorem evT_add {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (γ γ' : Cochain (totChains R X) L t) (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (γ + γ') a b s h U y = evT γ a b s h U y + evT γ' a b s h U y := by
  unfold evT
  rw [Cochain.add_v, Preadditive.comp_add, Preadditive.comp_add]
  exact map_add (mapHom _ _ (freeGen R _ U y)) _ _

theorem crossT_add_left (α' : Cochain ((chains R).obj E) I n) :
    crossT V ℓ μ hk (α + α') z = crossT V ℓ μ hk α z + crossT V ℓ μ hk α' z :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_add, evT_crossT, evT_crossT, evT_crossT, ev_add, map_add (f := _), LinearMap.add_apply, smul_add]

theorem evT_zero {X : SimplicialObject Spc} {L : Cx R} {t : ℤ} (a b : ℕ) (s : ℤ)
    (h : -((a + b : ℕ) : ℤ) + t = s) (U : Scheme.{0}) (y : BSx X a b U) :
    evT (0 : Cochain (totChains R X) L t) a b s h U y = 0 := by
  unfold evT
  rw [Cochain.zero_v, comp_zero, comp_zero]
  exact map_zero (mapHom _ _ (freeGen R _ U y))

theorem crossT_zero_right : crossT V ℓ μ hk α (0 : Cochain ((chains R).obj B) J m) = 0 :=
  evT_ext _ _ fun a b s h U y => by
    rw [evT_crossT, evT_zero, ev_zero, map_zero, smul_zero]

end Cross

def twPairI (q : ℕ) (i j : ℤ) : Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q i)) :=
  Eq.rec (motive := fun k _ => Pair (res (ZMod q) (tw q (i - j))) (res (ZMod q) (tw q j)) (res (ZMod q) (tw q k)))
    (twPair q (i - j) j) (sub_add_cancel i j)

def phi (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) :
    (∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) →+
      Cochain (totChains (ZMod q) (twX E V)) (res _ (tw q i)) n :=
  AddMonoidHom.mk' (fun α => ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j))
    (fun α α' => by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => crossT_add_left V ℓ _ _ _ _ _)

theorem phi_apply (q : ℕ) {E : Spc} {N : ℕ} (V : E ⟶ ofCat (glCat N)) {B : Spc}
    (ℓ : twX E V ⟶ (Functor.const SimplexCategoryᵒᵖ).obj B) (i : ℤ)
    (z : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj B) (res _ (tw q ((j : ℕ) : ℤ))) (2 * ((j : ℕ) : ℤ)))
    (n : ℤ) (α : ∀ j : Fin N, Cochain ((chains (ZMod q)).obj E) (res _ (tw q (i - ((j : ℕ) : ℤ)))) (n - 2 * ((j : ℕ) : ℤ))) :
    phi q V ℓ i z n α = ∑ j : Fin N, crossT V ℓ (twPairI q i ((j : ℕ) : ℤ)) (sub_add_cancel n _) (α j) (z j) := rfl

end GlobalTheory.PBFc

end
end
