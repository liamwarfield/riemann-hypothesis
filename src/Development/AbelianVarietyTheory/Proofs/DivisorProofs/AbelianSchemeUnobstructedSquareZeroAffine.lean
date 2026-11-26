module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfCohomologyStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimOfAxes
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh.PrimForm

variable {R : Type} [CommRing R]

theorem pF_comp {A B C : Over (Sp R)} (f : B ⟶ C) (g : A ⟶ B) (a : GlobForm C.hom) :
    pF g (pF f a) = pF (g ≫ f) a :=
  (GlobalTheory.AbCoh.pull_comp_cup_id.1 R R C.left B.left C.hom B.hom (RingHom.id R) f.left (ovw f) R A.left A.hom
    (RingHom.id R) g.left (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) (fun _ ↦ rfl)).2.2.1 a

theorem pF_id (A : Over (Sp R)) (a : GlobForm A.hom) : pF (𝟙 A) a = a :=
  (GlobalTheory.AbCoh.pull_comp_cup_id.2.2 R A).2.2.1 a

theorem pF_unit {A B : Over (Sp R)} (f : 𝟙_ (Over (Sp R)) ⟶ A) (a : GlobForm A.hom) :
    pF (toUnit B ≫ f) a = 0 := by
  rw [← pF_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).1
  rw [Subsingleton.elim (pF f a) 0, map_zero]

theorem prim_of_axes (A : Over (Sp R)) [GrpObj A]
    (H : ∀ y : GlobForm (A ⊗ A).hom, pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 →
      pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0) : PrimF A := by
  intro x
  have e := H (pF μ[A] x - pF (fst A A) x - pF (snd A A) x) ?_ ?_
  · exact (sub_eq_zero.1 ((sub_sub _ _ _).symm.trans e))
  · rw [map_sub, map_sub, pF_comp, pF_comp, pF_comp, lift_fst, lift_snd, lift_comp_one_right, pF_id, pF_unit,
      sub_self, sub_zero]
  · rw [map_sub, map_sub, pF_comp, pF_comp, pF_comp, lift_fst, lift_snd, lift_comp_one_left, pF_id, pF_unit,
      sub_zero, sub_self]

end GlobalTheory.AbCoh.PrimForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndPrimitiveOneForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantOneFormFrameAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLawTranslateDerivationInvariantForms
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveSpMapOfSq
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem surjective_spMap_of_sq {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π)
    (hsq : ∀ a ∈ RingHom.ker π, a * a = 0) : Function.Surjective (spMap π) := fun x ↦ by
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker π : Set A) := fun a ha ↦
    (x.isPrime.mem_or_mem ((hsq a ha).symm ▸ x.asIdeal.zero_mem)).elim id id
  rw [← range_comap_of_surjective B π hπ] at hx
  exact hx

theorem pt_dual_le_of_fst : ∀ (R : Type) [CommRing R] (H : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D]
      (Z : Over.mk (spMap (algebraMap R (DualNumber D))) ⟶ H) (U : H.left.Opens),
      ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R D D) ≫ Z).left ⁻¹ᵁ U → ⊤ ≤ Z.left ⁻¹ᵁ U := by
  intro R _ H D _ _ Z U h x _
  have hs : Function.Surjective (spMap ((TrivSqZeroExt.fstHom R D D : DualNumber D →ₐ[R] D) : DualNumber D →+* D)) :=
    surjective_spMap_of_sq _ (fun d ↦ ⟨TrivSqZeroExt.inl d, rfl⟩) fun a ha ↦ by
      have h0 : a.fst = 0 := ha
      ext <;> simp [h0]
  obtain ⟨y, rfl⟩ := hs x
  have hy := h (show y ∈ (⊤ : (Sp D).Opens) from trivial)
  simpa [Over.comp_left, PDiv.spOver_left] using hy

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLawTranslateDerivationInvariantForms
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvForm

section Alg
variable {R C E : Type} [CommRing R] [CommRing C] [Algebra R C] [CommRing E] [Algebra R E]

theorem dVal_smul_left (φ : C →ₐ[R] DualNumber E) (c : C) (x : Ω[C⁄R]) :
    dVal φ (c • x) = (φ c).fst * dVal φ x := by
  letI : Algebra C E := (redHom φ).toAlgebra
  haveI : IsScalarTower R C E := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.coe_restrictScalars]
  rw [LinearMap.map_smul]
  rfl

def semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    C →ₐ[R] DualNumber E where
  toFun c := TrivSqZeroExt.inl (σ c) + TrivSqZeroExt.inr (θ (KaehlerDifferential.D R C c))
  map_one' := by ext <;> simp
  map_mul' a b := by
    ext
    · simp
    · simp [hθ, MulOpposite.smul_eq_mul_unop]; ring
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  commutes' r := by ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem fst_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x)
    (c : C) : (semiDerHom σ θ hθ c).fst = σ c := by simp [semiDerHom]

theorem dVal_semiDerHom (σ : C →ₐ[R] E) (θ : Ω[C⁄R] →ₗ[R] E) (hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = σ c * θ x) :
    dVal (semiDerHom σ θ hθ) = θ := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using GlobalTheory.CechDR.ind1 with
  | h b c =>
    rw [dVal_smul_left, dVal_D, hθ, fst_semiDerHom]
    simp [semiDerHom]
  | h0 => simp
  | ha x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

end Alg
end GlobalTheory.InvForm

namespace GlobalTheory.InvForm

theorem exists_transl_val : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left)
    (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
    (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) →
    ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1),
      (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧
      ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  intro R _ A _ U V θ hθ
  let T := Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1
  let σ : Sec A.hom V.unop.1 →ₐ[R] T := Algebra.TensorProduct.includeRight
  let τ : Sec A.hom U.unop.1 →ₐ[R] T := Algebra.TensorProduct.includeLeft
  have hθ' : ∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = σ c * θ x := hθ
  let φ := semiDerHom σ θ hθ'
  let aV : Over.mk (spMap (algebraMap R (Sec A.hom V.unop.1))) ⟶ A :=
    Over.homMk (affPt A.hom V.unop) (affPt_w A.hom V.unop)
  let aU : Over.mk (spMap (algebraMap R (Sec A.hom U.unop.1))) ⟶ A :=
    Over.homMk (affPt A.hom U.unop) (affPt_w A.hom U.unop)
  let p := GlobalTheory.DeRham.spOver φ ≫ aV
  let x₀ := GlobalTheory.DeRham.spOver τ ≫ aU
  let y₀ := GlobalTheory.DeRham.spOver σ ≫ aV
  let q' := y₀⁻¹ * x₀
  let dualInclusion := TrivSqZeroExt.inlAlgHom R T T
  let dualProjection := TrivSqZeroExt.fstHom R T T
  let q := GlobalTheory.DeRham.spOver dualInclusion ≫ q'
  let red := GlobalTheory.DeRham.spOver dualProjection
  have h1 : red ≫ p = y₀ := by
    have hφ : dualProjection.comp φ = σ := AlgHom.ext fun c ↦ fst_semiDerHom σ θ hθ' c
    simp only [red, p, y₀, ← Category.assoc, GlobalTheory.DeRham.spOver_comp, hφ]
  have h2 : red ≫ q = q' := by
    have hsection : dualProjection.comp dualInclusion = AlgHom.id R T := AlgHom.ext fun _ ↦ rfl
    have hid : GlobalTheory.DeRham.spOver (AlgHom.id R T) = 𝟙 (Over.mk (spMap (algebraMap R T))) := by
      apply Over.OverMorphism.ext
      simp only [GlobalTheory.DeRham.spOver, Over.homMk_left, Over.id_left]
      exact Cris.spMap_id T
    simp only [red, q, ← Category.assoc, GlobalTheory.DeRham.spOver_comp, hsection, hid, Category.id_comp]
  have h3 : red ≫ (p * q) = x₀ := by
    rw [MonObj.comp_mul, h1, h2, mul_inv_cancel_left]
  have h3Left : spMap dualProjection.toRingHom ≫ (p * q).left = spMap τ.toRingHom ≫ affPt A.hom U.unop := by
    simpa only [Over.comp_left, red, x₀, aU, GlobalTheory.DeRham.spOver, Over.homMk_left,
      AlgHom.toRingHom_eq_coe]
      using congrArg (fun f ↦ f.left) h3
  have htop : ⊤ ≤ (p * q).left ⁻¹ᵁ U.unop.1 := by
    have hsurj : Function.Surjective (spMap dualProjection.toRingHom) :=
      GlobalTheory.PtExt.surjective_spMap_of_sq _ TrivSqZeroExt.fst_surjective fun a ha ↦ by
        have ha' : a.fst = 0 := ha
        ext <;> simp [ha']
    intro x _
    obtain ⟨t, rfl⟩ := hsurj x
    change ((spMap dualProjection.toRingHom ≫ (p * q).left).base t) ∈ U.unop.1
    rw [h3Left]
    change U.unop.2.fromSpec.base ((spMap τ.toRingHom).base t) ∈ U.unop.1
    exact (Set.ext_iff.mp U.unop.2.range_fromSpec _).1 ⟨_, rfl⟩
  have hs : (p * q).left ≫ A.hom = spMap (algebraMap R (DualNumber T)) := Over.w (p * q)
  let ψ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := U.unop.1) (p * q).left htop hs
  have hψ : spMap ψ.toRingHom ≫ affPt A.hom U.unop = (p * q).left :=
    GlobalTheory.CechKS.FormLocal.valHom_pt U.unop.2 _ htop hs
  have hfst : dualProjection.toRingHom.comp ψ.toRingHom = τ.toRingHom := by
    apply GlobalTheory.CechKS.FormLocal.ringHom_ext_affPt (s := A.hom) U.unop.2
    change spMap _ ≫ affPt A.hom U.unop = spMap _ ≫ affPt A.hom U.unop
    rw [Cris.spMap_comp, Category.assoc, hψ]
    exact h3Left
  refine ⟨ψ, fun b ↦ RingHom.congr_fun hfst b, fun w ↦ ?_⟩
  have hp : p.left = spMap φ.toRingHom ≫ affPt A.hom V.unop := by
    simp only [p, aV, Over.comp_left, GlobalTheory.DeRham.spOver, Over.homMk_left, AlgHom.toRingHom_eq_coe]
  have hq : q.left = spMap (algebraMap T (DualNumber T)) ≫ q'.left := by
    have hι : (dualInclusion : T →+* DualNumber T) = algebraMap T (DualNumber T) := RingHom.ext fun _ ↦ rfl
    simp only [q, Over.comp_left, GlobalTheory.DeRham.spOver, Over.homMk_left, hι]
  have key := w.2 T V.unop U.unop φ ψ p q q'.left hp hq hψ.symm
  rw [dVal_semiDerHom] at key
  exact key

end GlobalTheory.InvForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLawTranslateDerivationInvariantFormsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_groupLawTranslate_derivation_invariantForms : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U V : AffOp A.left) (θ : Ω[Sec A.hom V.unop.1⁄R] →ₗ[R] Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1), (∀ (c : Sec A.hom V.unop.1) (x : Ω[Sec A.hom V.unop.1⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → ∃ ψ : Sec A.hom U.unop.1 →ₐ[R] DualNumber (Sec A.hom U.unop.1 ⊗[R] Sec A.hom V.unop.1), (∀ b, (ψ b).fst = b ⊗ₜ 1) ∧ ∀ w : GlobalTheory.InvForm.InvForm A, θ (evForm A.hom V w.1) = GlobalTheory.InvForm.dVal ψ (evForm A.hom U w.1) := by
  first | exact @GlobalTheory.InvForm.exists_transl_val | exact GlobalTheory.InvForm.exists_transl_val | (intros; apply GlobalTheory.InvForm.exists_transl_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorKaehlerEqZeroOfDerivationsVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorKaehlerEqZeroOfDerivationsVanish
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem tensor_kaehler_eq_zero_of_derivations_vanish :
  ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C], Module.Projective C Ω[C⁄R] → ∀ z : B ⊗[R] Ω[C⁄R], (∀ θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C, (∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → LinearMap.liftBaseChange B θ z = 0) → z = 0 := by
  intro R B C _ _ _ _ _ hP z hz
  classical
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := C) (P := Ω[C⁄R])).1 hP
  let π : (Ω[C⁄R] →₀ C) →ₗ[C] Ω[C⁄R] := Finsupp.linearCombination C id
  have hcomp : (LinearMap.lTensor B (π.restrictScalars R)) ∘ₗ (LinearMap.lTensor B (s.restrictScalars R))
      = LinearMap.id := by
    rw [← LinearMap.lTensor_comp]
    have : (π.restrictScalars R) ∘ₗ (s.restrictScalars R) = LinearMap.id := by
      exact LinearMap.ext fun x => LinearMap.congr_fun hs x
    rw [this, LinearMap.lTensor_id]
  have key : LinearMap.lTensor B (s.restrictScalars R) z = 0 := by
    apply (TensorProduct.finsuppRight R R B C Ω[C⁄R]).injective
    rw [map_zero]
    ext i
    let θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C :=
      (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toLinearMap ∘ₗ
        ((Finsupp.lapply (R := C) (M := C) i).restrictScalars R ∘ₗ s.restrictScalars R)
    have hθ : ∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x := by
      intro c x
      simp [θ, Algebra.TensorProduct.tmul_mul_tmul]
    have h1 := hz θ hθ
    have heq : ∀ w : B ⊗[R] Ω[C⁄R], (TensorProduct.finsuppRight R R B C Ω[C⁄R]
        (LinearMap.lTensor B (s.restrictScalars R) w)) i = LinearMap.liftBaseChange B θ w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul b x =>
        simp [θ, TensorProduct.finsuppRight_apply_tmul_apply, LinearMap.liftBaseChange_tmul,
          TensorProduct.smul_tmul']
      | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
    rw [heq, h1]; rfl
  have := congrArg (fun f => f z) hcomp
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [← this, key, map_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorKaehlerEqZeroOfDerivationsVanishStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_liftBaseChange_derivations_eq_zero : ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C], Module.Projective C Ω[C⁄R] → ∀ z : B ⊗[R] Ω[C⁄R], (∀ θ : Ω[C⁄R] →ₗ[R] B ⊗[R] C, (∀ (c : C) (x : Ω[C⁄R]), θ (c • x) = (1 ⊗ₜ c) * θ x) → LinearMap.liftBaseChange B θ z = 0) → z = 0 := by
  first | exact @GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish | exact GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish | (intros; apply GlobalTheory.tensor_kaehler_eq_zero_of_derivations_vanish <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormEqZeroOfAffineCoverRestrictions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormEqZeroOfAffineCoverRestrictions
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverForms

open KaehlerDifferential

theorem exists_pow_smul_eq_zero {R C B : Type} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra R B] (g : C →ₐ[R] B) (f : C)
    (hloc : @IsLocalization.Away C _ f B _ g.toRingHom.toAlgebra)
    (L : Ω[C⁄R] →ₗ[R] Ω[B⁄R]) (hD : ∀ c, L (D R C c) = D R B (g c))
    (hs : ∀ (c : C) (α : Ω[C⁄R]), L (c • α) = g c • L α)
    (α : Ω[C⁄R]) (h : L α = 0) : ∃ m : ℕ, f ^ m • α = 0 := by
  letI : Algebra C B := g.toRingHom.toAlgebra
  haveI : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq (fun r => (g.commutes r).symm)
  have hL : ∀ β, L β = KaehlerDifferential.map R R C B β := by
    intro β
    have hβ : β ∈ Submodule.span C (Set.range (D R C)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hβ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, rfl⟩ := hx
      rw [hD, KaehlerDifferential.map_D]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul c x _ hx =>
      rw [hs, hx, (KaehlerDifferential.map R R C B).map_smul]
      exact algebraMap_smul B c _
  haveI := KaehlerDifferential.isLocalizedModule_map R C B (Submonoid.powers f)
  have h' : KaehlerDifferential.map R R C B α = KaehlerDifferential.map R R C B 0 := by
    rw [← hL, h, map_zero]
  obtain ⟨⟨c, hc⟩, hc0⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) h'
  obtain ⟨m, rfl⟩ := hc
  refine ⟨m, ?_⟩
  simpa [Submonoid.smul_def] using hc0

theorem eq_zero_of_cover : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), CompactSpace X → ∃ (n : ℕ) (V : Fin n → AffOp X), ∀ w : GlobForm s, (∀ k, evForm s (V k) w = 0) → w = 0 := by
  intro R _ X s hX
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : X.affineOpens => (U.1 : Set X))
    (fun U => U.1.isOpen) (fun x _ => by
      obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, hxU⟩)
  refine ⟨t.card, fun k => Opposite.op (t.equivFin.symm k).1, fun w hw => ?_⟩
  have hcov : ∀ x : X, ∃ U ∈ t, x ∈ (U.1 : Set X) := fun x => by
    simpa using ht (Set.mem_univ x)
  have hV0 : ∀ U ∈ t, w.1 (Opposite.op U) = 0 := fun U hU => by
    have : evForm s (Opposite.op (t.equivFin.symm (t.equivFin ⟨U, hU⟩)).1) w = 0 := hw _
    have e : t.equivFin.symm (t.equivFin ⟨U, hU⟩) = ⟨U, hU⟩ := Equiv.symm_apply_apply _ _
    rw [e] at this
    exact this
  apply Subtype.ext
  funext W
  obtain ⟨W₀⟩ := W
  have hW : IsAffineOpen W₀.1 := W₀.2
  let S : Set Γ(X, W₀.1) := {f | ∃ U ∈ t, X.basicOpen f ≤ U.1}
  have hS : Ideal.span S = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun f => X.basicOpen_le _) ?_
    intro x hx
    obtain ⟨U, hU, hxU⟩ := hcov x
    obtain ⟨f, hf, hxf⟩ := hW.exists_basicOpen_le (V := U.1) ⟨x, hxU⟩ hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, U, hU, hf⟩, hxf⟩
  let α : Ω[Sec s W₀.1⁄R] := w.1 (Opposite.op W₀)
  let I : Ideal (Sec s W₀.1) := LinearMap.ker (LinearMap.toSpanSingleton (Sec s W₀.1) _ α)
  have hrad : ∀ f ∈ S, f ∈ I.radical := by
    rintro f ⟨U, hU, hf⟩
    let D' : X.affineOpens := ⟨X.basicOpen f, hW.basicOpen f⟩
    let φ : (Opposite.op W₀ : AffOp X) ⟶ Opposite.op D' := (homOfLE (X.basicOpen_le f)).op
    let ψ : (Opposite.op U : AffOp X) ⟶ Opposite.op D' := (homOfLE hf).op
    have h0 : p1 (OAff s) φ α = 0 := by
      have e1 := w.2 φ
      have e2 := w.2 ψ
      rw [hV0 U hU, map_zero] at e2
      exact e1.symm.trans e2
    obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero (mp (OAff s) φ) f
      (hW.isLocalization_basicOpen f) (p1 (OAff s) φ) (p1_D (OAff s) φ) (oneFormsMapOfFunctorMorphism_smul (OAff s) φ) α h0
    exact ⟨m, by simpa [I] using hm⟩
  have hI : I = ⊤ := by
    rw [← Ideal.radical_eq_top, eq_top_iff]
    have h2 := Ideal.span_le.2 hrad
    exact (show (⊤ : Ideal (Sec s W₀.1)) ≤ Ideal.span S from hS.ge).trans h2
  have h1 : (1 : Sec s W₀.1) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end GlobalTheory.CoverForms
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormEqZeroOfAffineCoverRestrictionsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_affineCover_globalForm_eq_zero_of_restrictions : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), CompactSpace X → ∃ (n : ℕ) (V : Fin n → AffOp X), ∀ w : GlobForm s, (∀ k, evForm s (V k) w = 0) → w = 0 := by
  first | exact @GlobalTheory.CoverForms.eq_zero_of_cover | exact GlobalTheory.CoverForms.eq_zero_of_cover | (intros; apply GlobalTheory.CoverForms.eq_zero_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAf
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.InvForm

namespace GlobalTheory.InvFormRetract

theorem dVal_smul {R B D : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing D] [Algebra R D] (φ : B →ₐ[R] DualNumber D) (b : B) (x : Ω[B⁄R]) : dVal φ (b • x) = redHom φ b * dVal φ x := by
  letI : Algebra B D := (redHom φ).toAlgebra
  haveI : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq fun r ↦ (redHom_algebraMap φ r).symm
  unfold dVal
  simp only [LinearMap.restrictScalars_apply, LinearMap.map_smul]
  rfl

theorem injective_baseChange {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (hab : IsAbelianScheme A) (U : AffOp A.left) :
    Function.Injective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
  haveI : Smooth A.hom := hab.smooth
  haveI : IsProper A.hom := hab.proper
  haveI : CompactSpace A.left := ⟨by simpa using QuasiCompact.isCompact_preimage (f := A.hom) Set.univ isOpen_univ isCompact_univ⟩
  haveI : Algebra.Smooth R (Sec A.hom U.unop.1) := smooth_sec_affine A.hom U.unop
  haveI : Module.Flat R (Sec A.hom U.unop.1) := Algebra.Smooth.flat R _
  obtain ⟨n, V, hV⟩ := GlobalTheory.T.exists_finite_affineCover_globalForm_eq_zero_of_restrictions R A.left A.hom inferInstance
  let f : ∀ k, InvForm A →ₗ[R] Ω[Sec A.hom (V k).unop.1⁄R] := fun k => evForm A.hom (V k) ∘ₗ (InvForm A).subtype
  let F : InvForm A →ₗ[R] ((k : Fin n) → Ω[Sec A.hom (V k).unop.1⁄R]) := LinearMap.pi f
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    exact Subtype.ext (hV w.1 fun k => congrFun hw k)
  have hFB : Function.Injective (LinearMap.lTensor (Sec A.hom U.unop.1) F) :=
    Module.Flat.lTensor_preserves_injective_linearMap F hF
  have hk : ∀ (k : Fin n) (z : Sec A.hom U.unop.1 ⊗[R] InvForm A), TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])
      (LinearMap.lTensor (Sec A.hom U.unop.1) F z) k = LinearMap.lTensor (Sec A.hom U.unop.1) (f k) z := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b w => simp [F]
    | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  apply hFB
  rw [map_zero]
  apply (TensorProduct.piRight R R (Sec A.hom U.unop.1) (fun k : Fin n => Ω[Sec A.hom (V k).unop.1⁄R])).injective
  rw [map_zero]
  funext k
  rw [hk, Pi.zero_apply]
  haveI : Algebra.Smooth R (Sec A.hom (V k).unop.1) := smooth_sec_affine A.hom (V k).unop
  refine GlobalTheory.T.eq_zero_of_liftBaseChange_derivations_eq_zero R (Sec A.hom U.unop.1) _ inferInstance _ (fun θ hθ => ?_)
  obtain ⟨ψ, hfst, hψ⟩ := GlobalTheory.T.exists_groupLawTranslate_derivation_invariantForms R A U (V k) θ hθ
  have key : ∀ y, LinearMap.liftBaseChange (Sec A.hom U.unop.1) θ (LinearMap.lTensor (Sec A.hom U.unop.1) (f k) y) =
      dVal ψ (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      rw [LinearMap.lTensor_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul, dVal_smul]
      have h1 : redHom ψ b = b ⊗ₜ 1 := hfst b
      rw [h1, Algebra.smul_def]
      simp only [f, LinearMap.comp_apply, Submodule.subtype_apply, hψ]
      rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [key, hz, map_zero]

theorem retract : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  intro R _ A _ g hab hdim U
  have hsurj : Function.Surjective (LinearMap.liftBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top R A g hab hdim U, Submodule.span_le]
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp⟩
  let e := LinearEquiv.ofBijective _ ⟨injective_baseChange A hab U, hsurj⟩
  refine ⟨e.symm.toLinearMap, fun w => ?_⟩
  apply e.injective
  rw [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]
  change _ = LinearMap.liftBaseChange _ _ (1 ⊗ₜ w)
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end GlobalTheory.InvFormRetract
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRetractionDifferentialsInvariantOneFormsAfStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_retraction_differentials_invariantOneForms_affine : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, ∃ r : Ω[Sec A.hom U.unop.1⁄R] →ₗ[Sec A.hom U.unop.1] (Sec A.hom U.unop.1 ⊗[R] GlobalTheory.InvForm.InvForm A), ∀ w : GlobalTheory.InvForm.InvForm A, r (evForm A.hom U w.1) = 1 ⊗ₜ w := by
  first | exact @GlobalTheory.InvFormRetract.retract | exact GlobalTheory.InvFormRetract.retract | (intros; apply GlobalTheory.InvFormRetract.retract <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantOneFormsAbelianSchemeFiniteProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantOneFormsAbelianSchemeFiniteProjective
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.InvFormProj

theorem finite_projective_of_locally_projective (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    (h : ∀ q : PrimeSpectrum R, ∃ r : R, r ∉ q.asIdeal ∧ ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
      (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
      (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
      (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ) :
    Module.Finite R M ∧ Module.Projective R M := by
  let s : Set R := {r | ∃ (F : Type) (_ : AddCommGroup F) (_ : Module R F)
    (_ : Module (Localization.Away r) F) (_ : IsScalarTower R (Localization.Away r) F)
    (_ : Module.Finite (Localization.Away r) F) (_ : Module.Projective (Localization.Away r) F)
    (ϕ : M →ₗ[R] F), IsBaseChange (Localization.Away r) ϕ}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr, hP⟩ := h ⟨m, hm.isPrime⟩
    exact hr (hsm (Ideal.subset_span hP))
  have hg : ∀ g : s, g.1 ∈ s := fun g => g.2
  choose F iA iM iL iT iFin iProj ϕ hϕ using hg
  letI := iA
  letI := iM
  letI := iL
  haveI := iT
  haveI := iFin
  haveI := iProj
  haveI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (ϕ g) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.1) (Localization.Away g.1) (ϕ g)).2 (hϕ g)
  haveI (g : s) : Module.Flat R (F g) := by
    haveI : Module.Flat R (Localization.Away g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans R (Localization.Away g.1) (F g)
  haveI hfp : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat R M :=
    Module.flat_of_isLocalized_span R M s hs F ϕ fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

theorem finite_projective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (GlobalTheory.InvForm.InvForm A).subtype)) → Module.Finite R (GlobalTheory.InvForm.InvForm A) ∧ Module.Projective R (GlobalTheory.InvForm.InvForm A) := by
  intro R _ A _ g _ hsm hbc
  haveI : SmoothOfRelativeDimension g A.hom := hsm
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  apply finite_projective_of_locally_projective
  intro q
  let e : Spec (CommRingCat.of R) ⟶ A.left := η[A].left
  have he : e ≫ A.hom = 𝟙 _ := by simp [e]
  obtain ⟨V, hV, hqV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp A.left.isBasis_affineOpens)
    (show e q ∈ (⊤ : A.left.Opens) from trivial)
  obtain ⟨_, ⟨r, rfl⟩, hr, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (a := q) (u := (e ⁻¹ᵁ V).1) hqV (e ⁻¹ᵁ V).2
  refine ⟨r, hr, ?_⟩
  let y : Sp (Localization.Away r) ⟶ A.left := spMap (algebraMap R (Localization.Away r)) ≫ e
  have hy : ⊤ ≤ y ⁻¹ᵁ V := by
    intro t _
    have : PrimeSpectrum.comap (algebraMap R (Localization.Away r)) t ∈
        (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact ⟨t, rfl⟩
    exact hsub this
  have hs : y ≫ A.hom = spMap (algebraMap R (Localization.Away r)) := by
    simp only [y, Category.assoc, he, Category.comp_id]
  let φ := GlobalTheory.CechKS.FormLocal.valHom (s := A.hom) (U := V) y hy hs
  letI : Algebra (Sec A.hom V) (Localization.Away r) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R (Sec A.hom V) (Localization.Away r) :=
    IsScalarTower.of_algebraMap_eq fun a => (φ.commutes a).symm
  haveI : Algebra.Smooth R (Sec A.hom V) := smooth_sec_affine A.hom ⟨V, hV⟩
  have hb := hbc (Opposite.op ⟨V, hV⟩)
  exact ⟨Localization.Away r ⊗[Sec A.hom V] Ω[Sec A.hom V⁄R], inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, _,
    hb.comp (TensorProduct.isBaseChange (Sec A.hom V) Ω[Sec A.hom V⁄R] (Localization.Away r))⟩

end GlobalTheory.InvFormProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantOneFormsAbelianSchemeFiniteProjectiveStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantOneForms_abelianScheme_finite_projective : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (GlobalTheory.InvForm.InvForm A).subtype)) → Module.Finite R (GlobalTheory.InvForm.InvForm A) ∧ Module.Projective R (GlobalTheory.InvForm.InvForm A) := by
  first | exact @GlobalTheory.InvFormProj.finite_projective | exact GlobalTheory.InvFormProj.finite_projective | (intros; apply GlobalTheory.InvFormProj.finite_projective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantOneFormFrameAbelianScheme
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.InvFormBC

open GlobalTheory.InvForm

theorem isBaseChange_invForm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ (InvForm A).subtype) := by
  intro R _ A _ g hab hdim U
  let f := evForm A.hom U ∘ₗ (InvForm A).subtype
  let L := f.liftBaseChange (Sec A.hom U.unop.1)
  have hs : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← GlobalTheory.T.span_invariantOneForms_affineOpen_abelianScheme_eq_top R A g hab hdim U]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨w, rfl⟩
    exact ⟨1 ⊗ₜ w, by simp [L, f]⟩
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_retraction_differentials_invariantOneForms_affine R A g hab hdim U
  have hl : ∀ x, r (L x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b w =>
      have : L (b ⊗ₜ w) = b • evForm A.hom U w.1 := by simp [L, f]
      rw [this, map_smul, hr, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hi : Function.Injective L := fun x y h ↦ by rw [← hl x, ← hl y, h]
  have hb : Function.Bijective L := ⟨hi, hs⟩
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective L hb) fun x ↦
    show L (1 ⊗ₜ x) = f x from (LinearMap.liftBaseChange_tmul _ f 1 x).trans (one_smul _ _)

theorem exists_invariant_frame : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (j : M →ₗ[R] GlobForm A.hom), Module.Finite R M ∧ Module.Projective R M ∧ ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ j) := by
  intro R _ A _ g hab hdim
  have hbc := isBaseChange_invForm R A g hab hdim
  obtain ⟨hfin, hproj⟩ := GlobalTheory.T.invariantOneForms_abelianScheme_finite_projective R A g hab hdim hbc
  exact ⟨InvForm A, inferInstance, inferInstance, (InvForm A).subtype, hfin, hproj, hbc⟩

end GlobalTheory.InvFormBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantOneFormFrameAbelianSchemeStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_oneForm_frame_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (j : M →ₗ[R] GlobForm A.hom), Module.Finite R M ∧ Module.Projective R M ∧ ∀ U : AffOp A.left, IsBaseChange (Sec A.hom U.unop.1) (evForm A.hom U ∘ₗ j) := by
  first | exact @GlobalTheory.InvFormBC.exists_invariant_frame | exact GlobalTheory.InvFormBC.exists_invariant_frame | (intros; apply GlobalTheory.InvFormBC.exists_invariant_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormsPrimitiveAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareGlobalOneFormEqZeroOfAxes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareGlobalOneFormEqZeroOfAxes
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh.AxesForm

open GlobalTheory.AbCoh.PrimForm

theorem eq_zero_of_axes : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ y : GlobForm (A ⊗ A).hom, GlobalTheory.AbCoh.pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 → GlobalTheory.AbCoh.pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0 := by
  intro R _ A _ g hA hg y h₁ h₂
  obtain ⟨hA2, hg2⟩ := (GlobalTheory.T.abelian_square_affine_h1_vanish R).1 A g hA hg
  obtain ⟨f1, p1, r1⟩ := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hg
  obtain ⟨f2, p2, r2⟩ := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R (A ⊗ A) (g + g) hA2 hg2
  let N : GlobForm (A ⊗ A).hom →ₗ[R] GlobForm A.hom × GlobForm A.hom :=
    LinearMap.prod (pF (lift (𝟙 A) (toUnit A ≫ η[A]))) (pF (lift (toUnit A ≫ η[A]) (𝟙 A)))
  let P : GlobForm A.hom × GlobForm A.hom →ₗ[R] GlobForm (A ⊗ A).hom :=
    LinearMap.coprod (pF (fst A A)) (pF (snd A A))
  have hNP : N ∘ₗ P = LinearMap.id := by
    refine LinearMap.ext fun x ↦ Prod.ext ?_ ?_
    · show pF (lift (𝟙 A) (toUnit A ≫ η[A])) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.1
      rw [map_add (f := _), pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, add_zero]
    · show pF (lift (toUnit A ≫ η[A]) (𝟙 A)) (pF (fst A A) x.1 + pF (snd A A) x.2) = x.2
      rw [map_add (f := _), pF_comp, pF_comp, lift_fst, lift_snd, pF_id, pF_unit, zero_add]
  have hinj := GlobalTheory.Obs.Axes.injective_of_section N P hNP (fun p ↦ by
    rw [Module.rankAtStalk_prod, Pi.add_apply, r1, r2])
  refine hinj (?_ : N y = N 0)
  rw [map_zero]
  exact Prod.ext h₁ h₂

end GlobalTheory.AbCoh.AxesForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareGlobalOneFormEqZeroOfAxesStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianSquare_globalOneForm_eq_zero_of_axes : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ y : GlobForm (A ⊗ A).hom, GlobalTheory.AbCoh.pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 → GlobalTheory.AbCoh.pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0 := by
  first | exact @GlobalTheory.AbCoh.AxesForm.eq_zero_of_axes | exact GlobalTheory.AbCoh.AxesForm.eq_zero_of_axes | (intros; apply GlobalTheory.AbCoh.AxesForm.eq_zero_of_axes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormsPrimitiveAbelianScheme
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.AbCoh.primF_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.PrimF A :=
  fun R _ A _ g hA hg ↦ GlobalTheory.AbCoh.PrimForm.prim_of_axes A (GlobalTheory.T.abelianSquare_globalOneForm_eq_zero_of_axes R A g hA hg)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormsPrimitiveAbelianSchemeStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalOneForms_primitive_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.PrimF A := by
  first | exact @GlobalTheory.AbCoh.primF_of_isAbelianScheme | exact GlobalTheory.AbCoh.primF_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.primF_of_isAbelianScheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndPrimitiveOneForms
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

private theorem hasFrame_of_isBaseChange_local : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), ∀ (W : Type) [AddCommGroup W] [Module R W] [Module.Finite R W] [Module.Projective R W] (j : W →ₗ[R] Glob1 F), (∀ T : C, ∃ e : W →ₗ[R] Ω[F.obj T⁄R], (∀ w, e w = (j w).1 T) ∧ IsBaseChange (F.obj T) e) → HasFrame F := by
  intro R _ C _ F W _ _ _ _ j h
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin' R W
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property v (LinearMap.id) hv
  have hw : ∀ x : W, x = ∑ i, σ x i • v (Pi.single i 1) := by
    intro x
    have := LinearMap.congr_fun hσ x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq] at this
    conv_lhs => rw [← this]
    conv_lhs => rw [show σ x = ∑ i, σ x i • Pi.single i (1 : R) from by
      ext k; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul]
  choose e he hb using h
  let l : Fin n → W →ₗ[R] R := fun i ↦ LinearMap.proj i ∘ₗ σ
  let δ : Fin n → ∀ T : C, Ω[F.obj T⁄R] →ₗ[F.obj T] F.obj T :=
    fun i T ↦ (hb T).lift (Algebra.linearMap R (F.obj T) ∘ₗ l i)
  have hδ : ∀ i T (x : W), δ i T (e T x) = algebraMap R (F.obj T) (σ x i) := by
    intro i T x
    exact (hb T).lift_eq _ x
  refine ⟨n, ⟨⟨fun i ↦ j (v (Pi.single i 1)), δ, ?_, ?_⟩⟩⟩
  · intro i T T' φ ω
    refine (hb T).inductionOn ω ?_ ?_ ?_
    · intro x
      have h1 : p1 F φ (e T x) = e T' x := by
        rw [he T x, he T' x]; exact ((j x).2 φ).symm
      rw [h1, hδ, hδ]
      exact ((mp F φ).commutes _).symm
    · intro s ω hω
      rw [oneFormsMapOfFunctorMorphism_smul, LinearMap.map_smul, LinearMap.map_smul, hω, smul_eq_mul, smul_eq_mul, map_mul]
    · intro a b ha hb'
      rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb', map_add (f := _)]
  · intro T ω
    refine (hb T).inductionOn ω ?_ ?_ ?_
    · intro x
      simp_rw [hδ, ← he T, algebraMap_smul]
      conv_lhs => rw [hw x]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; simp_rw [map_smul]
    · intro s ω hω
      conv_lhs => rw [hω]
      simp_rw [LinearMap.map_smul, Finset.smul_sum, smul_eq_mul, mul_smul]
    · intro a b ha hb'
      conv_lhs => rw [ha, hb']
      simp_rw [map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem hasFrame_and_primF_of_isAbelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ PrimF A := by
  intro R _ A _ g hA hg
  obtain ⟨M, _, _, j, hfin, hproj, hb⟩ := GlobalTheory.T.exists_invariant_oneForm_frame_abelianScheme R A g hA hg
  exact ⟨hasFrame_of_isBaseChange_local R (AffOp A.left) (OAff A.hom) M j fun U ↦ ⟨_, fun _ ↦ rfl, hb U⟩,
    GlobalTheory.T.globalOneForms_primitive_abelianScheme R A g hA hg⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndPrimitiveOneFormsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_oneFormFrame_and_primitiveOneForms : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.PrimF A := by
  first | exact @GlobalTheory.AbCoh.hasFrame_and_primF_of_isAbelianScheme | exact GlobalTheory.AbCoh.hasFrame_and_primF_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.hasFrame_and_primF_of_isAbelianScheme <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffine
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UnobTop.abelianUnobstructed : GlobalTheory.Published.AbelianUnobstructed :=
  GlobalTheory.T.abelianScheme_unobstructed_of_cohomology_structure GlobalTheory.T.abelian_structure_cohomology_statement fun R _ A _ g hA hg =>
    ⟨(GlobalTheory.T.abelianScheme_oneFormFrame_and_primitiveOneForms R A g hA hg).1, GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme R A hA, (GlobalTheory.T.abelianScheme_oneFormFrame_and_primitiveOneForms R A g hA hg).2⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffineStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine : GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.UnobTop.abelianUnobstructed | exact GlobalTheory.UnobTop.abelianUnobstructed | (intros; apply GlobalTheory.UnobTop.abelianUnobstructed <;> assumption)
end
