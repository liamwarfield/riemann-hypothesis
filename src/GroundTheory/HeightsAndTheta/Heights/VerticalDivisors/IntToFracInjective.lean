module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section NumberField

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def parPrime (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Ideal (MvPolynomial (Par e n) (𝓞 K)) :=
  Ideal.map C v.asIdeal

instance parPrime_isPrime (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : (parPrime e n v).IsPrime := by
  have h : parPrime e n v = RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk v.asIdeal) :
      MvPolynomial (Par e n) (𝓞 K) →+* MvPolynomial (Par e n) (𝓞 K ⧸ v.asIdeal)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
    rfl
  rw [h]
  exact RingHom.ker_isPrime _

abbrev ParDVR (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  Localization.AtPrime (parPrime e n v)

instance parDVR_isDomain (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : IsDomain (ParDVR e n v) :=
  IsLocalization.isDomain_of_atPrime _ (parPrime e n v)

def parY (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : Par e n → ParDVR e n v :=
  fun p => algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (X p)

def modelR (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    Ideal (MvPolynomial (Fin n) (ParDVR e n v)) :=
  (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))

abbrev SecB (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  SecAlg (modelR e I v) (parY e n v)

abbrev ParFrac (K : Type*) [Field K] [NumberField K] (e n : ℕ) : Type _ :=
  FractionRing (MvPolynomial (Par e n) (𝓞 K))

def parToFrac (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : ParDVR e n v →+* ParFrac K e n :=
  IsLocalization.lift (M := (parPrime e n v).primeCompl) (g := algebraMap _ (ParFrac K e n))
    fun s => IsUnit.mk0 _ fun h => (s.2 : (s : MvPolynomial (Par e n) (𝓞 K)) ∉ parPrime e n v)
      (by rw [(IsFractionRing.injective _ (ParFrac K e n)) (h.trans (map_zero _).symm)]
          exact Ideal.zero_mem _)

theorem intToFrac_injective (K : Type*) [Field K] [NumberField K] (e n : ℕ) :
    Function.Injective ((algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n)).comp C) := by
  simp only [RingHom.coe_comp]
  exact (IsFractionRing.injective _ _).comp (MvPolynomial.C_injective _ _)

def kToFrac (K : Type*) [Field K] [NumberField K] (e n : ℕ) : K →+* ParFrac K e n :=
  IsFractionRing.lift (intToFrac_injective K e n)

def parYF (K : Type*) [Field K] [NumberField K] (e n : ℕ) : Par e n → ParFrac K e n :=
  fun p => algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParFrac K e n) (X p)

def idealF (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) :
    Ideal (MvPolynomial (Fin n) (ParFrac K e n)) :=
  I.map (MvPolynomial.map (kToFrac K e n))

def specComps (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    Set (Ideal (MvPolynomial (Fin n) (𝓞 K))) :=
  relComps (integralModel I ⊔ Ideal.map C v.asIdeal)

def secIdealOf (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) : Ideal (SecB e I v) :=
  (W.map (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)))).map (Ideal.Quotient.mk _)

def vertDeg (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K)
    (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  ∑ᶠ W ∈ vertComps I u v,
    GroundTheory.Heights₂.Heights.localMult
      (integralModel I ⊔ Ideal.span {linForm u}) W * chowDegree (reduceMod v W) (e + 1)

end NumberField

def ParDVRIsDVR.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)),
    IsDiscreteValuationRing (ParDVR e n v)

def ParAlgIndep.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ),
    letI := (kToFrac K e n).toAlgebra
    AlgebraicIndependent K (parYF K e n)

def GaussDVR.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (g : MvPolynomial (Par e n) (𝓞 K)), g ≠ 0 →
      gaussNorm v (g.map (algebraMap (𝓞 K) K)) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ (Ring.ord (ParDVR e n v) (algebraMap _ _ g)).toNat = 1

def PrimitiveScale.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (σ : Type)
    (f : MvPolynomial σ K), f ≠ 0 →
      ∃ (c : K) (g : MvPolynomial σ (𝓞 K)), c ≠ 0 ∧ g.map (algebraMap (𝓞 K) K) = C c * f ∧
        ∃ m, g.coeff m ∉ v.asIdeal

def SecBFinite.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → Module.Finite (ParDVR e n v) (SecB e I v)

def SecBTorsionFree.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∀ (r : ParDVR e n v) (b : SecB e I v), r ≠ 0 → r • b = 0 → b = 0

def SecBGeneric.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)), IsProjPrime I →
      ∃ φ : SecB e I v →+* SecAlg (idealF e I) (parYF K e n),
        (∀ j, φ (secCoord _ _ j) = secCoord _ _ j) ∧
        (∀ r : ParDVR e n v, φ (algebraMap _ _ r) = algebraMap _ _ (parToFrac e n v r)) ∧
        letI := φ.toAlgebra
        IsLocalization (Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)))
          (SecAlg (idealF e I) (parYF K e n))

def SecBLinInj.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      Function.Injective fun b : SecB e I v =>
        secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) * b

def SpecMax.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f →
      (∀ W ∈ specComps I v, (secIdealOf e I v W).IsMaximal) ∧
        ∀ 𝔫 : Ideal (SecB e I v), 𝔫.IsMaximal → ∃! W, W ∈ specComps I v ∧ secIdealOf e I v W = 𝔫


open Classical in
def SpecLength.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      ∀ 𝔫 : MaximalSpectrum (SecB e I v), ∀ W ∈ specComps I v, secIdealOf e I v W = 𝔫.asIdeal →
        Ring.ord (Localization.AtPrime 𝔫.asIdeal)
            (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
              (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)))) =
          (letI : Decidable (linForm u ∈ W) := Classical.propDecidable _
           if linForm u ∈ W then
             (GroundTheory.Heights₂.Heights.localMult
               (integralModel I ⊔ Ideal.span {linForm u}) W : ℕ∞) else 0)

def SpecResidue.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → ∀ W ∈ specComps I v,
      Module.length (ParDVR e n v) (SecB e I v ⧸ secIdealOf e I v W) = chowDegree (reduceMod v W) (e + 1)

def VertSpec.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin (e + 1) × Fin n) K) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm (fun j => (u j : K)) ∉ I →
      vertComps I u v = {W | W ∈ specComps I v ∧ linForm u ∈ W}

def NormIdentity.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) →
    linForm (fun j => (u j : K)) ∉ I → (∃ m, g.coeff m ∉ v.asIdeal) →
      ∃ w : (ParDVR e n v)ˣ,
        algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename Sum.inl (specFirst g u)) =
          w * Algebra.norm (ParDVR e n v)
            (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)))

def OrdEq.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) →
    linForm (fun j => (u j : K)) ∉ I → (∃ m, g.coeff m ∉ v.asIdeal) →
      Ring.ord (ParDVR e n v)
          (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename Sum.inl (specFirst g u))) =
        vertDeg e I u v

def VertTermEq.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
      GroundTheory.Heights₂.Heights.vertTermAt I (e + 1) u v =
        vertDeg e I u v * Real.log (Ideal.absNorm v.asIdeal)

def GaussEq.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)),
    IsProjPrime I → IsChowForm I (e + 1) (g.map (algebraMap (𝓞 K) K)) →
    linForm (fun j => (u j : K)) ∉ I → (∃ m, g.coeff m ∉ v.asIdeal) →
      gaussNorm v (specFirst (g.map (algebraMap (𝓞 K) K)) fun j => (u j : K)) *
          (Ideal.absNorm v.asIdeal : ℝ) ^ vertDeg e I u v = 1 ∧
        gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormEval
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial TensorProduct

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

section Basis

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

def polyTensorAlgEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₐ[R] MvPolynomial (Fin n) A :=
  (Algebra.TensorProduct.comm R (MvPolynomial (Fin n) R) A).trans
    ((algebraTensorAlgEquiv R A).restrictScalars R)

theorem polyTensorAlgEquiv_tmul (p : MvPolynomial (Fin n) R) (a : A) :
    polyTensorAlgEquiv R A n (p ⊗ₜ a) = a • MvPolynomial.map (algebraMap R A) p := by
  simp [polyTensorAlgEquiv]

def polyTensorEquiv (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    (MvPolynomial (Fin n) R ⊗[R] A) ≃ₗ[MvPolynomial (Fin n) R] MvPolynomial (Fin n) A where
  toFun := polyTensorAlgEquiv R A n
  invFun := (polyTensorAlgEquiv R A n).symm
  map_add' := map_add _
  left_inv := (polyTensorAlgEquiv R A n).symm_apply_apply
  right_inv := (polyTensorAlgEquiv R A n).apply_symm_apply
  map_smul' q t := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p a =>
      rw [smul_tmul', smul_eq_mul, polyTensorAlgEquiv_tmul, polyTensorAlgEquiv_tmul, RingHom.id_apply,
        Algebra.smul_def q, MvPolynomial.algebraMap_def, map_mul, mul_smul_comm]
    | add s t hs ht =>
      rw [smul_add, map_add (f := _), map_add (f := _), hs, ht, smul_add]

def polyBasis {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) :
    Module.Basis ι (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) A) :=
  (Algebra.TensorProduct.basis (MvPolynomial (Fin n) R) b).map (polyTensorEquiv R A n)

theorem polyBasis_apply {ι : Type*} (b : Module.Basis ι R A) (n : ℕ) (i : ι) :
    polyBasis b n i = C (b i) := by
  simp [polyBasis, polyTensorEquiv, Algebra.TensorProduct.basis_apply, polyTensorAlgEquiv_tmul,
    smul_eq_C_mul]

end Basis

theorem normForm_eq_det {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (x : Fin n → A) :
    normForm A x = (∑ j, (X j : MvPolynomial (Fin n) R) • (Algebra.leftMulMatrix b (x j)).map C).det := by
  let bP := polyBasis b n
  let M : Fin n → Matrix ι ι R := fun j => Algebra.leftMulMatrix b (x j)
  have hM : ∀ j k, x j * b k = ∑ i, M j i k • b i := fun j k => by
    simp only [M, Algebra.leftMulMatrix_eq_repr_mul]
    exact (b.sum_repr (x j * b k)).symm
  have key : ∀ (q : MvPolynomial (Fin n) R) (a : A),
      q • (C a : MvPolynomial (Fin n) A) = MvPolynomial.map (algebraMap R A) q * C a := fun q a => by
    rw [Algebra.smul_def, MvPolynomial.algebraMap_def]
  have hmat : Algebra.leftMulMatrix bP (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) =
      ∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C := by
    refine Matrix.ext fun i k => ?_
    rw [Algebra.leftMulMatrix_eq_repr_mul, polyBasis_apply]
    have hsum : (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k) =
        ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
      calc (∑ j, X j * C (x j) : MvPolynomial (Fin n) A) * C (b k)
          = ∑ j, ∑ i', (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            set_option synthInstance.maxHeartbeats 100000 in
              rw [mul_assoc, ← C_mul, hM j k, map_sum, Finset.mul_sum]
        _ = ∑ i', ∑ j, (X j : MvPolynomial (Fin n) A) * C (M j i' k • b i') := Finset.sum_comm
        _ = ∑ i', (∑ j, (X j : MvPolynomial (Fin n) R) * C (M j i' k)) • bP i' := by
            refine Finset.sum_congr rfl fun i' _ => ?_
            set_option synthInstance.maxHeartbeats 100000 in
              rw [polyBasis_apply, key, map_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_mul, map_X, map_C, Algebra.smul_def, C_mul, mul_assoc]
    rw [hsum, bP.repr_sum_self, Matrix.sum_apply]
    simp [Matrix.map_apply]
  rw [normForm, Algebra.norm_eq_matrix_det bP, hmat]

theorem NormFormEval.proof : NormFormEval.Statement := by
  intro R A _ _ _ _ _ n x u
  classical
  let b := Module.Free.chooseBasis R A
  let M : Fin n → Matrix (Module.Free.ChooseBasisIndex R A) (Module.Free.ChooseBasisIndex R A) R :=
    fun j => Algebra.leftMulMatrix b (x j)
  rw [normForm_eq_det b, RingHom.map_det]
  have hev : (MvPolynomial.eval u).mapMatrix (∑ j, (X j : MvPolynomial (Fin n) R) • (M j).map C) =
      Algebra.leftMulMatrix b (∑ j, algebraMap R A (u j) * x j) := by
    ext i k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul, map_sum, map_mul, eval_X, eval_C, M]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [AlgHom.commutes, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.smul_apply, smul_eq_mul]
  rw [hev, ← Algebra.norm_eq_matrix_det b]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsOrd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

noncomputable section

def FiniteOrd.Statement : Prop :=
  ∀ (R B : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (b : B), Function.Injective (fun x : B => b * x) →
      ∀ 𝔫 : MaximalSpectrum B,
        Ring.ord (Localization.AtPrime 𝔫.asIdeal) (algebraMap B (Localization.AtPrime 𝔫.asIdeal) b) ≠ ⊤

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSpecFirst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

def SpecFirstNeField.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F),
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → specFirst f u ≠ 0

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open Module IsLocalRing LinearMap Submodule

noncomputable section

namespace LengthDecomp

open Classical

variable {B : Type*} [CommRing B]

theorem length_localizedModule_eq_of_isLocalizedModule (p : Ideal B) [p.IsPrime]
    {X Y : Type*} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    [Module (Localization.AtPrime p) Y] [IsScalarTower B (Localization.AtPrime p) Y]
    (g : X →ₗ[B] Y) [IsLocalizedModule p.primeCompl g] :
    length (Localization.AtPrime p) (LocalizedModule p.primeCompl X) =
      length (Localization.AtPrime p) Y :=
  ((IsLocalizedModule.iso p.primeCompl g).extendScalarsOfIsLocalization p.primeCompl
    (Localization.AtPrime p)).length_eq

theorem length_localizedModule_quotient (n m : MaximalSpectrum B) :
    length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl (B ⧸ m.asIdeal)) =
      if n = m then 1 else 0 := by
  have hn := n.isMaximal
  have hm := m.isMaximal
  split_ifs with h
  · subst h
    rw [length_localizedModule_eq_of_isLocalizedModule n.asIdeal
      (n.asIdeal.toLocalizedQuotient' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
        (Algebra.linearMap B (Localization.AtPrime n.asIdeal)))]
    have hmax : n.asIdeal.localized' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
        (Algebra.linearMap B (Localization.AtPrime n.asIdeal)) =
          maximalIdeal (Localization.AtPrime n.asIdeal) := by
      rw [Submodule.localized'_eq_span, ← Localization.AtPrime.map_eq_maximalIdeal]
      rfl
    rw [hmax]
    have : IsSimpleModule (Localization.AtPrime n.asIdeal)
        (Localization.AtPrime n.asIdeal ⧸ maximalIdeal (Localization.AtPrime n.asIdeal)) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
    exact Module.length_eq_one _ _
  · rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
    obtain ⟨s, hsm, hsn⟩ : ∃ s ∈ m.asIdeal, s ∉ n.asIdeal := by
      by_contra! hc
      exact h (MaximalSpectrum.ext (hm.eq_of_le hn.ne_top hc).symm)
    intro x
    refine ⟨s, hsn, ?_⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hsm,
      zero_mul]

variable {R : Type*} [CommRing R] [Algebra R B]
variable {N : Type*} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]

theorem step {p q : Submodule B N} (h : p ⋖ q) :
    ∃ m : MaximalSpectrum B, length R q = length R p + length R (B ⧸ m.asIdeal) ∧
      ∀ n : MaximalSpectrum B,
        length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl q) =
          length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl p) +
            if n = m then 1 else 0 := by
  let f : p →ₗ[B] q := inclusion h.le
  have key : IsSimpleModule B (q ⧸ range f) := by
    rwa [range_inclusion, ← covBy_iff_quot_is_simple h.le]
  obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
  let g : q →ₗ[B] B ⧸ m := e.toLinearMap.comp (range f).mkQ
  have hf : Function.Injective f := inclusion_injective _
  have hg : Function.Surjective g := e.surjective.comp (range f).mkQ_surjective
  have hfg : Function.Exact f g := exact_iff.mpr ((e.ker_comp _).trans (range f).ker_mkQ)
  refine ⟨⟨m, hm⟩, length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R) hf hg hfg,
    fun n => ?_⟩
  rw [← length_localizedModule_quotient n ⟨m, hm⟩]
  exact length_eq_add_of_exact
    ((IsLocalizedModule.map n.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ p)
      (LocalizedModule.mkLinearMap _ q) f).extendScalarsOfIsLocalization n.asIdeal.primeCompl
        (Localization.AtPrime n.asIdeal))
    ((IsLocalizedModule.map n.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ q)
      (LocalizedModule.mkLinearMap _ (B ⧸ m)) g).extendScalarsOfIsLocalization
        n.asIdeal.primeCompl (Localization.AtPrime n.asIdeal))
    (IsLocalizedModule.map_injective _ _ _ f hf) (IsLocalizedModule.map_surjective _ _ _ g hg)
    (LocalizedModule.map_exact _ f g hfg)

theorem length_eq_sum [Fintype (MaximalSpectrum B)] (hN : IsFiniteLength B N) :
    length R N = ∑ n : MaximalSpectrum B,
      length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl N) *
        length R (B ⧸ n.asIdeal) := by
  obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp hN
  have H : ∀ k, length R (s k) = ∑ n : MaximalSpectrum B,
      length (Localization.AtPrime n.asIdeal) (LocalizedModule n.asIdeal.primeCompl (s k)) *
        length R (B ⧸ n.asIdeal) := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [← RelSeries.head, hs_bot]
      simp [Module.length_eq_zero]
    | succ i hi =>
      obtain ⟨m, h1, h2⟩ := step (R := R) (s.step i)
      rw [h1, hi]
      simp_rw [h2, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have := H (Fin.last _)
  rw [← RelSeries.last, hs_top] at this
  rw [← ((Submodule.topEquiv (R := B) (M := N)).restrictScalars R).length_eq, this]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [length_localizedModule_eq_of_isLocalizedModule n.asIdeal
    ((LocalizedModule.mkLinearMap n.asIdeal.primeCompl N).comp
      (Submodule.topEquiv (R := B) (M := N)).toLinearMap)]

theorem finite_maximalSpectrum [IsLocalRing R] [Module.Finite R B] :
    Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := R) (S := B) (maximalIdeal R)
  have := hfin.to_subtype
  refine Finite.of_injective (β := (maximalIdeal R).primesOver B)
    (fun n => ⟨n.asIdeal, n.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R) n.asIdeal)).symm⟩⟩) ?_
  intro n n' hnn'
  exact MaximalSpectrum.ext (congrArg Subtype.val hnn')

end LengthDecomp

theorem LengthDecomp.proof : LengthDecomp.Statement := by
  intro R B _ _ _ _ _ _ b hfin
  have := LengthDecomp.finite_maximalSpectrum (R := R) (B := B)
  let _ : Fintype (MaximalSpectrum B) := Fintype.ofFinite _
  have hB : IsFiniteLength B (B ⧸ Ideal.span {b}) := by
    rw [length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin
    rw [isFiniteLength_iff_isNoetherian_isArtinian]
    exact hfin.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
  rw [LengthDecomp.length_eq_sum (R := R) hB, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  have hspan : (Ideal.span {b}).localized' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
      (Algebra.linearMap B (Localization.AtPrime n.asIdeal)) =
        Ideal.span {algebraMap B (Localization.AtPrime n.asIdeal) b} := by
    rw [Ideal.span, Submodule.localized'_span, Set.image_singleton]
    rfl
  rw [Ring.ord, LengthDecomp.length_localizedModule_eq_of_isLocalizedModule n.asIdeal
    ((Ideal.span {b}).toLocalizedQuotient' (Localization.AtPrime n.asIdeal) n.asIdeal.primeCompl
      (Algebra.linearMap B (Localization.AtPrime n.asIdeal))), hspan]

end

end GroundTheory.Heights₂.Heights.Vertical
end
