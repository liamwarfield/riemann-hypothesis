module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPointExtOfComponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitary
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

noncomputable section

namespace GlobalTheory.ColAction

theorem sympl_eq_neg_dotProduct {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, Finset.sum_neg_distrib, mul_comm]
  ring

theorem mem_symplecticGroup_of_sympl {l : Type} [Fintype l] [DecidableEq l] (M : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (M *ᵥ u) (M *ᵥ v) = sympl u v) : M ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff']
  ext a b
  have key : ∀ u v, (M *ᵥ u) ⬝ᵥ (Matrix.J l ℝ *ᵥ (M *ᵥ v)) = u ⬝ᵥ ((Mᵀ * Matrix.J l ℝ * M) *ᵥ v) := by
    intro u v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u Mᵀ, Matrix.vecMul_transpose]
  have := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_neg_dotProduct, sympl_eq_neg_dotProduct, neg_inj, key] at this
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

theorem signed_sum_eq_trace {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) :
    ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) = Matrix.trace (Jm P Q * X * Jm R S * Yᴴ) := by
  have e : Jm P Q * X * Jm R S =
      Matrix.of fun a b => ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) a * X a b * ((fun _ => (1 : ℂ)) ⊕ᵥ fun _ => -1) b := by
    ext a b
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply]
  simp [Fintype.sum_sum_type, lineSign]

theorem signed_sum_mul_transpose {P Q R S : ℕ} (X Y : Matrix (Ix P Q) (Ix R S) ℂ) (k : Mat R S)
    (hk : kᴴ * Jm R S * k = Jm R S) :
    ∑ a, ∑ b, lineSign a b * (X * kᵀ) a b * star ((Y * kᵀ) a b) = ∑ a, ∑ b, lineSign a b * X a b * star (Y a b) := by
  have hJ : (Jm R S)ᵀ = Jm R S := by
    simp [Jm, Formalism.UG.P.Jpq_eq_diagonal]
  have e : (kᵀ)ᴴ = k.map star := by ext i j; simp
  have hk' : kᵀ * Jm R S * (kᵀ)ᴴ = Jm R S := by
    have := congrArg Matrix.transpose hk
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hJ, Matrix.conjTranspose_transpose] at this
    rw [e, Matrix.mul_assoc, this]
  rw [signed_sum_eq_trace, signed_sum_eq_trace, Matrix.conjTranspose_mul]
  congr 1
  calc Jm P Q * (X * kᵀ) * Jm R S * ((kᵀ)ᴴ * Yᴴ) = Jm P Q * X * (kᵀ * Jm R S * (kᵀ)ᴴ) * Yᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hk']

theorem exists_symplectic_hom_of_unitary : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ G _ _ k hk hkJ
  let A : G → (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) := fun g =>
    { toFun := fun c w => c w * (k g w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  let T : G → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ) := fun g => φ.toLinearMap ∘ₗ A g ∘ₗ φ.symm.toLinearMap
  have hT : ∀ g c, T g (φ c) = φ (fun w => c w * (k g w)ᵀ) := fun g c => by simp [T, A]
  have hsy : ∀ g u v, sympl (T g u) (T g v) = sympl u v := by
    intro g u v
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    rw [hT, hT, hφ, hφ]
    simp only [signed_sum_mul_transpose _ _ _ (hkJ g _)]
  have hmem : ∀ g, LinearMap.toMatrix' (T g) ∈ Matrix.symplecticGroup l ℝ := fun g =>
    mem_symplecticGroup_of_sympl _ (fun u v => by simpa only [LinearMap.toMatrix'_mulVec] using hsy g u v)
  have hTmul : ∀ g h, T (g * h) = T g ∘ₗ T h := by
    intro g h
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    show T (g * h) (φ c) = T g (T h (φ c))
    rw [hT, hT, hT]
    congr 1
    ext w : 1
    simp [map_mul, Pi.mul_apply, Matrix.transpose_mul, Matrix.mul_assoc]
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    rw [hT]
    simp
  let s : G →* Matrix.symplecticGroup l ℝ :=
    { toFun := fun g => ⟨LinearMap.toMatrix' (T g), hmem g⟩
      map_one' := by
        apply Subtype.ext
        simp only [hT1, LinearMap.toMatrix'_id]
        rfl
      map_mul' := fun g h => by
        apply Subtype.ext
        simp only [hTmul, LinearMap.toMatrix'_comp]
        rfl }
  refine ⟨s, ?_, fun g c => ?_⟩
  · apply Continuous.subtype_mk
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have e : ∀ g, LinearMap.toMatrix' (T g) a b = φ (fun w => φ.symm (Pi.single b 1) w * (k g w)ᵀ) a := by
      intro g
      rw [LinearMap.toMatrix'_apply, ← hT, φ.apply_symm_apply]
    simp only [e]
    exact (continuous_apply a).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (continuous_pi fun w => continuous_const.matrix_mul ((continuous_apply w).comp hk).matrix_transpose))
  · show LinearMap.toMatrix' (T g) *ᵥ φ c = _
    rw [LinearMap.toMatrix'_mulVec, hT]

end GlobalTheory.ColAction
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitaryStatement
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_symplecticHom_of_indefiniteUnitary : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  first | exact @GlobalTheory.ColAction.exists_symplectic_hom_of_unitary | exact GlobalTheory.ColAction.exists_symplectic_hom_of_unitary | (intros; apply GlobalTheory.ColAction.exists_symplectic_hom_of_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotM
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotM
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal

namespace GlobalTheory.ExtPrime


open MvPolynomial Filter in
open scoped ENNReal in
theorem _root_.GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L]
    [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L]
    [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K))
    (hP : P.IsPrime) :
    (P.map (MvPolynomial.map (algebraMap K L) :
      MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).IsPrime ∧
    ((∃ j, X j ∉ P) →
      (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j :
        MvPolynomial (Fin N) L) ∉
      P.map (MvPolynomial.map (algebraMap K L) :
        MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
  classical
  haveI := hP
  let e := (commAlgEquiv K (Fin N) (Fin N)).toRingEquiv
  let ι : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K) :=
    MvPolynomial.map (algebraMap K (MvPolynomial (Fin N) K))
  let π : MvPolynomial (Fin N) (MvPolynomial (Fin N) K) →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K ⧸ P) :=
    (MvPolynomial.map (Ideal.Quotient.mk P)).comp e.toRingHom
  have heι : ∀ p, e (ι p) = C p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp [e, ι, commAlgEquiv_C]
    | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _)]
    | mul_X p i hp => rw [map_mul, map_mul, hp, map_X]; simp [e, commAlgEquiv_X]
  have hQ : P.map ι = RingHom.ker π := by
    ext b
    rw [RingHom.mem_ker]
    have hb : b = e.symm (e b) := (e.symm_apply_apply b).symm
    constructor
    · intro hb'
      have h1 : P.map ι ≤ RingHom.ker π := by
        rw [Ideal.map_le_iff_le_comap]
        intro p hp
        rw [Ideal.mem_comap, RingHom.mem_ker]
        show MvPolynomial.map (Ideal.Quotient.mk P) (e (ι p)) = 0
        rw [heι p, map_C, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
      exact h1 hb'
    · intro hb'
      have hmem : e b ∈ Ideal.map C P := by
        have hk : Ideal.map (C : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) P =
            RingHom.ker (MvPolynomial.map (σ := Fin N) (Ideal.Quotient.mk P)) := by
          rw [MvPolynomial.ker_map, Ideal.mk_ker]
        rw [hk, RingHom.mem_ker]
        exact hb'
      rw [hb]
      have h2 : Ideal.map e.symm (Ideal.map C P) ≤ P.map ι := by
        rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
        intro p hp
        have h4 : e.symm (C p) = ι p := by
          rw [← heι p]; exact e.symm_apply_apply _
        have h3 : e.symm (C p) ∈ P.map ι := by
          rw [h4]; exact Ideal.mem_map_of_mem ι hp
        exact h3
      exact h2 (Ideal.mem_map_of_mem _ hmem)
  have hQprime : (P.map ι).IsPrime := by rw [hQ]; exact RingHom.ker_isPrime π
  letI : Algebra (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L) :=
    (MvPolynomial.map (algebraMap (MvPolynomial (Fin N) K) L)).toAlgebra
  let Mₛ : Submonoid (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) :=
    Submonoid.map (C : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) (MvPolynomial (Fin N) K))
      (nonZeroDivisors (MvPolynomial (Fin N) K))
  haveI hloc : IsLocalization Mₛ (MvPolynomial (Fin N) L) :=
    MvPolynomial.isLocalization (nonZeroDivisors (MvPolynomial (Fin N) K)) L
  have hdisj : Disjoint (Mₛ : Set (MvPolynomial (Fin N) (MvPolynomial (Fin N) K))) ↑(P.map ι) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    rw [SetLike.mem_coe, hQ, RingHom.mem_ker] at hrQ
    have hπ : π (C r) = MvPolynomial.map (algebraMap K (MvPolynomial (Fin N) K ⧸ P)) r := by
      simp only [π, RingHom.coe_comp, Function.comp_apply]
      rw [show e.toRingHom (C r) = MvPolynomial.map C r from commAlgEquiv_C (R := K) (S₁ := Fin N) r,
        MvPolynomial.map_map]
      rfl
    rw [hπ] at hrQ
    have hinj := MvPolynomial.map_injective (σ := Fin N) _
      (algebraMap K (MvPolynomial (Fin N) K ⧸ P)).injective
    have hr0 : r = 0 := hinj (by rw [hrQ, map_zero])
    exact nonZeroDivisors.ne_zero hr hr0
  have hcomp : (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) =
      (algebraMap (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L)).comp ι := by
    refine RingHom.ext fun p => ?_
    simp only [RingHom.coe_comp, Function.comp_apply, ι, RingHom.algebraMap_toAlgebra, MvPolynomial.map_map]
    rw [← IsScalarTower.algebraMap_eq]
  have hmapeq : P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L) =
      (P.map ι).map (algebraMap (MvPolynomial (Fin N) (MvPolynomial (Fin N) K)) (MvPolynomial (Fin N) L)) := by
    rw [hcomp, Ideal.map_map]
  rw [hmapeq]
  refine ⟨IsLocalization.isPrime_of_isPrime_disjoint _ _ _ hQprime hdisj, ?_⟩
  rintro ⟨j, hj⟩ hG
  let G₀ : MvPolynomial (Fin N) (MvPolynomial (Fin N) K) := ∑ i : Fin N, C (X i) * X i
  have hG₀ : algebraMap _ (MvPolynomial (Fin N) L) G₀ =
      ∑ i : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X i)) * X i := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [G₀, RingHom.algebraMap_toAlgebra, map_sum]
  rw [← hG₀] at hG
  have hG₀Q : G₀ ∈ P.map ι := by
    have h := IsLocalization.under_map_of_isPrime_disjoint _ (MvPolynomial (Fin N) L) hQprime hdisj
    rw [← h]
    exact hG
  rw [hQ, RingHom.mem_ker] at hG₀Q
  have hπG : π G₀ = ∑ i : Fin N, X i * C (Ideal.Quotient.mk P (X i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [π, G₀, RingHom.coe_comp, Function.comp_apply, map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show e.toRingHom (C (X i)) = X i from commAlgEquiv_C_X (R := K) (S₁ := Fin N) i,
      show e.toRingHom (X i) = C (X i) from commAlgEquiv_X (R := K) (S₂ := Fin N) i, map_X, map_C]
  rw [hπG] at hG₀Q
  have hcoeff := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single j 1)) hG₀Q
  simp only [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  simp_rw [mul_comm (X _), coeff_C_mul, coeff_X, Finsupp.single_left_inj one_ne_zero] at hcoeff
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hcoeff
  exact hj (Ideal.Quotient.eq_zero_iff_mem.mp hcoeff)

end GlobalTheory.ExtPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeMapRationalFunctionsGenericLinearFormNotMStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPrime_map_rationalFunctions_generic_linearForm_not_mem : ∀ (K L : Type) [Field K] [Field L] (N : ℕ) [Algebra K L] [Algebra (MvPolynomial (Fin N) K) L] [IsScalarTower K (MvPolynomial (Fin N) K) L] [IsFractionRing (MvPolynomial (Fin N) K) L] (P : Ideal (MvPolynomial (Fin N) K)), P.IsPrime → (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)).IsPrime ∧ ((∃ j, X j ∉ P) → (∑ j : Fin N, C (algebraMap (MvPolynomial (Fin N) K) L (X j)) * X j : MvPolynomial (Fin N) L) ∉ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) := by
  first | exact @GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem | exact GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem | (intros; apply GlobalTheory.ExtPrime.isPrime_map_and_generic_form_notMem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyPsiEqMapMinpoly
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip Polynomial
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem charpoly_psi_eq_map_minpoly {p : ℕ} [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (γ : G.C)
    (hdeg : (minpoly G.F γ).natDegree = G.n) :
    (G.psi v γ).charpoly = (minpoly G.F γ).map v.embedding := by
  letI : Algebra G.F ℂ := v.embedding.toAlgebra
  have hg : ∀ a, G.psi v (algebraMap G.F G.C a) = algebraMap G.F (Matrix (Fin G.n) (Fin G.n) ℂ) a :=
    fun a => by rw [G.psi_F, Matrix.algebraMap_eq_diagonal]; rfl
  let g : G.C →ₐ[G.F] Matrix (Fin G.n) (Fin G.n) ℂ := { G.psi v with commutes' := hg }
  let L : ℂ ⊗[G.F] G.C →ₐ[ℂ] Matrix (Fin G.n) (Fin G.n) ℂ :=
    Algebra.TensorProduct.lift (Algebra.ofId ℂ _) g (fun r _ => Algebra.commute_algebraMap_left r _)
  haveI : Nonempty (Fin G.n) := ⟨⟨0, G.n_pos⟩⟩
  have hinj : Function.Injective L :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain L.toRingHom).resolve_right (not_subsingleton _)
  have hL : ∀ x : G.C, L ((1 : ℂ) ⊗ₜ x) = G.psi v x := fun x => by
    show (Algebra.TensorProduct.lift _ g _) ((1 : ℂ) ⊗ₜ x) = _
    erw [Algebra.TensorProduct.lift_tmul]
    rw [map_one, one_mul]
    rfl
  have hli : LinearIndependent G.F (fun i : Fin G.n => γ ^ (i : ℕ)) := by
    have := linearIndependent_pow (K := G.F) γ
    rw [hdeg] at this
    exact this
  have hT : LinearIndependent ℂ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) :=
    Module.Flat.linearIndependent_one_tmul hli
  have hM : LinearIndependent ℂ (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) := by
    have := hT.map' L.toLinearMap (LinearMap.ker_eq_bot.2 hinj)
    have e : (fun i : Fin G.n => (G.psi v γ) ^ (i : ℕ)) =
        L.toLinearMap ∘ (fun i : Fin G.n => (1 : ℂ) ⊗ₜ[G.F] (γ ^ (i : ℕ))) := by
      funext i
      simp only [Function.comp_apply, AlgHom.toLinearMap_apply]
      rw [hL, map_pow]
    rw [e]
    exact this
  have hint : IsIntegral ℂ (G.psi v γ) := Algebra.IsIntegral.isIntegral _
  set q := minpoly ℂ (G.psi v γ) with hq
  have hqm : q.Monic := minpoly.monic hint
  have hqdeg : G.n ≤ q.natDegree := by
    by_contra hlt
    push_neg at hlt
    have h0 : aeval (G.psi v γ) q = 0 := minpoly.aeval _ _
    rw [Polynomial.aeval_eq_sum_range' hlt, Finset.sum_range] at h0
    have h1 := Fintype.linearIndependent_iff.1 hM (fun i => q.coeff i) h0 ⟨q.natDegree, hlt⟩
    have h2 : q.coeff q.natDegree = 1 := hqm.coeff_natDegree
    rw [h2] at h1
    exact one_ne_zero h1
  have hpol : aeval (G.psi v γ) ((minpoly G.F γ).map v.embedding) = 0 := by
    have h : aeval (g γ) (minpoly G.F γ) = 0 := by rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
    change aeval (G.psi v γ) ((minpoly G.F γ).map (algebraMap G.F ℂ)) = 0
    rw [Polynomial.aeval_map_algebraMap]
    exact h
  have hFint : IsIntegral G.F γ := Algebra.IsIntegral.isIntegral _
  have hm1 : ((minpoly G.F γ).map v.embedding).Monic := (minpoly.monic hFint).map _
  have hn1 : ((minpoly G.F γ).map v.embedding).natDegree = G.n := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have e1 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm hm1 (minpoly.dvd _ _ hpol)
    (by rw [hn1]; exact hqdeg)
  have e2 := Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqm (Matrix.charpoly_monic _)
    (Matrix.minpoly_dvd_charpoly _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]; exact hqdeg)
  rw [e2, e1]

theorem charpoly_psi_separable : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F) (g : G.C),
    (minpoly G.F g).natDegree = G.n → (minpoly G.F g).Separable → (G.psi v g).charpoly.Separable := by
  intro p _ G v g hdeg hsep
  rw [charpoly_psi_eq_map_minpoly G v g hdeg]
  exact hsep.map

end GlobalTheory.LKMid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLine
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

theorem fixL_pos_unique_of_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 →
    ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β,
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n →
    (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable →
    ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re →
    FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z := by
  intro p _ G v hsig β hsh hR y₀ hdeg hsep z z' hz hz' hf hf'
  obtain ⟨_, _, Z, hZ⟩ := GlobalTheory.LKCx.herm_laws p G v β hsh hR
  set g0 : Matrix (Fin G.n) (Fin G.n) ℂ := (toV G v β y₀ : Matrix (Fin G.n) (Fin G.n) ℂ) with hg0
  set Zm : Matrix (Fin G.n) (Fin G.n) ℂ := (Z : Matrix (Fin G.n) (Fin G.n) ℂ) with hZm
  set Zi : Matrix (Fin G.n) (Fin G.n) ℂ := ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) with hZi
  have hZiZ : Zi * Zm = 1 := by rw [hZi, hZm, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hZZi : Zm * Zi = 1 := by rw [hZi, hZm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  set s : ℝ := ((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs
  have hspos : 0 < s := by rw [hs]; exact_mod_cast y₀.2.2
  have hsim0 := GlobalTheory.LKCx.grp_similitude_herm p G v β y₀
  set g : Matrix (Fin G.n) (Fin G.n) ℂ := Zm * g0 * Zi with hg
  have hsim : gᴴ * G.gram v * g = (s : ℂ) • G.gram v := by
    have e1 : gᴴ * G.gram v * g = Ziᴴ * (g0ᴴ * (Zmᴴ * G.gram v * Zm) * g0) * Zi := by
      rw [hg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [e1, ← hZ, hsim0]
    have e2 : Ziᴴ * ((((((y₀ : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℂ)) • herm G v β) * Zi =
        (s : ℂ) • ((Zm * Zi)ᴴ * G.gram v * (Zm * Zi)) := by
      rw [hZ, Matrix.mul_smul, Matrix.smul_mul, Matrix.conjTranspose_mul]
      congr 1
      simp only [Matrix.mul_assoc]
    rw [e2, hZZi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hcp : g.charpoly.Separable := by
    have e : g = (Z : Matrix (Fin G.n) (Fin G.n) ℂ) * g0 * ((Z⁻¹ : GL (Fin G.n) ℂ) : Matrix (Fin G.n) (Fin G.n) ℂ) := rfl
    rw [e, Matrix.coe_units_inv, Matrix.charpoly_units_conj]
    exact GlobalTheory.LKMid.charpoly_psi_separable p G v _ hdeg hsep
  have hpos : ∀ w : Fin G.n → ℂ, star (Zm *ᵥ w) ⬝ᵥ G.gram v *ᵥ (Zm *ᵥ w) = star w ⬝ᵥ (herm G v β *ᵥ w) := by
    intro w; rw [hZ, GlobalTheory.form_conjTranspose_mul_mul]
  have heig : ∀ w : Fin G.n → ℂ, FixL G v β y₀ w → ∃ μ : ℂ, g *ᵥ (Zm *ᵥ w) = μ • (Zm *ᵥ w) := by
    rintro w ⟨μ, hμ⟩
    refine ⟨μ, ?_⟩
    rw [hg, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hZiZ, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hμ, Matrix.mulVec_smul]
  obtain ⟨c, hc⟩ := GlobalTheory.eigvec_pos_unique_of_similitude (G.gram v) (G.gram_herm v) (G.gram_det v) hsig g s hspos
    hsim hcp (Zm *ᵥ z) (Zm *ᵥ z') (by rw [hpos]; exact hz) (by rw [hpos]; exact hz') (heig z hf) (heig z' hf')
  refine ⟨c, ?_⟩
  have := congrArg (Zi *ᵥ ·) hc
  simp only [Matrix.mulVec_mulVec, hZiZ, Matrix.one_mulVec, Matrix.mulVec_smul] at this
  exact this

end GlobalTheory.LKCx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableFormGroupElementFixesUniquePositiveLineStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_formGroup_element_fixes_unique_positive_line : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (v : InfinitePlace G.F), sigPosH (G.gram_herm v) = 1 → ∀ (β : G.Cˣ), sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ y₀ : grp G β, (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n → (minpoly G.F (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable → ∀ z z' : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re → 0 < (star z' ⬝ᵥ (herm G v β *ᵥ z')).re → FixL G v β y₀ z → FixL G v β y₀ z' → ∃ c : ℂ, z' = c • z := by
  first | (exact @GlobalTheory.LKCx.fixL_pos_unique_of_sep) | (exact GlobalTheory.LKCx.fixL_pos_unique_of_sep) | (intros; apply GlobalTheory.LKCx.fixL_pos_unique_of_sep  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieOfIndefiniteUnitaryLieRightAc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieOfIndefiniteUnitaryLieRightAc
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

namespace GlobalTheory.RealLift.SpLie

open Matrix

def sgnD {p q : ℕ} : Ix p q → ℂ
  | .inl _ => 1
  | .inr _ => -1

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal sgnD := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, sgnD, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem lineSign_eq_mul {p q r s : ℕ} (a : Ix p q) (b : Ix r s) : lineSign a b = sgnD a * sgnD b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign, sgnD]

theorem upq_entry {r s : ℕ} {Y : Mat r s} (hY : Y ∈ upq r s) (b k : Ix r s) :
    star (Y k b) * sgnD k + sgnD b * Y b k = 0 := by
  have h : (Yᴴ * Jm r s + Jm r s * Y) b k = 0 := by
    rw [show Yᴴ * Jm r s + Jm r s * Y = 0 from hY]; rfl
  rw [Jm_eq_diagonal] at h
  simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h

theorem sympl_eq_dot {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, ite_mul, Finset.sum_ite_eq]
  simp only [mul_comm (v _)]
  ring

theorem sum_zero {P Q R S : ℕ} (c c' : Matrix (Ix P Q) (Ix R S) ℂ) (Y : Mat R S) (hY : Y ∈ upq R S) :
    (∑ a, ∑ b, lineSign a b * (c * Yᵀ) a b * star (c' a b)) +
      ∑ a, ∑ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) = 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  have e1 : ∀ b, lineSign a b * (c * Yᵀ) a b * star (c' a b) =
      ∑ k, sgnD a * c a k * star (c' a b) * (sgnD b * Y b k) := by
    intro b
    rw [lineSign_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply]; ring
  have e2 : ∀ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) =
      ∑ k, sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k)) := by
    intro b
    rw [lineSign_eq_mul, Matrix.mul_apply, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply, star_mul']; ring
  simp only [e1, e2]
  rw [Finset.sum_comm (f := fun b k => sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k))),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  linear_combination (sgnD a * c a k * star (c' a b)) * upq_entry hY b k

theorem mem_sp_of_sympl {l : Type} [Fintype l] [DecidableEq l] (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (Z *ᵥ u) v + sympl u (Z *ᵥ v) = 0) : Z ∈ LieAlgebra.Symplectic.sp l ℝ := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  show Zᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -Z
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_dot, sympl_eq_dot] at h1
  simp [mulVec, dotProduct, Pi.single_apply, Matrix.mul_apply] at h1 ⊢
  linarith

theorem exists_sp_rightAct : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ Y hY
  let G : (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) :=
    { toFun := fun c w => c w * (Y w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  set Z := LinearMap.toMatrix' (φ.toLinearMap ∘ₗ G ∘ₗ φ.symm.toLinearMap) with hZdef
  have hZ : ∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ := by
    intro c; rw [hZdef, LinearMap.toMatrix'_mulVec]; simp [G]
  refine ⟨Z, ?_, hZ, ?_⟩
  · refine mem_sp_of_sympl Z fun u v => ?_
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    have hs : (∑ w, ∑ a, ∑ b, lineSign a b * (c w * (Y w)ᵀ) a b * star (c' w a b)) +
        (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star ((c' w * (Y w)ᵀ) a b)) = 0 := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun w _ => sum_zero _ _ _ (hY w)
    rw [hZ, hZ, hφ, hφ, ← mul_add, ← Complex.add_im]
    simp only [hs, Complex.zero_im, mul_zero]
  · intro t c
    have hpow : ∀ (n : ℕ) (c : ι → Matrix (Ix P Q) (Ix R S) ℂ),
        (t • Z) ^ n *ᵥ φ c = φ fun w => c w * ((t • Y w) ^ n)ᵀ := by
      intro n
      induction n with
      | zero => intro c; simp
      | succ n ih =>
        intro c
        rw [pow_succ, ← mulVec_mulVec, Matrix.smul_mulVec, hZ, ← φ.map_smul]
        have : (t • fun w => c w * (Y w)ᵀ) = fun w => c w * (t • Y w)ᵀ := by
          funext w; simp [Matrix.transpose_smul, Matrix.mul_smul]
        rw [this, ih]
        congr 1; funext w
        rw [pow_succ, Matrix.transpose_mul, Matrix.mul_assoc]
    letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
    letI : NormedRing (Mat R S) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℝ (Mat R S) := Matrix.linftyOpNormedAlgebra
    have h1 : HasSum (fun n : ℕ => (((n.factorial : ℝ)⁻¹) • (t • Z) ^ n) *ᵥ φ c)
        (NormedSpace.exp (t • Z) *ᵥ φ c) :=
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Z)).map
        (Matrix.mulVec.addMonoidHomLeft (φ c)) (Continuous.matrix_mulVec continuous_id continuous_const)
    have hw : ∀ w, HasSum (fun n : ℕ => c w * (((n.factorial : ℝ)⁻¹ • (t • Y w) ^ n))ᵀ)
        (c w * (NormedSpace.exp (t • Y w))ᵀ) := by
      intro w
      have := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • Y w)).matrix_transpose
      exact this.map (AddMonoidHom.mk' (fun M => c w * M) fun _ _ => Matrix.mul_add _ _ _)
        (continuous_const.matrix_mul continuous_id)
    have h2 := (Pi.hasSum.2 hw).map φ (LinearMap.continuous_of_finiteDimensional φ.toLinearMap)
    refine h1.unique ?_
    convert h2 using 1
    funext n
    rw [Matrix.smul_mulVec, hpow, ← φ.map_smul]
    congr 1; funext w
    simp [Matrix.transpose_smul, Matrix.mul_smul]

end GlobalTheory.RealLift.SpLie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieOfIndefiniteUnitaryLieRightAcStatement
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLie_of_indefiniteUnitaryLie_rightAction : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ Y : ι → Mat R S, (∀ w, Y w ∈ upq R S) →
    ∃ Z ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ c, Z *ᵥ φ c = φ fun w => c w * (Y w)ᵀ) ∧
      ∀ (t : ℝ) c, NormedSpace.exp (t • Z) *ᵥ φ c = φ fun w => c w * (NormedSpace.exp (t • Y w))ᵀ := by
  first | exact @GlobalTheory.RealLift.SpLie.exists_sp_rightAct | exact GlobalTheory.RealLift.SpLie.exists_sp_rightAct | (intros; apply GlobalTheory.RealLift.SpLie.exists_sp_rightAct <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DRepAddAndBracket
noncomputable section

open GlobalTheory.SmoothForms NormedSpace
open scoped ContDiff Topology InnerProductSpace

namespace GlobalTheory.DerivedAction

variable {𝔸 H : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

def dOp (π : 𝔸 → (H →L[ℂ] H)) (X : 𝔸) (v : H) : H := deriv (fun t : ℝ => π (exp (t • X)) v) 0

theorem abstract (σ : 𝔸 →ₗ[ℝ] 𝔸) (anti : ∀ a b, σ (a * b) = σ b * σ a) (one : σ 1 = 1) (invol : ∀ a, σ (σ a) = a)
    (π : 𝔸 → (H →L[ℂ] H)) (π1 : π 1 = 1) (πm : ∀ a b, σ a * a = 1 → σ b * b = 1 → π (a * b) = π a * π b) (v : H)
    (hv : ∀ (k : ℕ) (Xs : Fin k → 𝔸), (∀ i, σ (Xs i) = -Xs i) →
      ContDiff ℝ ∞ fun t : Fin k → ℝ => π ((List.ofFn fun i => exp (t i • Xs i)).prod) v)
    (X : 𝔸) (hX : σ X = -X) (Y : 𝔸) (hY : σ Y = -Y) :
    dOp π (X + Y) v = dOp π X v + dOp π Y v ∧
      dOp π (X * Y - Y * X) v = dOp π X (dOp π Y v) - dOp π Y (dOp π X v) := by
  classical
  let L : Submodule ℝ 𝔸 := LinearMap.ker (σ + LinearMap.id)
  have hL : ∀ Z, Z ∈ L ↔ σ Z = -Z := fun Z => by
    simp only [L, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  have hunit : ∀ a, σ a * a = 1 → IsUnit (π a) := fun a ha => by
    have hr : a * σ a = 1 := by
      have : IsArtinianRing 𝔸 := IsArtinianRing.of_finite ℝ 𝔸
      exact mul_eq_one_comm.1 ha
    have hs : σ (σ a) * σ a = 1 := by rw [invol, hr]
    exact ⟨⟨π a, π (σ a), by rw [← πm _ _ ha hs, hr, π1], by rw [← πm _ _ hs ha, ha, π1]⟩, rfl⟩
  have hmul : ∀ a b, σ a * a = 1 → σ b * b = 1 → σ (a * b) * (a * b) = 1 := fun a b ha hb => by
    rw [anti, mul_assoc, ← mul_assoc (σ a), ha, one_mul, hb]
  let s : 𝔸 → (H →L[ℂ] H)ˣ := fun a => if h : IsUnit (π a) then h.unit else 1
  have hs : ∀ a, σ a * a = 1 → (s a : H →L[ℂ] H) = π a := fun a ha => by
    simp only [s, dif_pos (hunit a ha), IsUnit.unit_spec]
  have hD : IsLieData σ L.subtype s :=
    ⟨anti, one, invol, L.injective_subtype,
      fun Z => ⟨fun h => ⟨⟨Z, (hL Z).2 h⟩, rfl⟩, by rintro ⟨Z, rfl⟩; exact (hL _).1 Z.2⟩,
      fun a b ha hb => Units.ext (by rw [Units.val_mul, hs _ ha, hs _ hb, hs _ (hmul a b ha hb), πm _ _ ha hb])⟩
  have hl := hasLog_of_isLieData _ _ _ _ _ _ hD
  have hu : ∀ Z : L, σ (exp Z.1) * exp Z.1 = 1 := fun Z => SecondKind.exp_unitary hD Z
  have he : ∀ Z : L, ((expMap L.subtype s Z : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = π (exp Z.1) := fun Z => hs _ (hu Z)
  have hprod : ∀ l : List L, σ (l.map fun Z => exp Z.1).prod * (l.map fun Z => exp Z.1).prod = 1 ∧
      (((l.map (expMap L.subtype s)).prod : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) = π (l.map fun Z => exp Z.1).prod := fun l => by
    induction l with
    | nil => simp [one, π1]
    | cons Z l ih =>
      simp only [List.map_cons, List.prod_cons, Units.val_mul]
      exact ⟨hmul _ _ (hu Z) ih.1, by rw [he, ih.2, πm _ _ (hu Z) ih.1]⟩

  have d1 : ∀ Z : L, DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) v) 0 := fun Z => by
    have h := (hv 1 (fun _ => Z.1) fun _ => (hL _).1 Z.2).comp
      (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun (t : ℝ) (_ : Fin 1) => t)
    have := (h.differentiable (by simp)).differentiableAt (x := 0)
    simpa [Function.comp_def] using this
  have hlin : ∀ (A : H →L[ℂ] H) (Z : L) (u : H), DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) u) 0 →
      HasDerivAt (fun t : ℝ => A (π (exp (t • Z.1)) u)) (A (dOp π Z.1 u)) 0 := fun A Z u h =>
    (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h.hasDerivAt
  have d2 : ∀ Z Z' : L, DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) (dOp π Z'.1 v)) 0 := fun Z Z' => by
    have h := (hv 2 ![Z.1, Z'.1] (by
      intro i; fin_cases i
      · exact (hL _).1 Z.2
      · exact (hL _).1 Z'.2)).comp
      (contDiff_pi.2 (by
        intro i; fin_cases i
        · exact contDiff_fst
        · exact contDiff_snd) : ContDiff ℝ ∞ fun (p : ℝ × ℝ) => ![p.1, p.2])
    have h' : ContDiff ℝ ∞ (Function.uncurry fun (t r : ℝ) => π (exp (t • Z.1)) (π (exp (r • Z'.1)) v)) := by
      convert h using 1
      funext p
      have := πm _ _ (hu (p.1 • Z)) (hu (p.2 • Z'))
      simp only [Submodule.coe_smul] at this
      simp [Function.uncurry, this]
    have h3 : ContDiff ℝ ∞ fun t : ℝ =>
        fderiv ℝ (fun r : ℝ => π (exp (t • Z.1)) (π (exp (r • Z'.1)) v)) 0 (1 : ℝ) :=
      (ContDiff.fderiv (m := ∞) h' contDiff_const (by simp)).clm_apply contDiff_const
    have h4 := (h3.differentiable (by simp)).differentiableAt (x := 0)
    exact h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => (hlin _ Z' v (d1 Z')).deriv.symm)

  let φ : H → H → (H →L[ℂ] H)ˣ → ℂ := fun w u g => ⟪w, (g : H →L[ℂ] H) u⟫_ℂ
  have hder : ∀ (w : H) (Z : L) (u : H), DifferentiableAt ℝ (fun t : ℝ => π (exp (t • Z.1)) u) 0 →
      Der (expMap L.subtype s) Z (φ w u) = φ w (dOp π Z.1 u) := fun w Z u h => by
    funext g
    have h1 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hlin g Z u h)
    refine Eq.trans ?_ h1.deriv
    simp only [Der, φ, Units.val_mul, he]
    rfl
  have hsm : ∀ w, Sm (expMap L.subtype s) (φ w v) := fun w => by
    refine (SecondKind.main _ _ _ _ _ _ hD hl Set.univ Submodule.span_univ _).2 fun k Z _ g => ?_
    have h1 := (((innerSL ℂ w).comp (g : H →L[ℂ] H)).restrictScalars ℝ).contDiff.comp
      (hv k (fun i => (Z i).1) fun i => (hL _).1 (Z i).2)
    convert h1 using 1
    funext t
    have h2 := (hprod (List.ofFn fun i => t i • Z i)).2
    rw [List.map_ofFn, List.map_ofFn] at h2
    simp only [φ, Units.val_mul]
    exact congrArg (fun A : H →L[ℂ] H => ⟪w, (g : H →L[ℂ] H) (A v)⟫_ℂ) h2
  let X' : L := ⟨X, (hL _).2 hX⟩
  let Y' : L := ⟨Y, (hL _).2 hY⟩
  let Z' : L := ⟨X * Y - Y * X, (hL _).2 (by rw [map_sub, anti, anti, hX, hY]; noncomm_ring)⟩
  refine ⟨ext_inner_left ℂ fun w => ?_, ext_inner_left ℂ fun w => ?_⟩
  · have h := (der_smooth_and_linear _ _ _ _ _ _ hD hl _ (hsm w)).2.1 X' Y'
    rw [hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d1 _)] at h
    rw [inner_add_right]
    exact congrFun h 1
  · have h := Bracket.der_bracket _ _ _ _ _ _ hD hl _ (hsm w) X' Y' Z' rfl
    rw [hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d1 _), hder w _ _ (d2 _ _), hder w _ _ (d2 _ _)] at h
    rw [inner_sub_right]
    exact (congrFun h 1).symm

open Matrix Formalism.MainNotions.S Formalism.L2.Theta


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem dRep_add_and_bracket : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (J : Matrix (Fin n) (Fin n) ℂ) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Jᴴ = J → IsUnit J.det → IsURepOn (Formalism.QuantumDeterminants.UH J) π → ∀ v, SmoothVec {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0} π v → ∀ X ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, ∀ Y ∈ {X : Matrix (Fin n) (Fin n) ℂ | Xᴴ * J + J * X = 0}, dRep π (X + Y) v = dRep π X v + dRep π Y v ∧ dRep π (X * Y - Y * X) v = dRep π X (dRep π Y v) - dRep π Y (dRep π X v) := by
  intro n H _ _ J π hJ hd hπ v hv X hX Y hY
  let σ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun X => J⁻¹ * Xᴴ * J
      map_add' := fun X Y => by rw [conjTranspose_add, mul_add, add_mul]
      map_smul' := fun c X => by
        rw [conjTranspose_smul, star_trivial, mul_smul_comm, smul_mul_assoc]; rfl }
  have hσ : ∀ Z, σ Z = J⁻¹ * Zᴴ * J := fun _ => rfl
  have hskew : ∀ Z, σ Z = -Z ↔ Zᴴ * J + J * Z = 0 := fun Z => by
    rw [hσ]
    constructor
    · intro h1
      rw [← mul_nonsing_inv_cancel_left _ (Zᴴ * J) hd, ← mul_assoc J⁻¹, h1, mul_neg, neg_add_cancel]
    · intro h1
      rw [mul_assoc, eq_neg_of_add_eq_zero_left h1, mul_neg, nonsing_inv_mul_cancel_left _ _ hd]
  have hun : ∀ u, σ u * u = 1 → u ∈ Formalism.QuantumDeterminants.UH J := fun u h1 => by
    change uᴴ * J * u = J
    have := congrArg (J * ·) h1
    simpa only [hσ, ← mul_assoc, mul_nonsing_inv _ hd, one_mul, mul_one] using this
  refine abstract σ (fun a b => ?_) ?_ (fun a => ?_) π hπ.1.1 (fun a b ha hb => hπ.1.2 _ (hun a ha) _ (hun b hb)) v
    (fun k Xs h => hv k Xs fun i => (hskew _).1 (h i)) X ((hskew _).2 hX) Y ((hskew _).2 hY)
  · simp only [hσ, conjTranspose_mul, mul_assoc]
    rw [mul_nonsing_inv_cancel_left _ _ hd]
  · rw [hσ, conjTranspose_one, mul_one, nonsing_inv_mul _ hd]
  · rw [hσ, hσ, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hJ]
    simp only [mul_assoc]
    rw [nonsing_inv_mul_cancel_left _ _ hd, nonsing_inv_mul _ hd, mul_one]

end GlobalTheory.DerivedAction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringOfPthPowerTwistedMonomialMem
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringOfPthPowerTwistedMonomialMem
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem LogDR.round_coeff_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  intro K _ p A n x I J t r g hp hA hr h
  have hP0 : (∏ j ∈ I \ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hQ0 : (∏ j ∈ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hcast : ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) = (t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j) := by
    push_cast; rfl
  rw [hcast] at h
  have hpow : ∀ j ∈ J, (x j : K) ^ p = (x j : K) ^ (r j) * (x j : K) * (x j : K) ^ (p - 1 - r j) := by
    intro j _
    rw [← pow_succ, ← pow_add]
    congr 1
    have := hr j
    omega
  have hprod : (∏ j ∈ J, (x j : K)) ^ p = (∏ j ∈ J, (x j : K) ^ (r j)) * (∏ j ∈ J, (x j : K)) *
      ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hpow
  have hS : ∏ j ∈ J ∪ I \ J, (x j : K) = (∏ j ∈ J, (x j : K)) * ∏ j ∈ I \ J, (x j : K) :=
    Finset.prod_union Finset.disjoint_sdiff
  have hB : ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) ∈ A :=
    Subring.prod_mem _ (fun j _ => Subring.pow_mem _ (hA.mem j) _)
  have key : (g * t * ∏ j ∈ J, (x j : K)) ^ p / ∏ j ∈ J ∪ I \ J, (x j : K) =
      (g ^ p * ((t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j)) / ∏ j ∈ I \ J, (x j : K)) *
        ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [hS, mul_pow, mul_pow, hprod]
    field_simp
  have h2 := hA.root (J ∪ I \ J) _ p hp (key ▸ A.mul_mem h hB)
  have e : (g * t * ∏ j ∈ J, (x j : K)) / ∏ j ∈ J ∪ I \ J, (x j : K) = g * t / ∏ j ∈ I \ J, (x j : K) := by
    rw [hS]
    field_simp
  rwa [e] at h2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringOfPthPowerTwistedMonomialMemStatement
open GlobalTheory GlobalTheory.LogDR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_subring_of_pthPower_twisted_monomial_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  first | exact @GlobalTheory.LogDR.round_coeff_mem | exact GlobalTheory.LogDR.round_coeff_mem | (intros; apply GlobalTheory.LogDR.round_coeff_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarDecompositionIndefiniteUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarDecompositionIndefiniteUnitary
open scoped Matrix
open Formalism.BasicNotions.TH

namespace GlobalTheory.UnitaryPolar

open Matrix
open scoped MatrixOrder ComplexOrder

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem root {S A : Matrix ι ι ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hA : A.PosSemidef)
    (h : A * S * A = S) : ∃ R : Matrix ι ι ℂ, R.PosSemidef ∧ R * R = A ∧ R * S * R = S := by
  obtain ⟨R, hR, hRR, hu⟩ : ∃ R : Matrix ι ι ℂ, R.PosSemidef ∧ R * R = A ∧
      ∀ T : Matrix ι ι ℂ, T.PosSemidef → T * T = A → R = T :=
    ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef, CFC.sqrt_mul_sqrt_self A hA.nonneg,
      fun T hT e => CFC.sqrt_unique e hT.nonneg⟩
  have a1 : R * (R * (S * A * S)) = 1 := by
    rw [← Matrix.mul_assoc, hRR, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, h1]
  have a2 : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R (Matrix.isUnit_det_of_right_inverse a1)
  have a3 : R⁻¹ * R⁻¹ = S * A * S := by
    calc R⁻¹ * R⁻¹ = R⁻¹ * R⁻¹ * (R * (R * (S * A * S))) := by rw [a1, Matrix.mul_one]
      _ = R⁻¹ * (R⁻¹ * R) * R * (S * A * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [a2, Matrix.mul_one, a2, Matrix.one_mul]
  have a4 : R = S * R⁻¹ * S := by
    refine hu _ ?_ ?_
    · have := hR.inv.conjTranspose_mul_mul_same S
      rwa [h2] at this
    · calc S * R⁻¹ * S * (S * R⁻¹ * S) = S * (R⁻¹ * (S * S) * R⁻¹) * S := by simp only [Matrix.mul_assoc]
        _ = (S * S) * A * (S * S) := by rw [h1, Matrix.mul_one, a3, ← h1]; simp only [Matrix.mul_assoc]
        _ = A := by rw [h1, Matrix.mul_one, Matrix.one_mul]
  refine ⟨R, hR, hRR, ?_⟩
  calc R * S * R = S * R⁻¹ * S * S * R := by rw [← a4]
    _ = S * (R⁻¹ * (S * S) * R) := by simp only [Matrix.mul_assoc]
    _ = S := by rw [h1, Matrix.mul_one, a2, Matrix.mul_one]

theorem polar_inv {S U : Matrix ι ι ℂ} (h1 : S * S = 1) (h2 : Sᴴ = S) (hU : Uᴴ * S * U = S) :
    ∃ K Q : Matrix ι ι ℂ, Kᴴ * S * K = S ∧ S * K = K * S ∧ Qᴴ * S * Q = S ∧ S * Q * S * Q = 1 ∧
      U = K * Q * Q := by
  have hS : ∀ X : Matrix ι ι ℂ, S * (S * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have b1 : (S * Uᴴ * S) * U = 1 := by
    rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hU, h1]
  have b2 : U * S * Uᴴ = S := by
    have := congrArg (· * S) (mul_eq_one_comm.1 b1)
    simpa only [Matrix.mul_assoc, h1, Matrix.mul_one, Matrix.one_mul] using this
  obtain ⟨P, hP, hPP, hPS⟩ := root h1 h2 (Matrix.posSemidef_conjTranspose_mul_self U) (by
    calc Uᴴ * U * S * (Uᴴ * U) = Uᴴ * (U * S * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = S := by rw [b2, hU])
  obtain ⟨Q, hQ, hQQ, hQS⟩ := root h1 h2 hP hPS
  have hP' : ∀ X : Matrix ι ι ℂ, P * (S * (P * X)) = S * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPS]
  have c0 : (U * (S * P * S))ᴴ = S * P * S * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, h2, hP.isHermitian.eq, Matrix.mul_assoc]
  have c1 : (U * (S * P * S))ᴴ * S * (U * (S * P * S)) = S := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * S * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU]; simp only [Matrix.mul_assoc, hS, hP']
  have c2 : (U * (S * P * S))ᴴ * (U * (S * P * S)) = 1 := by
    rw [c0]
    calc _ = S * P * S * (Uᴴ * U) * (S * P * S) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [← hPP]; simp only [Matrix.mul_assoc, hS, hP', h1]
  refine ⟨U * (S * P * S), Q, c1, ?_, by rw [hQ.isHermitian.eq, hQS], ?_, ?_⟩
  · generalize U * (S * P * S) = K at c1 c2
    calc S * K = (K * Kᴴ) * S * K := by rw [mul_eq_one_comm.1 c2, Matrix.one_mul]
      _ = K * (Kᴴ * S * K) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [c1]
  · rw [Matrix.mul_assoc S, Matrix.mul_assoc S, hQS, h1]
  · rw [Matrix.mul_assoc _ Q, hQQ, Matrix.mul_assoc, Matrix.mul_assoc S, Matrix.mul_assoc S, hPS, h1, Matrix.mul_one]

theorem jm_mul_self (R S : ℕ) : Jm R S * Jm R S = 1 := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]

theorem jm_conjTranspose (R S : ℕ) : (Jm R S)ᴴ = Jm R S := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem polar (R S : ℕ) (u : Mat R S) (hu : uᴴ * Jm R S * u = Jm R S) :
    ∃ k q : Mat R S, kᴴ * Jm R S * k = Jm R S ∧
      Jm R S * k = k * Jm R S ∧ qᴴ * Jm R S * q = Jm R S ∧ Jm R S * q * Jm R S * q = 1 ∧ u = k * q * q :=
  polar_inv (jm_mul_self R S) (jm_conjTranspose R S) hu

end GlobalTheory.UnitaryPolar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarDecompositionIndefiniteUnitaryStatement
open scoped Matrix
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polar_decomposition_indefiniteUnitary : ∀ (R S : ℕ) (u : Mat R S), uᴴ * Jm R S * u = Jm R S → ∃ k q : Mat R S, kᴴ * Jm R S * k = Jm R S ∧
    Jm R S * k = k * Jm R S ∧ qᴴ * Jm R S * q = Jm R S ∧ Jm R S * q * Jm R S * q = 1 ∧ u = k * q * q := by
  first | exact @GlobalTheory.UnitaryPolar.polar | exact GlobalTheory.UnitaryPolar.polar | (intros; apply GlobalTheory.UnitaryPolar.polar <;> assumption)
end
end
