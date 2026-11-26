module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal
noncomputable section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

abbrev genPt {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) : Z := π (genericPoint Y)

abbrev fieldK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z)
    (hK : IsField (Z.presheaf.stalk (genPt π))) : Field (Z.presheaf.stalk (genPt π)) :=
  hK.toField

abbrev algKL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) :
    Algebra (Z.presheaf.stalk (genPt π)) Y.functionField :=
  (π.stalkMap (genericPoint Y)).hom.toAlgebra

abbrev algAK {Y Z : Scheme.{0}} [IrreducibleSpace Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Z, U) (Z.presheaf.stalk (genPt π)) :=
  (Z.presheaf.germ U (genPt π) h).hom.toAlgebra

abbrev algBL {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) (U : Z.Opens) (h : genPt π ∈ U) :
    Algebra Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
  (Y.presheaf.germ (π ⁻¹ᵁ U) (genericPoint Y) h).hom.toAlgebra


open scoped Classical in
def famIdeal {Y Z : Scheme.{0}} [IsIntegral Y] (π : Y ⟶ Z) [IsAffineHom π]
    (hK : IsField (Z.presheaf.stalk (genPt π)))
    (hfd : letI := fieldK π hK; letI := algKL π
      FiniteDimensional (Z.presheaf.stalk (genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) : Ideal Γ(Z, U) := by
  classical
  exact if h : genPt π ∈ U.1 then
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    GlobalTheory.NormSheaf.normIdeal Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField Γ(Y, π ⁻¹ᵁ U.1)
      (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
  else ⊤

end GlobalTheory.NormSheafDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsIsFractionRingStalkImageOfGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsIsFractionRingStalkImageOfGenericPoint
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem sections_isDomain_isFractionRing_stalk : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  intro Y Z π _ _ U hU hUr h
  set ζ := genPt π with hζ
  have hcl : (U : Set Z) ⊆ closure {ζ} := by
    rintro _ hx
    obtain ⟨y, rfl⟩ := hUr hx
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes y).map π.continuous)
  have hirr : IsIrreducible (U : Set Z) :=
    ⟨⟨ζ, h⟩, (isIrreducible_singleton.closure).isPreirreducible.open_subset U.isOpen hcl⟩
  obtain ⟨hD, -⟩ := GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible hirr
  refine ⟨hD, ?_⟩
  letI := algAK π U h
  have hl := hU.isLocalization_stalk ⟨ζ, h⟩
  have hbot : (hU.primeIdealOf ⟨ζ, h⟩).asIdeal = ⊥ := by
    let q : PrimeSpectrum Γ(Z, U) := ⟨⊥, Ideal.isPrime_bot⟩
    have hq : hU.fromSpec q ∈ U := hU.range_fromSpec.le ⟨_, rfl⟩
    have hs : hU.fromSpec (hU.primeIdealOf ⟨ζ, h⟩) ⤳ hU.fromSpec q := by
      rw [hU.fromSpec_primeIdealOf]
      exact specializes_iff_mem_closure.mpr (hcl hq)
    have hs' := hU.fromSpec.isOpenEmbedding.toIsInducing.specializes_iff.mp hs
    exact le_bot_iff.mp ((PrimeSpectrum.le_iff_specializes _ q).mpr hs')
  have hc : (hU.primeIdealOf ⟨ζ, h⟩).asIdeal.primeCompl = nonZeroDivisors Γ(Z, U) := by
    ext x; simp [hbot, Ideal.primeCompl, mem_nonZeroDivisors_iff_ne_zero]
  unfold IsLocalization.AtPrime at hl
  rw [hc] at hl
  exact hl

end GlobalTheory.NormSheafDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsIsFractionRingStalkImageOfGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z] (U : Z.Opens), IsAffineOpen U →
    (U : Set Z) ⊆ Set.range π → ∀ h : GlobalTheory.NormSheafDescent.genPt π ∈ U,
    IsDomain Γ(Z, U) ∧ (letI := GlobalTheory.NormSheafDescent.algAK π U h
      IsFractionRing Γ(Z, U) (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))) := by
  first | exact @GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | exact GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk | (intros; apply GlobalTheory.NormSheafDescent.sections_isDomain_isFractionRing_stalk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoeffIdealFamilyMapBasicOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffNormFormOfFamilyMemRangeIntegrallyClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffNormFormOfFamilyMemRangeIntegrallyClosed
open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace GlobalTheory.NormSheaf.IntegralCoeff

open MvPolynomial
open scoped TensorProduct

theorem leftMulMatrix_sum_tmul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (x : Fin m → L) :
    Algebra.leftMulMatrix (Algebra.TensorProduct.basis (MvPolynomial (Fin m) K) (Module.finBasis K L))
      (∑ i, (X i : MvPolynomial (Fin m) K) ⊗ₜ[K] x i) =
    ∑ i, (X i : MvPolynomial (Fin m) K) •
      (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* MvPolynomial (Fin m) K) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext a c
  simp [Algebra.leftMulMatrix_eq_repr_mul, Algebra.TensorProduct.basis_repr_tmul,
    Algebra.TensorProduct.basis_apply]

theorem isIntegral_det_of_aeval {R' F : Type} [CommRing R'] [Field F] [Algebra R' F] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n F) (g : Polynomial R') (hg : g.Monic)
    (h : Polynomial.aeval M (g.map (algebraMap R' F)) = 0) : IsIntegral R' M.det := by
  have hd := GlobalTheory.CharpolyDvd.matrix_charpoly_dvd_pow M _ h
  rw [← Polynomial.map_pow] at hd
  have hc := Polynomial.isIntegral_coeff_of_dvd (g ^ Fintype.card n) M.charpoly (hg.pow _) M.charpoly_monic hd 0
  rw [Matrix.det_eq_sign_charpoly_coeff]
  exact (isIntegral_one.neg.pow _).mul hc

end GlobalTheory.NormSheaf.IntegralCoeff

namespace GlobalTheory.NormSheaf.IntegralCoeff

open MvPolynomial
open scoped TensorProduct

theorem isIntegral_normForm (A K L : Type) [CommRing A] [Field K] [Field L] [Algebra A K]
    [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L) (hx : ∀ i, IsIntegral A (x i)) :
    @IsIntegral (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) _ _
      MvPolynomial.algebraMvPolynomial (GlobalTheory.NormSheaf.normForm K L x) := by
  classical
  letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
  set R := MvPolynomial (Fin m) K
  set R' := MvPolynomial (Fin m) A
  let F := FractionRing R
  haveI : IsScalarTower R' R F := inferInstance
  let S := R ⊗[K] L
  letI : Algebra R' S := ((algebraMap R S).comp (algebraMap R' R)).toAlgebra
  let y : S := ∑ i, (X i : R) ⊗ₜ[K] x i
  have hy : IsIntegral R' y := by
    refine IsIntegral.sum _ fun i _ => ?_
    have e : (X i : R) ⊗ₜ[K] x i = algebraMap R' S (X i) * (1 ⊗ₜ[K] x i) := by
      have hX : algebraMap R' R (X i) = X i := MvPolynomial.map_X _ _
      change _ = algebraMap R S (algebraMap R' R (X i)) * _
      rw [hX]
      change _ = ((X i : R) ⊗ₜ[K] (1 : L)) * (1 ⊗ₜ[K] x i)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e]
    refine isIntegral_algebraMap.mul ?_
    refine IsIntegral.map_of_comp_eq (algebraMap A R')
      (Algebra.TensorProduct.includeRight : L →ₐ[K] S).toRingHom ?_ (hx i)
    refine RingHom.ext fun a => ?_
    change (algebraMap R' R (algebraMap A R' a)) ⊗ₜ[K] (1 : L) = (1 : R) ⊗ₜ[K] algebraMap A L a
    have h1 : algebraMap R' R (algebraMap A R' a) = algebraMap K R (algebraMap A K a) := by
      change MvPolynomial.map (algebraMap A K) (C a) = C (algebraMap A K a)
      exact MvPolynomial.map_C _ _
    rw [h1, IsScalarTower.algebraMap_apply A K L, Algebra.algebraMap_eq_smul_one (A := R) (algebraMap A K a),
      Algebra.algebraMap_eq_smul_one (A := L) (algebraMap A K a), TensorProduct.smul_tmul]
  obtain ⟨g, hgm, hgy⟩ := hy
  let bS := Algebra.TensorProduct.basis R (Module.finBasis K L)
  let φ : S →ₐ[R] Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F :=
    (AlgHom.mapMatrix (Algebra.ofId R F)).comp (Algebra.leftMulMatrix bS)
  have hM : φ y = (algebraMap R F).mapMatrix
      (∑ i, (X i : R) • (Algebra.leftMulMatrix (Module.finBasis K L) (x i)).map (C : K →+* R)) := by
    rw [← leftMulMatrix_sum_tmul K L x]
    rfl
  have h0 : Polynomial.aeval (φ y) (g.map (algebraMap R' F)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hh : (algebraMap F (Matrix (Fin (Module.finrank K L)) (Fin (Module.finrank K L)) F)).comp (algebraMap R' F)
        = φ.toRingHom.comp (algebraMap R' S) := by
      refine RingHom.ext fun r => ?_
      change algebraMap F _ (algebraMap R' F r) = φ (algebraMap R S (algebraMap R' R r))
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R' R F]
      exact (IsScalarTower.algebraMap_apply R F _ _).symm
    rw [hh]
    have h2 := Polynomial.hom_eval₂ g (algebraMap R' S) φ.toRingHom y
    rw [hgy, map_zero] at h2
    exact h2.symm
  have hdet := isIntegral_det_of_aeval _ g hgm h0
  rw [hM, ← RingHom.map_det] at hdet
  exact (isIntegral_algebraMap_iff ).mp hdet

end GlobalTheory.NormSheaf.IntegralCoeff

namespace GlobalTheory.NormSheaf.IntegralCoeff

theorem coeff_normForm_mem_range : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by
  intro A K L _ _ _ _ _ _ _ _ _ _ _ m x hx s
  letI : Algebra (MvPolynomial (Fin m) A) (MvPolynomial (Fin m) K) := MvPolynomial.algebraMvPolynomial
  have key := isIntegral_normForm A K L x hx
  have hc := MvPolynomial.isIntegral_iff_isIntegral_coeff.mp key s
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc
  exact ⟨a, ha⟩

end GlobalTheory.NormSheaf.IntegralCoeff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffNormFormOfFamilyMemRangeIntegrallyClosedStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed : ∀ (A K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L] [Algebra A K]
    [IsFractionRing A K] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L] {m : ℕ}
    (x : Fin m → L), (∀ i, IsIntegral A (x i)) →
    ∀ s, (GlobalTheory.NormSheaf.normForm K L x).coeff s ∈ (algebraMap A K).range := by
  first | exact @GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | exact GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range | (intros; apply GlobalTheory.NormSheaf.IntegralCoeff.coeff_normForm_mem_range <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFormCoefficientIdealMapLocalizationAway
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFormCoefficientIdealMapLocalizationAway
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheaf

theorem normForm_coeff_smul (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] {m : ℕ}
    (y : Fin m → L) (c : K) (s : Fin m →₀ ℕ) :
    (normForm K L (fun i => algebraMap K L c * y i)).coeff s =
      c ^ Module.finrank K L * (normForm K L y).coeff s := by
  have hM : ∀ i, (Algebra.leftMulMatrix (Module.finBasis K L) (algebraMap K L c * y i)).map
      (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) =
      (MvPolynomial.C c : MvPolynomial (Fin m) K) • (Algebra.leftMulMatrix (Module.finBasis K L) (y i)).map
        (MvPolynomial.C : K →+* MvPolynomial (Fin m) K) := by
    intro i
    rw [← Algebra.smul_def, map_smul]
    ext a b
    simp [Matrix.map_apply, Matrix.smul_apply, MvPolynomial.C_mul]
  have : normForm K L (fun i => algebraMap K L c * y i) =
      MvPolynomial.C (c ^ Module.finrank K L) * normForm K L y := by
    unfold normForm
    simp_rw [hM, smul_comm (MvPolynomial.X _ : MvPolynomial (Fin m) K) (MvPolynomial.C c), ← Finset.smul_sum,
      Matrix.det_smul, Fintype.card_fin, map_pow]
  rw [this, MvPolynomial.coeff_C_mul]

end GlobalTheory.NormSheaf

namespace GlobalTheory.NormSheaf

theorem normIdeal_map_away : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by
  intro A K L B A' B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f _ _ h1 h2 h3 hinj hcoef J
  have e1 : ∀ x : A, algebraMap A' K (algebraMap A A' x) = algebraMap A K x := fun x => by
    simpa using RingHom.congr_fun h1 x
  have e2 : ∀ x : B, algebraMap B' L (algebraMap B B' x) = algebraMap B L x := fun x => by
    simpa using RingHom.congr_fun h2 x
  have e3 : ∀ x : A, algebraMap K L (algebraMap A K x) = algebraMap B L (algebraMap A B x) := fun x => by
    simpa using RingHom.congr_fun h3 x
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    unfold normIdeal
    rw [Ideal.span_le]
    rintro a ⟨m, g, hg, s, hs⟩
    rw [SetLike.mem_coe, Ideal.mem_comap]
    apply Ideal.subset_span
    refine ⟨m, fun i => algebraMap B B' (g i), fun i => Ideal.mem_map_of_mem _ (hg i), s, ?_⟩
    rw [e1, hs]
    simp only [e2]
  · unfold normIdeal
    rw [Ideal.span_le]
    rintro a' ⟨m, g', hg', s, hs⟩
    set b := algebraMap A B f with hb
    have hloc : ∀ i, ∃ (j : B) (n : ℕ), j ∈ J ∧ g' i * algebraMap B B' (b ^ n) = algebraMap B B' j := by
      intro i
      obtain ⟨⟨⟨j, hj⟩, ⟨_, n, rfl⟩⟩, h⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (Submonoid.powers b) B').1 (hg' i)
      exact ⟨j, n, hj, h⟩
    choose j n hj hn using hloc
    set N := ∑ i, n i
    have hN : ∀ i, g' i * algebraMap B B' (b ^ N) = algebraMap B B' (j i * b ^ (N - n i)) := by
      intro i
      have hle : n i ≤ N := Finset.single_le_sum (fun k _ => Nat.zero_le (n k)) (Finset.mem_univ i)
      rw [← Nat.add_sub_cancel' hle, pow_add, map_mul, ← mul_assoc, hn i, Nat.add_sub_cancel_left, map_mul]
    have hjJ : ∀ i, j i * b ^ (N - n i) ∈ J := fun i => J.mul_mem_right _ (hj i)
    set c := algebraMap A K f
    have himg : ∀ i, algebraMap B L (j i * b ^ (N - n i)) =
        algebraMap K L (c ^ N) * algebraMap B' L (g' i) := by
      intro i
      rw [← e2, ← hN i, map_mul, e2, map_pow, map_pow, hb, ← e3, mul_comm]
    obtain ⟨a, ha⟩ := hcoef (fun i => j i * b ^ (N - n i)) s
    have hcoef' : algebraMap A K a = (c ^ N) ^ Module.finrank K L * algebraMap A' K a' := by
      rw [ha, hs]
      simp only [himg]
      exact normForm_coeff_smul K L _ _ s
    have hmem : a ∈ normIdeal A K L B J := Ideal.subset_span ⟨m, _, hjJ, s, ha⟩
    have key : algebraMap A A' a = algebraMap A A' (f ^ (N * Module.finrank K L)) * a' := by
      apply hinj
      rw [map_mul, e1, e1, hcoef', map_pow, pow_mul]
    have hu : IsUnit (algebraMap A A' (f ^ (N * Module.finrank K L))) := by
      rw [map_pow]; exact (IsLocalization.Away.algebraMap_isUnit f).pow _
    rw [SetLike.mem_coe, ← Ideal.unit_mul_mem_iff_mem _ hu, ← key]
    exact Ideal.mem_map_of_mem _ hmem

end GlobalTheory.NormSheaf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFormCoefficientIdealMapLocalizationAwayStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normFormCoefficientIdeal_map_localizationAway : ∀ (A K L B A' B' : Type) [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra A K] [Algebra B L] [Algebra A' K] [Algebra B' L]
    [Algebra A A'] [Algebra B B'] [Algebra A B] (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'],
    (algebraMap A' K).comp (algebraMap A A') = algebraMap A K →
    (algebraMap B' L).comp (algebraMap B B') = algebraMap B L →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp (algebraMap A B) →
    Function.Injective (algebraMap A' K) →
    (∀ {m : ℕ} (g : Fin m → B) s,
      (GlobalTheory.NormSheaf.normForm K L (fun i => algebraMap B L (g i))).coeff s ∈ (algebraMap A K).range) →
    ∀ J : Ideal B, (GlobalTheory.NormSheaf.normIdeal A K L B J).map (algebraMap A A') =
      GlobalTheory.NormSheaf.normIdeal A' K L B' (J.map (algebraMap B B')) := by
  first | exact @GlobalTheory.NormSheaf.normIdeal_map_away | exact GlobalTheory.NormSheaf.normIdeal_map_away | (intros; apply GlobalTheory.NormSheaf.normIdeal_map_away <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoeffIdealFamilyMapBasicOpen
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem isLocalization_away_of_eq_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U)
    (g : Γ(X, U)) (V : X.Opens) (hV : V = X.basicOpen g) (hle : V ≤ U) :
    letI := (X.presheaf.map (homOfLE hle).op).hom.toAlgebra;
    IsLocalization.Away g Γ(X, V) := by
  subst hV
  exact hU.isLocalization_basicOpen g

theorem famIdeal_map_basicOpen : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y] [GlobalTheory.IsNormalScheme Z]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ Set.range π →
    (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      GlobalTheory.NormSheafDescent.famIdeal π hK hfd I (Z.affineBasicOpen f) := by
  intro Y Z π _ _ _ hK hfd I U f hU
  by_cases hD : genPt π ∈ Z.basicOpen f
  · have hζU : genPt π ∈ U.1 := Z.basicOpen_le f hD
    have hD' : genPt π ∈ (Z.affineBasicOpen f).1 := hD
    have hUD : ((Z.affineBasicOpen f : Z.affineOpens) : Set Z) ⊆ Set.range π :=
      fun x hx => hU (Z.basicOpen_le f hx)
    letI := fieldK π hK
    letI := algKL π
    obtain ⟨hdomA, hfrA⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hU hζU
    obtain ⟨_, hfrA'⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π (Z.basicOpen f) (Z.affineBasicOpen f).2 hUD hD
    letI iA := algAK π U.1 hζU
    letI iB := algBL π U.1 hζU
    letI iA' := algAK π (Z.basicOpen f) hD
    letI iB' := algBL π (Z.basicOpen f) hD
    letI iAA' : Algebra Γ(Z, U) Γ(Z, Z.basicOpen f) :=
      (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom.toAlgebra
    have hleY : π ⁻¹ᵁ Z.basicOpen f ≤ π ⁻¹ᵁ U.1 := π.preimage_mono (Z.basicOpen_le f)
    letI iBB' : Algebra Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) :=
      (Y.presheaf.map (homOfLE hleY).op).hom.toAlgebra
    letI iAB : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1) := (π.app U.1).hom.toAlgebra
    haveI : IsLocalization.Away f Γ(Z, Z.basicOpen f) := U.2.isLocalization_basicOpen f
    haveI : IsLocalization.Away (algebraMap Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1) f) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) :=
      isLocalization_away_of_eq_basicOpen (U.2.preimage π) (π.app U.1 f) _
        (Scheme.preimage_basicOpen π f) hleY
    have h1 : (algebraMap Γ(Z, Z.basicOpen f) (Z.presheaf.stalk (genPt π))).comp
        (algebraMap Γ(Z, U) Γ(Z, Z.basicOpen f)) = algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π)) := by
      ext a
      exact Z.presheaf.germ_res_apply (homOfLE (Z.basicOpen_le f)) (genPt π) hD a
    have h2 : (algebraMap Γ(Y, π ⁻¹ᵁ Z.basicOpen f) Y.functionField).comp
        (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f)) =
          algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField := by
      ext a
      exact Y.presheaf.germ_res_apply (homOfLE hleY) (genericPoint Y) hD a
    have h3 : (algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp
        (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π))) =
          (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField).comp (algebraMap Γ(Z, U) Γ(Y, π ⁻¹ᵁ U.1)) := by
      ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) hζU a
    have h4 : Function.Injective (algebraMap Γ(Z, Z.basicOpen f) (Z.presheaf.stalk (genPt π))) :=
      IsFractionRing.injective _ _
    have h5 : ∀ {m : ℕ} (g : Fin m → Γ(Y, π ⁻¹ᵁ U.1)) s,
        (GlobalTheory.NormSheaf.normForm (Z.presheaf.stalk (genPt π)) Y.functionField
          (fun i => algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField (g i))).coeff s ∈
            (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π))).range := by
      intro m g s
      haveI : IsIntegrallyClosed Γ(Z, U) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2
      letI iAL : Algebra Γ(Z, U) Y.functionField :=
        ((algebraMap (Z.presheaf.stalk (genPt π)) Y.functionField).comp
          (algebraMap Γ(Z, U) (Z.presheaf.stalk (genPt π)))).toAlgebra
      haveI : IsScalarTower Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField :=
        IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      have hfin : (π.app U.1).hom.Finite := π.finite_app U.1 U.2
      let φ : Γ(Y, π ⁻¹ᵁ U.1) →ₐ[Γ(Z, U)] Y.functionField :=
        { algebraMap Γ(Y, π ⁻¹ᵁ U.1) Y.functionField with
          commutes' := fun a => (congrArg (fun h => h a) h3).symm }
      refine GlobalTheory.T.coeff_normFormOfFamily_mem_range_integrallyClosed Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField _ (fun i => ?_) s
      have hi : IsIntegral Γ(Z, U) (g i) := hfin.to_isIntegral (g i)
      exact hi.map φ
    have hJ : I.ideal ⟨π ⁻¹ᵁ (Z.affineBasicOpen f).1, (Z.affineBasicOpen f).2.preimage π⟩ =
        (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩).map
          (algebraMap Γ(Y, π ⁻¹ᵁ U.1) Γ(Y, π ⁻¹ᵁ Z.basicOpen f)) :=
      (I.map_ideal (U := ⟨π ⁻¹ᵁ (Z.affineBasicOpen f).1, (Z.affineBasicOpen f).2.preimage π⟩)
        (V := ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) hleY).symm
    simp only [famIdeal, dif_pos hζU, dif_pos hD']
    rw [hJ]
    exact GlobalTheory.T.normFormCoefficientIdeal_map_localizationAway Γ(Z, U) (Z.presheaf.stalk (genPt π)) Y.functionField Γ(Y, π ⁻¹ᵁ U.1)
      Γ(Z, Z.basicOpen f) Γ(Y, π ⁻¹ᵁ Z.basicOpen f) f h1 h2 h3 h4 h5 _
  · have hbot : Z.basicOpen f = ⊥ := by
      ext x
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨y, rfl⟩ := hU (Z.basicOpen_le f hx)
      exact hD (((genericPoint_specializes y).map π.continuous).mem_open (Z.basicOpen f).isOpen hx)
    haveI : Subsingleton Γ(Z, Z.basicOpen f) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)
    haveI : Subsingleton Γ(Z, (Z.affineBasicOpen f : Z.Opens)) := this
    ext x
    rw [Subsingleton.elim x 0]
    exact iff_of_true (Ideal.zero_mem _) (Ideal.zero_mem _)

end GlobalTheory.NormSheafDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoeffIdealFamilyMapBasicOpenStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCoeffIdealFamily_map_basicOpen : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y] [GlobalTheory.IsNormalScheme Z]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ Set.range π →
    (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      GlobalTheory.NormSheafDescent.famIdeal π hK hfd I (Z.affineBasicOpen f) := by
  first | exact @GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen | exact GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen | (intros; apply GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkImageOfGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charZero_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK;
    CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ hY hK
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hL : CharZero Y.functionField :=
    charZero_of_injective_ringHom (f := (Y.germToFunctionField ⊤).hom)
      (Y.germToFunctionField_injective ⊤)
  exact (π.stalkMap (genericPoint Y)).hom.charZero
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldStalkImageOfGenericPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldStalkImageOfGenericPoint
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent

theorem isField_stalk_of_forall_specializes {Z : Scheme.{0}} (ζ : Z) [IsDomain (Z.presheaf.stalk ζ)]
    (h : ∀ z : Z, z ⤳ ζ → z = ζ) : IsField (Z.presheaf.stalk ζ) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  let p : Spec (Z.presheaf.stalk ζ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Z.presheaf.stalk ζ))
  have hp : Z.fromSpecStalk ζ p ∈ Set.range (Z.fromSpecStalk ζ) := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  have h1 : Z.fromSpecStalk ζ p = Z.fromSpecStalk ζ (IsLocalRing.closedPoint _) :=
    (h _ hp).trans Scheme.fromSpecStalk_closedPoint.symm
  have h2 := (Z.fromSpecStalk ζ).isEmbedding.injective h1
  exact (congrArg PrimeSpectrum.asIdeal h2).symm

theorem isField_stalk_genPt :
    ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ _ hW
  haveI := GlobalTheory.IsNormalScheme.isDomain_stalk (X := Z) (genPt π)
  refine isField_stalk_of_forall_specializes _ fun z hz => ?_
  obtain ⟨y, rfl⟩ : z ∈ Set.range π := hz.mem_open hW ⟨_, rfl⟩
  exact (hz.antisymm ((genericPoint_specializes y).map π.continuous)).eq

end GlobalTheory.NormSheafDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldStalkImageOfGenericPointStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y] [GlobalTheory.IsNormalScheme Z], IsOpen (Set.range π) →
    IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  first | exact @GlobalTheory.NormSheafDescent.isField_stalk_genPt | exact GlobalTheory.NormSheafDescent.isField_stalk_genPt | (intros; apply GlobalTheory.NormSheafDescent.isField_stalk_genPt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfIsClopenFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfIsClopenFamily
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.ClopenIdealSheaf

theorem map_comap_localization {R A S T : Type*} [CommRing R] [CommRing A] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra A T] (f : R) [IsLocalization.Away f S] (ρ : R →+* A)
    [IsLocalization.Away (ρ f) T] (τ : S →+* T)
    (hcomm : ∀ a, τ (algebraMap R S a) = algebraMap A T (ρ a)) (I : Ideal A) :
    (I.comap ρ).map (algebraMap R S) = (I.map (algebraMap A T)).comap τ := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    refine Ideal.mem_comap.mpr (Ideal.mem_comap.mpr ?_)
    rw [hcomm]
    exact Ideal.mem_map_of_mem _ ha
  · intro s hs
    obtain ⟨⟨⟨x, hx⟩, ⟨_, n, rfl⟩⟩, hxs⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (.powers (ρ f)) T).mp (Ideal.mem_comap.mp hs)
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ := IsLocalization.surj (.powers f) s
    simp only at hxs hb
    have h1 : algebraMap A T (ρ b * ρ f ^ n) = algebraMap A T (x * ρ f ^ k) := by
      calc algebraMap A T (ρ b * ρ f ^ n)
          = τ (algebraMap R S b) * algebraMap A T (ρ f ^ n) := by rw [map_mul, hcomm]
        _ = τ s * τ (algebraMap R S (f ^ k)) * algebraMap A T (ρ f ^ n) := by
          rw [← hb, map_mul]
        _ = τ s * algebraMap A T (ρ f ^ n) * algebraMap A T (ρ f ^ k) := by
          rw [hcomm, map_pow]; ring
        _ = algebraMap A T (x * ρ f ^ k) := by rw [hxs, map_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (.powers (ρ f)) T).mp h1
    simp only at hm
    rw [IsLocalization.mem_map_algebraMap_iff (.powers f)]
    refine ⟨⟨⟨f ^ (m + n) * b, ?_⟩, ⟨f ^ (m + n + k), m + n + k, rfl⟩⟩, ?_⟩
    · have e : ρ (f ^ (m + n) * b) = ρ f ^ m * (ρ b * ρ f ^ n) := by
        rw [map_mul, map_pow, pow_add]; ring
      rw [Ideal.mem_comap, e, hm]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hx)
    · simp only
      rw [map_mul, pow_add, map_mul, ← hb]
      ring

theorem map_comap_eq {Z : Scheme.{0}} (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U))
    {U V B : Z.affineOpens} (hVU : (V : Z.Opens) ≤ U) (f : Γ(Z, U))
    (hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f) = B)
    (hBD : (B : Z.Opens) ≤ Z.basicOpen f)
    (hI : (F V).map (Z.presheaf.map (homOfLE (Z.basicOpen_le
        ((Z.presheaf.map (homOfLE hVU).op).hom f))).op).hom =
      F (Z.affineBasicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) :
    ((F V).comap (Z.presheaf.map (homOfLE hVU).op).hom).map
        (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      (F B).comap (Z.presheaf.map (homOfLE hBD).op).hom := by
  subst hB
  rw [← hI]
  haveI := U.2.isLocalization_basicOpen f
  haveI := V.2.isLocalization_basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f)
  refine map_comap_localization (S := Γ(Z, Z.basicOpen f)) f _
    (T := Γ(Z, Z.basicOpen ((Z.presheaf.map (homOfLE hVU).op).hom f))) _ ?_ _
  intro a
  change (Z.presheaf.map (homOfLE hBD).op).hom
      ((Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom a) =
    (Z.presheaf.map (homOfLE (Z.basicOpen_le _)).op).hom
      ((Z.presheaf.map (homOfLE hVU).op).hom a)
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

end GlobalTheory.ClopenIdealSheaf

namespace GlobalTheory.ClopenIdealSheaf

theorem exists_idealSheafData_of_isClopen : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W →
    ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by
  intro Z W hW F hF
  let W' : Z.Opens := ⟨W, hW.isOpen⟩
  let Wc : Z.Opens := ⟨Wᶜ, hW.isClosed.isOpen_compl⟩
  have hAff : ∀ U : Z.affineOpens, IsAffineOpen ((U : Z.Opens) ⊓ W') := by
    intro U
    obtain ⟨e, -, he, -⟩ := GlobalTheory.IsNormalScheme.exists_isIdempotentElem_basicOpen_eq (X := Z)
      (U := (U : Z.Opens)) (V := (U : Z.Opens) ⊓ W') (W := (U : Z.Opens) ⊓ Wc)
      (by
        rw [← inf_sup_left]
        have : W' ⊔ Wc = ⊤ := by
          ext x; simp [W', Wc, em]
        rw [this, inf_top_eq])
      (by
        refine Disjoint.mono inf_le_right inf_le_right ?_
        rw [disjoint_iff]; ext x; simp [W', Wc])
    rw [← he]; exact U.2.basicOpen e
  let V : Z.affineOpens → Z.affineOpens := fun U => ⟨(U : Z.Opens) ⊓ W', hAff U⟩
  have hVU : ∀ U, (V U : Z.Opens) ≤ U := fun U => inf_le_left
  have hVW : ∀ U, ((V U : Z.Opens) : Set Z) ⊆ W := fun U => Set.inter_subset_right
  let I : ∀ U : Z.affineOpens, Ideal Γ(Z, U) := fun U =>
    (F (V U)).comap (Z.presheaf.map (homOfLE (hVU U)).op).hom
  refine ⟨{ ideal := I, map_ideal_basicOpen := ?_ }, ?_, ?_⟩
  · intro U f
    have hB : Z.affineBasicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) =
        V (Z.affineBasicOpen f) := by
      apply Subtype.ext
      change Z.basicOpen ((Z.presheaf.map (homOfLE (hVU U)).op).hom f) = Z.basicOpen f ⊓ W'
      rw [Scheme.basicOpen_res]
      have := Z.basicOpen_le f
      apply le_antisymm
      · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
      · exact le_inf (le_inf (inf_le_left.trans this) inf_le_right) inf_le_left
    exact map_comap_eq F (hVU U) f hB (hVU _) (hF (V U) _ (hVW U))
  · intro U hU
    have key : ∀ (A B : Z.affineOpens), A = B → ∀ hle : (B : Z.Opens) ≤ A,
        (F B).comap (Z.presheaf.map (homOfLE hle).op).hom = F A := by
      rintro A B rfl hle
      have : homOfLE hle = 𝟙 _ := rfl
      rw [this, op_id, CategoryTheory.Functor.map_id, CommRingCat.hom_id]
      exact Ideal.comap_id _
    exact key U (V U) (Subtype.ext (inf_eq_left.mpr (show (U : Z.Opens) ≤ W' from hU)).symm) (hVU U)
  · intro x hx
    by_contra hxW
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      Z.isBasis_affineOpens.exists_subset_of_mem_open hxW hW.isClosed.isOpen_compl
    replace hx := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    have hbot : ((V ⟨U, hU⟩ : Z.affineOpens) : Z.Opens) = ⊥ := by
      ext y
      simp only [V, W', TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_mk,
        Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun h => hUW h.1 h.2
    haveI : Subsingleton Γ(Z, (V ⟨U, hU⟩ : Z.Opens)) :=
      CommRingCat.subsingleton_of_isTerminal (Z.sheaf.isTerminalOfEqEmpty hbot)
    have htop : F (V ⟨U, hU⟩) = ⊤ := by
      rw [Ideal.eq_top_iff_one, Subsingleton.elim (1 : Γ(Z, (V ⟨U, hU⟩ : Z.Opens))) 0]
      exact zero_mem _
    have hI : I ⟨U, hU⟩ = ⊤ := by
      simp only [I, htop, Ideal.comap_top]
    change x ∈ Z.zeroLocus (U := U) (I ⟨U, hU⟩ : Set Γ(Z, U)) at hx
    rw [hI, Scheme.mem_zeroLocus_iff] at hx
    exact hx 1 (Submodule.mem_top) (by rw [Scheme.basicOpen_one]; exact hxU)

end GlobalTheory.ClopenIdealSheaf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSheafDataOfIsClopenFamilyStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idealSheafData_of_isClopen_family : ∀ (Z : Scheme.{0}) (W : Set Z), IsClopen W → ∀ (F : ∀ U : Z.affineOpens, Ideal Γ(Z, U)),
    (∀ (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ W →
      (F U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom = F (Z.affineBasicOpen f)) →
    ∃ J : Z.IdealSheafData, (∀ U : Z.affineOpens, (U : Set Z) ⊆ W → J.ideal U = F U) ∧
      (J.support : Set Z) ⊆ W := by
  first | exact @GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen | exact GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen | (intros; apply GlobalTheory.ClopenIdealSheaf.exists_idealSheafData_of_isClopen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFunctionFieldStalkImageGenericPStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK;
    letI := GlobalTheory.NormSheafDescent.algKL π;
    FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField := by
  intro Y Z π _ _ hK
  let := GlobalTheory.NormSheafDescent.fieldK π hK
  let := GlobalTheory.NormSheafDescent.algKL π
  let K := Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)
  have hFinite : FiniteDimensional K Y.functionField := by
    obtain ⟨U, hU, hζU, -⟩ := exists_isAffineOpen_mem_and_subset
      (X := Z) (U := ⊤) (x := GlobalTheory.NormSheafDescent.genPt π) trivial
    have hηU : genericPoint Y ∈ π ⁻¹ᵁ U := hζU
    have hV : IsAffineOpen (π ⁻¹ᵁ U) := hU.preimage π
    have : Nonempty (π ⁻¹ᵁ U) := ⟨⟨_, hηU⟩⟩
    let f : Γ(Z, U) →+* K :=
      (Z.presheaf.germ U (GlobalTheory.NormSheafDescent.genPt π) hζU).hom
    let φ : Γ(Y, π ⁻¹ᵁ U) →+* Y.functionField := (Y.germToFunctionField (π ⁻¹ᵁ U)).hom
    let g : Γ(Z, U) →+* Γ(Y, π ⁻¹ᵁ U) := (π.app U).hom
    have hsq : ∀ a, algebraMap K Y.functionField (f a) = φ (g a) :=
      fun a => Scheme.Hom.germ_stalkMap_apply π U _ hζU a
    let : Algebra Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := g.toAlgebra
    have : Module.Finite Γ(Z, U) Γ(Y, π ⁻¹ᵁ U) := π.finite_app U hU
    have : IsFractionRing Γ(Y, π ⁻¹ᵁ U) Y.functionField :=
      functionField_isFractionRing_of_isAffineOpen Y _ hV
    have hint (b : Γ(Y, π ⁻¹ᵁ U)) : IsIntegral K (φ b) := by
      obtain ⟨p, hp, hpb⟩ := Algebra.IsIntegral.isIntegral (R := Γ(Z, U)) b
      refine ⟨p.map f, hp.map f, ?_⟩
      have e : (algebraMap K Y.functionField).comp f = φ.comp g := RingHom.ext hsq
      have hpb' : p.eval₂ g b = 0 := hpb
      rw [Polynomial.eval₂_map, e, ← Polynomial.hom_eval₂, hpb', map_zero]
    obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := Γ(Z, U)) (M := Γ(Y, π ⁻¹ᵁ U))
    have : Finite (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U))) := (s.finite_toSet.image φ).to_subtype
    let E := IntermediateField.adjoin K (φ '' (s : Set Γ(Y, π ⁻¹ᵁ U)))
    have hE : FiniteDimensional K E := IntermediateField.finiteDimensional_adjoin (by
      rintro _ ⟨b, -, rfl⟩
      exact hint b)
    have hmem (b : Γ(Y, π ⁻¹ᵁ U)) : φ b ∈ E := by
      have hb : b ∈ Submodule.span Γ(Z, U) (s : Set Γ(Y, π ⁻¹ᵁ U)) :=
        hs ▸ Submodule.mem_top
      induction hb using Submodule.span_induction with
      | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx =>
        have e : φ (a • x) = algebraMap K Y.functionField (f a) * φ x := by
          rw [hsq, Algebra.smul_def, map_mul]
          rfl
        rw [e]
        exact mul_mem (IntermediateField.algebraMap_mem _ _) hx
    have htop : E = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨b, c, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Y, π ⁻¹ᵁ U)) x
      exact div_mem (hmem b) (hmem c)
    have : FiniteDimensional K (⊤ : IntermediateField K Y.functionField) := htop ▸ hE
    exact LinearEquiv.finiteDimensional IntermediateField.topEquiv.toLinearEquiv
  exact hFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealFamilyEqTopOfDisjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealFamilyEqTopOfDisjoint
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.NormSheafDescent


open MvPolynomial in
theorem normIdeal_top (A K L B : Type) [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
    [FiniteDimensional K L] [CommRing B] [Algebra B L] :
    GlobalTheory.NormSheaf.normIdeal A K L B (⊤ : Ideal B) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  apply Ideal.subset_span
  refine ⟨1, fun _ => 1, fun _ => Submodule.mem_top, Finsupp.single 0 (Module.finrank K L), ?_⟩
  have hform : GlobalTheory.NormSheaf.normForm K L (fun _ : Fin 1 => algebraMap B L 1) =
      X 0 ^ Module.finrank K L := by
    unfold GlobalTheory.NormSheaf.normForm
    simp [Fin.sum_univ_one, map_one, Matrix.det_smul]
  rw [hform, coeff_X_pow]
  simp

theorem ideal_eq_top_of_forall_not_mem {X : Scheme.{0}} (I : X.IdealSheafData) (V : X.affineOpens)
    (h : ∀ x ∈ I.support, x ∉ V.1) : I.ideal V = ⊤ := by
  have hV : IsAffineOpen V.1 := V.2
  have hempty : X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)) ∩ V.1 = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxV
    exact h x ((Scheme.IdealSheafData.mem_support_iff_of_mem hxV).2 hx) hxV
  rw [← hV.fromSpec_image_zeroLocus] at hempty
  have h0 : PrimeSpectrum.zeroLocus (I.ideal V : Set Γ(X, V.1)) = ∅ := Set.image_eq_empty.mp hempty
  rw [PrimeSpectrum.zeroLocus_empty_iff_eq_top] at h0
  exact h0

theorem famIdeal_eq_top_of_disjoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by
  intro Y Z π _ _ hK hfd I U hU
  unfold famIdeal
  split_ifs with h
  · have hV : I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ = ⊤ :=
      ideal_eq_top_of_forall_not_mem I _ (fun y hy hyV => hU y hy hyV)
    simp only [hV]
    letI := fieldK π hK; letI := algKL π; letI := algAK π U.1 h; letI := algBL π U.1 h
    exact normIdeal_top _ _ _ _
  · rfl

end GlobalTheory.NormSheafDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealFamilyEqTopOfDisjointStatement
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by
  first | exact @GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint | exact GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint | (intros; apply GlobalTheory.NormSheafDescent.famIdeal_eq_top_of_disjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedNormIdealSheafFiniteNormal
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM

namespace GlobalTheory.NormSheafDescent

theorem descendedIdealSheaf_exists : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π], IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) → CharZero Γ(Y, ⊤) →
    ∀ I : Y.IdealSheafData, ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      CharZero K ∧ ∃ J : Z.IdealSheafData, (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ U : Z.affineOpens, (U : Set Z) ⊆ Set.range π → (U : Set Z).Nonempty →
        ∃ (_ : Algebra Γ(Z, U) K) (_ : Algebra Γ(Y, π ⁻¹ᵁ U.1) L),
          IsDomain Γ(Z, U) ∧ IsIntegrallyClosed Γ(Z, U) ∧ IsDomain Γ(Y, π ⁻¹ᵁ U.1) ∧ (π.app U.1).hom.Finite ∧
          IsFractionRing Γ(Z, U) K ∧ IsFractionRing Γ(Y, π ⁻¹ᵁ U.1) L ∧
          (algebraMap K L).comp (algebraMap Γ(Z, U) K) = (algebraMap Γ(Y, π ⁻¹ᵁ U.1) L).comp (π.app U.1).hom ∧
          J.ideal U = GlobalTheory.NormSheaf.normIdeal Γ(Z, U) K L Γ(Y, π ⁻¹ᵁ U.1) (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) := by
  intro Y Z π _ hY _ _ hnZ hW hchar I
  have hK := GlobalTheory.T.isField_stalk_imageOfGenericPoint Y Z π hW
  have hfd := GlobalTheory.T.finiteDimensional_functionField_stalk_imageGenericPoint Y Z π hK
  letI := GlobalTheory.NormSheafDescent.fieldK π hK
  letI := GlobalTheory.NormSheafDescent.algKL π
  have hcl : IsClosed (Set.range π) := π.isClosedMap.isClosed_range
  obtain ⟨J, hJ, hJs⟩ := GlobalTheory.T.exists_idealSheafData_of_isClopen_family Z (Set.range π) ⟨hcl, hW⟩ (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I)
    (fun U f hU => GlobalTheory.T.normCoeffIdealFamily_map_basicOpen Y Z π hK hfd I U f hU)
  have hgen : ∀ (U : Z.Opens) (x : Z), x ∈ U → x ∈ Set.range π →
      GlobalTheory.NormSheafDescent.genPt π ∈ U := by
    rintro U _ hx ⟨y, rfl⟩
    exact ((genericPoint_specializes y).map π.continuous).mem_open U.isOpen hx
  refine ⟨Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π), Y.functionField, inferInstance, inferInstance,
    inferInstance, hfd, GlobalTheory.T.charZero_stalk_imageOfGenericPoint Y Z π hchar hK, J, ?_, ?_⟩
  · intro x hx
    by_contra hne
    push_neg at hne
    have hxW := hJs hx
    have hS : IsClosed (π '' (I.support : Set Y)) := π.isClosedMap _ I.support.isClosed
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUsub⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ (π '' (I.support : Set Y))ᶜ ∩ Set.range π from ⟨fun ⟨y, hy, e⟩ => hne y hy e, hxW⟩)
      (hS.isOpen_compl.inter hW)
    have htop := GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint Y Z π hK hfd I ⟨U, hU⟩ (fun y hy hyU => (hUsub hyU).1 ⟨y, hy, rfl⟩)
    have hx' := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨U, hU⟩) hxU).mp hx
    rw [hJ ⟨U, hU⟩ (fun z hz => (hUsub hz).2), htop] at hx'
    exact (Scheme.mem_zeroLocus_iff _ _ _).mp hx' 1 Submodule.mem_top (by simpa using hxU)
  · rintro U hUW ⟨x, hxU⟩
    have h := hgen U.1 x hxU (hUW hxU)
    obtain ⟨hdom, hfr⟩ := GlobalTheory.T.sections_isFractionRing_stalk_imageOfGenericPoint Y Z π U.1 U.2 hUW h
    letI := GlobalTheory.NormSheafDescent.algAK π U.1 h
    letI := GlobalTheory.NormSheafDescent.algBL π U.1 h
    haveI : Nonempty (π ⁻¹ᵁ U.1) := ⟨⟨genericPoint Y, h⟩⟩
    refine ⟨inferInstance, inferInstance, hdom, GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen U.2,
      inferInstance, ?_, hfr, ?_, ?_, ?_⟩
    · exact π.finite_app U.1 U.2
    · exact functionField_isFractionRing_of_isAffineOpen Y _ (U.2.preimage π)
    · ext a
      exact Scheme.Hom.germ_stalkMap_apply π U.1 (genericPoint Y) h a
    · rw [hJ U hUW]
      simp only [GlobalTheory.NormSheafDescent.famIdeal, dif_pos h]

end GlobalTheory.NormSheafDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedNormIdealSheafFiniteNormalStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descended_normIdealSheaf_finite_normal : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π], IsIntegral Y → IsLocallyNoetherian Y →
    GlobalTheory.IsNormalScheme Y → GlobalTheory.IsNormalScheme Z → IsOpen (Set.range π) → CharZero Γ(Y, ⊤) →
    ∀ I : Y.IdealSheafData, ∃ (K L : Type) (_ : Field K) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L),
      CharZero K ∧ ∃ J : Z.IdealSheafData, (∀ x ∈ J.support, ∃ y ∈ I.support, π y = x) ∧
      ∀ U : Z.affineOpens, (U : Set Z) ⊆ Set.range π → (U : Set Z).Nonempty →
        ∃ (_ : Algebra Γ(Z, U) K) (_ : Algebra Γ(Y, π ⁻¹ᵁ U.1) L),
          IsDomain Γ(Z, U) ∧ IsIntegrallyClosed Γ(Z, U) ∧ IsDomain Γ(Y, π ⁻¹ᵁ U.1) ∧ (π.app U.1).hom.Finite ∧
          IsFractionRing Γ(Z, U) K ∧ IsFractionRing Γ(Y, π ⁻¹ᵁ U.1) L ∧
          (algebraMap K L).comp (algebraMap Γ(Z, U) K) = (algebraMap Γ(Y, π ⁻¹ᵁ U.1) L).comp (π.app U.1).hom ∧
          J.ideal U = GlobalTheory.NormSheaf.normIdeal Γ(Z, U) K L Γ(Y, π ⁻¹ᵁ U.1) (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) := by
  first | exact @GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists | exact GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists | (intros; apply GlobalTheory.NormSheafDescent.descendedIdealSheaf_exists <;> assumption)
end
