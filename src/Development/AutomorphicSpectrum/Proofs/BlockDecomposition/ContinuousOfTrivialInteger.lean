module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriContraction
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterCuspidalRootSumRegular
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSubValueZeroRapidDecay
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSum

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfTrivialInteger
open PositivityTheory.JacquetShalikaLocal

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel NNReal Pointwise

namespace GlobalTheory.CompanionTheory.JSBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_trivial_integer {ψ : AddChar F ℂ} (h : ∀ x ∈ 𝒪[F], ψ x = 1) : Continuous ψ := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' (𝒪[F] : Set F),
    (Valuation.isOpen_integer).preimage (by fun_prop), ?_, ?_⟩
  · simpa using (𝒪[F]).zero_mem
  · intro y hy
    have hxy : y = x + (y - x) := by ring
    rw [hxy, AddChar.map_add_eq_mul, h _ hy, mul_one]

theorem uniformizer_pow_ne_zero (M : ℕ) : (uniformizer F : F) ^ M ≠ 0 :=
  pow_ne_zero _ ((Valuation.ne_zero_iff _).mp (valuation_uniformizer_ne_zero F))

theorem lat_eq_preimage (m M : ℕ) : lat F m M =
    (Homeomorph.smulOfNeZero ((uniformizer F : F) ^ M) (uniformizer_pow_ne_zero M)) ⁻¹'
      Measures.box (F := F) (ι := Fin m) := by
  ext x
  simp [lat, Measures.mem_box]

theorem isOpen_lat (m M : ℕ) : IsOpen (lat F m M) := by
  rw [lat_eq_preimage]
  exact Measures.isOpen_box.preimage (Homeomorph.continuous _)

theorem isCompact_lat (m M : ℕ) : IsCompact (lat F m M) := by
  rw [lat_eq_preimage]
  exact (Homeomorph.isCompact_preimage _).2 Measures.isCompact_box

theorem zero_mem_lat (m M : ℕ) : (0 : Fin m → F) ∈ lat F m M := by
  intro i
  simpa using (𝒪[F]).zero_mem

variable [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [μ.IsAddHaarMeasure]

theorem lat_measure_pos (m M : ℕ) :
    0 < (Measure.pi fun _ : Fin m => μ).real (lat F m M) := by
  haveI := Measures.sigmaCompactSpace F
  have h0 := (isOpen_lat (F := F) m M).measure_ne_zero (Measure.pi fun _ : Fin m => μ)
    ⟨0, zero_mem_lat m M⟩
  have h1 := (isCompact_lat (F := F) m M).measure_lt_top (μ := Measure.pi fun _ : Fin m => μ)
  exact ENNReal.toReal_pos h0 h1.ne

theorem setIntegral_image_mulVec {m : ℕ} (g : GL (Fin m) F) (A : Set (Fin m → F))
    (f : (Fin m → F) → ℂ) :
    ∫ x in (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A, f x ∂(Measure.pi fun _ => μ) =
      ((Measures.modulus (g : Matrix (Fin m) (Fin m) F).det : ℝ) : ℂ) *
        ∫ x in A, f ((g : Matrix (Fin m) (Fin m) F) *ᵥ x) ∂(Measure.pi fun _ => μ) := by
  haveI := Measures.sigmaCompactSpace F
  haveI := Measures.metrizableSpace F
  set ν : Measure (Fin m → F) := Measure.pi fun _ => μ with hν
  set L := Measures.glEquiv g with hL
  let e : (Fin m → F) ≃ᵐ (Fin m → F) := (Homeomorph.smul L).toMeasurableEquiv
  have he : ∀ x, e x = (g : Matrix (Fin m) (Fin m) F) *ᵥ x := fun x => Measures.glEquiv_apply g x
  have hc : distribHaarChar (Fin m → F) L =
      Measures.modulus (g : Matrix (Fin m) (Fin m) F).det := by
    rw [hL, Measures.distribHaarChar_glEquiv, ← Measures.modulus_units]
    rfl
  have hmap : ν.map e.symm = (Measures.modulus (g : Matrix (Fin m) (Fin m) F).det) • ν := by
    refine Measure.ext fun s _ => ?_
    have hs : e.symm ⁻¹' s = L • s := (e.image_eq_preimage_symm s).symm
    rw [e.symm.map_apply, hs, ← distribHaarChar_mul ν L s, hc, Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul]
  have himg : (fun x => (g : Matrix (Fin m) (Fin m) F) *ᵥ x) '' A = e.symm ⁻¹' A := by
    rw [← e.image_eq_preimage_symm]
    exact Set.image_congr fun x _ => (he x).symm
  have key := setIntegral_map_equiv (μ := ν) e.symm (fun x => f (e x)) A
  simp only [MeasurableEquiv.apply_symm_apply] at key
  rw [himg, ← key, hmap, Measure.restrict_smul, integral_smul_nnreal_measure]
  simp only [he, NNReal.smul_def, Complex.real_smul]

theorem l0 : L0 := by
  intro F _ _ _ _ _ _ μ _ ψ hψ
  refine ⟨continuous_of_trivial_integer hψ.1, fun m => ⟨fun M => ?_, fun g A f _ => ?_⟩⟩
  · exact ⟨isCompact_lat m M, isOpen_lat m M, (isOpen_lat m M).measurableSet, lat_measure_pos μ m M⟩
  · exact setIntegral_image_mulVec μ g A f

end GlobalTheory.CompanionTheory.JSBound

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumRangeEsymmLMulSchur
noncomputable section

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {n : ℕ}

theorem prod_varL_eq_monomial (S : Finset (Fin n)) :
    ∏ k ∈ S, varL k = monomial (lamS S) := by
  have h : lamS S = ∑ k ∈ S, (Pi.single k 1 : Fin n → ℤ) := by
    funext x
    simp [lamS_apply, Finset.sum_apply, Pi.single_apply]
  rw [h]
  simp only [varL, monomial]
  rw [AddMonoidAlgebra.prod_single, Finset.prod_const_one]

theorem sum_esymmL_mul_pow (i : Fin n) :
    ∑ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r * varL i ^ (n - r) = 0 := by
  have h0 : ∏ k : Fin n, (-varL k + varL i) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Finset.prod_add, Finset.sum_powerset] at h0
  rw [← h0, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [esymmL, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hc := (Finset.mem_powersetCard.1 hS).2
  rw [Finset.prod_neg, hc, prod_varL_eq_monomial, Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ S),
    Finset.card_univ, Fintype.card_fin, hc]

theorem altQuot_zero' : altQuot (0 : LaurentRing n) = 0 :=
  altQuot_eq_of_mul (by simp)

theorem sum_esymmL_mul_schur (hn : 0 < n) (j : ℤ) :
    ∑ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single (⟨0, hn⟩ : Fin n) (j - (r : ℤ))) = 0 := by
  set i₀ : Fin n := ⟨0, hn⟩
  set P : LaurentRing n := monomial (Pi.single i₀ (j - (n : ℤ)) + staircase n) with hP
  have hterm : ∀ r ∈ Finset.range (n + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single i₀ (j - (r : ℤ))) =
      altQuot ((-1) ^ r * esymmL n r * varL i₀ ^ (n - r) * P) := by
    intro r hr
    have hr' : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have hsym : ∀ σ, permAct σ ((-1) ^ r * esymmL n r) = (-1) ^ r * esymmL n r := by
      intro σ
      rw [map_mul, map_pow, map_neg, map_one, permAct_esymmL]
    rw [mul_assoc ((-1) ^ r * esymmL n r), altQuot_mul_of_symm hsym, schur]
    congr 2
    rw [← monomial_single_natCast, hP, ← monomial_add, ← add_assoc, ← Pi.single_add]
    congr 3
    push_cast [Nat.cast_sub hr']
    ring
  rw [Finset.sum_congr rfl hterm, ← altQuot_sum, ← Finset.sum_mul, sum_esymmL_mul_pow, zero_mul,
    altQuot_zero']

theorem schur_single_eq_zero (hn : 0 < n) {m : ℤ} (h1 : 1 - (n : ℤ) ≤ m) (h2 : m ≤ -1) :
    schur (Pi.single (⟨0, hn⟩ : Fin n) m) = 0 := by
  refine altQuot_eq_of_mul ?_
  rw [mul_zero]
  have hlt : (-m).toNat < n := by omega
  refine (alternant_eq_zero (i := (⟨0, hn⟩ : Fin n)) (j := ⟨(-m).toNat, hlt⟩) ?_ ?_).symm
  · intro h
    have := congrArg Fin.val h
    simp only at this
    omega
  · have hne : (⟨(-m).toNat, hlt⟩ : Fin n) ≠ ⟨0, hn⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hne, staircase]
    have : (((-m).toNat : ℕ) : ℤ) = -m := by omega
    simp only [this]
    ring

theorem schur_zero_eq_one : schur (0 : Fin n → ℤ) = 1 :=
  altQuot_eq_of_mul (by rw [mul_one, zero_add]; rfl)

theorem sum_range_esymmL_mul_schur (hn : 0 < n) {j : ℕ} (hj : 1 ≤ j) :
    ∑ r ∈ Finset.range (j + 1), (-1) ^ r * esymmL n r *
      schur (Pi.single (⟨0, hn⟩ : Fin n) ((j - r : ℕ) : ℤ)) = 0 := by
  set f : ℕ → LaurentRing n := fun r => (-1) ^ r * esymmL n r *
    schur (Pi.single (⟨0, hn⟩ : Fin n) ((j : ℤ) - (r : ℤ))) with hf
  have h1 : ∑ r ∈ Finset.range (j + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    have hjr : j < r := by
      have := Finset.mem_range.not.1 hr'
      omega
    by_cases hrn : n < r
    · simp only [hf]
      rw [esymmL_eq_zero hrn, mul_zero, zero_mul]
    · simp only [hf]
      rw [schur_single_eq_zero hn (by omega) (by omega), mul_zero]
  have h2 : ∑ r ∈ Finset.range (n + 1), f r = ∑ r ∈ Finset.range (j + n + 1), f r := by
    refine Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun r hr hr' => ?_
    have hrn : n < r := by
      have := Finset.mem_range.not.1 hr'
      omega
    simp only [hf]
    rw [esymmL_eq_zero hrn, mul_zero, zero_mul]
  have h3 : ∑ r ∈ Finset.range (j + 1), f r = 0 := by
    rw [h1, ← h2]
    exact sum_esymmL_mul_schur hn (j : ℤ)
  rw [← h3]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' : r ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  simp only [hf]
  rw [Nat.cast_sub hr']

theorem monomialChar_lamS (S : Finset (Fin n)) (z : Fin n → ℂˣ) :
    monomialChar (lamS S) z = ∏ i ∈ S, (z i : ℂ) := by
  rw [monomialChar_apply]
  have h : ∀ i, ((z i ^ lamS S i : ℂˣ) : ℂ) = if i ∈ S then (z i : ℂ) else 1 := by
    intro i
    rw [lamS_apply]
    split_ifs <;> simp
  simp only [h]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem schur_row_recursion : L8 := by
  intro n hn z
  refine ⟨?_, fun j hj => ?_⟩
  · have h0 : (Pi.single (⟨0, hn⟩ : Fin n) ((0 : ℕ) : ℤ) : Fin n → ℤ) = 0 := by
      simp
    rw [h0, schur_zero_eq_one, map_one]
  · have h := congrArg (evalAt z) (sum_range_esymmL_mul_schur hn hj)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_zero, evalAt_esymmL,
      monomialChar_lamS] at h
    exact h

end GlobalTheory.CompanionTheory.SatakeBound

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabel
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabel
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin.CuspLabel

theorem root_pow_eq_one {K : Type} [Field K] [Fintype K] {P : K[X]} (hmon : P.Monic) (hirr : Irreducible P)
    (hX : P ≠ X) {x : AlgebraicClosure K} (hx : aeval x P = 0) :
    x ^ (Fintype.card K ^ P.natDegree - 1) = 1 := by
  have hmin : P = minpoly K x := minpoly.eq_of_irreducible_of_monic hirr hx hmon
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfr : Module.finrank K (IntermediateField.adjoin K {x}) = P.natDegree := by
    rw [hmin, IntermediateField.adjoin.finrank hint]
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hX (hmin.trans (minpoly.zero K _))
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
  letI := Fintype.ofFinite (IntermediateField.adjoin K {x})
  have hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ P.natDegree := by
    rw [← hfr]; exact Module.card_eq_pow_finrank
  have hy : IntermediateField.AdjoinSimple.gen K x ≠ 0 := by
    intro h
    exact hx0 (by simpa using congrArg (algebraMap (IntermediateField.adjoin K {x}) (AlgebraicClosure K)) h)
  have h := FiniteField.pow_card_sub_one_eq_one _ hy
  rw [hcard] at h
  simpa using congrArg (algebraMap (IntermediateField.adjoin K {x}) (AlgebraicClosure K)) h

theorem rootSum_minpoly {K : Type} [Field K] [Fintype K] (θ : AlgebraicClosure K →* ℂ) {d : ℕ} (hd : 0 < d)
    {w : AlgebraicClosure K} (hw : w ^ (Fintype.card K ^ d - 1) = 1) (hdeg : (minpoly K w).natDegree = d)
    (j : ℕ) : GlobalTheory.CuspGL.rootSum θ j (minpoly K w) =
      ∑ i ∈ Finset.range d, θ (w ^ Fintype.card K ^ i) ^ j := by
  have h := (GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum K θ d hd w (by
    show w ^ (Nat.card K ^ d - 1) = 1
    rw [Nat.card_eq_fintype_card]; exact hw)).2.2 j
  rw [hdeg, Nat.div_self hd, pow_one, Nat.card_eq_fintype_card] at h
  exact h

theorem exists_cuspidal_label : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (d : ℕ), 1 ≤ d → ∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
    ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P := by
  intro K _ _ _ C d hd P hmon hirr hX hdeg
  have hcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hqd : 1 < Fintype.card K ^ d := Nat.one_lt_pow (by omega) hq
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) P
    (by
      intro h
      have h0 : P.natDegree = 0 := natDegree_eq_of_degree_eq_some (by simpa using h)
      omega)
  have hroot : ∀ w : AlgebraicClosure K, aeval w P = 0 → w ^ (Fintype.card K ^ d - 1) = 1 := fun w hw => by
    rw [← hdeg]; exact root_pow_eq_one hmon hirr hX hw
  have hminP : ∀ w : AlgebraicClosure K, aeval w P = 0 → minpoly K w = P := fun w hw =>
    (minpoly.eq_of_irreducible_of_monic hirr hw hmon).symm
  have hprim : IsPrimitiveRoot (C.gen d) (Fintype.card K ^ d - 1) := by
    rw [← C.gen_order d hd]; exact IsPrimitiveRoot.orderOf _
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨by omega⟩
  obtain ⟨k, -, hkx⟩ := hprim.eq_pow_of_pow_eq_one (hroot x₀ hx₀)
  have hreg := GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow K d k (C.gen d) hd (by rw [hcard]; exact C.gen_order d hd)
    (by rw [hkx, hminP x₀ hx₀, hdeg])
  obtain ⟨hch, hip⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular K C.ι C.ι_inj d k hd hreg
  have hadd := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow K C.ι k).1
  obtain ⟨n, ρ, hρ⟩ := (GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex _ _).2 hch
  have hchar : ∀ g : GL (Fin d) K, (PI.SerBridgeGLW.repOfGL ρ).character g = (-1) ^ (d - 1) *
      GlobalTheory.CuspGL.psi (GlobalTheory.CuspGL.rootSum C.ι k) (Fin d → K)
        (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K)) := fun g => by
    rw [PI.SerBridgeGLW.repOfGL_character, ← hρ]
  refine ⟨PI.SerBridgeGLW.repOfGL ρ, ?_, ?_, hmon, hirr, hX, by simpa using hdeg, ?_⟩
  · rw [FDRep.simple_iff_char_is_norm_one]
    rw [(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties K d (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype, GlobalTheory.CuspGL.glCard] at hip
    rw [← hip]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : ((-1 : ℂ) ^ (d - 1)) * ((-1 : ℂ) ^ (d - 1)) = 1 := by
      rw [← mul_pow]; simp
    rw [← PI.SerBridgeGLW.conjugate_character_formula _ (PI.SerBridgeGLW.repOfGL ρ) x, hchar, star_mul', star_pow,
      star_neg, star_one, mul_mul_mul_comm, h1, one_mul]
  · refine GlobalTheory.T.cuspidal_of_unipotent_sums_vanish K d _ fun a ha had => ?_
    have h := GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive K d _ (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse K (Fin d → K) _ hadd) a ha had
    rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
    have h2 := congrArg (fun z : ℂ => (-1 : ℂ) ^ (d - 1) * z) h
    simp only [mul_zero, Finset.mul_sum] at h2
    refine Eq.trans ?_ h2
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
        ((i : ℕ) < a ∧ a ≤ (j : ℕ))
    · rw [if_pos hu, Set.indicator_of_mem (by exact hu), hchar]
    · rw [if_neg hu, Set.indicator_of_notMem (by exact hu), mul_zero]
  · intro x hx γ hγ z hz m hm
    simp only [Fintype.card_fin] at hm ⊢
    have hQ : minpoly K z = Matrix.charpoly (γ : Matrix (Fin d) (Fin d) K) :=
      (minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)).symm
    have hQd : (minpoly K z).natDegree = d := by
      rw [hQ, Matrix.charpoly_natDegree_eq_dim]; simp
    have hz1 : z ^ (Fintype.card K ^ d - 1) = 1 := by
      rw [← hm, ← pow_mul, mul_comm, pow_mul, ← C.gen_order d hd, pow_orderOf_eq_one, one_pow]
    have hval := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible K (Fin d → K) _ hadd
      (Matrix.toLin' (γ : Matrix (Fin d) (Fin d) K)) (by rw [Matrix.charpoly_toLin']; exact hγ)
    rw [Matrix.charpoly_toLin'] at hval
    show (PI.SerBridgeGLW.repOfGL ρ).character γ = _
    rw [hchar, hval, ← hQ, rootSum_minpoly C.ι hd hz1 hQd k]
    congr 1
    have hxd : (minpoly K x).natDegree = d := by rw [hminP x hx, hdeg]
    have hx₀d : (minpoly K x₀).natDegree = d := by rw [hminP x₀ hx₀, hdeg]
    calc ∑ i ∈ Finset.range d, C.ι (z ^ Fintype.card K ^ i) ^ k
        = ∑ i ∈ Finset.range d, C.ι (x₀ ^ Fintype.card K ^ i) ^ m := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← map_pow, ← map_pow, ← hm, ← hkx]
          congr 1
          simp only [← pow_mul]
          congr 1
          ring
      _ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x₀) := (rootSum_minpoly C.ι hd (hroot x₀ hx₀) hx₀d m).symm
      _ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x) := by rw [hminP x₀ hx₀, hminP x hx]
      _ = ∑ i ∈ Finset.range d, C.ι (x ^ Fintype.card K ^ i) ^ m := rootSum_minpoly C.ι hd (hroot x hx) hxd m
      _ = ∑ i ∈ Finset.range d, C.ι x ^ (m * Fintype.card K ^ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_pow, ← pow_mul, mul_comm (Fintype.card K ^ i) m]

end GlobalTheory.CompanionTheory.TyFin.CuspLabel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabelStatement
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspidal_with_label : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (d : ℕ), 1 ≤ d → ∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
    ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label | exact GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label | (intros; apply GlobalTheory.CompanionTheory.TyFin.CuspLabel.exists_cuspidal_label <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SymmetricFunctionAbsoluteValues
open PositivityTheory.JacquetShalikaLocal GroundTheory.Automorphic GroundTheory.Automorphic.Spherical

namespace GlobalTheory.CompanionTheory.JSBound

theorem evalAt_esymmL_eq_sum_prod {n : ℕ} (z : Fin n → ℂˣ) (r : ℕ) :
    evalAt z (esymmL n r) =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, (z i : ℂ) := by
  unfold esymmL
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [evalAt, monomial, AddMonoidAlgebra.lift_single, one_smul, pointHom, monomialChar,
    MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, lamS]
  rw [← Fintype.prod_ite_mem S]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs <;> simp

theorem prod_one_add_mul_eq {n : ℕ} (w : Fin n → ℂ) (t : ℂ) :
    ∏ j, (1 + t * w j) = ∑ r ∈ Finset.range (n + 1),
      t ^ r * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, w i := by
  have h := Finset.prod_add (fun j => t * w j) (fun _ => (1 : ℂ)) (Finset.univ : Finset (Fin n))
  simp only [Finset.prod_const_one, mul_one, Finset.prod_mul_distrib, Finset.prod_const] at h
  rw [show (∏ j, (1 + t * w j)) = ∏ j, (t * w j + 1) from Finset.prod_congr rfl fun _ _ => add_comm _ _, h,
    Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [(Finset.mem_powersetCard.1 hS).2]

theorem prod_add_eq {n : ℕ} (z : Fin n → ℂ) (t : ℂ) :
    ∏ j, (t + z j) = ∑ r ∈ Finset.range (n + 1),
      t ^ (n - r) * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∏ i ∈ S, z i := by
  rw [show (∏ j, (t + z j)) = ∏ j, (z j + t) from Finset.prod_congr rfl fun _ _ => add_comm _ _,
    Finset.prod_add, Finset.sum_powerset, Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun S hS => ?_
  rw [Finset.prod_const, ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin,
    (Finset.mem_powersetCard.1 hS).2, mul_comm]

theorem mul_prod_one_add_conj_eq {n : ℕ} (z : Fin n → ℂˣ)
    (h : ∀ r ≤ n, starRingEnd ℂ (evalAt z (esymmL n r)) * evalAt z (esymmL n n) =
      evalAt z (esymmL n (n - r))) (t : ℂ) :
    evalAt z (esymmL n n) * ∏ j, (1 + t * starRingEnd ℂ (z j : ℂ)) = ∏ j, (t + (z j : ℂ)) := by
  simp only [evalAt_esymmL_eq_sum_prod] at h ⊢
  rw [prod_one_add_mul_eq, prod_add_eq, Finset.mul_sum]
  conv_rhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun r hr => ?_
  have hrn : r ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
  have key := h r hrn
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_prod] at key
  rw [Nat.add_sub_cancel, Nat.sub_sub_self hrn, ← key]
  ring

theorem symmetric_function_absolute_values : ParameterAbsoluteValues := by
  unfold ParameterAbsoluteValues
  intro n z h i
  have h0 := mul_prod_one_add_conj_eq z h 0
  have h1 := mul_prod_one_add_conj_eq z h (-(z i : ℂ))
  simp only [zero_mul, add_zero, zero_add, Finset.prod_const_one, mul_one] at h0
  have hne : evalAt z (esymmL n n) ≠ 0 := by
    rw [h0]
    exact Finset.prod_ne_zero_iff.2 fun j _ => (z j).ne_zero
  have hz : ∏ j, (-(z i : ℂ) + z j) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by ring)
  rw [hz, mul_eq_zero] at h1
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.1 (h1.resolve_left hne)
  refine ⟨j, ?_⟩
  have hc : (z i : ℂ) * starRingEnd ℂ (z j : ℂ) = 1 := by linear_combination -hj
  have hn := congrArg norm hc
  rw [norm_mul, Complex.norm_conj, norm_one] at hn
  rw [mul_comm]
  exact hn

end GlobalTheory.CompanionTheory.JSBound
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinalFormBesselBound
noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical PositivityTheory.JacquetShalikaLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem inv_top {n : ℕ} (hn : 1 < n) {ρ : Representation ℂ (GL (Fin n) F) V} {ψ : AddChar F ℂ}
    {l : V →ₗ[ℂ] ℂ} {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) : Inv ρ ψ l (n - 1) B := by
  obtain ⟨hh, hp, hi⟩ := hU
  refine ⟨hh, fun u => ?_, fun u hu => ?_, fun g _ u u' => ?_, fun g hg u u' => ?_⟩
  · by_cases h : u = 0
    · simp [h]
    · exact (hp u h).le
  · by_cases h : u = 0
    · simp [h]
    · have := hp u h
      rw [hu] at this
      simp at this
  · rw [hi, Nat.sub_self, pow_zero, one_mul]
  · have h1 : g = 1 := by
      apply Units.ext
      ext i j
      exact hg.2 i j (by omega)
    subst h1
    rw [Whittaker.psiN_one]
    simp

theorem inv_step [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ}
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {k : ℕ} (hk : k + 1 < n) {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hB : Inv ρ ψ l (k + 1) B) :
    ∃ B', Char μ ρ ψ k B B' ∧ Inv ρ ψ l k B' := by
  obtain ⟨B', hC⟩ := h4a F μ ψ hψ n V ρ hρ l k B hk hB
  obtain ⟨hh, hp, hz⟩ := h4b F μ ψ hψ n V ρ hρ l k B B' hk hW hB hC
  exact ⟨B', hC, hh, hp, hz, h4c F μ ψ hψ n V ρ hρ l k B B' hk hB hC,
    h4d F μ ψ hψ n V ρ hρ l k B B' hk hB hC⟩

theorem inv_down [MeasurableSpace F] [BorelSpace F] (h4a : StableAverageExists) (h4b : FormHermitianPositive) (h4c : FormQuasiInvariantMirabolic) (h4d : FormEquivariantColumn)
    (μ : Measure F) [μ.IsAddHaarMeasure] {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {n : ℕ} (hn : 1 < n)
    {ρ : Representation ℂ (GL (Fin n) F) V} (hρ : Smooth ρ) {l : V →ₗ[ℂ] ℂ} (hW : Whit ρ ψ l)
    {B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} (hU : Unit' ρ B) (d : ℕ) (hd : d ≤ n - 2) :
    ∃ B₁, Inv ρ ψ l (n - 1 - d) B₁ := by
  induction d with
  | zero => exact ⟨B, inv_top hn hU⟩
  | succ d ih =>
    obtain ⟨B₁, h₁⟩ := ih (by omega)
    have e : n - 1 - d = n - 1 - (d + 1) + 1 := by omega
    rw [e] at h₁
    obtain ⟨B₂, -, h₂⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (by omega) h₁
    exact ⟨B₂, h₂⟩

theorem final_form_bessel_bound : StableAverageExists → FormHermitianPositive → FormQuasiInvariantMirabolic → FormEquivariantColumn → L5 → L6 := by
  intro h4a h4b h4c h4d h5 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l B hn hW hU
  obtain ⟨B₁, h₁⟩ := inv_down h4a h4b h4c h4d μ hψ hn hρ hW hU (n - 2) le_rfl
  have e : n - 1 - (n - 2) = 0 + 1 := by omega
  rw [e] at h₁
  obtain ⟨B', hC, h'⟩ := inv_step h4a h4b h4c h4d μ hψ hρ hW (k := 0) (by omega) h₁
  exact ⟨B', h', h5 F μ ψ hψ n V ρ hρ l B₁ B' hn h₁ hC⟩

end GlobalTheory.CompanionTheory.SatakeBound

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrthogonalityOfLatticeCharacter
open PositivityTheory.JacquetShalikaLocal
open MeasureTheory ValuativeRel

namespace GlobalTheory.CompanionTheory.SatakeBound

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_integer_psi_mul_ne_one {ψ : AddChar F ℂ} (hψ : PsiOK ψ) {b : F}
    (hb : b ∉ (valuation F).integer) :
    ∃ t ∈ (valuation F).integer, ψ (t * b) ≠ 1 := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (zero_mem _)
  have hvb : 1 < valuation F b := by
    rw [Valuation.mem_integer_iff, not_le] at hb
    exact hb
  have hvinv : valuation F b⁻¹ < 1 := ((valuation F).one_lt_val_iff hb0).mp hvb
  have hinvO : b⁻¹ ∈ (valuation F).integer := by
    rw [Valuation.mem_integer_iff]
    exact hvinv.le
  have hynu : (⟨b⁻¹, hinvO⟩ : (valuation F).integer) ∈ IsLocalRing.maximalIdeal (valuation F).integer := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (ne_of_lt hvinv) ((Valuation.integer.integers (valuation F)).isUnit_iff_valuation_eq_one.mp hu)
  have hmax := GroundTheory.Automorphic.GLnLocal.maximalIdeal_pow_eq F 1
  rw [pow_one, pow_one] at hmax
  rw [hmax, Ideal.mem_span_singleton] at hynu
  obtain ⟨u, hu⟩ := hynu
  obtain ⟨x, hx, hψx⟩ := hψ.2.1
  refine ⟨(↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F), mul_mem hx u.2, ?_⟩
  have hu' : b⁻¹ = (GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * (u : F) := by
    have h := congrArg Subtype.val hu
    simpa using h
  have hx' : (↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F) * b = x := by
    calc (↑(GroundTheory.Automorphic.GLnLocal.uniformizer F) * x) * (u : F) * b
        = x * ((GroundTheory.Automorphic.GLnLocal.uniformizer F : F) * u) * b := by ring
      _ = x * b⁻¹ * b := by rw [hu']
      _ = x := by rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]
  rw [hx']
  exact hψx

theorem mem_lat_zero {m : ℕ} {x : Fin m → F} :
    x ∈ lat F m 0 ↔ ∀ i, x i ∈ (valuation F).integer := by
  simp only [lat, Set.mem_ofPred_eq, pow_zero, one_mul]

theorem orthogonality_of_lattice_character : L0 → L1 := by
  unfold L0 L1 ForF
  intro hL0 F _ _ _ _ _ _ μ _ ψ hψ m y
  have hL := hL0 F μ ψ hψ
  dsimp only at hL ⊢
  by_cases hy : ∀ i, y i ∈ (valuation F).integer
  · rw [if_pos hy]
    have hmeas : MeasurableSet (lat F m 0) := ((hL.2 m).1 0).2.2.1
    have h1 : Set.EqOn (fun ξ : Fin m → F => ψ (ξ ⬝ᵥ y)) (fun _ => (1 : ℂ)) (lat F m 0) := by
      intro ξ hξ
      rw [mem_lat_zero] at hξ
      refine hψ.1 _ ?_
      unfold dotProduct
      exact sum_mem fun j _ => mul_mem (hξ j) (hy j)
    rw [setIntegral_congr_fun hmeas h1, setIntegral_const]
    simp
  · rw [if_neg hy]
    simp only [not_forall] at hy
    obtain ⟨i, hi⟩ := hy
    obtain ⟨t, ht, hne⟩ := exists_integer_psi_mul_ne_one hψ hi
    have hsO : ∀ j, (Pi.single i t : Fin m → F) j ∈ (valuation F).integer := by
      intro j
      by_cases hj : j = i
      · rw [hj, Pi.single_eq_same]
        exact ht
      · rw [Pi.single_eq_of_ne hj]
        exact zero_mem _
    have hinv : (fun ξ : Fin m → F => Pi.single i t + ξ) ⁻¹' lat F m 0 = lat F m 0 := by
      ext ξ
      simp only [Set.mem_preimage, mem_lat_zero, Pi.add_apply]
      constructor
      · intro h j
        have h2 := sub_mem (h j) (hsO j)
        simpa using h2
      · intro h j
        exact add_mem (hsO j) (h j)
    have hsd : (Pi.single i t : Fin m → F) ⬝ᵥ y = t * y i := by
      first
        | exact single_dotProduct t i
        | simp [dotProduct, Pi.single_apply]
    have hmp := measurePreserving_add_left (Measure.pi fun _ : Fin m => μ) (Pi.single i t : Fin m → F)
    have hemb := measurableEmbedding_addLeft (Pi.single i t : Fin m → F)
    have hshift := hmp.setIntegral_preimage_emb hemb (fun ξ => ψ (ξ ⬝ᵥ y)) (lat F m 0)
    rw [hinv] at hshift
    simp only [add_dotProduct, AddChar.map_add_eq_mul, hsd] at hshift
    rw [integral_const_mul] at hshift
    have h0 : (∫ ξ in lat F m 0, ψ (ξ ⬝ᵥ y) ∂Measure.pi fun _ => μ) * (ψ (t * y i) - 1) = 0 := by
      linear_combination hshift
    exact (mul_eq_zero.mp h0).resolve_right (sub_ne_zero.mpr hne)

end GlobalTheory.CompanionTheory.SatakeBound
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeffEqPowOfMulOneSub
open PositivityTheory.JacquetShalikaLocal

namespace GlobalTheory.CompanionTheory.SatakeBound

open PowerSeries Filter Topology

theorem tendsto_coeff_mul_one_sub (G : ℂ⟦X⟧) (b : ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * (1 - C b * X))) atTop (𝓝 0) := by
  rw [← tendsto_add_atTop_iff_nat 1]
  have e : ∀ j : ℕ, coeff (j + 1) (G * (1 - C b * X)) = coeff (j + 1) G - b * coeff j G := by
    intro j
    have : G * (1 - C b * X) = G - C b * (G * X) := by ring
    rw [this, map_sub, coeff_C_mul, coeff_succ_mul_X]
  simp only [e]
  have h1 := (tendsto_add_atTop_iff_nat 1).2 h
  simpa using h1.sub (h.const_mul b)

theorem tendsto_coeff_mul_prod (G : ℂ⟦X⟧) {ι : Type*} (s : Finset ι) (β : ι → ℂ)
    (h : Tendsto (fun j => coeff j G) atTop (𝓝 0)) :
    Tendsto (fun j => coeff j (G * ∏ k ∈ s, (1 - C (β k) * X))) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have : G * ((1 - C (β a) * X) * ∏ k ∈ s, (1 - C (β k) * X)) =
        (G * ∏ k ∈ s, (1 - C (β k) * X)) * (1 - C (β a) * X) := by ring
    rw [this]
    exact tendsto_coeff_mul_one_sub _ _ ih

theorem coeff_eq_pow_of_mul_one_sub (H : ℂ⟦X⟧) (b : ℂ) (h : H * (1 - C b * X) = 1) (j : ℕ) :
    coeff j H = b ^ j := by
  have e : H = 1 + C b * (H * X) := by
    calc H = H * (1 - C b * X) + C b * (H * X) := by ring
      _ = 1 + C b * (H * X) := by rw [h]
  induction j with
  | zero =>
    rw [e]; simp
  | succ j ih =>
    rw [e, map_add (f := _), coeff_C_mul, coeff_succ_mul_X, ih, pow_succ]
    simp [coeff_one, mul_comm]

theorem coeff_prod_one_sub {n : ℕ} (β : Fin n → ℂ) (r : ℕ) :
    coeff r (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) =
      (-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i := by
  classical
  have e : ∀ t : Finset (Fin n), ∏ i ∈ t, (-(C (β i) * X) : ℂ⟦X⟧) =
      C ((-1) ^ t.card * ∏ i ∈ t, β i) * X ^ t.card := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, ih, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
  have e2 : (∏ i, (1 - C (β i) * X) : ℂ⟦X⟧) = ∏ i, (1 + -(C (β i) * X)) := by
    simp only [sub_eq_add_neg]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, Finset.prod_one_add, map_sum, Finset.powersetCard_eq_filter, Finset.sum_filter,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [e, coeff_C_mul, coeff_X_pow]
  by_cases h : r = t.card
  · subst h; simp
  · rw [if_neg h, if_neg (fun h' => h h'.symm)]; simp

theorem mk_mul_prod_eq_one {n : ℕ} (β : Fin n → ℂ) (g : ℕ → ℂ) (h0 : g 0 = 1)
    (hrec : ∀ j : ℕ, 1 ≤ j → ∑ r ∈ Finset.range (j + 1),
      ((-1) ^ r * ∑ S ∈ Finset.powersetCard r Finset.univ, ∏ i ∈ S, β i) * g (j - r) = 0) :
    (PowerSeries.mk g : ℂ⟦X⟧) * ∏ i, (1 - C (β i) * X) = 1 := by
  ext j
  rw [mul_comm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_sub, coeff_mk]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [h0, coeff_one]
  · rw [hrec j hj, coeff_one, if_neg (by omega)]

end GlobalTheory.CompanionTheory.SatakeBound

theorem GlobalTheory.CompanionTheory.SatakeBound.norm_lt_one : liftZP_newton := by
  intro n β g h0 hrec hg i
  classical
  have hG := GlobalTheory.CompanionTheory.SatakeBound.mk_mul_prod_eq_one β g h0 hrec
  have hc : Filter.Tendsto (fun j => PowerSeries.coeff j (PowerSeries.mk g : PowerSeries ℂ))
      Filter.atTop (nhds 0) := by
    simpa [PowerSeries.coeff_mk] using hg
  have hH := GlobalTheory.CompanionTheory.SatakeBound.tendsto_coeff_mul_prod _ (Finset.univ.erase i) β hc
  have hone : ((PowerSeries.mk g : PowerSeries ℂ) *
      ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) *
      (1 - PowerSeries.C (β i) * PowerSeries.X) = 1 := by
    have hs := Finset.mul_prod_erase Finset.univ
      (fun k => (1 - PowerSeries.C (β k) * PowerSeries.X : PowerSeries ℂ)) (Finset.mem_univ i)
    calc _ = (PowerSeries.mk g : PowerSeries ℂ) * ((1 - PowerSeries.C (β i) * PowerSeries.X) *
          ∏ k ∈ Finset.univ.erase i, (1 - PowerSeries.C (β k) * PowerSeries.X)) := by ring
      _ = 1 := by rw [hs, hG]
  have hp := GlobalTheory.CompanionTheory.SatakeBound.coeff_eq_pow_of_mul_one_sub _ _ hone
  simp only [hp] at hH
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 hH
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaCIntLtrSubThetaCConst
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.AdelicThetaSeries

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

namespace ThcInt

theorem scalC_mul (a b : IdeleGroup k) :
    (scalC (a * b) : GL ι 𝔸[k]) = scalC a * scalC b := by
  simp only [scalC, map_mul]

theorem scalC_commute (a : IdeleGroup k) (A : GL ι 𝔸[k]) :
    (scalC a : GL ι 𝔸[k]) * A = A * scalC a := by
  apply Units.ext
  simp only [Units.val_mul, scalC, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact (Matrix.scalar_commute _ (fun r ↦ Commute.all _ r) _)

theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  refine Continuous.units_map _ ?_
  refine continuous_matrix fun i j ↦ ?_
  by_cases h : i = j
  · subst h
    simpa [Matrix.scalar_apply] using continuous_id'
  · simpa [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ h] using continuous_const

theorem thetaC_ltr (A h : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    thetaC (ltr A F) h = thetaC F (A * h) := by
  simp only [thetaC, ltr, Units.val_mul, Matrix.mulVec_mulVec]

theorem ltr_apply_zero (A : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) : ltr A F 0 = F 0 := by
  simp [ltr]

theorem continuousOn_thetaC {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι))
    {C : Set (GL ι 𝔸[k])} (hC : IsCompact C) : ContinuousOn (thetaC F) C := by
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF hC
  refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hb h hh ξ
  refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
  exact Units.continuous_val.matrix_mulVec continuous_const

theorem continuous_char (ω : HeckeCharacter k) :
    Continuous fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ) :=
  continuous_subtype_val.comp (ω.continuous_toIdele.comp continuous_subtype_val)

theorem integrableOn_thetaCIntegrand {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι))
    (A : GL ι 𝔸[k]) (ω : HeckeCharacter k) (s : IdeleGroup k) :
    IntegrableOn (fun u : normOneSubgroup k ↦
      thetaC (ltr A F) (scalC (s * (u : IdeleGroup k))) * (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hφ : Continuous fun u : normOneSubgroup k ↦
      A * (scalC (s * (u : IdeleGroup k)) : GL ι 𝔸[k]) :=
    continuous_const.mul (continuous_scalC.comp (continuous_const.mul continuous_subtype_val))
  have h1 : ContinuousOn (fun u : normOneSubgroup k ↦
      thetaC (ltr A F) (scalC (s * (u : IdeleGroup k))))
      (closure (normOneFundamentalDomain k)) := by
    simp only [thetaC_ltr]
    exact (continuousOn_thetaC hF (hE.image hφ)).comp hφ.continuousOn (Set.mapsTo_image _ _)
  exact ((h1.mul (continuous_char ω).continuousOn).integrableOn_compact hE).mono_set subset_closure

theorem integrableOn_char' (ω : HeckeCharacter k) :
    IntegrableOn (fun u : normOneSubgroup k ↦ (ω.toIdele (u : IdeleGroup k) : ℂ))
      (normOneFundamentalDomain k) (normOneMeasure k) :=
  ((continuous_char ω).continuousOn.integrableOn_compact
    (isCompact_closure_normOneFundamentalDomain k)).mono_set subset_closure

theorem thetaCInt_ltr_sub_thetaCConst (w : InfinitePlace k) {F : (ι → 𝔸[k]) → ℂ}
    (hF : F ∈ schwartzBruhatPi (K := k) (ι := ι)) (A : GL ι 𝔸[k]) (ω : HeckeCharacter k)
    (t : {r : ℝ // 0 < r}) :
    thetaCInt w (ltr A F) ω t - thetaCConst (ltr A F) ω =
      ∫ u in normOneFundamentalDomain k,
        (thetaC (ltr A F) (scalC (moduleSection w t * (u : IdeleGroup k))) - ltr A F 0) *
          (ω.toIdele (u : IdeleGroup k) : ℂ) ∂normOneMeasure k := by
  rw [thetaCInt, thetaCConst, volChar, ← integral_const_mul,
    ← integral_sub (integrableOn_thetaCIntegrand hF A ω _) ((integrableOn_char' ω).const_mul _)]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  simp only []
  ring

end ThcInt


open ThcInt in
theorem exists_norm_thetaCInt_sub_le (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi (K := k) (ι := ι)) (ω : HeckeCharacter k) {C : Set (GL ι 𝔸[k])}
    (hC : IsCompact C) (r : ℕ) :
    ∃ M : ℝ, ∀ A ∈ C, ∀ t : {x : ℝ // 0 < x}, 1 ≤ (t : ℝ) →
      ‖thetaCInt w (ltr A Ψ) ω t - thetaCConst (ltr A Ψ) ω‖ ≤ ((t : ℝ) ^ r)⁻¹ * M := by
  have hE := isCompact_closure_normOneFundamentalDomain k
  have hS : Continuous fun p : normOneSubgroup k × GL ι 𝔸[k] ↦
      p.2 * (scalC (p.1 : IdeleGroup k) : GL ι 𝔸[k]) :=
    continuous_snd.mul (continuous_scalC.comp (continuous_subtype_val.comp continuous_fst))
  obtain ⟨M, hM⟩ := GlobalTheory.T.theta_sub_value_zero_rapid_decay w hΨ ((hE.prod hC).image hS) r
  refine ⟨M * (normOneMeasure k).real (normOneFundamentalDomain k), fun A hA t ht ↦ ?_⟩
  rw [thetaCInt_ltr_sub_thetaCConst w hΨ A ω t, ← mul_assoc]
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top k)
    fun u hu ↦ ?_
  have hc : A * (scalC (moduleSection w t * (u : IdeleGroup k)) : GL ι 𝔸[k]) =
      scalC (moduleSection w t) * (A * scalC (u : IdeleGroup k)) := by
    rw [scalC_mul, ← mul_assoc, ← mul_assoc, scalC_commute]
  rw [norm_mul, Circle.norm_coe, mul_one, thetaC_ltr, ltr_apply_zero, hc]
  exact hM _ ⟨(u, A), ⟨subset_closure hu, hA⟩, rfl⟩ t ht

end GlobalTheory.CompanionTheory.AdelicThetaSeries
end
