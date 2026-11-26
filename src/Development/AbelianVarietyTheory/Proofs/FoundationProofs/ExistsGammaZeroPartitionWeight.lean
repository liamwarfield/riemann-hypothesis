module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerUnitsFiniteModPowersAtLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionCoeffMemNonunits
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinsetSpanPrincipalCongruenceLevelFunction
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGammaZeroPartitionWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteSlTwoSmulMemFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteSlTwoSmulMemFundamentalDomain
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem finite_smul_mem_fd : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  intro τ
  have hP : {p : Fin 2 → ℤ | ¬ (2 * τ.im < Complex.normSq ((p 0 : ℂ) * τ + p 1))}.Finite :=
    Filter.eventually_cofinite.1
      ((ModularGroup.tendsto_normSq_coprime_pair τ).eventually_gt_atTop (2 * τ.im))
  have hrow : ∀ p : Fin 2 → ℤ, {γ : SL(2, ℤ) | γ 1 = p ∧ |(γ • τ).re| ≤ 1 / 2}.Finite := by
    intro p
    by_cases hp : IsCoprime (p 0) (p 1)
    · have h := Filter.eventually_cofinite.1
        ((ModularGroup.tendsto_abs_re_smul τ hp).eventually_gt_atTop (1 / 2 : ℝ))
      refine (h.image Subtype.val).subset ?_
      rintro γ ⟨h1, h2⟩
      exact ⟨⟨γ, h1⟩, not_lt.2 h2, rfl⟩
    · refine Set.finite_empty.subset ?_
      rintro γ ⟨h1, -⟩
      exact hp (h1 ▸ ModularGroup.bottom_row_coprime γ)
  refine (hP.biUnion fun p _ => hrow p).subset ?_
  intro γ hγ
  have h3 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hγ
  have hpos := (γ • τ).im_pos
  have hhalf : (1 : ℝ) / 2 ≤ (γ • τ).im := by nlinarith
  rw [ModularGroup.im_smul_eq_div_normSq, le_div_iff₀ (Complex.normSq_pos.2 (denom_ne_zero _ _))] at hhalf
  rw [Set.mem_iUnion₂]
  refine ⟨γ 1, ?_, rfl, hγ.2⟩
  simp only [Set.mem_setOf_eq, not_lt]
  simp [UpperHalfPlane.denom] at hhalf ⊢
  linarith

end GlobalTheory.EisM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteSlTwoSmulMemFundamentalDomainStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_slTwo_smul_mem_fundamentalDomain : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  first | exact @GlobalTheory.EisM.finite_smul_mem_fd | exact GlobalTheory.EisM.finite_smul_mem_fd | (intros; apply GlobalTheory.EisM.finite_smul_mem_fd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGammaZeroPartitionWeight
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

lemma wt_countable : Countable SL(2, ℤ) := by
  have : Function.Injective (fun g : SL(2, ℤ) => fun i j => (g : Matrix (Fin 2) (Fin 2) ℤ) i j) := by
    intro g h e; ext i j; exact congrFun (congrFun e i) j
  exact this.countable

lemma wt_cont (g : SL(2, ℤ)) : Continuous (fun τ : ℍ => g • τ) :=
  continuous_const_smul (g : GL (Fin 2) ℝ)

lemma wt_fd_closed : IsClosed ModularGroup.fd := by
  have h1 : IsClosed {z : ℍ | 1 ≤ normSq (z : ℂ)} :=
    isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have h2 : IsClosed {z : ℍ | |z.re| ≤ 1 / 2} :=
    isClosed_le (continuous_abs.comp (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)) continuous_const
  exact h1.inter h2

theorem wt_exists : ∀ L : ℕ, 0 < L → ∃ ρ, Wt L ρ := by
  intro L hL
  haveI : NeZero L := ⟨hL.ne'⟩
  haveI := wt_countable
  haveI hfin : Finite (SL(2, ℤ) ⧸ Gamma0 L) := Subgroup.finite_quotient_of_finiteIndex
  set S : Finset SL(2, ℤ) := (Set.finite_range (fun q : SL(2, ℤ) ⧸ Gamma0 L => q.out)).toFinset with hS
  have hcov : ∀ g : SL(2, ℤ), ∃ s ∈ S, ∃ γ ∈ Gamma0 L, g = s * γ := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Gamma0 L) g
    refine ⟨(QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma0 L).out, by simp [hS], ((h⁻¹ : Gamma0 L) : SL(2, ℤ)), (h⁻¹).2, ?_⟩
    rw [hh]; simp
  set K : Set ℍ := {τ | ∃ s ∈ S, s • τ ∈ ModularGroup.fd} with hK
  have hKm : MeasurableSet K := by
    have : K = ⋃ s ∈ S, (fun τ : ℍ => s • τ) ⁻¹' ModularGroup.fd := by
      ext τ; simp [hK]
    rw [this]
    exact Finset.measurableSet_biUnion _ fun s _ => (wt_fd_closed.preimage (wt_cont s)).measurableSet
  have hKfin : ∀ τ : ℍ, {γ : Gamma0 L | (γ : SL(2, ℤ)) • τ ∈ K}.Finite := by
    intro τ
    have h1 : {g : SL(2, ℤ) | g • τ ∈ K}.Finite := by
      have : {g : SL(2, ℤ) | g • τ ∈ K} = ⋃ s ∈ S, (fun g => s * g) ⁻¹' {g | g • τ ∈ ModularGroup.fd} := by
        ext g; simp [hK, mul_smul]
      rw [this]
      exact Set.Finite.biUnion S.finite_toSet fun s _ =>
        (GlobalTheory.T.finite_slTwo_smul_mem_fundamentalDomain τ).preimage (mul_right_injective s).injOn
    exact Set.Finite.preimage (f := (Subtype.val : Gamma0 L → SL(2, ℤ))) Subtype.val_injective.injOn h1
  have hKne : ∀ τ : ℍ, ∃ γ : Gamma0 L, (γ : SL(2, ℤ)) • τ ∈ K := by
    intro τ
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd τ
    obtain ⟨s, hs, γ, hγ, rfl⟩ := hcov g
    exact ⟨⟨γ, hγ⟩, s, hs, by rwa [mul_smul] at hg⟩
  let N : ℍ → ENNReal := fun τ => ∑' γ : Gamma0 L, K.indicator (1 : ℍ → ENNReal) ((γ : SL(2, ℤ)) • τ)
  have hNm : Measurable N := by
    refine Measurable.tsum fun γ => ?_
    exact (measurable_one.indicator hKm).comp (wt_cont (γ : SL(2, ℤ))).measurable
  have hNcard : ∀ τ, N τ = ((hKfin τ).toFinset.card : ENNReal) := by
    intro τ
    simp only [N]
    rw [tsum_eq_sum (s := (hKfin τ).toFinset)]
    · rw [Finset.card_eq_sum_ones, Nat.cast_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      rw [Set.indicator_of_mem hγ]; simp
    · intro γ hγ
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      rw [Set.indicator_of_notMem hγ]
  have hNinv : ∀ (γ : Gamma0 L) τ, N ((γ : SL(2, ℤ)) • τ) = N τ := by
    intro γ τ
    simp only [N]
    rw [← (Equiv.mulRight γ).tsum_eq (fun δ : Gamma0 L => K.indicator (1 : ℍ → ENNReal) ((δ : SL(2, ℤ)) • τ))]
    simp [mul_smul]
  let ρ : ℍ → ℝ := fun τ => K.indicator (fun τ => ((N τ).toReal)⁻¹) τ
  refine ⟨ρ, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (ENNReal.measurable_toReal.comp hNm).inv.indicator hKm
  · intro τ; simp only [ρ]; apply Set.indicator_nonneg; intro τ _; positivity
  · intro τ
    have hz : ∀ γ ∉ (hKfin τ).toFinset, ρ ((γ : SL(2, ℤ)) • τ) = 0 := by
      intro γ hγ
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
      simp only [ρ]; rw [Set.indicator_of_notMem hγ]
    have hpos : 0 < (hKfin τ).toFinset.card := by
      obtain ⟨γ, hγ⟩ := hKne τ
      exact Finset.card_pos.mpr ⟨γ, by simpa using hγ⟩
    have heq : ∑ γ ∈ (hKfin τ).toFinset, ρ ((γ : SL(2, ℤ)) • τ) = 1 := by
      rw [Finset.sum_congr rfl (g := fun _ => (((hKfin τ).toFinset.card : ℝ))⁻¹)]
      · rw [Finset.sum_const, nsmul_eq_mul]
        have : ((hKfin τ).toFinset.card : ℝ) ≠ 0 := by positivity
        field_simp
      · intro γ hγ
        have hγ' : (γ : SL(2, ℤ)) • τ ∈ K := by
          simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ; exact hγ
        simp only [ρ]
        rw [Set.indicator_of_mem hγ', hNinv, hNcard]
        simp
    exact heq ▸ hasSum_sum_of_ne_finset_zero hz
  · refine ⟨S, fun τ hτ => ?_⟩
    have : τ ∈ K := by
      by_contra h; exact hτ (by simp only [ρ]; rw [Set.indicator_of_notMem h])
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGammaZeroPartitionWeightStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gammaZeroPartitionWeight : ∀ L : ℕ, 0 < L → ∃ ρ, Wt L ρ := by
  first | exact @GlobalTheory.wt_exists | exact GlobalTheory.wt_exists | (intros; apply GlobalTheory.wt_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CoprimeFactorizationUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CoprimeFactorizationUnique
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

theorem sl2_right_factor_of_coprime_factorizations :
    ∀ (a c : ℤ), IsCoprime a c → c ≠ 0 → ∀ (y y' β β' : Matrix (Fin 2) (Fin 2) ℤ),
      y.det = a → y'.det = a → β.det = c → β'.det = c → y * β = y' * β' →
      ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * β = β' := by
  intro a c hac hc y y' β β' hy hy' hβ hβ' hyβ
  set P : Matrix (Fin 2) (Fin 2) ℤ := β' * adjugate β with hP
  set Q : Matrix (Fin 2) (Fin 2) ℤ := adjugate y' * y with hQ
  have hPQ : a • P = c • Q := by
    have h1 : adjugate y' * y * β = a • β' := by
      rw [Matrix.mul_assoc, hyβ, ← Matrix.mul_assoc, adjugate_mul, hy', Matrix.smul_mul, Matrix.one_mul]
    have h2 : β * adjugate β = c • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [mul_adjugate, hβ]
    calc a • P = (a • β') * adjugate β := by rw [hP, Matrix.smul_mul]
      _ = adjugate y' * y * β * adjugate β := by rw [h1]
      _ = Q * (β * adjugate β) := by rw [hQ, Matrix.mul_assoc]
      _ = c • Q := by rw [h2, Matrix.mul_smul, Matrix.mul_one]
  have hdiv : ∀ i j, c ∣ P i j := by
    intro i j
    have := congrFun (congrFun hPQ i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact hac.symm.dvd_of_dvd_mul_left ⟨Q i j, this⟩
  choose M hM using hdiv
  set Mm : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of M with hMm
  have hPM : P = c • Mm := by
    ext i j; simp [hMm, hM i j]
  have hMβ : Mm * β = β' := by
    have : c • (Mm * β) = c • β' := by
      rw [← Matrix.smul_mul, ← hPM, hP, Matrix.mul_assoc, adjugate_mul, hβ, Matrix.mul_smul, Matrix.mul_one]
    ext i j
    have := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  have hdet : Mm.det = 1 := by
    have h1 : P.det = c * c := by
      rw [hP, det_mul, det_adjugate, hβ, hβ']
      simp
    rw [hPM, det_smul] at h1
    simp at h1
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    have : c ^ 2 * Mm.det = c ^ 2 * 1 := by rw [h1]; ring
    exact mul_left_cancel₀ hc2 this
  exact ⟨⟨Mm, hdet⟩, hMβ⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CoprimeFactorizationUniqueStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sl2_mul_eq_of_coprime_det_factorization : ∀ (a c : ℤ), IsCoprime a c → c ≠ 0 → ∀ (y y' β β' : Matrix (Fin 2) (Fin 2) ℤ), y.det = a → y'.det = a → β.det = c → β'.det = c → y * β = y' * β' → ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * β = β' := by
  first | exact @GlobalTheory.sl2_right_factor_of_coprime_factorizations | exact GlobalTheory.sl2_right_factor_of_coprime_factorizations | (intros; apply GlobalTheory.sl2_right_factor_of_coprime_factorizations <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationUniqueOnLthRootLevelFields
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionUniqueOfGauss
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionUniqueOfGauss
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.BertiniNoether

theorem gauss_extension_unique_of_gauss : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, Gauss t V W₁ → Gauss t V W₂ → W₁ = W₂ := by
  intro F _ _ _ _ L _ _ t ht hfin
  obtain ⟨Φ, ω, hmon, hirr, hroot, hspan⟩ := GlobalTheory.FunctionFieldPrimitive.exists_integral_primitive t ht hfin
  obtain ⟨s, Ψ₀, hΨ₀, hgr⟩ := GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation Φ hmon hirr
  obtain ⟨S, hS⟩ := GlobalTheory.exists_finset_primes_forall_mem_valuationSubring s
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ => ?_⟩
  have hcl : Subring.closure (s : Set F) ≤ V.toSubring :=
    (Subring.closure_le).2 (fun x hx => hS q hq hqS V hV x hx)
  let ι : Subring.closure (s : Set F) →+* V :=
    { toFun := fun x => ⟨x.1, hcl x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : V.subtype.comp ι = (Subring.closure (s : Set F)).subtype := RingHom.ext fun _ => rfl
  set Ψ := Ψ₀.map (Polynomial.mapRingHom ι) with hΨdef
  have hΨ : Ψ.map (Polynomial.mapRingHom V.subtype) = Φ := by
    rw [hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp, hcomp, hΨ₀]
  have hinj : Function.Injective (Polynomial.mapRingHom V.subtype) :=
    Polynomial.map_injective _ (fun a b h => Subtype.ext h)
  have hΨmon : Ψ.Monic := Polynomial.monic_of_injective hinj (by rw [hΨ]; exact hmon)
  have hdeg : Ψ.natDegree = Φ.natDegree := by
    rw [← hΨ, Polynomial.natDegree_map_eq_of_injective hinj]
  have hgrV : ∀ (k : Type) [Field k] (φ : V →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
      A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
    intro k _ φ A B hA hB hAB
    refine hgr k (φ.comp ι) A B hA hB ?_
    rw [hAB, hΨdef, Polynomial.map_map, Polynomial.mapRingHom_comp]
  have hcoef : ∀ i j, (Φ.coeff i).coeff j ∈ V := by
    intro i j; rw [← hΨ]; simp only [Polynomial.coeff_map, Polynomial.coe_mapRingHom]
    exact ((Ψ.coeff i).coeff j).2
  have hrootΨ : (Ψ.map (Polynomial.mapRingHom V.subtype)).eval₂ (Polynomial.aeval t).toRingHom ω = 0 := by
    rw [hΨ]; exact hroot
  have key : ∀ W : ValuationSubring L, Gauss t V W →
      ∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits := by
    intro W hW R hR
    exact GlobalTheory.gaussExtension_coeff_mem_nonunits t V W hW.1 hW.2 Ψ ω hΨmon hrootΨ hgrV R (hdeg ▸ hR)
  exact le_antisymm (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₁ W₂ h₁ h₂ (key W₁ h₁))
    (GlobalTheory.BertiniNoether.le_of_residue_independent t V Φ ω hmon hcoef hroot hspan W₂ W₁ h₂ h₁ (key W₂ h₂))

end GlobalTheory.BertiniNoether
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussExtensionUniqueOfGaussStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gauss_valuationSubring_unique_away_finset : ∀ {F : Type} [Field F] [CharZero F] [IsAlgClosed F] [Algebra.IsAlgebraic ℚ F] {L : Type} [Field L] [Algebra F L] (t : L), Transcendental F t → FiniteDimensional (IntermediateField.adjoin F {t}) L → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring F, ((q : ℕ) : F) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring L, Gauss t V W₁ → Gauss t V W₂ → W₁ = W₂ := by
  first | exact @GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss | exact GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss | (intros; apply GlobalTheory.BertiniNoether.gauss_extension_unique_of_gauss <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationUniqueOnLthRootLevelFields
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.UniqRoot

theorem exists_finite_field {F E : Type} [Field F] [Field E] [Algebra F E] (t : E) (A : Set E) (hfin : A.Finite)
    (hA : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin F {t}) a) :
    ∃ (L : IntermediateField F E) (ht : t ∈ L), A ⊆ L ∧
      FiniteDimensional (IntermediateField.adjoin F {(⟨t, ht⟩ : L)}) L := by
  let K₀ : IntermediateField F E := IntermediateField.adjoin F {t}
  let L' : IntermediateField K₀ E := IntermediateField.adjoin K₀ A
  haveI : Finite A := hfin
  have hL' : FiniteDimensional K₀ L' := IntermediateField.finiteDimensional_adjoin fun a ha => (hA a ha).isIntegral
  let L : IntermediateField F E := L'.restrictScalars F
  have hK : ∀ x : K₀, (x : E) ∈ L := fun x => L'.algebraMap_mem x
  have ht : t ∈ L := hK ⟨t, IntermediateField.mem_adjoin_simple_self F t⟩
  refine ⟨L, ht, fun a ha => IntermediateField.subset_adjoin K₀ A ha, ?_⟩
  let K' : IntermediateField F L := IntermediateField.adjoin F {(⟨t, ht⟩ : L)}
  have hmap : K'.map L.val = K₀ := by
    simp only [K', K₀, IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ x : K₀, (⟨x, hK x⟩ : L) ∈ K' := by
    intro x
    have hx : (x : E) ∈ K'.map L.val := by rw [hmap]; exact x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = ⟨x, hK x⟩ := Subtype.ext hyx
    exact this ▸ hy
  let φ : K₀ →+* K' :=
    { toFun := fun x => ⟨⟨x, hK x⟩, hmem x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  letI : Algebra K₀ K' := φ.toAlgebra
  letI : Algebra K₀ L := (inferInstance : Algebra K₀ L')
  haveI : Module.Finite K₀ L := hL'
  haveI : IsScalarTower K₀ K' L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K₀ K' L

theorem valuation_eq_one_iff' {K : Type} [Field K] (W : ValuationSubring K) (x : K) :
    W.valuation x = 1 ↔ x ≠ 0 ∧ x ∈ W ∧ x⁻¹ ∈ W := by
  rw [← W.valuation_le_one_iff, ← W.valuation_le_one_iff, map_inv₀]
  constructor
  · intro h
    refine ⟨?_, h.le, by rw [h, inv_one]⟩
    rintro rfl
    simp at h
  · rintro ⟨h0, h1, h2⟩
    have hp : 0 < W.valuation x := zero_lt_iff.2 ((map_ne_zero _).2 h0)
    exact le_antisymm h1 ((inv_le_one₀ hp).1 h2)

theorem gauss_comap {F E : Type} [Field F] [Field E] [Algebra F E] {t : E} (L : IntermediateField F E) (ht : t ∈ L)
    {V : ValuationSubring F} {W : ValuationSubring E} (h : Gauss t V W) :
    Gauss (⟨t, ht⟩ : L) V (W.comap (algebraMap L E)) := by
  refine ⟨fun a => ?_, fun P hP hu => ?_⟩
  · rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact h.1 a
  · have h1 := (valuation_eq_one_iff' _ _).1 (h.2 P hP hu)
    have e : algebraMap L E (Polynomial.aeval (⟨t, ht⟩ : L) P) = Polynomial.aeval t P :=
      (Polynomial.aeval_algHom_apply L.val (⟨t, ht⟩ : L) P).symm
    rw [valuation_eq_one_iff', ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, e]
    refine ⟨fun h0 => h1.1 ?_, h1.2⟩
    rw [← e, h0, map_zero]

theorem transcendental_j {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  intro h
  have hd := IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible h.isIntegral)
  obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one Ω X.jK hd
  have h1 := X.j_exp.1
  rw [← hc, AlgHom.commutes] at h1
  simp [HahnSeries.algebraMap_apply', HahnSeries.coeff_single] at h1

theorem gauss_unique_root : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring (AlgebraicClosure X.K), Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₁ → Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₂ → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), f ∈ X.Un l → Lev X M₀ f → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → ∀ x ∈ IntermediateField.adjoin (levF X M₀) {θ}, x ∈ W₁ ↔ x ∈ W₂ := by
  classical
  intro Ω _ _ _ ε X hj l M₀ hl hM
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have halgΩ : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by
    convert halgΩ
    exact Subsingleton.elim _ _
  obtain ⟨R, hR⟩ := GlobalTheory.KZ.FinLev.finite_mod_powers ε X ε.injective hj M₀ l hM hl.pos
  obtain ⟨T, -, hT⟩ := GlobalTheory.T.exists_finset_span_principalCongruenceLevel_functions ε X hj M₀ hM
  let E := AlgebraicClosure X.K
  let ι : X.K →ₐ[Ω] E := IsScalarTower.toAlgHom Ω X.K E
  let t : E := algebraMap X.K E X.jK
  have hmap : (IntermediateField.adjoin Ω {X.jK}).map ι = IntermediateField.adjoin Ω {t} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin Ω {X.jK}, ι c ∈ IntermediateField.adjoin Ω {t} :=
    fun c => hmap ▸ ⟨c, c.2, rfl⟩
  have halg : ∀ f : X.K, IsAlgebraic (IntermediateField.adjoin Ω {t}) (algebraMap X.K E f) := by
    intro f
    let φ : IntermediateField.adjoin Ω {X.jK} →+* IntermediateField.adjoin Ω {t} :=
      (ι.toRingHom.comp (algebraMap (IntermediateField.adjoin Ω {X.jK}) X.K)).codRestrict
        (IntermediateField.adjoin Ω {t}) hmem
    exact ((X.alg_j f).isIntegral.map_of_comp_eq φ (algebraMap X.K E) (RingHom.ext fun _ => rfl)).isAlgebraic
  let A : Set E := algebraMap X.K E '' (T : Set X.K) ∪
    ⋃ r ∈ (R : Set X.Kˣ), {y : E | y ^ l = algebraMap X.K E (r : X.K)}
  have hAfin : A.Finite := by
    refine (T.finite_toSet.image _).union (R.finite_toSet.biUnion fun r _ => ?_)
    refine (Polynomial.nthRoots l (algebraMap X.K E (r : X.K))).toFinset.finite_toSet.subset fun y hy => ?_
    simpa [Polynomial.mem_nthRoots hl.pos] using hy
  have hAalg : ∀ a ∈ A, IsAlgebraic (IntermediateField.adjoin Ω {t}) a := by
    rintro a (⟨f, -, rfl⟩ | ha)
    · exact halg f
    · simp only [Set.mem_iUnion, Set.mem_setOf_eq] at ha
      obtain ⟨r, -, hr⟩ := ha
      exact IsAlgebraic.of_pow hl.pos (hr ▸ halg r)
  obtain ⟨L, ht, hAL, hfin⟩ := exists_finite_field (F := Ω) t A hAfin hAalg
  have htr : Transcendental Ω (⟨t, ht⟩ : L) := by
    intro h
    have h1 : IsAlgebraic Ω (ι X.jK) := h.algHom L.val
    exact transcendental_j X ((isAlgebraic_algHom_iff ι ι.toRingHom.injective).1 h1)
  obtain ⟨S, hS⟩ := GlobalTheory.T.gauss_valuationSubring_unique_away_finset (F := Ω) (⟨t, ht⟩ : L) htr hfin
  have hlev : ∀ f : X.K, Lev X M₀ f → algebraMap X.K E f ∈ L := by
    intro f hf
    have hsp := hT f hf
    clear hf
    induction hsp using Submodule.span_induction with
    | mem x hx => exact hAL (Or.inl ⟨x, hx, rfl⟩)
    | zero => rw [map_zero]; exact L.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact L.add_mem hx hy
    | smul c x _ hx =>
      have hc : ι c ∈ L := (IntermediateField.adjoin_simple_le_iff.2 ht) (hmem c)
      have e : algebraMap X.K E (c • x) = ι c * algebraMap X.K E x := by
        rw [IntermediateField.smul_def, smul_eq_mul, map_mul]
        rfl
      rw [e]
      exact L.mul_mem hc hx
  have hlevF : levF X M₀ ≤ L := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨f, hf, rfl⟩
    exact hlev f hf
  refine ⟨S, fun q hq hqS V hV W₁ W₂ h₁ h₂ θ f hf hfl hθ x hx => ?_⟩
  have hW := hS q hq hqS V hV _ _ (gauss_comap L ht h₁) (gauss_comap L ht h₂)
  obtain ⟨r, hr, g, hg, c, hc, hfe⟩ := hR f hf hfl
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hl.pos
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_pow hl.ne_zero] at hd
    exact hc hd.symm
  let u : E := algebraMap X.K E (g : X.K) * algebraMap Ω E d
  have hu0 : u ≠ 0 := mul_ne_zero ((map_ne_zero _).2 g.ne_zero) ((map_ne_zero _).2 hd0)
  have huL : u ∈ L := L.mul_mem (hlev g hg) (L.algebraMap_mem d)
  have hy : (θ / u) ^ l = algebraMap X.K E (r : X.K) := by
    rw [div_pow, div_eq_iff (pow_ne_zero _ hu0), hθ, hfe, mul_pow, ← map_pow, ← map_pow, hd, map_mul, map_mul,
      ← IsScalarTower.algebraMap_apply, mul_assoc]
  have hθL : θ ∈ L := by
    have h1 : θ / u ∈ L := hAL (Or.inr (Set.mem_biUnion (Finset.mem_coe.2 hr) hy))
    have := L.mul_mem h1 huL
    rwa [div_mul_cancel₀ _ hu0] at this
  have hxL : x ∈ L := by
    have hle : IntermediateField.adjoin (levF X M₀) {θ} ≤ IntermediateField.extendScalars hlevF :=
      IntermediateField.adjoin_simple_le_iff.2 hθL
    exact hle hx
  have := SetLike.ext_iff.1 hW ⟨x, hxL⟩
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap] at this
  exact this

end GlobalTheory.KZ.ES.UniqRoot
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussValuationUniqueOnLthRootLevelFieldsStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussValuation_unique_on_lthRoot_level_fields : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l M₀ : ℕ), l.Prime → 0 < M₀ → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits → ∀ W₁ W₂ : ValuationSubring (AlgebraicClosure X.K), Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₁ → Gauss (algebraMap X.K (AlgebraicClosure X.K) X.jK) V W₂ → ∀ (θ : AlgebraicClosure X.K) (f : X.Kˣ), f ∈ X.Un l → Lev X M₀ f → θ ^ l = algebraMap X.K (AlgebraicClosure X.K) (f : X.K) → ∀ x ∈ IntermediateField.adjoin (levF X M₀) {θ}, x ∈ W₁ ↔ x ∈ W₂ := by
  first | exact @GlobalTheory.KZ.ES.UniqRoot.gauss_unique_root | exact GlobalTheory.KZ.ES.UniqRoot.gauss_unique_root | (intros; apply GlobalTheory.KZ.ES.UniqRoot.gauss_unique_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelGLengthConj
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelGLengthConj
noncomputable section

namespace GlobalTheory.SelConj

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations ReciprocityTheory.Gal TensorProduct

section Hf

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    {ρ ρ' : Representation LL G V} [TopologicalSpace G]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem blochKatoCocycle_map_equivariant (f : V →ₗ[LL] V) (hf : Continuous f) (he : ∀ g x, f (ρ g x) = ρ' g (f x))
    (c : G → V) (hc : c ∈ finiteCocycles PD ρ) : (fun g => f (c g)) ∈ finiteCocycles PD ρ' := by
  obtain ⟨⟨h1, h2⟩, x, hx⟩ := hc
  refine ⟨⟨hf.comp h1, fun g h => ?_⟩,
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B) x, fun g => ?_⟩
  · simp only [h2, map_add (f := _), he]
  · have e := congrArg (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[Qp] B)) (hx g)
    rw [map_sub, AlgebraTensorModule.map_tmul, LinearMap.id_apply] at e
    rw [e]
    congr 1
    clear e hx
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [actVB, he]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem hfD_map (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (f : V →ₗ[LL] V)
    (hf : Continuous f) (he : ∀ g x, f (ρ g x) = ρ' g (f x))
    (q : (V ⧸ L.T) → (V ⧸ L'.T)) (hadd : ∀ a b, q (a + b) = q a + q b)
    (hq : ∀ x, q (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x))
    (c : G → V ⧸ L.T) (hc : c ∈ HfD PD L) : (fun g => q (c g)) ∈ HfD PD L' := by
  obtain ⟨a, ⟨z, hz, rfl⟩, b, ⟨m, rfl⟩, rfl⟩ := Submodule.mem_sup.1 hc
  obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  refine Submodule.mem_sup.2 ⟨_, ⟨fun g => f (z g), blochKatoCocycle_map_equivariant PD f hf he z hz, rfl⟩, _,
    ⟨Submodule.Quotient.mk (f m), rfl⟩, ?_⟩
  funext g
  show Submodule.Quotient.mk (f (z g)) + Submodule.Quotient.mk (ρ' g (f m) - f m) =
    q (Submodule.Quotient.mk (z g) + Submodule.Quotient.mk (ρ g m - m))
  rw [hadd, hq, hq, map_sub, he]

end Hf

section Std

variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] {k : ℕ}

def qMat (LL : Type) [Field LL] [Algebra O LL] (U : Matrix (Fin k) (Fin k) O) :
    ((Fin k → LL) ⧸ stdG O LL k) →ₗ[O] ((Fin k → LL) ⧸ stdG O LL k) :=
  Submodule.mapQ _ _ ((U.map (algebraMap O LL)).mulVecLin.restrictScalars O) (by
    rintro _ ⟨u, rfl⟩
    refine ⟨U.mulVec u, ?_⟩
    funext j
    exact RingHom.map_mulVec (algebraMap O LL) U u j)

theorem qMat_mk (U : Matrix (Fin k) (Fin k) O) (x : Fin k → LL) :
    qMat LL U (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((U.map (algebraMap O LL)).mulVec x) := rfl

theorem qMat_mul (U U' : Matrix (Fin k) (Fin k) O) (x : (Fin k → LL) ⧸ stdG O LL k) :
    qMat LL U (qMat LL U' x) = qMat LL (U * U') x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [qMat_mk, qMat_mk, qMat_mk, Matrix.mulVec_mulVec, Matrix.map_mul]

theorem qMat_one (x : (Fin k → LL) ⧸ stdG O LL k) : qMat LL 1 x = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [qMat_mk, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]

end Std

section W

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {k : ℕ}

theorem wkg_apply (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) (x : KOG O k) :
    WKG M g x = qMat (FractionRing O) (M g) x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem qMat_equiv (M M' : Γ →* Matrix (Fin k) (Fin k) O) (U : Matrix (Fin k) (Fin k) O)
    (h : ∀ g, M' g * U = U * M g) (g : Γ) (x : KOG O k) :
    qMat (FractionRing O) U (WKG M g x) = WKG M' g (qMat (FractionRing O) U x) := by
  rw [wkg_apply, wkg_apply, qMat_mul, qMat_mul, h]

end W

section Coh

variable {R : Type} [CommRing R] {G : Type} [Group G] [TopologicalSpace G]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

theorem res_map (rho rho' : Representation R G M) (u : M →ₗ[R] M) (hu : Continuous u)
    (he : ∀ g m, u (rho g m) = rho' g (u m)) {H : Type} [Group H] [TopologicalSpace H]
    (phi : H →* G) (hphi : Continuous phi) (x : H1 rho) :
    resH1 rho' phi hphi (mapH1 rho rho' u hu he x) =
      mapH1 (rho.comp phi) (rho'.comp phi) u hu (fun g m => he (phi g) m)
        (resH1 rho phi hphi x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem ur_map (rho rho' : Representation R G M) (u : M →ₗ[R] M) (hu : Continuous u)
    (he : ∀ g m, u (rho g m) = rho' g (u m)) (J : Subgroup G) (x : H1 rho)
    (hx : x ∈ H1ur rho J) : mapH1 rho rho' u hu he x ∈ H1ur rho' J := by
  have hx' : resH1 rho J.subtype continuous_subtype_val x = 0 := hx
  exact (res_map rho rho' u hu he J.subtype continuous_subtype_val x).trans
    ((congrArg _ hx').trans (map_zero _))

theorem map_left_inv (rho rho' : Representation R G M) (u u' : M →ₗ[R] M) (hu : Continuous u)
    (hu' : Continuous u') (he : ∀ g m, u (rho g m) = rho' g (u m))
    (he' : ∀ g m, u' (rho' g m) = rho g (u' m)) (hi : ∀ m, u' (u m) = m) (x : H1 rho) :
    mapH1 rho' rho u' hu' he' (mapH1 rho rho' u hu he x) = x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  exact Subtype.ext (funext fun g => hi _)

end Coh

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O) [IsDomain O]

set_option synthInstance.maxHeartbeats 400000 in
theorem phi_qMat {k : ℕ} (U : Matrix (Fin k) (Fin k) O) (x : KOG O k) :
    Br.phi Bw k (qMat (FractionRing O) U x) =
      qMat (Br.LLw Bw) (U.map Bw.eO.toRingHom) (Br.phi Bw k x) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Submodule.Quotient.mk (Br.vecS Bw k ((U.map (algebraMap O (FractionRing O))).mulVec x)) =
    Submodule.Quotient.mk (((U.map Bw.eO.toRingHom).map
      (algebraMap (Br.Ow Bw) (Br.LLw Bw))).mulVec (Br.vecS Bw k x))
  congr 1
  funext j
  show Br.toLLK Bw (((U.map (algebraMap O (FractionRing O))).mulVec x) j) = _
  rw [RingHom.map_mulVec]
  congr 1
  exact Matrix.ext fun a b => Br.toLLK_alg Bw (U a b)

set_option synthInstance.maxHeartbeats 400000 in
theorem bk_map (P : LocPrime l) {k : ℕ} (rho rho' : Representation O ↥Gw (KOG O k))
    (M M' : ↥Gw →* Matrix (Fin k) (Fin k) O) (U : Matrix (Fin k) (Fin k) O)
    (h : ∀ g, M' g * U = U * M g) (hu : Continuous (qMat (FractionRing O) U))
    (he : ∀ g m, qMat (FractionRing O) U (rho g m) = rho' g (qMat (FractionRing O) U m))
    (x : H1 rho) (hx : x ∈ Br.bkG Bw P rho M) :
    mapH1 rho rho' (qMat (FractionRing O) U) hu he x ∈ Br.bkG Bw P rho' M' := by
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨cocycles1MapOfEquivariant rho rho' (qMat (FractionRing O) U) hu he c, ?_, rfl⟩
  have key := hfD_map (P.PD Bw.Kw) (Br.lat Bw M) (Br.lat Bw M')
    (((U.map Bw.eO.toRingHom).map (algebraMap (Br.Ow Bw) (Br.LLw Bw))).mulVecLin)
    (continuous_const.matrix_mulVec continuous_id) ?_
    (qMat (Br.LLw Bw) (U.map Bw.eO.toRingHom)) (map_add _) (fun _ => rfl) _ hc
  · have e : Br.Phi Bw rho' (cocycles1MapOfEquivariant rho rho' (qMat (FractionRing O) U) hu he c) =
        fun g => qMat (Br.LLw Bw) (U.map Bw.eO.toRingHom) (Br.Phi Bw rho c g) := by
      funext g
      exact phi_qMat Bw U _
    show Br.Phi Bw rho' (cocycles1MapOfEquivariant rho rho' (qMat (FractionRing O) U) hu he c) ∈
      HfD (P.PD Bw.Kw) (Br.lat Bw M')
    rw [e]
    exact key
  · intro g v
    show Matrix.mulVec ((U.map Bw.eO.toRingHom).map (algebraMap (Br.Ow Bw) (Br.LLw Bw)))
        (Matrix.mulVec (((M (Br.ι Bw g)).map Bw.eO.toRingHom).map
          (algebraMap (Br.Ow Bw) (Br.LLw Bw))) v) =
      Matrix.mulVec (((M' (Br.ι Bw g)).map Bw.eO.toRingHom).map
          (algebraMap (Br.Ow Bw) (Br.LLw Bw)))
        (Matrix.mulVec ((U.map Bw.eO.toRingHom).map (algebraMap (Br.Ow Bw) (Br.LLw Bw))) v)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Matrix.map_mul,
      ← Matrix.map_mul, ← Matrix.map_mul, h]

end Bridge

section Sel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω)
  (l : ℕ) [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (P : LocPrime l)
  (nb : ∀ w, w ∈ placesOver E l → LocBridge l E Ω (Dec (F := E) (A.1 w)) O)
  (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) {k : ℕ}

theorem sel_map (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : Matrix (Fin k) (Fin k) O)
    (h : ∀ g, M' g * U = U * M g) (x : H1 (WKG M)) (hx : x ∈ Br.selG A l P nb Sig M) :
    mapH1 (WKG M) (WKG M') (qMat (FractionRing O) U) continuous_of_discreteTopology
      (qMat_equiv M M' U h) x ∈ Br.selG A l P nb Sig M' := by
  refine (mem_Sel _ _ _ _ _).2 fun v => ?_
  have hv := (mem_Sel _ _ _ _ _).1 hx v
  refine (res_map (WKG M) (WKG M') (qMat (FractionRing O) U) continuous_of_discreteTopology
    (qMat_equiv M M' U h) (Dec (F := E) (A.1 v)).subtype continuous_subtype_val x).symm ▸ ?_
  unfold Formalism.GaloisCohomology.bkCond at hv ⊢
  split_ifs at hv ⊢ with h1 h2
  · unfold Br.LlG at hv ⊢
    split_ifs at hv ⊢ with h3
    · exact bk_map (nb v h3) P _ _ _ _ U (fun g => h g) _ _ _ hv
    · trivial
  · trivial
  · exact ur_map _ _ _ _ _ _ _ hv

theorem sel_le (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O)
    (U U' : Matrix (Fin k) (Fin k) O) (hi : U' * U = 1)
    (h : ∀ g, M' g * U = U * M g) (h' : ∀ g, M g * U' = U' * M' g) :
    Module.length O (Br.selG A l P nb Sig M) ≤ Module.length O (Br.selG A l P nb Sig M') := by
  refine Module.length_le_of_injective
    ((mapH1 (WKG M) (WKG M') (qMat (FractionRing O) U) continuous_of_discreteTopology
      (qMat_equiv M M' U h)).restrict (sel_map A l P nb Sig M M' U h)) ?_
  intro x y hxy
  apply Subtype.ext
  have e := congrArg (fun z => mapH1 (WKG M') (WKG M) (qMat (FractionRing O) U')
    continuous_of_discreteTopology (qMat_equiv M' M U' h') (Subtype.val z)) hxy
  have hi' : ∀ m, qMat (FractionRing O) U' (qMat (FractionRing O) U m) = m := fun m => by
    rw [qMat_mul, hi, qMat_one]
  simpa only [LinearMap.restrict_apply, map_left_inv _ _ _ _ _ _ _ _ hi'] using e

end Sel

theorem selG_length_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (P : LocPrime l) (nb : ∀ w, w ∈ Formalism.BasicNotions.placesOver E l → LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) (A.1 w)) O) (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (k : ℕ) (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : GL (Fin k) O), (∀ g, M' g * (U : Matrix (Fin k) (Fin k) O) = (U : Matrix (Fin k) (Fin k) O) * M g) → Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M) = Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M') := by
  intro E Ω _ _ _ _ A l _ O _ _ _ _ P nb Sig k M M' U h
  have h' : ∀ g, M g * ((U⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) =
      ((U⁻¹ : GL (Fin k) O) : Matrix (Fin k) (Fin k) O) * M' g := fun g => by
    rw [Units.mul_inv_eq_iff_eq_mul, mul_assoc, h, ← mul_assoc, Units.inv_mul, one_mul]
  exact le_antisymm (sel_le A l P nb Sig M M' _ _ (Units.inv_mul U) h h')
    (sel_le A l P nb Sig M' M _ _ (Units.mul_inv U) h' h)

end GlobalTheory.SelConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelGLengthConjStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selG_length_eq_of_conj : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : Formalism.GaloisCohomology.Places E Ω) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O] (P : LocPrime l) (nb : ∀ w, w ∈ Formalism.BasicNotions.placesOver E l → LocBridge l E Ω (ReciprocityTheory.Gal.Dec (F := E) (A.1 w)) O) (Sig : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))) (k : ℕ) (M M' : Formalism.ConjugateSelfDual.G E Ω →* Matrix (Fin k) (Fin k) O) (U : GL (Fin k) O), (∀ g, M' g * (U : Matrix (Fin k) (Fin k) O) = (U : Matrix (Fin k) (Fin k) O) * M g) → Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M) = Module.length O (Formalism.MainNotions.N.Br.selG A l P nb Sig M') := by
  first | exact @GlobalTheory.SelConj.selG_length_conj | exact GlobalTheory.SelConj.selG_length_conj | (intros; apply GlobalTheory.SelConj.selG_length_conj <;> assumption)
end
end
