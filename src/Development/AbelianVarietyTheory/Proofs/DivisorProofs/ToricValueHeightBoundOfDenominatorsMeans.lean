module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanValuationNormOverDegreeSmulEqAddValuation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanInfLogNormEmbeddingEqLogNormDiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanInfLogNormEmbeddingEqLogNormDiv
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory

theorem meanInf_log_norm_embedding (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : K) (ha : a ≠ 0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  have hprod := InfinitePlace.prod_eq_abs_norm (K := K) a
  have hmult : ∀ v : InfinitePlace K, v.mult = 2 := fun v => by
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v))]
  have hpos : ∀ v : InfinitePlace K, 0 < v a := fun v => by
    rw [InfinitePlace.pos_iff]; exact ha
  have hsum : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ v : InfinitePlace K, 2 * Real.log (v a) := by
    rw [show |((Algebra.norm ℚ a : ℚ) : ℝ)| = ((|Algebra.norm ℚ a| : ℚ) : ℝ) by push_cast; rfl, ← hprod, Real.log_prod]
    · refine Finset.sum_congr rfl fun v _ => ?_
      rw [hmult, Real.log_pow]; push_cast; ring
    · intro v _; exact pow_ne_zero _ (hpos v).ne'
  have he : ∀ v : InfinitePlace K, ‖v.embedding a‖ = v a := fun v => InfinitePlace.norm_embedding_eq v a
  simp only [he]
  rw [hsum, ← Finset.mul_sum]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeanInfLogNormEmbeddingEqLogNormDivStatement
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.meanInf_log_norm_embedding_eq_log_norm_div : ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (a : K), a ≠ 0 → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K := by
  first | exact @GlobalTheory.meanInf_log_norm_embedding | exact GlobalTheory.meanInf_log_norm_embedding | (intros; apply GlobalTheory.meanInf_log_norm_embedding <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMinpolyCoeffZeroGeOfPowMulIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMinpolyCoeffZeroGeOfPowMulIntegral
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.FunObj.SqNum.LowVal

theorem coeff_zero_mul_pow_mem {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {β : ℂ} {p : K[X]}
    (h : IsMinPol σ β p) {c : ℕ} (hc0 : (c : K) ≠ 0) (hc : IsIntegral ℤ ((c : ℂ) * β)) :
    ∃ a : 𝓞 K, p.coeff 0 * (c : K) ^ p.natDegree = (a : K) := by
  letI : Algebra K ℂ := σ.toAlgebra
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  haveI : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower ℤ (𝓞 K) ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hβ : IsIntegral K β := ⟨p, h.1, h.2.2⟩
  have es : (c : K) • β = (c : ℂ) * β := by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_natCast]
  have hγ : IsIntegral (𝓞 K) ((c : K) • β) := by
    rw [es]; exact hc.tower_top
  have e1 := IsIntegrallyClosed.minpoly_smul (R := K) hc0 hβ
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' K hγ
  rw [← h.eq_minpoly] at e1
  refine ⟨(minpoly (𝓞 K) ((c : K) • β)).coeff 0, ?_⟩
  rw [RingOfIntegers.coe_eq_algebraMap, ← coeff_map, ← e2, e1, coeff_scaleRoots, Nat.sub_zero]

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] {w : Formalism.PairingDivisionLocalBalance.Pl K} {l n : ℕ} (hn : n.Coprime l)
    (hw : (l : 𝓞 K) ∈ w.asIdeal) : (n : 𝓞 K) ∉ w.asIdeal := by
  intro h
  obtain ⟨x, y, e⟩ := (Nat.isCoprime_iff_coprime.2 hn).map (Int.castRingHom (𝓞 K))
  refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← e]
  exact add_mem (Ideal.mul_mem_left _ _ (by simpa using h)) (Ideal.mul_mem_left _ _ (by simpa using hw))

theorem vw_coeff_zero_ge : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (l N : ℕ),
    GlobalTheory.FunObj.SqNum.IsMinPol σ β p → l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ (N : ℤ) * β) →
    ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, (l : 𝓞 K) ∈ w.asIdeal → -(((N * p.natDegree : ℕ) : ℤ) * vw w (l : K)) ≤ vw w (p.coeff 0) := by
  intro K _ _ _ σ β p l N h hl ⟨n, hn, hi⟩ w hw
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hl.one_lt.ne' (Nat.coprime_zero_left l |>.1 hn)
  have hc : IsIntegral ℤ (((n * l ^ N : ℕ) : ℂ) * β) := by
    convert hi using 1
    push_cast
    rw [zpow_natCast]
    ring
  have hl0 : (l : K) ≠ 0 := by exact_mod_cast hl.ne_zero
  have hn0' : (n : K) ≠ 0 := by exact_mod_cast hn0
  have hc0 : ((n * l ^ N : ℕ) : K) ≠ 0 := by
    push_cast
    exact mul_ne_zero hn0' (pow_ne_zero _ hl0)
  obtain ⟨a, ha⟩ := coeff_zero_mul_pow_mem h hc0 hc
  have h1 : 0 ≤ vw w (p.coeff 0 * ((n * l ^ N : ℕ) : K) ^ p.natDegree) := by
    rw [ha]; exact Formalism.DivisionValues.ValuationRepresentative.vw_int_nonneg w a
  have hvn : vw w (n : K) = 0 := by
    have := Formalism.DivisionValues.ReductionFirst.vw_unit w (n : 𝓞 K) (natCast_not_mem hn hw)
    simpa using this
  have hvl := Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l
  by_cases hp0 : p.coeff 0 = 0
  · rw [hp0, Formalism.DivisionValues.ValuationRepresentative.vw_zero]
    have : (0 : ℤ) ≤ ((N * p.natDegree : ℕ) : ℤ) := Int.natCast_nonneg _
    nlinarith
  · rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hp0 (pow_ne_zero _ hc0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hc0] at h1
    push_cast at h1
    rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hn0' (pow_ne_zero _ hl0), Formalism.PairingDivisionLocalBalance.vw_pow w _ hl0, hvn] at h1
    push_cast
    nlinarith

end GlobalTheory.FunObj.SqNum.LowVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMinpolyCoeffZeroGeOfPowMulIntegralStatement
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_minpoly_coeff_zero_ge_of_pow_mul_integral : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (l N : ℕ), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ (N : ℤ) * β) → ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, (l : 𝓞 K) ∈ w.asIdeal → -(((N * p.natDegree : ℕ) : ℤ) * vw w (l : K)) ≤ vw w (p.coeff 0) := by
  first | exact @GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge | exact GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge | (intros; apply GlobalTheory.FunObj.SqNum.LowVal.vw_coeff_zero_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMinpolyCoeffZeroPowNumberField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMinpolyCoeffZeroPowNumberField
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)

namespace GlobalTheory.NormTower

open IntermediateField

theorem abs_norm_coeff_zero_pow (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X])
    (h : GlobalTheory.FunObj.SqNum.IsMinPol σ β p) (hβ : IsAlgebraic ℚ β) :
    |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree =
      |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  obtain ⟨hm, hirr, hev⟩ := h
  haveI := Fact.mk hirr
  let pb := AdjoinRoot.powerBasis hirr.ne_zero
  haveI : Module.Finite K (AdjoinRoot p) := pb.finite
  haveI : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans K (AdjoinRoot p)
  set r := AdjoinRoot.root p
  have hNK : Algebra.norm K r = (-1) ^ p.natDegree * p.coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rwa [AdjoinRoot.minpoly_powerBasis_gen_of_monic hm, AdjoinRoot.powerBasis_gen, AdjoinRoot.powerBasis_dim] at this
  let φ : AdjoinRoot p →+* ℂ := AdjoinRoot.lift σ β hev
  have hφ : φ r = β := AdjoinRoot.lift_root hev
  have hmin : minpoly ℚ r = minpoly ℚ β := by
    rw [← hφ]; exact (minpoly.algHom_eq φ.toRatAlgHom φ.injective r).symm
  have hint : IsIntegral ℚ r := .of_finite ℚ r
  have h1 : Algebra.norm ℚ r = Algebra.norm ℚ ((-1) ^ p.natDegree * p.coeff 0 : K) := by
    rw [← hNK, Algebra.norm_norm]
  have h2 := Algebra.norm_eq_norm_adjoin ℚ r
  have h3 : Algebra.norm ℚ (IntermediateField.AdjoinSimple.gen ℚ r) =
      (-1) ^ (minpoly ℚ β).natDegree * (minpoly ℚ β).coeff 0 := by
    have := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly (IntermediateField.adjoin.powerBasis hint)
    rw [IntermediateField.adjoin.powerBasis_gen hint, IntermediateField.minpoly_gen, IntermediateField.adjoin.powerBasis_dim, hmin] at this
    exact this
  have hdeg : Module.finrank ℚ (AdjoinRoot p) = p.natDegree * Module.finrank ℚ K := by
    rw [← Module.finrank_mul_finrank ℚ K (AdjoinRoot p), pb.finrank, AdjoinRoot.powerBasis_dim, mul_comm]
  have hdeg2 : Module.finrank ℚ (AdjoinRoot p) = (minpoly ℚ β).natDegree * Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    rw [← Module.finrank_mul_finrank ℚ ℚ⟮r⟯ (AdjoinRoot p), IntermediateField.adjoin.finrank hint, hmin]
  have hn1 : |Algebra.norm ℚ (-1 : K)| = 1 := by
    rw [show (-1 : K) = algebraMap ℚ K (-1) by simp, Algebra.norm_algebraMap]; simp
  have key : |Algebra.norm ℚ (p.coeff 0)| = |(minpoly ℚ β).coeff 0| ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p) := by
    have e := congrArg abs (h1.symm.trans (h2.trans (congrArg (· ^ Module.finrank ℚ⟮r⟯ (AdjoinRoot p)) h3)))
    rw [map_mul, map_pow, abs_mul, abs_pow, hn1, one_pow, one_mul, abs_pow, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul] at e
    exact e
  rw [key, ← pow_mul, mul_comm, ← hdeg2, hdeg]

end GlobalTheory.NormTower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMinpolyCoeffZeroPowNumberFieldStatement
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_norm_minpoly_coeff_zero_pow_numberField : ∀ (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]), GlobalTheory.FunObj.SqNum.IsMinPol σ β p → IsAlgebraic ℚ β → |(Algebra.norm ℚ (p.coeff 0) : ℚ)| ^ (minpoly ℚ β).natDegree = |(minpoly ℚ β).coeff 0| ^ (p.natDegree * Module.finrank ℚ K) := by
  first | exact @GlobalTheory.NormTower.abs_norm_coeff_zero_pow | exact GlobalTheory.NormTower.abs_norm_coeff_zero_pow | (intros; apply GlobalTheory.NormTower.abs_norm_coeff_zero_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeans
noncomputable section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
open GlobalTheory.FunObj.SqNum (IsMinPol meanVal_vw)

namespace GlobalTheory.HeightMeanValueBounds

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (w : Formalism.PairingDivisionLocalBalance.Pl K) : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ w.asIdeal := by
  set n := Ideal.absNorm w.asIdeal with hn
  have h0 : n ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hmem : (n : 𝓞 K) ∈ w.asIdeal := Ideal.absNorm_mem _
  have e : ((n : ℕ) : 𝓞 K) = ∏ p ∈ n.primeFactors, ((p : 𝓞 K)) ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self h0]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    push_cast; rfl
  rw [e] at hmem
  obtain ⟨p, hp, hpw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hmem
  exact ⟨p, Nat.prime_of_mem_primeFactors hp, w.isPrime.mem_of_pow_mem _ hpw⟩

theorem height_meanVal [StarRing K] [_root_.NumberField.IsTotallyComplex K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (n : ℕ → ℕ) (A B : ℝ)
    (hp : IsMinPol σ β p) (hβ : β ≠ 0) (halg : IsAlgebraic ℚ β)
    (hlow : ∀ l, l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ ((12 * n l : ℕ) : ℤ) * β))
    (harch : Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤ (minpoly ℚ β).natDegree * (12 * A))
    (hden : ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (n l : ℝ) * Real.log l ≤ B) :
    (Function.support fun w : Formalism.PairingDivisionLocalBalance.Pl K => lw w * |meanVal_vw w p / 12|).Finite ∧
      ∑ᶠ w : Formalism.PairingDivisionLocalBalance.Pl K, lw w * |meanVal_vw w p / 12| ≤ A + 2 * B := by
  obtain ⟨ha0, hd0⟩ := hp.ne_zero hβ
  set a := p.coeff 0 with ha
  set d := p.natDegree with hd
  have hfin : {w : Formalism.PairingDivisionLocalBalance.Pl K | vw w a ≠ 0}.Finite := by
    have := Filter.eventually_cofinite.1
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a))
    simpa [vw] using this
  set S : Finset ℕ := (GlobalTheory.FunObj.SqNum.finite_primes_under (p := fun w => vw w a ≠ 0) hfin).toFinset with hSdef
  have hS : ∀ l ∈ S, l.Prime := fun l hl => by
    rw [hSdef, Set.Finite.mem_toFinset] at hl; exact hl.1
  set N0 : ℕ → ℝ := fun l => ((12 * n l * d : ℕ) : ℝ) with hN0
  have hwt : ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, 0 ≤ Formalism.PairingDivisionLocalBalance.wt S N0 w := fun w =>
    Finset.sum_nonneg fun l _ => mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l)
  have hlowv : ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, -(Formalism.PairingDivisionLocalBalance.wt S N0 w) ≤ ((vw w a : ℤ) : ℝ) := by
    intro w
    by_cases h : vw w a = 0
    · rw [h]; simpa using hwt w
    · obtain ⟨l, hl, hlw⟩ := exists_prime_mem w
      have hlS : l ∈ S := by
        rw [hSdef, Set.Finite.mem_toFinset]; exact ⟨hl, w, h, hlw⟩
      have key := GlobalTheory.T.valuation_minpoly_coeff_zero_ge_of_pow_mul_integral K σ β p l (12 * n l) hp hl (hlow l hl) w hlw
      have h1 : N0 l * (vw w (l : K) : ℝ) ≤ Formalism.PairingDivisionLocalBalance.wt S N0 w :=
        Finset.single_le_sum (f := fun l => N0 l * (vw w (l : K) : ℝ))
          (fun l' _ => mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l')) hlS
      have h2 : -(N0 l * (vw w (l : K) : ℝ)) ≤ (vw w a : ℝ) := by
        have : (-(((12 * n l * d : ℕ) : ℤ) * vw w (l : K)) : ℝ) ≤ (vw w a : ℝ) := by exact_mod_cast key
        simpa [hN0] using this
      linarith
  have HC := Formalism.PairingDivisionLocalBalance.height_bound_essential K a 1 0 1 (fun _ => 0) (fun w => vw w a) S N0 ha0 one_ne_zero
    (fun w => by simp [vw, FractionalIdeal.count_one]) (fun w => by simp) (fun w => by simp) (fun l _ => by positivity) hlowv
  have hm : Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding (a ^ 12 * ((1 : K) ^ 0)⁻¹)‖) =
      12 * Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) := by
    simp only [pow_zero, inv_one, mul_one, map_pow, norm_pow, Real.log_pow, Formalism.PairingDivisionLocalBalance.meanInf]
    rw [← Finset.mul_sum]; push_cast; ring
  rw [hm, GlobalTheory.T.meanInf_log_norm_embedding_eq_log_norm_div K a ha0] at HC

  set e := (minpoly ℚ β).natDegree with he
  have he0 : 0 < e := minpoly.natDegree_pos halg.isIntegral
  have hnorm := GlobalTheory.T.abs_norm_minpoly_coeff_zero_pow_numberField K σ β p hp halg
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hlogN : (e : ℝ) * Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| =
      ((d * Module.finrank ℚ K : ℕ) : ℝ) * Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| := by
    have := congrArg (fun x : ℚ => Real.log (x : ℝ)) hnorm
    simpa [Real.log_pow] using this
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have harch' : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K ≤ d * (12 * A) := by
    rw [div_le_iff₀ hK]
    have heR : (0 : ℝ) < e := by exact_mod_cast he0
    have : (e : ℝ) * Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| ≤ e * (d * (12 * A) * Module.finrank ℚ K) := by
      rw [hlogN]; push_cast
      have := mul_le_mul_of_nonneg_left harch (by positivity : (0 : ℝ) ≤ d * Module.finrank ℚ K)
      nlinarith
    exact le_of_mul_le_mul_left this heR
  have hsum : ∑ l ∈ S, N0 l * Real.log l = 12 * d * ∑ l ∈ S, (n l : ℝ) * Real.log l := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; simp [hN0]; ring
  have hB := hden S hS
  have hmain : ∑ᶠ w : Formalism.PairingDivisionLocalBalance.Pl K, lw w * |((vw w a : ℤ) : ℝ)| ≤ 12 * d * (A + 2 * B) := by
    have := HC.2
    rw [hsum] at this
    simp only [Nat.cast_zero, zero_mul, add_zero] at this
    nlinarith
  have efun : (fun w : Formalism.PairingDivisionLocalBalance.Pl K => lw w * |meanVal_vw w p / 12|) =
      fun w => (12 * d : ℝ)⁻¹ * (lw w * |((vw w a : ℤ) : ℝ)|) := by
    funext w
    simp only [meanVal_vw, ← ha, ← hd]
    rw [div_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < d * 12)]
    field_simp
  rw [efun]
  have hsupp : (Function.support fun w : Formalism.PairingDivisionLocalBalance.Pl K => (12 * d : ℝ)⁻¹ * (lw w * |((vw w a : ℤ) : ℝ)|)) =
      Function.support fun w : Formalism.PairingDivisionLocalBalance.Pl K => lw w * |((vw w a : ℤ) : ℝ)| :=
    by
      have h12 : (12 * d : ℝ)⁻¹ ≠ 0 := by positivity
      ext w; simp only [Function.mem_support, ne_eq, mul_eq_zero, h12, false_or]
  refine ⟨hsupp ▸ HC.1, ?_⟩
  rw [← mul_finsum]
  rw [inv_mul_le_iff₀ (by positivity)]
  exact hmain

theorem lw_nonneg [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) : 0 ≤ lw w := by
  unfold lw
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have : (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
  exact div_nonneg (Real.log_nonneg this) (Nat.cast_nonneg _)

theorem htLe_of_real [StarRing K] (g : Formalism.PairingDivisionLocalBalance.Pl K → ℤ) (y y' : Formalism.PairingDivisionLocalBalance.Pl K → ℝ) (z : K) (H : ℝ)
    (hg : ∀ w, g w = GlobalTheory.LeafRestExamples.truncZero (y w)) (hy' : ∀ w, y' w = vw w z + y w)
    (h1 : (Function.support fun w => lw w * |y w|).Finite) (h2 : (Function.support fun w => lw w * |y' w|).Finite)
    (s1 : ∑ᶠ w, lw w * |y w| ≤ H) (s2 : ∑ᶠ w, lw w * |y' w| ≤ H) :
    Formalism.PairingDivisionLocalBalance.HtLe g z (2 * H) := by
  have hb : ∀ w, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ lw w * |y' w| + lw w * |y w| := fun w => by
    rw [← mul_add, hg, hy']
    exact mul_le_mul_of_nonneg_left (GlobalTheory.LeafRestExamples.abs_truncZero_le (y w) (vw w z)).2 (lw_nonneg w)
  have hfin : (Function.support fun w => lw w * |y' w| + lw w * |y w|).Finite :=
    (h2.union h1).subset (Function.support_add _ _)
  refine ⟨hfin.subset fun w hw => ?_, ?_⟩
  · intro h; apply hw
    have := hb w
    have h0 : 0 ≤ lw w * |((vw w z + g w : ℤ) : ℝ)| := mul_nonneg (lw_nonneg w) (abs_nonneg _)
    simp only [Function.mem_support, ne_eq, not_not] at h ⊢
    linarith
  · calc ∑ᶠ w, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ ∑ᶠ w, (lw w * |y' w| + lw w * |y w|) :=
          finsum_le_finsum' (hfin.subset fun w hw => by
            intro h; apply hw
            have := hb w
            have h0 : 0 ≤ lw w * |((vw w z + g w : ℤ) : ℝ)| := mul_nonneg (lw_nonneg w) (abs_nonneg _)
            simp only [Function.mem_support, ne_eq, not_not] at h ⊢
            linarith) hfin (fun w => hb w)
      _ = ∑ᶠ w, lw w * |y' w| + ∑ᶠ w, lw w * |y w| := finsum_add_distrib h2 h1
      _ ≤ 2 * H := by linarith

end GlobalTheory.HeightMeanValueBounds

namespace GlobalTheory.SqTop

open GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.ChiGrid in
theorem thbSt_of_inputs : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → DenEx → DenSum → BetaArch → ThbSt := by
  intro hTD hFD hTor _ hDS hBA
  obtain ⟨F1, hF⟩ := hFD
  obtain ⟨F2, hT⟩ := hTor
  obtain ⟨F4, hS⟩ := hDS
  obtain ⟨F5, hB⟩ := hBA
  refine ⟨max F1 (max F2 (max F4 F5)), fun ε CF hCF => ?_⟩
  obtain ⟨hf1, hf2, hf4, hf5⟩ : F1 ≤ CF ∧ F2 ≤ CF ∧ F4 ≤ CF ∧ F5 ≤ CF := by simpa [max_le_iff] using hCF
  obtain ⟨C1, y1, h1⟩ := hF ε CF hf1
  obtain ⟨C2, y2, h2⟩ := hT ε CF hf2
  obtain ⟨C4, y4, h4⟩ := hS ε CF hf4
  obtain ⟨C5, y5, h5⟩ := hB ε CF hf5
  refine ⟨6 * max C1 (max C2 (max C4 C5)), max y1 (max y2 (max y4 y5)), fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => ?_⟩
  have hC' : max C1 (max C2 (max C4 C5)) ≤ C / 6 := by linarith
  obtain ⟨hc1, hc2, hc4, hc5⟩ : C1 ≤ C / 6 ∧ C2 ≤ C / 6 ∧ C4 ≤ C / 6 ∧ C5 ≤ C / 6 := by simpa [max_le_iff] using hC'
  obtain ⟨hx1, hx2, hx4, hx5⟩ : y1 ≤ large₂.sc.x ∧ y2 ≤ large₂.sc.x ∧ y4 ≤ large₂.sc.x ∧ y5 ≤ large₂.sc.x := by simpa [max_le_iff] using hx
  have H1 := h1 (C / 6) hc1 D large₂ hε hx1 hR T Lc μ₀ hμ G
  have H2 := h2 (C / 6) hc2 D large₂ hε hx2 hR T Lc μ₀ hμ G
  have H4 := h4 (C / 6) hc4 D large₂ hε hx4 hR T Lc μ₀ hμ G
  have H5 := h5 (C / 6) hc5 D large₂ hε hx5 hR T Lc μ₀ hμ G
  dsimp only at H1 H2 H4 H5 ⊢
  intro i j s hs1 hs2 zd g hTV
  obtain ⟨hCM, hAb, hFDat, hBase, -⟩ := H1
  obtain ⟨z, hz, HD⟩ := hTD D.host.E D.what₂.Tau D.host.d (cmPhi D) s hFDat hs1
  obtain ⟨x, hx, hx0, hxc, Λ, p, hΛ, hp, hg⟩ := hTV
  set B' := bTH D (C / 6) large₂.sc.x large₂.sc.b with hB'
  have hB6 : bTH D C large₂.sc.x large₂.sc.b = 2 * (B' + 2 * B') := by rw [hB']; unfold bTH; ring
  set n : ℕ → ℕ := fun l => ⌈GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D (1 : ℝ) i j s) (condF G.pl) z l / 12⌉₊ with hn
  have hden : IsDenom G i j s (fun l => (n l : ℝ)) := ⟨z, hz, fun l _ => rfl⟩
  have hd0 : 0 < D.host.d := hFDat.1.pos
  have beta_ne : ∀ y : ℂ, y ≠ 0 → GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ y ≠ 0 := by
    intro y hy
    unfold GlobalTheory.CMVal.beta
    refine div_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ hy)) (pow_ne_zero _ (Formalism.L2.Th1.F.discNeZero Λ))
    exact_mod_cast (GlobalTheory.CMVal.cmValueConst_pos D.host.E hd0 (by omega) _).ne'
  have tor_ne : ∀ c y, IsTor G i j s (fam G μ₀ i j c) y → y ≠ 0 ∧
      IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ y) := by
    intro c y hty
    obtain ⟨y', hy', hy'0, -, halg⟩ := H2 i j s hs1 hs2 c
    obtain rfl : y' = y := hy'.2.unique hty.2
    exact ⟨hy'0, halg Λ hΛ⟩
  have fam_bd : ∀ (c : Option Bool) (y : ℂ) (q : D.what₂.LL[X]), IsTor G i j s (fam G μ₀ i j c) y →
      IsMinPol D.what₂.embLL (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ y) q →
      (Function.support fun w => lw w * |meanVal_vw w q / 12|).Finite ∧
        ∑ᶠ w, lw w * |meanVal_vw w q / 12| ≤ B' + 2 * B' := by
    intro c y q hty hq
    obtain ⟨hy0, halg⟩ := tor_ne c y hty
    refine GlobalTheory.HeightMeanValueBounds.height_meanVal D.what₂.embLL _ q n B' B' hq (beta_ne y hy0) halg ?_
      (H5 i j s hs1 hs2 c y Λ hty hΛ) fun S hS => (H4 i j s hs1 hs2 _ hden S hS).2
    intro l hl
    have hT' : GlobalTheory.CMVal.IsToricSum (cmPhi D) s (kap D (1 : ℝ) i j s) (GlobalTheory.CMVal.condQ (condF G.pl) ∅)
        (fam G μ₀ i j c * 1) y := by
      simpa [GlobalTheory.CMVal.condQ] using hty.2
    have hv := ((HD (kap D (1 : ℝ) i j s) (condF G.pl) Λ (fam G μ₀ i j c) hBase hΛ hty.1 l hl ∅
      (by simp [GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor]) (by simp)).2 1 y ⟨fun _ => rfl, fun _ _ => rfl⟩ hT')
    have hle : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D (1 : ℝ) i j s) (condF G.pl) z l ≤
        (((12 * n l : ℕ) : ℤ) : ℝ) / ((1 : ℕ) : ℝ) := by
      have := Nat.le_ceil (GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D (1 : ℝ) i j s) (condF G.pl) z l / 12)
      simp only [hn] at *
      push_cast
      linarith
    simpa using hv ((12 * n l : ℕ) : ℤ) 1 one_pos hle
  obtain ⟨fin0, sum0⟩ := fam_bd none x p hx hp
  have hB0 : 0 ≤ B' := by
    have : 0 ≤ ∑ᶠ w, lw w * |meanVal_vw w p / 12| :=
      finsum_nonneg fun w => mul_nonneg (GlobalTheory.HeightMeanValueBounds.lw_nonneg w) (abs_nonneg _)
    linarith
  rw [hB6]
  refine ⟨GlobalTheory.HeightMeanValueBounds.htLe_of_real g _ _ 1 _ hg (fun w => by simp [vw, FractionalIdeal.count_one]) fin0 fin0 sum0 sum0,
    fun c => ?_⟩
  have hxc' : IsTor G i j s (fam G μ₀ i j (some c)) (D.what₂.embLL (zd c) * x) := hxc c
  obtain ⟨hy0, halg⟩ := tor_ne (some c) _ hxc'
  have hz0 : zd c ≠ 0 := fun h => hy0 (by simp [h])
  obtain ⟨qc, hqc⟩ := exists_isMinPol (σ := D.what₂.embLL) halg
  have e12 : GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ (D.what₂.embLL (zd c) * x) =
      D.what₂.embLL (zd c ^ 12) * GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ x := by
    unfold GlobalTheory.CMVal.beta; rw [map_pow]; ring
  have hqc' := hqc
  rw [e12] at hqc'
  have hmv := GlobalTheory.T.meanValuationNormOverDegree_smul_eq_add_valuation D.what₂.LL D.what₂.embLL _ (zd c ^ 12) p qc hp hqc' (beta_ne x hx0) (pow_ne_zero _ hz0)
  obtain ⟨finc, sumc⟩ := fam_bd (some c) _ qc hxc' hqc
  refine ⟨hz0, GlobalTheory.HeightMeanValueBounds.htLe_of_real g _ _ (zd c) _ hg (fun w => ?_) fin0 finc sum0 sumc⟩
  rw [hmv w, Formalism.PairingDivisionLocalBalance.vw_pow w _ hz0]
  push_cast; ring

end GlobalTheory.SqTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeansStatement
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricValueHeightBound_of_denominatorsMeans : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → DenEx → DenSum → BetaArch → ThbSt := by
  first | exact @GlobalTheory.SqTop.thbSt_of_inputs | exact GlobalTheory.SqTop.thbSt_of_inputs | (intros; apply GlobalTheory.SqTop.thbSt_of_inputs <;> assumption)
end
