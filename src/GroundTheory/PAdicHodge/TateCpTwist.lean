module

public import GroundTheory.PAdicHodge.PerfectoidField
public import GroundTheory.PAdicHodge.BdRSeries

@[expose] public section

section -- merged from GroundTheory.PAdicHodge.TateCpTwist
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open UniformSpace

variable {p : ℕ} [Fact p.Prime]

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem algebraMap_intermediateField_cp (k : K) :
    algebraMap K ℂ_[p] k = ((k : PadicAlgCl p) : ℂ_[p]) := rfl

theorem gal_smul_algebraMap_intermediateField (σ : Gal(PadicAlgCl p/K)) (k : K) :
    σ • algebraMap K ℂ_[p] k = algebraMap K ℂ_[p] k :=
  gal_smul_coe_of_mem σ k

theorem gal_smul_smul_intermediateField (σ : Gal(PadicAlgCl p/K)) (k : K) (x : ℂ_[p]) :
    σ • (k • x) = k • (σ • x) := by
  rw [Algebra.smul_def, Algebra.smul_def, smul_mul', gal_smul_algebraMap_intermediateField]

noncomputable def cycloChar : Gal(PadicAlgCl p/K) →* ℤ_[p]ˣ :=
  (cyclotomicCharacter (PadicAlgCl p) p).comp
    (MulSemiringAction.toRingAut Gal(PadicAlgCl p/K) (PadicAlgCl p))

theorem continuous_cycloChar : Continuous (cycloChar K) :=
  cyclotomicCharacter.continuous p K (PadicAlgCl p)

theorem cycloChar_spec (σ : Gal(PadicAlgCl p/K)) {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ p ^ n = 1) :
    σ ζ = ζ ^ ((cycloChar K σ : ℤ_[p]).toZModPow n).val :=
  cyclotomicCharacter.spec p (MulSemiringAction.toRingAut Gal(PadicAlgCl p/K) (PadicAlgCl p) σ) ζ hζ

noncomputable def twistScalar (j : ℤ) (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] :=
  algebraMap ℚ_[p] ℂ_[p] (((cycloChar K σ ^ j : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])

theorem twistScalar_one (j : ℤ) : twistScalar K j 1 = 1 := by
  simp [twistScalar]

theorem twistScalar_mul (j : ℤ) (σ τ : Gal(PadicAlgCl p/K)) :
    twistScalar K j (σ * τ) = twistScalar K j σ * twistScalar K j τ := by
  simp only [twistScalar, map_mul, mul_zpow, Units.val_mul, PadicInt.coe_mul]

theorem twistScalar_zero (σ : Gal(PadicAlgCl p/K)) : twistScalar K 0 σ = 1 := by
  simp [twistScalar]

theorem gal_smul_twistScalar (j : ℤ) (σ τ : Gal(PadicAlgCl p/K)) :
    σ • twistScalar K j τ = twistScalar K j τ :=
  gal_smul_algebraMap σ _

noncomputable def cpTwistMap (j : ℤ) (σ : Gal(PadicAlgCl p/K)) : ℂ_[p] →L[K] ℂ_[p] where
  toFun x := twistScalar K j σ * (σ • x)
  map_add' x y := by rw [smul_add, mul_add]
  map_smul' k x := by
    rw [gal_smul_smul_intermediateField, RingHom.id_apply, mul_smul_comm]
  cont := continuous_const.mul (continuous_const_smul σ)

theorem cpTwistMap_apply (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    cpTwistMap K j σ x = twistScalar K j σ * (σ • x) := rfl

noncomputable def cpTwistRep (j : ℤ) : ContRepresentation K Gal(PadicAlgCl p/K) ℂ_[p] :=
  .ofMonoidHom
    { toFun := cpTwistMap K j
      map_one' := by
        ext x
        simp [cpTwistMap_apply, twistScalar_one]
      map_mul' := fun σ τ => by
        ext x
        change cpTwistMap K j (σ * τ) x = cpTwistMap K j σ (cpTwistMap K j τ x)
        simp only [cpTwistMap_apply, twistScalar_mul, smul_mul', gal_smul_twistScalar, mul_smul]
        ring }

theorem cpTwistRep_apply (j : ℤ) (σ : Gal(PadicAlgCl p/K)) (x : ℂ_[p]) :
    cpTwistRep K j σ x = twistScalar K j σ * (σ • x) := rfl

end GroundTheory.PAdicHodge
end

section -- merged from GroundTheory.PAdicHodge.HighIndexSingleZeroOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Laurent

set_option linter.unusedSectionVars false

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

structure AnnulusRing (I : Set ℝ) where

@[ext]
structure Robba where

  coeff : ℤ → K
  exists_convergesAt' : ∃ r < 1, ∀ ρ, r ≤ ρ → ρ < 1 → 0 < ρ → ConvergesAt coeff ρ

variable {K}

namespace AnnulusRing

variable {I : Set ℝ}

variable [hI : Fact (∃ ρ ∈ I, 0 < ρ)]

end AnnulusRing

namespace Robba

end Robba

namespace AnnulusRing

variable {r : ℝ} [Fact (r < 1)]

end AnnulusRing

namespace Robba

end Robba

namespace Laurent

end Laurent

namespace Robba

end Robba

namespace Laurent

end Laurent

namespace Robba

end Robba

end GroundTheory.PAdicHodge
end
end

section -- merged from GroundTheory.PAdicHodge.LogMul
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open PowerSeries

section Formal

theorem exp_subst_log : (exp ℚ).subst (log ℚ) = (1 + X : ℚ⟦X⟧) :=
  PowerSeries.subst_exp_log ℚ

end Formal

section Nilpotent

variable {S : Type*} [CommRing S] [Algebra ℚ S]

theorem truncEval_pow_eq_zero {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧}
    (hg : constantCoeff g = 0) : (truncEval s hs g) ^ n = 0 := by
  obtain ⟨h, rfl⟩ := X_dvd_iff.2 hg
  rw [← map_pow, mul_pow, map_mul, map_pow, truncEval_X, hs, zero_mul]

theorem truncEval_subst {n : ℕ} {s : S} (hs : s ^ n = 0) {g : ℚ⟦X⟧} (hg : constantCoeff g = 0)
    (f : ℚ⟦X⟧) :
    truncEval s hs (f.subst g) = truncEval (truncEval s hs g) (truncEval_pow_eq_zero hs hg) f := by
  have hS := HasSubst.of_constantCoeff_zero' hg
  have key := truncEval_unique ((truncEval s hs).comp (substAlgHom hS)) (truncEval s hs g)
    (truncEval_pow_eq_zero hs hg) (by rw [AlgHom.comp_apply, coe_substAlgHom, subst_X hS])
  rw [← key, AlgHom.comp_apply, coe_substAlgHom]

theorem truncEval_exp {n : ℕ} {s : S} (hs : s ^ n = 0) :
    truncEval s hs (exp ℚ) = IsNilpotent.exp s := by
  rw [truncEval_eq_sum, IsNilpotent.exp_eq_sum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_exp, Algebra.smul_def, one_div]
  simp

theorem isNilpotent_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent (truncEval s hs (log ℚ)) :=
  ⟨n, truncEval_pow_eq_zero hs constantCoeff_log⟩

theorem exp_truncEval_log {n : ℕ} {s : S} (hs : s ^ n = 0) :
    IsNilpotent.exp (truncEval s hs (log ℚ)) = 1 + s := by
  rw [← truncEval_exp (truncEval_pow_eq_zero hs constantCoeff_log),
    ← truncEval_subst hs (g := log ℚ) constantCoeff_log,
    exp_subst_log, map_add, map_one, truncEval_X]

theorem eq_zero_of_exp_eq_one {c : S} (hc : IsNilpotent c) (h : IsNilpotent.exp c = 1) : c = 0 := by
  obtain ⟨k, hk⟩ := hc
  set w : S := ∑ i ∈ Finset.range k, ((i + 1).factorial : ℚ)⁻¹ • c ^ i with hw
  have hexp : IsNilpotent.exp c = 1 + c * w := by
    rw [IsNilpotent.exp_eq_sum (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ',
      hw, Finset.mul_sum]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, pow_succ, mul_comm c]
  have hw1 : IsUnit w := by
    rcases k with _ | k
    · have : Subsingleton S := subsingleton_of_zero_eq_one (by simpa using hk.symm)
      exact isUnit_of_subsingleton w
    · have hsplit : w = 1 + c * ∑ i ∈ Finset.range k, ((i + 2).factorial : ℚ)⁻¹ • c ^ i := by
        rw [hw, Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, zero_add, Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
        rw [add_comm]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_smul_comm, pow_succ, mul_comm c]
      rw [hsplit]
      exact IsNilpotent.isUnit_one_add ⟨k + 1, by rw [mul_pow, hk, zero_mul]⟩
  have h0 : c * w = 0 := by
    have := hexp.symm.trans h
    rwa [add_eq_left] at this
  simpa using (hw1.mul_left_eq_zero).1 h0

theorem eq_of_exp_eq {a b : S} (ha : IsNilpotent a) (hb : IsNilpotent b)
    (h : IsNilpotent.exp a = IsNilpotent.exp b) : a = b := by
  have hnb : IsNilpotent (-b) := hb.neg
  have h1 : IsNilpotent.exp (a + -b) = 1 := by
    rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) ha hnb, h,
      IsNilpotent.exp_mul_exp_neg_self hb]
  have h2 := eq_zero_of_exp_eq_one (Commute.isNilpotent_add (Commute.all _ _) ha hnb) h1
  rw [← sub_eq_add_neg, sub_eq_zero] at h2
  exact h2

theorem truncEval_log_mul {l m n : ℕ} {x y z : S} (hx : x ^ l = 0) (hy : y ^ m = 0)
    (hz : z ^ n = 0) (hxyz : 1 + z = (1 + x) * (1 + y)) :
    truncEval z hz (log ℚ) = truncEval x hx (log ℚ) + truncEval y hy (log ℚ) := by
  have hnx := isNilpotent_truncEval_log hx
  have hny := isNilpotent_truncEval_log hy
  apply eq_of_exp_eq (isNilpotent_truncEval_log hz) (Commute.isNilpotent_add (Commute.all _ _) hnx hny)
  rw [IsNilpotent.exp_add_of_commute (Commute.all _ _) hnx hny, exp_truncEval_log,
    exp_truncEval_log, exp_truncEval_log, hxyz]

end Nilpotent

section Complete

variable {B : Type*} [CommRing B] [Algebra ℚ B] {I : Ideal B} [IsAdicComplete I B]

theorem mk_seriesEval_eq_truncEval {z : B} (hz : z ∈ I) (f : ℚ⟦X⟧) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (seriesEval I z hz f) =
      truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n) f :=
  IsAdicComplete.mk_liftAlgHom I
    (fun n => truncEval (Ideal.Quotient.mk (I ^ n) z) (pow_mk_eq_zero I hz n))
    (fun hle => factorₐ_comp_truncEval I hz hle) n f

theorem logOnePlus_mul {x y z : B} (hx : x ∈ I) (hy : y ∈ I) (hz : z ∈ I)
    (hxyz : 1 + z = (1 + x) * (1 + y)) :
    logOnePlus I z hz = logOnePlus I x hx + logOnePlus I y hy := by
  refine eq_of_forall_sub_mem_pow I fun n => ?_
  rw [← Ideal.Quotient.eq, map_add (f := _), logOnePlus, logOnePlus, logOnePlus,
    mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval, mk_seriesEval_eq_truncEval]
  exact truncEval_log_mul _ _ _ (by rw [← map_one (Ideal.Quotient.mk (I ^ n)), ← map_add (f := _), hxyz,
    map_mul, map_add, map_add, map_one])

end Complete

end GroundTheory.PAdicHodge
end
end
