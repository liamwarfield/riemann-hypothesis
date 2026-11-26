module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFourierTermWirtingerWordDifferentiableOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FTermIteratedFDerivBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierSumsCosetsSemidirectCyclic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinNonconstantFourierSumSmoothHolomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinFourierTermMoveUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinFourierTermMoveUnit
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.HeckeTwoUnit

theorem phi_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (w : ℂ) :
    phi σ ((l : ℂ) * w) = ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * phi σ w := by
  unfold phi
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg l) (norm_nonneg w), mul_inv, mul_pow]
  ring

theorem abs_mul_inv_sq {l : ℝ} (hl : l ≠ 0) :
    ((|l| : ℝ) : ℂ) * (l : ℂ)⁻¹ ^ 2 = ((|l| : ℝ) : ℂ)⁻¹ := by
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hl
  have h2 : (l : ℂ) ^ 2 = ((|l| : ℝ) : ℂ) ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, sq_abs]
  rw [inv_pow, h2]; field_simp

theorem hTrans_smul (σ : ℂ) {l : ℝ} (hl : l ≠ 0) (ν y : ℝ) :
    hTrans σ ν (l * y) = ((|l| : ℝ) : ℂ) ^ (-1 - 2 * σ) * hTrans σ (l * ν) y := by
  have key := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))) l
  unfold hTrans
  rw [← smul_eq_mul (a := ((|l| : ℝ) : ℂ) ^ _)]
  have habs : |l⁻¹| = |l|⁻¹ := abs_inv l
  have hpos : 0 < |l| := abs_pos.2 hl
  have e1 : ∫ t : ℝ, phi σ ((t : ℂ) + ((l * y : ℝ) : ℂ) * I) *
      Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ))) =
      |l| • ∫ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) := by
    rw [key, habs, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [e1]
  have e2 : ∀ t : ℝ, phi σ (((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * ((l * t : ℝ) : ℂ))) =
      ((l : ℂ)⁻¹ ^ 2 * ((|l| : ℝ) : ℂ) ^ (-2 * σ)) * (phi σ ((t : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(2 * (Real.pi : ℂ) * I * ((l * ν : ℝ) : ℂ) * (t : ℂ)))) := by
    intro t
    rw [show ((l * t : ℝ) : ℂ) + ((l * y : ℝ) : ℂ) * I = (l : ℂ) * ((t : ℂ) + (y : ℂ) * I) by push_cast; ring,
      phi_smul σ hl]
    push_cast; ring_nf
  simp_rw [e2]
  rw [MeasureTheory.integral_const_mul, Complex.real_smul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
    abs_mul_inv_sq hl]
  congr 1
  have h1 : ((|l| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [sub_eq_add_neg, Complex.cpow_add _ _ h1, Complex.cpow_neg_one, neg_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

theorem prod_abs_unit_cpow {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (ε : (𝓞 F)ˣ) (s : ℂ) :
    ∏ τ : Emb F, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s = 1 := by
  have hprod : ∀ (S : Finset (Emb F)), ∏ τ ∈ S, ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s =
      ((∏ τ ∈ S, |τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ s := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (Finset.prod_nonneg fun _ _ => abs_nonneg _)]
  rw [hprod]
  have h := GlobalTheory.HeckeTwoExp.abs_norm_eq_prod ((ε : 𝓞 F) : F)
  rw [← Complex.ofReal_prod] at h
  have hn : |((Algebra.norm ℚ ((ε : 𝓞 F) : F) : ℚ) : ℝ)| = 1 := by
    have := Units.norm F ε
    exact_mod_cast this
  rw [← h, hn, Complex.ofReal_one, Complex.one_cpow]

theorem fTerm_unit_mul {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F)
    (ε : (𝓞 F)ˣ) :
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) := by
  have hne : ∀ τ : Emb F, τ ((ε : 𝓞 F) : F) ≠ 0 := fun τ h => by
    have hu : ((ε : 𝓞 F) : F) ≠ 0 := by
      intro h0; have := unit_inv_mul ε; rw [h0, mul_zero] at this; exact zero_ne_one this
    exact hu ((map_eq_zero τ).1 h)
  unfold fTerm
  have e : ∀ τ : Emb F, Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ (((ε : 𝓞 F) : F) * b) * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ ν) (τ (((ε : 𝓞 F) : F) * b) * (z τ).im) =
      ((|τ ((ε : 𝓞 F) : F)| : ℝ) : ℂ) ^ (-1 - 2 * σ) *
      (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ (((ε : 𝓞 F) : F) * ν) * τ b * (z τ).re : ℝ) : ℂ)) *
      hTrans σ (τ (((ε : 𝓞 F) : F) * ν)) (τ b * (z τ).im)) := by
    intro τ
    rw [map_mul, map_mul, mul_assoc (τ ((ε : 𝓞 F) : F)) (τ b), hTrans_smul σ (hne τ)]
    rw [show τ ν * (τ ((ε : 𝓞 F) : F) * τ b) * (z τ).re = τ ((ε : 𝓞 F) : F) * τ ν * τ b * (z τ).re by ring]
    ring
  simp_rw [e]
  rw [Finset.prod_mul_distrib, prod_abs_unit_cpow, one_mul]

end GlobalTheory.HeckeTwoUnit

namespace GlobalTheory.HeckeTwoUnit

theorem fTerm_unit_move : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F) (ε : (𝓞 F)ˣ),
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) :=
  fun _ _ _ _ σ z b ν ε => fTerm_unit_mul σ z b ν ε

end GlobalTheory.HeckeTwoUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeEisensteinFourierTermMoveUnitStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinFourierTerm_move_unit : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (σ : ℂ) (z : Emb F → ℂ) (b ν : F) (ε : (𝓞 F)ˣ),
    fTerm σ z (((ε : 𝓞 F) : F) * b) ν = fTerm σ z b (((ε : 𝓞 F) : F) * ν) := by
  first | exact @GlobalTheory.HeckeTwoUnit.fTerm_unit_move | exact GlobalTheory.HeckeTwoUnit.fTerm_unit_move | (intros; apply GlobalTheory.HeckeTwoUnit.fTerm_unit_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedUnitMultipleTotallyReal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedUnitMultipleTotallyReal
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.BalancedUnits

open NumberField.InfinitePlace NumberField.mixedEmbedding NumberField.Units
open NumberField.Units.dirichletUnitTheorem

theorem sum_mult_log_sub {K : Type} [Field K] [NumberField K] (x : mixedSpace K)
    (hx : mixedEmbedding.norm x ≠ 0) :
    ∑ w : InfinitePlace K, (mult w : ℝ) * (Real.log (normAtPlace w x) -
      Real.log (mixedEmbedding.norm x) * (Module.finrank ℚ K : ℝ)⁻¹) = 0 := by
  have h1 : ∑ w : InfinitePlace K, (mult w : ℝ) * Real.log (normAtPlace w x) =
      Real.log (mixedEmbedding.norm x) := by
    rw [mixedEmbedding.norm_apply, Real.log_prod]
    · refine Finset.sum_congr rfl fun w _ => ?_
      rw [Real.log_pow]
    · intro w _
      exact pow_ne_zero _ (mixedEmbedding.norm_ne_zero_iff.mp hx w)
  have h2 : ∑ w : InfinitePlace K, (mult w : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast sum_mult_eq
  have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  simp_rw [mul_sub, Finset.sum_sub_distrib, h1, ← Finset.sum_mul, h2]
  field_simp
  ring

theorem exists_unit_log_bound (K : Type) [Field K] [NumberField K] : ∃ M : ℝ, 0 ≤ M ∧
    ∀ b : K, b ≠ 0 → ∃ ε : (𝓞 K)ˣ, ∀ w : InfinitePlace K,
      |Real.log (w (((ε : 𝓞 K) : K) * b)) -
        Real.log (mixedEmbedding.norm (mixedEmbedding K (((ε : 𝓞 K) : K) * b))) *
          (Module.finrank ℚ K : ℝ)⁻¹| ≤ M := by
  classical
  obtain ⟨R, hR⟩ := (ZSpan.fundamentalDomain_isBounded
    ((basisUnitLattice K).ofZLatticeBasis ℝ (unitLattice K))).subset_closedBall 0
  refine ⟨(Fintype.card (InfinitePlace K) : ℝ) * |R|, by positivity, ?_⟩
  intro b hb
  have hx : mixedEmbedding.norm (mixedEmbedding K b) ≠ 0 := by
    rw [norm_eq_norm]; simpa using hb
  obtain ⟨ε, hε⟩ := fundamentalCone.exists_unit_smul_mem hx
  refine ⟨ε, ?_⟩
  have hxy : ε • mixedEmbedding K b = mixedEmbedding K (((ε : 𝓞 K) : K) * b) := by
    rw [unitSMul_smul, map_mul]
  rw [hxy] at hε
  set y : K := ((ε : 𝓞 K) : K) * b with hy_def
  set X := mixedEmbedding K y
  set L := Real.log (mixedEmbedding.norm X) * (Module.finrank ℚ K : ℝ)⁻¹
  have hcard : (1 : ℝ) ≤ Fintype.card (InfinitePlace K) := by
    exact_mod_cast Fintype.card_pos
  have hlog : ∀ w : {w : InfinitePlace K // w ≠ w₀},
      |(mult w.val : ℝ) * (Real.log (normAtPlace w.val X) - L)| ≤ |R| := by
    intro w
    have h0 := hR hε.1
    rw [mem_closedBall_zero_iff] at h0
    have h2 := (norm_le_pi_norm (logMap X) w).trans h0
    rw [logMap_apply, Real.norm_eq_abs] at h2
    exact h2.trans (le_abs_self R)
  have hmul : ∀ w : InfinitePlace K,
      |(mult w : ℝ) * (Real.log (normAtPlace w X) - L)| ≤ (Fintype.card (InfinitePlace K) : ℝ) * |R| := by
    intro w
    by_cases hw : w = w₀
    · subst hw
      have hs := sum_mult_log_sub X hε.2
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w₀)] at hs
      rw [eq_neg_of_add_eq_zero_left hs, abs_neg]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ w ∈ Finset.univ.erase w₀, |(mult w : ℝ) * (Real.log (normAtPlace w X) - L)|
          ≤ ∑ _w ∈ Finset.univ.erase w₀, |R| := Finset.sum_le_sum fun w hw =>
            hlog ⟨w, Finset.ne_of_mem_erase hw⟩
        _ ≤ (Fintype.card (InfinitePlace K) : ℝ) * |R| := by
            rw [Finset.sum_const, nsmul_eq_mul]
            gcongr
            exact_mod_cast (Finset.card_erase_le).trans (le_of_eq Finset.card_univ)
    · exact (hlog ⟨w, hw⟩).trans (le_mul_of_one_le_left (abs_nonneg R) hcard)
  intro w
  have h := hmul w
  rw [abs_mul, normAtPlace_apply] at h
  refine le_trans ?_ h
  rw [abs_of_pos (by exact_mod_cast mult_pos : (0:ℝ) < mult w)]
  exact le_mul_of_one_le_left (abs_nonneg _) one_le_mult

theorem balanced_unit_multiple (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ b : F, b ≠ 0 → ∃ ε : (𝓞 F)ˣ, ∀ τ τ' : Emb F,
      |τ (((ε : 𝓞 F) : F) * b)| ≤ C * |τ' (((ε : 𝓞 F) : F) * b)| := by
  obtain ⟨M, hM0, hM⟩ := exists_unit_log_bound F
  refine ⟨Real.exp (2 * M), Real.one_le_exp (by positivity), ?_⟩
  intro b hb
  obtain ⟨ε, hε⟩ := hM b hb
  refine ⟨ε, ?_⟩
  set y : F := ((ε : 𝓞 F) : F) * b with hy_def
  have hy : y ≠ 0 := mul_ne_zero (by simp) hb
  have hw : ∀ τ : Emb F, InfinitePlace.mk (Complex.ofRealHom.comp τ) y = |τ y| := by
    intro τ
    rw [InfinitePlace.apply]
    simp
  have hpos : ∀ τ : Emb F, 0 < |τ y| := fun τ => abs_pos.mpr ((map_ne_zero τ).mpr hy)
  intro τ τ'
  have h1 := hε (InfinitePlace.mk (Complex.ofRealHom.comp τ))
  have h2 := hε (InfinitePlace.mk (Complex.ofRealHom.comp τ'))
  rw [hw] at h1 h2
  have key : Real.log |τ y| ≤ 2 * M + Real.log |τ' y| := by
    have := (abs_le.mp h1).2
    have := (abs_le.mp h2).1
    linarith
  calc |τ y| = Real.exp (Real.log |τ y|) := (Real.exp_log (hpos τ)).symm
    _ ≤ Real.exp (2 * M + Real.log |τ' y|) := Real.exp_le_exp.mpr key
    _ = Real.exp (2 * M) * |τ' y| := by rw [Real.exp_add, Real.exp_log (hpos τ')]

end GlobalTheory.BalancedUnits
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBalancedUnitMultipleTotallyRealStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_balanced_unit_multiple_totallyReal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], ∃ C : ℝ, 1 ≤ C ∧
    ∀ b : F, b ≠ 0 → ∃ ε : (𝓞 F)ˣ, ∀ τ τ' : Emb F, |τ (((ε : 𝓞 F) : F) * b)| ≤ C * |τ' (((ε : 𝓞 F) : F) * b)| := by
  first | exact @GlobalTheory.BalancedUnits.balanced_unit_multiple | exact GlobalTheory.BalancedUnits.balanced_unit_multiple | (intros; apply GlobalTheory.BalancedUnits.balanced_unit_multiple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeBalancedLatticeDoubleSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeBalancedLatticeDoubleSum
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.LatSum

variable {F : Type} [Field F] [NumberField F]

def absSum (x : F) : ℝ := ∑ τ : Emb F, |τ x|

theorem absSum_nonneg (x : F) : 0 ≤ absSum x := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_absSum (x : F) (τ : Emb F) : |τ x| ≤ absSum x :=
  Finset.single_le_sum (f := fun τ : Emb F => |τ x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)

theorem one_add_sum_le_prod {ι : Type} (s : Finset ι) (a : ι → ℝ) (h : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => h j
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith [h i] : (0:ℝ) ≤ 1 + a i), mul_nonneg (h i) h1]

theorem bound_eq (K₁ s x q : ℝ) (a b : ℕ) (hs : s ≠ 0) (hx : x ≠ 0) (hq : q ≠ 0) :
    (K₁ * s) ^ a / (x * (s / q)) ^ (a + b) = K₁ ^ a * q ^ (a + b) * ((s ^ b)⁻¹ * (x ^ (a + b))⁻¹) := by
  rw [mul_pow, mul_pow, div_pow, pow_add s]
  field_simp

variable [IsTotallyReal F]


open scoped Classical in
theorem norm_mixedEmbedding_le (x : F) : ‖mixedEmbedding F x‖ ≤ absSum x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) x,
    Real.norm_eq_abs]
  exact abs_le_absSum x _

open scoped Classical in
theorem absSum_pos {x : F} (hx : x ≠ 0) : 0 < absSum x := by
  have h : 0 < ‖mixedEmbedding F x‖ := norm_pos_iff.2 fun h =>
    hx ((mixedEmbedding F).injective (h.trans (map_zero _).symm))
  exact h.trans_le (norm_mixedEmbedding_le x)


open scoped Classical in
theorem summable_absSum_inv_pow (I : Frac F) {k : ℕ} (hk : Module.finrank ℚ F < k) :
    Summable (fun x : NZ (I : FractionalIdeal (𝓞 F)⁰ F) => ((absSum x.1) ^ k)⁻¹) := by
  let L := mixedEmbedding.idealLattice F I
  have hL := ZLattice.summable_norm_rpow L (-(k : ℝ)) (by
    rw [ZLattice.rank ℝ L, mixedEmbedding.finrank F]
    have : (Module.finrank ℚ F : ℝ) < k := by exact_mod_cast hk
    linarith)
  let j : NZ (I : FractionalIdeal (𝓞 F)⁰ F) → L := fun x =>
    ⟨mixedEmbedding F x.1, (mixedEmbedding.mem_idealLattice F I).2 ⟨x.1, x.2.1, rfl⟩⟩
  have hj : Function.Injective j := fun x y h =>
    Subtype.ext ((mixedEmbedding F).injective (congrArg Subtype.val h))
  refine (hL.comp_injective hj).of_nonneg_of_le (fun x => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))
    (fun x => ?_)
  have hpos : 0 < ‖mixedEmbedding F x.1‖ := norm_pos_iff.2 fun h =>
    x.2.2 ((mixedEmbedding F).injective (h.trans (map_zero _).symm))
  show ((absSum x.1) ^ k)⁻¹ ≤ ‖mixedEmbedding F x.1‖ ^ (-(k : ℝ))
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  exact inv_anti₀ (pow_pos hpos k) (pow_le_pow_left₀ hpos.le (norm_mixedEmbedding_le x.1) k)

theorem prod_abs_emb (x : F) : ∏ τ : Emb F, |τ x| = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := congrArg (fun z : ℂ => ‖z‖) (prod_emb x)
  simp only [norm_prod, Complex.norm_real, Real.norm_eq_abs] at h
  rw [h, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem exists_absSum_lower (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ I, x ≠ 0 → β ≤ absSum x := by
  obtain ⟨d, hd, h⟩ := I.isFractional
  have hd0 : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd
  set D := |((Algebra.norm ℚ ((d : 𝓞 F) : F) : ℚ) : ℝ)| with hD
  have hDpos : 0 < D := by simp [hD, Algebra.norm_eq_zero_iff, hd0]
  have hn : 1 ≤ Fintype.card (Emb F) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact Fintype.card_pos_iff.2 ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩
  refine ⟨min 1 D⁻¹, lt_min one_pos (inv_pos.2 hDpos), fun x hx hx0 => ?_⟩
  obtain ⟨g, hg⟩ := h x hx
  have hg' : ((g : 𝓞 F) : F) = ((d : 𝓞 F) : F) * x := by
    rw [← Algebra.smul_def] at *; simpa using hg
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0] at hg'; simp at hg'
    exact hg'.elim (fun h => hd0 (by exact_mod_cast h)) hx0
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ g : ℤ) : ℝ)| := by
    have : Algebra.norm ℤ g ≠ 0 := Algebra.norm_ne_zero_iff.2 hg0
    exact_mod_cast Int.one_le_abs this
  have e1 : ((Algebra.norm ℤ g : ℤ) : ℚ) = Algebra.norm ℚ ((d : 𝓞 F) : F) * Algebra.norm ℚ x := by
    rw [Algebra.coe_norm_int, hg', map_mul]
  have e2 : ((Algebra.norm ℤ g : ℤ) : ℝ) =
      ((Algebra.norm ℚ ((d : 𝓞 F) : F) : ℚ) : ℝ) * ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  rw [e2, abs_mul, ← hD, ← prod_abs_emb] at h1
  have hle : ∏ τ : Emb F, |τ x| ≤ absSum x ^ Fintype.card (Emb F) := by
    calc ∏ τ : Emb F, |τ x| ≤ ∏ _τ : Emb F, absSum x :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun τ _ => abs_le_absSum x τ)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  have hS0 := absSum_nonneg x
  rcases le_or_gt 1 (absSum x) with hS | hS
  · exact (min_le_left _ _).trans hS
  · have hpow : absSum x ^ Fintype.card (Emb F) ≤ absSum x := pow_le_of_le_one hS0 hS.le (by omega)
    refine (min_le_right _ _).trans ?_
    have : 1 ≤ D * absSum x := h1.trans (mul_le_mul_of_nonneg_left (hle.trans hpow) hDpos.le)
    rw [inv_le_iff_one_le_mul₀ hDpos]
    linarith

end GlobalTheory.HeckeTwo.LatSum


open GlobalTheory.HeckeTwo.LatSum in
theorem GlobalTheory.HeckeTwo.summable_balanced_latSum :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (C₀ : ℝ) (m : ℕ), ∃ N : ℕ,
    ∀ ε : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → (𝓞 F)ˣ,
      (∀ c (τ τ' : Emb F), |τ (((ε c : 𝓞 F) : F) * c.out.1)| ≤ C₀ * |τ' (((ε c : 𝓞 F) : F) * c.out.1)|) →
      Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
        ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N) := by
  intro F _ _ _ 𝔞 𝔟 C₀ m
  set n := Fintype.card (Emb F) with hn_def
  set f := Module.finrank ℚ F with hf_def
  refine ⟨m * n + (f + 1), fun ε hbal => ?_⟩
  set N := m * n + (f + 1) with hN
  rcases isEmpty_or_nonempty (Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) with hE | ⟨⟨c₀⟩⟩
  · exact summable_empty
  have hn : 1 ≤ n := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact Fintype.card_pos_iff.2 ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩
  obtain ⟨τ₀⟩ : Nonempty (Emb F) := Fintype.card_pos_iff.1 hn
  obtain ⟨β, hβ, hβS⟩ := exists_absSum_lower (𝔟 : FractionalIdeal (𝓞 F)⁰ F)

  let bp : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → F := fun c => ((ε c : 𝓞 F) : F) * c.out.1
  have hunit0 : ∀ u : (𝓞 F)ˣ, ((u : 𝓞 F) : F) ≠ 0 := fun u h =>
    u.ne_zero (by exact_mod_cast h)
  have hbp_mem : ∀ c, bp c ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := fun c => by
    have := Submodule.smul_mem (𝔟 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε c : 𝓞 F) c.out.2.1
    rwa [Algebra.smul_def] at this
  have hbp0 : ∀ c, bp c ≠ 0 := fun c => mul_ne_zero (hunit0 _) c.out.2.2
  have hC₀ : 1 ≤ C₀ := by
    have h := hbal c₀ τ₀ τ₀
    have hpos : 0 < |τ₀ (bp c₀)| := abs_pos.2 ((map_ne_zero τ₀).2 (hbp0 c₀))
    exact le_of_mul_le_mul_right (by rw [one_mul]; exact h) hpos
  have hq : 0 < (n : ℝ) * C₀ := mul_pos (by exact_mod_cast hn) (by linarith)
  have hlow : ∀ c (τ : Emb F), absSum (bp c) / (n * C₀) ≤ |τ (bp c)| := by
    intro c τ
    rw [div_le_iff₀ hq]
    calc absSum (bp c) = ∑ τ' : Emb F, |τ' (bp c)| := rfl
      _ ≤ ∑ _τ' : Emb F, C₀ * |τ (bp c)| := Finset.sum_le_sum fun τ' _ => hbal c τ' τ
      _ = |τ (bp c)| * (n * C₀) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

  let g : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → ℝ := fun c => ((absSum (bp c)) ^ (f + 1))⁻¹
  let h : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ := fun y => ((absSum y.1) ^ N)⁻¹
  have hg : Summable g := by
    refine (summable_absSum_inv_pow 𝔟 (k := f + 1) (by omega)).comp_injective
      (i := fun c => (⟨bp c, hbp_mem c, hbp0 c⟩ : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) ?_
    intro c c' hcc
    have e : bp c = bp c' := congrArg Subtype.val hcc
    refine Quotient.out_equiv_out.1 ⟨(ε c')⁻¹ * ε c, ?_⟩
    have h1 : (((ε c')⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c' : 𝓞 F) : F) = 1 := unit_inv_mul (ε c')
    simp only [bp] at e
    push_cast
    linear_combination (-(c'.out.1) * h1) - ((((ε c')⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * e
  have hh : Summable h := summable_absSum_inv_pow 𝔞 (k := N) (by omega)
  let e : (Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → (Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := fun p =>
    (p.1, ⟨((((ε p.1)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * p.2.1, by
      have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule
        (((ε p.1)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) p.2.2.1
      rwa [Algebra.smul_def] at this, mul_ne_zero (hunit0 _) p.2.2.2⟩)
  have he : Function.Injective e := by
    rintro ⟨c, ν⟩ ⟨c', ν'⟩ hcc
    have h1 : c = c' := congrArg Prod.fst hcc
    subst h1
    have h2 := congrArg (fun p => (p.2 : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)).1) hcc
    simp only [e] at h2
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel₀ (hunit0 _) h2))
  have hV := (hg.mul_of_nonneg hh (fun c => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))
    (fun y => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))).comp_injective he
  set K₁ : ℝ := 1 + n * C₀ / β ^ 2 with hK₁
  refine (hV.mul_left (K₁ ^ (m * n) * (n * C₀) ^ N)).of_nonneg_of_le
    (fun p => Finset.prod_nonneg fun τ _ => div_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _))
    (fun p => ?_)

  obtain ⟨c, ν⟩ := p
  set b' := bp c with hb'
  set ν' := ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1 with hν'
  set s := absSum b' with hs
  set x := absSum ν' with hx
  have hsβ : β ≤ s := hβS _ (hbp_mem c) (hbp0 c)
  have hs0 : 0 < s := hβ.trans_le hsβ
  have hx0 : 0 < x := absSum_pos (mul_ne_zero (hunit0 _) ν.2.2)
  have hid : ∀ τ : Emb F, |τ ν.1 * τ c.out.1| = |τ ν'| * |τ b'| := by
    intro τ
    have h1 : (((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c : 𝓞 F) : F) = 1 := unit_inv_mul (ε c)
    rw [← abs_mul, ← map_mul, ← map_mul]
    congr 2
    simp only [hν', hb', bp]
    linear_combination (-(ν.1 * c.out.1)) * h1
  have hA : ∀ τ : Emb F, |τ b'| + |τ b'|⁻¹ ≤ K₁ * s := by
    intro τ
    have hlo := hlow c τ
    have hpos : 0 < s / (n * C₀) := div_pos hs0 hq
    have h1 : |τ b'|⁻¹ ≤ n * C₀ / s := by
      calc |τ b'|⁻¹ ≤ (s / (n * C₀))⁻¹ := inv_anti₀ hpos hlo
        _ = n * C₀ / s := inv_div _ _
    have h2 : n * C₀ / s ≤ n * C₀ / β ^ 2 * s := by
      rw [div_le_iff₀ hs0]
      have hβ2 : β ^ 2 ≤ s * s := by nlinarith
      calc (n : ℝ) * C₀ = n * C₀ / β ^ 2 * β ^ 2 := by field_simp
        _ ≤ n * C₀ / β ^ 2 * (s * s) := mul_le_mul_of_nonneg_left hβ2 (by positivity)
        _ = _ := by ring
    have h3 : |τ b'| ≤ s := abs_le_absSum _ τ
    rw [hK₁]; nlinarith
  have hnum : ∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m ≤ (K₁ * s) ^ (m * n) := by
    calc ∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m ≤ ∏ _τ : Emb F, (K₁ * s) ^ m :=
          Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (by positivity) _) (fun τ _ => pow_le_pow_left₀ (by positivity) (hA τ) m)
      _ = (K₁ * s) ^ (m * n) := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hden : (x * (s / (n * C₀))) ^ N ≤ ∏ τ : Emb F, (1 + |τ ν.1 * τ c.out.1|) ^ N := by
    rw [Finset.prod_pow]
    refine pow_le_pow_left₀ (mul_nonneg hx0.le (div_pos hs0 hq).le) ?_ N
    calc x * (s / (n * C₀)) = ∑ τ : Emb F, |τ ν'| * (s / (n * C₀)) := by rw [hx, absSum, Finset.sum_mul]
      _ ≤ ∑ τ : Emb F, |τ ν.1 * τ c.out.1| := Finset.sum_le_sum fun τ _ => by
          rw [hid]; exact mul_le_mul_of_nonneg_left (hlow c τ) (abs_nonneg _)
      _ ≤ 1 + ∑ τ : Emb F, |τ ν.1 * τ c.out.1| := by linarith
      _ ≤ _ := one_add_sum_le_prod _ _ fun τ => abs_nonneg _
  have hdpos : 0 < (x * (s / (n * C₀))) ^ N := pow_pos (mul_pos hx0 (div_pos hs0 hq)) N
  show ∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m / (1 + |τ ν.1 * τ c.out.1|) ^ N ≤
    K₁ ^ (m * n) * (n * C₀) ^ N * (((s) ^ (f + 1))⁻¹ * ((x) ^ N)⁻¹)
  rw [Finset.prod_div_distrib]
  calc (∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m) / ∏ τ : Emb F, (1 + |τ ν.1 * τ c.out.1|) ^ N
      ≤ (K₁ * s) ^ (m * n) / (x * (s / (n * C₀))) ^ N :=
        div_le_div₀ (by positivity) hnum hdpos hden
    _ = K₁ ^ (m * n) * (n * C₀) ^ N * ((s ^ (f + 1))⁻¹ * (x ^ N)⁻¹) := by
        rw [hN]
        exact bound_eq _ _ _ _ _ _ hs0.ne' hx0.ne' hq.ne'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeBalancedLatticeDoubleSumStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_heckeBalancedLatticeDoubleSum : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (C₀ : ℝ) (m : ℕ), ∃ N : ℕ,
    ∀ ε : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → (𝓞 F)ˣ,
      (∀ c (τ τ' : Emb F), |τ (((ε c : 𝓞 F) : F) * c.out.1)| ≤ C₀ * |τ' (((ε c : 𝓞 F) : F) * c.out.1)|) →
      Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
        ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N) := by
  first | exact @GlobalTheory.HeckeTwo.summable_balanced_latSum | exact GlobalTheory.HeckeTwo.summable_balanced_latSum | (intros; apply GlobalTheory.HeckeTwo.summable_balanced_latSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBound
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem fTerm_deriv_summable_bound : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  intro F _ _ _ 𝔞 𝔟 K hK hKH L hL hLU n
  obtain ⟨m, hm⟩ := GlobalTheory.T.norm_iteratedFDeriv_fTerm_le_of_isCompact F K hK hKH L hL hLU n
  obtain ⟨C₀, -, hC₀⟩ := GlobalTheory.T.exists_balanced_unit_multiple_totallyReal F
  obtain ⟨N, hN⟩ := GlobalTheory.T.summable_heckeBalancedLatticeDoubleSum F 𝔞 𝔟 C₀ m
  obtain ⟨C, hC⟩ := hm N
  choose ε hε using fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) => hC₀ c.out.1 c.out.2.2
  refine ⟨fun p => C * ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N, (hN ε hε).mul_left C, ?_⟩
  rintro ⟨c, ν⟩ σ hσ z hz
  have hee : (((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c : 𝓞 F) : F) = 1 := unit_inv_mul (ε c)
  have hfun : (fun z : Emb F → ℂ => fTerm σ z c.out.1 ν.1) =
      fun z => fTerm σ z (((ε c : 𝓞 F) : F) * c.out.1) (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) := by
    funext z
    have hb : c.out.1 = ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (((ε c : 𝓞 F) : F) * c.out.1) := by
      rw [← mul_assoc, hee, one_mul]
    conv_lhs => rw [hb]
    exact GlobalTheory.T.heckeEisensteinFourierTerm_move_unit F σ z _ _ (ε c)⁻¹
  have hb0 : ((ε c : 𝓞 F) : F) * c.out.1 ≠ 0 := mul_ne_zero (right_ne_zero_of_mul_eq_one hee) c.out.2.2
  have hν0 : ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1 ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hee) ν.2.2
  dsimp only
  rw [hfun]
  refine (hC σ hσ z hz _ _ hb0 hν0).trans (le_of_eq ?_)
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrArg τ hee
  rw [map_mul, map_one] at h1
  have h2 : τ (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) * τ (((ε c : 𝓞 F) : F) * c.out.1) = τ ν.1 * τ c.out.1 := by
    rw [map_mul, map_mul]; linear_combination (τ ν.1 * τ c.out.1) * h1
  rw [h2]

end GlobalTheory.HeckeTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBoundStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  first | exact @GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | exact GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound | (intros; apply GlobalTheory.HeckeTwo.fTerm_deriv_summable_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoIsGoodOfTsum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoIsGoodOfTsum
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.SumGood

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [ProperSpace V] {ι : Type}

def GoodFam {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (U : Set V) (f : ι → V → E) : Prop :=
  (∀ i, ContDiffOn ℝ ∞ (f i) U) ∧
  ∀ L : Set V, IsCompact L → L ⊆ U → ∀ k : ℕ,
    ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ z ∈ L, ‖iteratedFDeriv ℝ k (f i) z‖ ≤ u i

theorem hasFDerivAt_tsum {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) {z : V} (hz : z ∈ U) :
    HasFDerivAt (fun y => ∑' i, f i y) (∑' i, fderiv ℝ (f i) z) z := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU z hz
  have hsub : Metric.closedBall z (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrU
  have hK : IsCompact (Metric.closedBall z (r / 2)) := isCompact_closedBall z (r / 2)
  obtain ⟨u1, hu1, hb1⟩ := hf.2 _ hK hsub 1
  obtain ⟨u0, hu0, hb0⟩ := hf.2 _ hK hsub 0
  have hzb : z ∈ Metric.ball z (r / 2) := Metric.mem_ball_self (by linarith)
  refine hasFDerivAt_tsum_of_isPreconnected hu1 Metric.isOpen_ball
    (convex_ball z (r / 2)).isPreconnected (fun i y hy => ?_) (fun i y hy => ?_) hzb ?_ hzb
  · have hyU : y ∈ U := hsub (Metric.ball_subset_closedBall hy)
    exact (((hf.1 i).contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)).hasFDerivAt
  · have := hb1 i y (Metric.ball_subset_closedBall hy)
    rwa [norm_iteratedFDeriv_one] at this
  · refine Summable.of_norm_bounded hu0 (fun i => ?_)
    have := hb0 i z (Metric.mem_closedBall_self (by linarith))
    rwa [norm_iteratedFDeriv_zero] at this

theorem goodFam_fderiv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) :
    GoodFam U (fun i => fderiv ℝ (f i)) := by
  refine ⟨fun i => (hf.1 i).fderiv_of_isOpen hU (by simp), fun L hL hLU k => ?_⟩
  obtain ⟨u, hu, hb⟩ := hf.2 L hL hLU (k + 1)
  exact ⟨u, hu, fun i z hz => by rw [norm_iteratedFDeriv_fderiv]; exact hb i z hz⟩

theorem contDiffOn_tsum {U : Set V} (hU : IsOpen U) (n : ℕ) :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : ι → V → E},
      GoodFam U f → ContDiffOn ℝ n (fun y => ∑' i, f i y) U := by
  induction n with
  | zero =>
    intro E _ _ _ f hf
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun z hz => (hasFDerivAt_tsum hU hf hz).continuousAt.continuousWithinAt
  | succ n ih =>
    intro E _ _ _ f hf
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    refine ⟨fun z hz => (hasFDerivAt_tsum hU hf hz).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, ?_⟩
    exact (ih (goodFam_fderiv hU hf)).congr fun z hz => (hasFDerivAt_tsum hU hf hz).fderiv

theorem contDiffOn_tsum_infty {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set V} (hU : IsOpen U) {f : ι → V → E} (hf : GoodFam U f) :
    ContDiffOn ℝ ∞ (fun y => ∑' i, f i y) U :=
  contDiffOn_infty.2 fun n => contDiffOn_tsum hU n hf

end General

section Wirtinger

variable {Φ : Type} [Fintype Φ] {ι : Type}

theorem wirt_eq_clm (τ : Φ) (b : Bool) :
    ∃ Λ : ((Φ → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ, ∀ (h : (Φ → ℂ) → ℂ) (z : Φ → ℂ),
      wirt τ b h z = Λ (fderiv ℝ h z) := by
  classical
  refine ⟨(1 / 2 : ℝ) • (ContinuousLinearMap.apply ℝ ℂ (Pi.single τ 1) +
    (ContinuousLinearMap.mul ℝ ℂ (if b then I else -I)).comp
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single τ I))), fun h z => ?_⟩
  simp only [wirt, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply',
    Complex.real_smul]
  push_cast
  ring

theorem wirtWord_congr {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool))
    {f g : (Φ → ℂ) → ℂ} (h : Set.EqOn f g U) : Set.EqOn (wirtWord w f) (wirtWord w g) U := by
  induction w with
  | nil => exact h
  | cons a w ih => exact GoodAdd.wirt_congr hU ih a.1 a.2

theorem norm_iteratedFDeriv_wirtWord {U : Set (Φ → ℂ)} (hU : IsOpen U) (w : List (Φ × Bool)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : (Φ → ℂ) → ℂ, ContDiffOn ℝ ∞ h U → ∀ k : ℕ, ∀ z ∈ U,
      ‖iteratedFDeriv ℝ k (wirtWord w h) z‖ ≤ C * ‖iteratedFDeriv ℝ (k + w.length) h z‖ := by
  induction w with
  | nil => exact ⟨1, zero_le_one, fun h _ k z _ => by simp [wirtWord_nil]⟩
  | cons a w ih =>
    obtain ⟨C, hC0, hC⟩ := ih
    obtain ⟨Λ, hΛ⟩ := wirt_eq_clm a.1 a.2
    refine ⟨‖Λ‖ * C, mul_nonneg (norm_nonneg _) hC0, fun h hh k z hz => ?_⟩
    have e : wirtWord (a :: w) h = Λ ∘ fderiv ℝ (wirtWord w h) := by
      rw [wirtWord_cons]; funext y; exact hΛ _ y
    have hs : ContDiffOn ℝ ∞ (wirtWord w h) U := GoodAdd.wirtWord_contDiffOn hU w hh
    have hd : ContDiffAt ℝ ∞ (fderiv ℝ (wirtWord w h)) z :=
      (hs.fderiv_of_isOpen hU (by simp)).contDiffAt (hU.mem_nhds hz)
    rw [e]
    calc ‖iteratedFDeriv ℝ k (Λ ∘ fderiv ℝ (wirtWord w h)) z‖
        ≤ ‖Λ‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ (wirtWord w h)) z‖ :=
          Λ.norm_iteratedFDeriv_comp_left hd (by exact_mod_cast le_top)
      _ = ‖Λ‖ * ‖iteratedFDeriv ℝ (k + 1) (wirtWord w h) z‖ := by rw [norm_iteratedFDeriv_fderiv]
      _ ≤ ‖Λ‖ * (C * ‖iteratedFDeriv ℝ (k + 1 + w.length) h z‖) :=
          mul_le_mul_of_nonneg_left (hC h hh (k + 1) z hz) (norm_nonneg _)
      _ = ‖Λ‖ * C * ‖iteratedFDeriv ℝ (k + (a :: w).length) h z‖ := by
          rw [List.length_cons, show k + 1 + w.length = k + (w.length + 1) by ring]; ring

theorem goodFam_wirtWord {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : ι → (Φ → ℂ) → ℂ}
    (hf : GoodFam U f) (w : List (Φ × Bool)) : GoodFam U (fun i => wirtWord w (f i)) := by
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_wirtWord hU w
  refine ⟨fun i => GoodAdd.wirtWord_contDiffOn hU w (hf.1 i), fun L hL hLU k => ?_⟩
  obtain ⟨u, hu, hb⟩ := hf.2 L hL hLU (k + w.length)
  refine ⟨fun i => C * u i, hu.mul_left C, fun i z hz => ?_⟩
  exact (hC (f i) (hf.1 i) k z (hLU hz)).trans (mul_le_mul_of_nonneg_left (hb i z hz) hC0)

theorem wirtWord_tsum {U : Set (Φ → ℂ)} (hU : IsOpen U) {f : ι → (Φ → ℂ) → ℂ}
    (hf : GoodFam U f) (w : List (Φ × Bool)) :
    Set.EqOn (wirtWord w (fun y => ∑' i, f i y)) (fun y => ∑' i, wirtWord w (f i) y) U := by
  induction w with
  | nil => intro z _; rfl
  | cons a w ih =>
    intro z hz
    obtain ⟨Λ, hΛ⟩ := wirt_eq_clm a.1 a.2
    have hg := goodFam_wirtWord hU hf w
    have hsum : Summable (fun i => fderiv ℝ (wirtWord w (f i)) z) := by
      obtain ⟨u, hu, hb⟩ := hg.2 {z} isCompact_singleton (Set.singleton_subset_iff.2 hz) 1
      exact Summable.of_norm_bounded hu fun i => by
        simpa [norm_iteratedFDeriv_one] using hb i z (Set.mem_singleton z)
    rw [wirtWord_cons, GoodAdd.wirt_congr hU ih a.1 a.2 hz, hΛ, (hasFDerivAt_tsum hU hg hz).fderiv,
      Λ.map_tsum hsum]
    simp only [wirtWord_cons, hΛ]

end Wirtinger

end GlobalTheory.HeckeTwo.SumGood


open GlobalTheory.HeckeTwo.SumGood in
theorem GlobalTheory.HeckeTwo.isGood_of_tsum : ∀ (F : Type) [Field F] [NumberField F] (ι : Type)
    (g : ι → ℂ → (Emb F → ℂ) → ℂ) (P : ℂ → (Emb F → ℂ) → ℂ),
    (∀ i, ∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (g i σ) (upperHalf F)) →
    (∀ i, ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F,
      DifferentiableOn ℂ (fun σ => wirtWord w (g i σ) z) halfPlane) →
    (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F →
      ∀ n : ℕ, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (g i σ) z‖ ≤ u i) →
    (∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F, P σ z = ∑' i, g i σ z) →
    IsGood P := by
  intro F _ _ ι g P h1 h2 h3 h4
  have hU := GoodAdd.upperHalf_isOpen F
  have hfam : ∀ σ ∈ halfPlane, GoodFam (upperHalf F) (fun i => g i σ) := fun σ hσ =>
    ⟨fun i => h1 i σ hσ, fun L hL hLU k => by
      obtain ⟨u, hu, hb⟩ := h3 {σ} isCompact_singleton (Set.singleton_subset_iff.2 hσ) L hL hLU k
      exact ⟨u, hu, fun i z hz => hb i σ rfl z hz⟩⟩
  have hPeq : ∀ σ ∈ halfPlane, Set.EqOn (P σ) (fun z => ∑' i, g i σ z) (upperHalf F) :=
    fun σ hσ z hz => h4 σ hσ z hz
  refine ⟨fun σ hσ => (contDiffOn_tsum_infty hU (hfam σ hσ)).congr (hPeq σ hσ), fun w z hz => ?_⟩
  have heq : ∀ σ ∈ halfPlane, wirtWord w (P σ) z = ∑' i, wirtWord w (g i σ) z := fun σ hσ => by
    rw [wirtWord_congr hU w (hPeq σ hσ) hz]
    exact wirtWord_tsum hU (hfam σ hσ) w hz
  obtain ⟨C, hC0, hC⟩ := norm_iteratedFDeriv_wirtWord hU w
  have hHo : IsOpen (halfPlane : Set ℂ) := isOpen_lt continuous_const Complex.continuous_re
  refine DifferentiableOn.congr ?_ heq
  intro σ₀ hσ₀
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hHo σ₀ hσ₀
  have hsub : Metric.closedBall σ₀ (r / 2) ⊆ halfPlane :=
    (Metric.closedBall_subset_ball (by linarith)).trans hrU
  obtain ⟨u, hu, hb⟩ := h3 _ (isCompact_closedBall σ₀ (r / 2)) hsub {z} isCompact_singleton
    (Set.singleton_subset_iff.2 hz) w.length
  have hd : DifferentiableOn ℂ (fun σ => ∑' i, wirtWord w (g i σ) z) (Metric.ball σ₀ (r / 2)) := by
    refine differentiableOn_tsum_of_summable_norm (hu.mul_left C)
      (fun i => (h2 i w z hz).mono (Metric.ball_subset_closedBall.trans hsub)) Metric.isOpen_ball ?_
    intro i σ hσ
    have := hC (g i σ) (h1 i σ (hsub (Metric.ball_subset_closedBall hσ))) 0 z hz
    rw [norm_iteratedFDeriv_zero, Nat.zero_add] at this
    exact this.trans (mul_le_mul_of_nonneg_left (hb i σ (Metric.ball_subset_closedBall hσ) z rfl) hC0)
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds
    (Metric.mem_ball_self (by linarith)))).differentiableWithinAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoIsGoodOfTsumStatement
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwo_isGood_of_tsum : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (g : ι → ℂ → (Emb F → ℂ) → ℂ) (P : ℂ → (Emb F → ℂ) → ℂ),
  (∀ i, ∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (g i σ) (upperHalf F)) →
  (∀ i, ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (g i σ) z) halfPlane) →
  (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (g i σ) z‖ ≤ u i) →
  (∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F, P σ z = ∑' i, g i σ z) →
  IsGood P := by
  first | exact @GlobalTheory.HeckeTwo.isGood_of_tsum | exact GlobalTheory.HeckeTwo.isGood_of_tsum | (intros; apply GlobalTheory.HeckeTwo.isGood_of_tsum <;> assumption)
end
end

noncomputable section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

namespace GlobalTheory.HeckeTwo

theorem bOne_isGood : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  intro F _ _ _ 𝔞 𝔟
  refine GlobalTheory.T.heckeWeightTwo_isGood_of_tsum F _ (fun p σ z => fTerm σ z (p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ×
      NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)).1.out.1 p.2.1) _
    (fun p σ hσ => GlobalTheory.T.contDiffOn_heckeEisensteinFourierTerm F _ _ p.1.out.2.2 σ hσ) (fun p w z hz => GlobalTheory.T.heckeFourierTerm_wirtingerWord_differentiableOn F _ _ p.1.out.2.2 w z hz)
    (GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound F 𝔞 𝔟) ?_
  intro σ hσ z hz
  obtain ⟨u, hu, hb⟩ := GlobalTheory.T.heckeWeightTwo_term_iteratedFDeriv_summable_bound F 𝔞 𝔟 {σ} isCompact_singleton (by simpa using hσ) {z} isCompact_singleton
    (by simpa using hz) 0
  have hs : Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
      fTerm σ z p.1.out.1 p.2.1) := by
    refine Summable.of_norm_bounded hu fun p => ?_
    have := hb p σ rfl z rfl
    rwa [norm_iteratedFDeriv_zero] at this
  unfold bOne
  exact (hs.tsum_prod' fun c => hs.prod_factor c).symm

end GlobalTheory.HeckeTwo
end
end

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEisensteinNonconstantFourierSum_smoothHolomorphic : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F), GlobalTheory.HeckeTwo.IsGood (GlobalTheory.HeckeTwo.bOne 𝔞 𝔟) := by
  first | exact @GlobalTheory.HeckeTwo.bOne_isGood | exact GlobalTheory.HeckeTwo.bOne_isGood | (intros; apply GlobalTheory.HeckeTwo.bOne_isGood <;> assumption)
