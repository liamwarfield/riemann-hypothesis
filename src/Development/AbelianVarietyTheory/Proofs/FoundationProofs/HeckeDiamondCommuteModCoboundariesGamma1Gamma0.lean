module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeriodMapEquivariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraDecompositionCocycle
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDoubleCosetRepsGammaOneGammaZeroLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommutesDiamond

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCompMul
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCompMul
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem isDia_mul {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : IsDia N l d σ) (hτ : IsDia N l e τ) :
    IsDia N l (d * e) (σ * τ) := by
  obtain ⟨hσ0, hσ1⟩ := hσ
  obtain ⟨hτ0, hτ1⟩ := hτ
  have hσ0' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    have := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hσ0
    simpa using this
  constructor
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hσ0, hτ0]; ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hσ0', hσ1, hτ1]; ring

theorem dia_mul : ∀ (N l : ℕ) (k d e : ℤ) (σ τ ρ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ →
    GlobalTheory.Hk.IsDia N l e τ → GlobalTheory.Hk.IsDia N l (d * e) ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.dia k τ (GlobalTheory.Hk.dia k σ ⇑f) = GlobalTheory.Hk.dia k ρ ⇑f := by
  intro N l k d e σ τ ρ hN hσ hτ hρ f
  have h := GlobalTheory.T.diamondOperatorOfMatrix_congr N l k (d * e) (σ * τ) ρ hN (isDia_mul hσ hτ) hρ f
  rw [← h]
  simp only [dia]
  rw [SlashAction.slash_mul]

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCompMulStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondOperatorOfMatrix_comp_mul : ∀ (N l : ℕ) (k d e : ℤ) (σ τ ρ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l e τ → GlobalTheory.Hk.IsDia N l (d * e) ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.dia k τ (GlobalTheory.Hk.dia k σ ⇑f) = GlobalTheory.Hk.dia k ρ ⇑f := by
  first | exact @GlobalTheory.Hk.dia_mul | exact GlobalTheory.Hk.dia_mul | (intros; apply GlobalTheory.Hk.dia_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1InterGamma0ModularFormHasSumQExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1InterGamma0ModularFormHasSumQExpansion
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem one_mem_strictPeriods_lev (N l : ℕ) :
    (1 : ℝ) ∈ ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem]
  · exact AddSubgroup.mem_zmultiples 1
  · refine ⟨?_, ?_⟩
    · show ModularGroup.T ∈ Gamma1 N
      rw [CongruenceSubgroup.Gamma1_mem]
      simp [ModularGroup.T]
    · show ModularGroup.T ∈ Gamma0 l
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [ModularGroup.T]

theorem lev_hasSum_coef : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ (f : ModularForm (lev N l) k) (τ : ℍ),
    HasSum (fun m => coef ⇑f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  intro N l k _ f τ
  have h1 := one_mem_strictPeriods_lev N l
  haveI : Fact (IsCusp OnePoint.infty ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularForm.hasSum_qExpansion f one_pos h1 τ

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1InterGamma0ModularFormHasSumQExpansionStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (τ : ℍ), HasSum (fun m => GlobalTheory.Hk.coef ⇑f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  first | exact @GlobalTheory.Hk.lev_hasSum_coef | exact GlobalTheory.Hk.lev_hasSum_coef | (intros; apply GlobalTheory.Hk.lev_hasSum_coef <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTCoeffFormulaCommDistinctPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffHeckeTOperatorGamma1InterGamma0
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffPeriodOneEqOfHasSum
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffPeriodOneEqOfHasSum
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory Filter Topology
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem hasSum_cuspFunction_of_hasSum {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hs : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ))
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    HasSum (fun m => a m • q ^ m) (cuspFunction 1 f q) := by
  have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq1 hq0
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q, h1⟩
  have h2 := Function.Periodic.cuspFunction_eq_of_nonzero 1 (f ∘ ofComplex) hq0
  have h3 : cuspFunction 1 f q = f τ := by
    simpa [cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  have h4 : Function.Periodic.qParam 1 (τ : ℂ) = q :=
    Function.Periodic.qParam_right_inv one_ne_zero hq0
  rw [h3, ← h4]
  exact hs τ

theorem analyticAt_cuspFunction_of_hasSum {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hs : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) :
    AnalyticAt ℂ (cuspFunction 1 f) 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hrad : 1 ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    have hq0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0
    have hq1 : ‖((r : ℝ) : ℂ)‖ < 1 := by
      have : (r : ℝ) < 1 := by exact_mod_cast hr
      simpa using this
    have ht := (hasSum_cuspFunction_of_hasSum hs hq0 hq1).summable.tendsto_atTop_zero.norm
    refine p.le_radius_of_tendsto (l := 0) ?_
    have ht' : Tendsto (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n) atTop (𝓝 0) := by simpa using ht
    convert ht' using 2 with n
    simp [hp, FormalMultilinearSeries.ofScalars_norm]
  have hpos : 0 < p.radius := lt_of_lt_of_le zero_lt_one hrad
  have hP := p.hasFPowerSeriesOnBall hpos
  have hAn : AnalyticAt ℂ p.sum 0 := hP.analyticAt
  have hne : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → cuspFunction 1 f q = p.sum q := by
    intro q hq0 hq1
    rw [hp, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq a q,
      (hasSum_cuspFunction_of_hasSum hs hq0 hq1).tsum_eq]
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
  have hev : ∀ᶠ q in 𝓝[≠] (0 : ℂ), cuspFunction 1 f q = p.sum q := by
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with q hq hq0
    exact hne q hq0 (by simpa using hq)
  have h0 : cuspFunction 1 f 0 = p.sum 0 := by
    have ht : Tendsto (cuspFunction 1 f) (𝓝[≠] 0) (𝓝 (p.sum 0)) :=
      (hAn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun q hq => hq.symm)
    simp only [cuspFunction, Function.Periodic.cuspFunction, Function.update_self]
    refine Tendsto.limUnder_eq ?_
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq0
    simp [cuspFunction, Function.Periodic.cuspFunction, Function.update_of_ne hq0]
  refine hAn.congr ?_
  filter_upwards [hball] with q hq
  rcases eq_or_ne q 0 with rfl | hq0
  · exact h0.symm
  · exact (hne q hq0 (by simpa using hq)).symm

theorem coef_of_hasSum : ∀ (f : ℍ → ℂ) (a : ℕ → ℂ),
    (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) →
      ∀ n, GlobalTheory.Hk.coef f n = a n := by
  intro f a hs n
  have han := analyticAt_cuspFunction_of_hasSum hs
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos han hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction 1 f)
      (FormalMultilinearSeries.ofScalars ℂ fun m => coef f m) 0 := by
    simpa [coef, qExpansion_coeff, div_eq_mul_inv, mul_comm] using han.hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · n) (h2.eq_formalMultilinearSeries h1)

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffPeriodOneEqOfHasSumStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionCoeffPeriodOne_eq_of_hasSum : ∀ (f : ℍ → ℂ) (a : ℕ → ℂ), (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ n, GlobalTheory.Hk.coef f n = a n := by
  first | exact @GlobalTheory.Hk.coef_of_hasSum | exact GlobalTheory.Hk.coef_of_hasSum | (intros; apply GlobalTheory.Hk.coef_of_hasSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeUOperatorExplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeUOperatorExplicit
noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold Real

namespace GlobalTheory.Hk

private theorem im_div_pos' {p : ℕ} (hp : 0 < p) {z : ℂ} (hz : 0 < z.im) (b : ℕ) :
    0 < ((z + b) / (p : ℂ)).im := by
  have : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Complex.div_natCast_im]
  simpa using div_pos hz this

private theorem sum_root' {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ∑ b ∈ Finset.range p, (Complex.exp (2 * π * Complex.I / p) ^ b) ^ m =
      if p ∣ m then (p : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp p hp.ne'
  set ζ := Complex.exp (2 * π * Complex.I / p)
  simp_rw [← pow_mul, fun b => mul_comm b m, pow_mul]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]; simp
  · have h1 : ζ ^ m ≠ 1 := fun e => h ((hζ.pow_eq_one_iff_dvd m).1 e)
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one]; simp

theorem hasSum_uOp (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (hq0 : 0 < q)
    (hf : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun m => a (q * m) • Function.Periodic.qParam 1 τ ^ m) (uOp q f τ) := by
  have hp0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hinj : Function.Injective fun m : ℕ => q * m := mul_right_injective₀ hq0.ne'
  have hrange : ∀ n, n ∉ Set.range (fun m : ℕ => q * m) → ¬ q ∣ n :=
    fun n hn ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
  set Q := Function.Periodic.qParam 1 τ with hQ
  set x := Complex.exp (2 * π * Complex.I * τ / q) with hx
  have hxq : x ^ q = Q := by
    rw [hx, ← Complex.exp_nat_mul, hQ, Function.Periodic.qParam]; congr 1; push_cast; field_simp
  have hB : ∀ b : ℕ, HasSum (fun m => a m * x ^ m * (Complex.exp (2 * π * Complex.I / q) ^ b) ^ m)
      (f (ofComplex (((τ : ℂ) + b) / q))) := fun b => by
    have h := hf (ofComplex (((τ : ℂ) + b) / q))
    rw [ofComplex_apply_of_im_pos (im_div_pos' hq0 τ.2 b)] at h ⊢
    convert h using 2 with m
    have e : Function.Periodic.qParam 1 (((τ : ℂ) + b) / q) =
        x * Complex.exp (2 * π * Complex.I / q) ^ b := by
      rw [hx, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    simp [e, mul_pow, mul_assoc]
  have hC := hasSum_sum (s := Finset.range q) fun b _ => hB b
  simp_rw [← Finset.mul_sum, sum_root' hq0] at hC
  rw [← hinj.hasSum_iff fun n hn => by simp [hrange n hn]] at hC
  have hD := hC.mul_left (q : ℂ)⁻¹
  refine cast (congrArg (HasSum · (uOp q f τ)) (funext fun n => ?_)) hD
  simp only [Function.comp, dvd_mul_right, if_true, pow_mul, hxq, smul_eq_mul]
  field_simp

end GlobalTheory.Hk
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeUOperatorExplicitStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_heckeUOperatorExplicit : ∀ (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < q → (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ τ : ℍ, HasSum (fun m => a (q * m) • Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.uOp q f τ) := by
  first | exact @GlobalTheory.Hk.hasSum_uOp | exact GlobalTheory.Hk.hasSum_uOp | (intros; apply GlobalTheory.Hk.hasSum_uOp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeVOperatorExplicit
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeVOperatorExplicit
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem vOp_hasSum (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ) (hq : 0 < q)
    (hf : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) (τ : ℍ) :
    HasSum (fun m => (if q ∣ m then a (m / q) else 0) • Function.Periodic.qParam 1 τ ^ m)
      (GlobalTheory.Hk.vOp q f τ) := by
  have him : 0 < ((q : ℂ) * (τ : ℂ)).im := by
    have : ((q : ℂ) * (τ : ℂ)).im = (q : ℝ) * τ.im := by simp
    rw [this]; exact mul_pos (by exact_mod_cast hq) τ.im_pos
  set τ' : ℍ := ofComplex ((q : ℂ) * τ) with hτ'
  have hc : (τ' : ℂ) = (q : ℂ) * τ := by
    rw [hτ', ofComplex_apply_of_im_pos him]
  have hqp : Function.Periodic.qParam 1 (τ' : ℂ) = Function.Periodic.qParam 1 (τ : ℂ) ^ q := by
    simp only [Function.Periodic.qParam, hc, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have h1 := hf τ'
  unfold vOp
  rw [← hτ']
  refine (Function.Injective.hasSum_iff (g := fun m : ℕ => q * m)
    (fun x y h => Nat.eq_of_mul_eq_mul_left hq h) ?_).mp ?_
  · intro x hx
    have : ¬ q ∣ x := by
      rintro ⟨c, rfl⟩; exact hx ⟨c, rfl⟩
    simp [this]
  · convert h1 using 1
    funext m
    simp only [Function.comp, dvd_mul_right, if_true, Nat.mul_div_cancel_left _ hq, hqp, ← pow_mul]

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumHeckeVOperatorExplicitStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_heckeVOperatorExplicit : ∀ (q : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < q → (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) → ∀ τ : ℍ, HasSum (fun m => (if q ∣ m then a (m / q) else 0) • Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.vOp q f τ) := by
  first | exact @GlobalTheory.Hk.vOp_hasSum | exact GlobalTheory.Hk.vOp_hasSum | (intros; apply GlobalTheory.Hk.vOp_hasSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffHeckeTOperatorGamma1InterGamma0
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem coef_heckeT : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l →
    GlobalTheory.Hk.IsDia N l q σ → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (n : ℕ),
    GlobalTheory.Hk.coef (GlobalTheory.Hk.heckeT k q σ ⇑f) n = GlobalTheory.Hk.coef ⇑f (q * n) +
      (q : ℂ) ^ (k - 1) * (if q ∣ n then GlobalTheory.Hk.coef (GlobalTheory.Hk.dia k σ ⇑f) (n / q) else 0) := by
  intro N l q k σ hN hq _ hσ f n
  have hq0 : 0 < q := hq.pos
  obtain ⟨g, hg⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k (q : ℤ) σ hN hσ f
  have hf := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN f
  have hgs := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN g
  have hU := GlobalTheory.T.hasSum_heckeUOperatorExplicit q (⇑f) (fun m => GlobalTheory.Hk.coef ⇑f m) hq0 hf
  have hV := GlobalTheory.T.hasSum_heckeVOperatorExplicit q (⇑g) (fun m => GlobalTheory.Hk.coef ⇑g m) hq0 hgs
  have hsum : ∀ τ : ℍ, HasSum (fun m => (GlobalTheory.Hk.coef ⇑f (q * m) +
      (q : ℂ) ^ (k - 1) * (if q ∣ m then GlobalTheory.Hk.coef ⇑g (m / q) else 0)) •
        Function.Periodic.qParam 1 τ ^ m) (GlobalTheory.Hk.heckeT k q σ ⇑f τ) := by
    intro τ
    have h2 := (hU τ).add ((hV τ).mul_left ((q : ℂ) ^ (k - 1)))
    have e : GlobalTheory.Hk.heckeT k q σ ⇑f τ =
        GlobalTheory.Hk.uOp q ⇑f τ + (q : ℂ) ^ (k - 1) * GlobalTheory.Hk.vOp q ⇑g τ := by
      rw [hg]; rfl
    rw [e]
    convert h2 using 1 <;> ext m <;> simp only [smul_eq_mul] <;> ring
  rw [GlobalTheory.T.qExpansionCoeffPeriodOne_eq_of_hasSum _ _ hsum n, ← hg]

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionCoeffHeckeTOperatorGamma1InterGamma0Statement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 : ∀ (N l q : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → q.Prime → ¬ q ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → ∀ (f : ModularForm (GlobalTheory.Hk.lev N l) k) (n : ℕ), GlobalTheory.Hk.coef (GlobalTheory.Hk.heckeT k q σ ⇑f) n = GlobalTheory.Hk.coef ⇑f (q * n) + (q : ℂ) ^ (k - 1) * (if q ∣ n then GlobalTheory.Hk.coef (GlobalTheory.Hk.dia k σ ⇑f) (n / q) else 0) := by
  first | exact @GlobalTheory.Hk.coef_heckeT | exact GlobalTheory.Hk.coef_heckeT | (intros; apply GlobalTheory.Hk.coef_heckeT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGamma1InterGamma0ExtQExpansionCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGamma1InterGamma0ExtQExpansionCoeff
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem eq_of_coef_eq : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ f g : ModularForm (GlobalTheory.Hk.lev N l) k,
    (∀ n, GlobalTheory.Hk.coef ⇑f n = GlobalTheory.Hk.coef ⇑g n) → f = g := by
  intro N l k hN f g h
  ext τ
  have hf := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN f τ
  have hg := GlobalTheory.T.gamma1InterGamma0_modularForm_hasSum_qExpansion N l k hN g τ
  simp_rw [h] at hf
  exact hf.unique hg

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFormGamma1InterGamma0ExtQExpansionCoeffStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularForm_gamma1InterGamma0_ext_qExpansionCoeff : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ f g : ModularForm (GlobalTheory.Hk.lev N l) k, (∀ n, GlobalTheory.Hk.coef ⇑f n = GlobalTheory.Hk.coef ⇑g n) → f = g := by
  first | exact @GlobalTheory.Hk.eq_of_coef_eq | exact GlobalTheory.Hk.eq_of_coef_eq | (intros; apply GlobalTheory.Hk.eq_of_coef_eq <;> assumption)
end
end

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

lemma isDia_mul_of_isDia {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : IsDia N l d σ)
    (hτ : IsDia N l e τ) : IsDia N l (d * e) (σ * τ) := by
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h3, h4⟩ := hτ
  have h1' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) h1
    simpa using this
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h3]; ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1', h2, h4]; ring

lemma heckeT_congr_dia {N l q : ℕ} {k : ℤ} {σ τ : SL(2, ℤ)} (hN : 0 < N)
    (hσ : IsDia N l q σ) (hτ : IsDia N l q τ) (f : ModularForm (lev N l) k) :
    heckeT k q σ ⇑f = heckeT k q τ ⇑f := by
  have := GlobalTheory.T.diamondOperatorOfMatrix_congr N l k q σ τ hN hσ hτ f
  unfold dia at this
  unfold heckeT
  rw [this]

lemma heckeT_coeff_formula_comm_distinct_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r) (kq kr : ℂ)
    (a b c e : ℕ → ℂ) (n : ℕ) :
    a (r * (q * n)) + kr * (if r ∣ q * n then b (q * n / r) else 0)
      + kq * (if q ∣ n then c (r * (n / q)) + kr * (if r ∣ n / q then e (n / q / r) else 0)
        else 0)
    = a (q * (r * n)) + kq * (if q ∣ r * n then c (r * n / q) else 0)
      + kr * (if r ∣ n then b (q * (n / r)) + kq * (if q ∣ n / r then e (n / r / q) else 0)
        else 0) := by
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hqr
  have i1 : r ∣ q * n ↔ r ∣ n := hcop.symm.dvd_mul_left
  have i2 : q ∣ r * n ↔ q ∣ n := hcop.dvd_mul_left
  have ha : r * (q * n) = q * (r * n) := by ring
  simp only [ha, i1, i2]
  by_cases hqn : q ∣ n <;> by_cases hrn : r ∣ n
  · have i3 : r ∣ n / q := by
      obtain ⟨m, rfl⟩ := hqn
      rw [Nat.mul_div_cancel_left _ hq.pos]
      exact (hcop.symm.dvd_mul_left).1 hrn
    have i4 : q ∣ n / r := by
      obtain ⟨m, rfl⟩ := hrn
      rw [Nat.mul_div_cancel_left _ hr.pos]
      exact (hcop.dvd_mul_left).1 hqn
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    have d3 : n / r / q = n / q / r := by
      rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm]
    simp only [hqn, hrn, i3, i4, if_true, d1, d2, d3]
    ring
  · have i3 : ¬ r ∣ n / q := by
      intro h
      exact hrn (h.trans (Nat.div_dvd_of_dvd hqn))
    have d2 : r * n / q = r * (n / q) := Nat.mul_div_assoc r hqn
    simp only [hqn, hrn, i3, if_true, if_false, d2]
    ring
  · have i4 : ¬ q ∣ n / r := by
      intro h
      exact hqn (h.trans (Nat.div_dvd_of_dvd hrn))
    have d1 : q * n / r = q * (n / r) := Nat.mul_div_assoc q hrn
    simp only [hqn, hrn, i4, if_true, if_false, d1]
    ring
  · simp only [hqn, hrn, if_false]
    ring

theorem heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ τ : SL(2, ℤ)), 0 < N → q.Prime → r.Prime →
    ¬ q ∣ N * l → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l q σ → GlobalTheory.Hk.IsDia N l r τ →
    ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
      GlobalTheory.Hk.heckeT k q σ (GlobalTheory.Hk.heckeT k r τ ⇑f) = GlobalTheory.Hk.heckeT k r τ (GlobalTheory.Hk.heckeT k q σ ⇑f) := by
  intro N l q r k σ τ hN hq hr hqN hrN hσ hτ f
  by_cases hqr : q = r
  · subst hqr
    obtain ⟨g, hg⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k τ hN hq hqN hτ f
    rw [heckeT_congr_dia hN hσ hτ f, ← hg, heckeT_congr_dia hN hσ hτ g]
  · obtain ⟨gr, hgr⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l r k τ hN hr hrN hτ f
    obtain ⟨gq, hgq⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN hq hqN hσ f
    obtain ⟨h1, hh1⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l q k σ hN hq hqN hσ gr
    obtain ⟨h2, hh2⟩ := GlobalTheory.T.heckeTOperatorExplicit_modularForm N l r k τ hN hr hrN hτ gq
    obtain ⟨fσ, hfσ⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k q σ hN hσ f
    obtain ⟨fτ, hfτ⟩ := GlobalTheory.T.diamondOperatorOfMatrix_modularForm_gamma1InterGamma0 N l k r τ hN hτ f
    have dσ : dia k σ ⇑gr = heckeT k r τ ⇑fσ := by
      rw [hgr, hfσ, GlobalTheory.T.hecke_operator_commutes_diamond N l r k q τ σ hN hr hrN hτ hσ f]
    have dτ : dia k τ ⇑gq = heckeT k q σ ⇑fτ := by
      rw [hgq, hfτ, GlobalTheory.T.hecke_operator_commutes_diamond N l q k r σ τ hN hq hqN hσ hτ f]
    have dd : dia k τ ⇑fσ = dia k σ ⇑fτ := by
      have h' : IsDia N l ((r : ℤ) * q) (σ * τ) := by
        rw [mul_comm]; exact isDia_mul_of_isDia hσ hτ
      rw [hfσ, hfτ, GlobalTheory.T.diamondOperatorOfMatrix_comp_mul N l k q r σ τ (σ * τ) hN hσ hτ (isDia_mul_of_isDia hσ hτ) f,
        GlobalTheory.T.diamondOperatorOfMatrix_comp_mul N l k r q τ σ (σ * τ) hN hτ hσ h' f]
    have key : h1 = h2 := by
      apply GlobalTheory.T.modularForm_gamma1InterGamma0_ext_qExpansionCoeff N l k hN
      intro n
      rw [hh1, hh2, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ gr, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ gq,
        dσ, dτ, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ fσ, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ fτ,
        hgr, hgq, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l r k τ hN hr hrN hτ f, GlobalTheory.T.qExpansionCoeff_heckeTOperator_gamma1InterGamma0 N l q k σ hN hq hqN hσ f,
        dd, hfσ, hfτ]
      exact heckeT_coeff_formula_comm_distinct_primes hq hr hqr _ _ _ _ _ _ n
    rw [← hgr, ← hgq, ← hh1, ← hh2, key]

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumRangeMulEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorExplicitCommDiamondOperatorOfMatriStatement
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeUOperatorExplicit_comm_diamondOperatorOfMatrix : ∀ (N l q : ℕ) (k d : ℤ) (ρ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → q ∣ N * l → GlobalTheory.Hk.IsDia N l d ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.uOp q (GlobalTheory.Hk.dia k ρ ⇑f) = GlobalTheory.Hk.dia k ρ (GlobalTheory.Hk.uOp q ⇑f) := by
  first | exact @GlobalTheory.Hk.uOp_dia_comm | exact GlobalTheory.Hk.uOp_dia_comm | (intros; apply GlobalTheory.Hk.uOp_dia_comm <;> assumption)
end

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem sum_range_mul_eq (h : ℕ → ℂ) (q r : ℕ) :
    ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range q, h (j + q * i) = ∑ m ∈ Finset.range (q * r), h m := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ih, Nat.mul_succ, Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.add_comm]

theorem im_div_pos (τ : ℍ) (j q : ℕ) (hq : 0 < q) : 0 < (((τ : ℂ) + j) / q).im := by
  rw [Complex.div_natCast_im]
  simp only [Complex.add_im, Complex.natCast_im, add_zero]
  exact div_pos τ.im_pos (by exact_mod_cast hq)

theorem uOp_uOp_eq (f : ℍ → ℂ) (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (τ : ℍ) :
    uOp a (uOp b f) τ =
      ((a : ℂ) * b)⁻¹ * ∑ m ∈ Finset.range (a * b), f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b))) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  simp only [uOp]
  rw [← sum_range_mul_eq (fun m : ℕ => f (ofComplex (((τ : ℂ) + m) / ((a : ℂ) * b)))) a b]
  conv_rhs => rw [Finset.sum_comm]
  rw [mul_inv, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ofComplex_apply_of_im_pos (im_div_pos τ j a ha)]
  congr 2
  push_cast
  field_simp
  ring

theorem uOp_comm (f : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) :
    uOp q (uOp r f) = uOp r (uOp q f) := by
  funext τ
  rw [uOp_uOp_eq f q r hq hr, uOp_uOp_eq f r q hr hq, mul_comm (r : ℂ), Nat.mul_comm r q]

theorem sum_mul_mod (G : ℕ → ℂ) (q r : ℕ) (hq : 0 < q) (hc : Nat.Coprime q r) :
    ∑ j ∈ Finset.range q, G (r * j % q) = ∑ j ∈ Finset.range q, G j := by
  have hinj : Set.InjOn (fun j => r * j % q) (Finset.range q : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    have h1 : a ≡ b [MOD q] := Nat.ModEq.cancel_left_of_coprime hc hab
    unfold Nat.ModEq at h1
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  have himg : (Finset.range q).image (fun j => r * j % q) = Finset.range q := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨a, _, rfl⟩ := hx
      exact Nat.mod_lt _ hq
    · rw [Finset.card_image_of_injOn hinj]
  rw [← Finset.sum_image hinj, himg]

theorem per_ofComplex (g : ℍ → ℂ) (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) (z : ℂ) (hz : 0 < z.im) :
    g (ofComplex (z + 1)) = g (ofComplex z) := by
  have hz1 : 0 < (z + 1).im := by simpa using hz
  have h1 : ofComplex (z + 1) = (1 : ℝ) +ᵥ ofComplex z := by
    apply UpperHalfPlane.ext
    rw [coe_vadd, ofComplex_apply_of_im_pos hz1, ofComplex_apply_of_im_pos hz]
    push_cast
    ring
  rw [h1, hper]

theorem uOp_vOp (g : ℍ → ℂ) (q r : ℕ) (hq : 0 < q) (hr : 0 < r) (hc : Nat.Coprime q r)
    (hper : ∀ τ : ℍ, g ((1 : ℝ) +ᵥ τ) = g τ) :
    uOp q (vOp r g) = vOp r (uOp q g) := by
  funext τ
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hw : 0 < ((r : ℂ) * τ).im := by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (by exact_mod_cast hr) τ.im_pos
  simp only [uOp, vOp]
  rw [ofComplex_apply_of_im_pos hw]
  congr 1
  set w : ℂ := (r : ℂ) * τ with hwdef
  set G : ℕ → ℂ := fun m => g (ofComplex ((w + m) / q)) with hG
  have hGq : ∀ m n : ℕ, G (m + q * n) = G m := by
    intro m n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih]
      simp only [hG]
      have hpos : 0 < ((w + ((m + q * n : ℕ) : ℂ)) / q).im := by
        rw [Complex.div_natCast_im]
        simp only [Complex.add_im, Complex.natCast_im, add_zero]
        exact div_pos hw (by exact_mod_cast hq)
      rw [← per_ofComplex g hper _ hpos]
      congr 2
      push_cast
      field_simp
      ring
  have hmod : ∀ m, G m = G (m % q) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m q]
    exact hGq _ _
  calc ∑ j ∈ Finset.range q, g (ofComplex ((r : ℂ) * ↑(ofComplex (((τ : ℂ) + j) / q))))
      = ∑ j ∈ Finset.range q, G (r * j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hG]
        rw [ofComplex_apply_of_im_pos (im_div_pos τ j q hq)]
        congr 2
        rw [hwdef]
        push_cast
        field_simp
    _ = ∑ j ∈ Finset.range q, G (r * j % q) := Finset.sum_congr rfl fun j _ => hmod _
    _ = ∑ j ∈ Finset.range q, G j := sum_mul_mod G q r hq hc
    _ = _ := rfl

theorem uOp_add (q : ℕ) (f g : ℍ → ℂ) : uOp q (f + g) = uOp q f + uOp q g := by
  funext τ
  simp [uOp, Finset.sum_add_distrib, mul_add]

theorem uOp_smul (q : ℕ) (c : ℂ) (f : ℍ → ℂ) : uOp q (c • f) = c • uOp q f := by
  funext τ
  simp [uOp, Finset.mul_sum, mul_left_comm]

theorem T_mem_lev (N l : ℕ) : ModularGroup.T ∈ lev N l := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [Gamma1_mem]
    simp [ModularGroup.T]
  · rw [Gamma0_mem]
    simp [ModularGroup.T]

theorem uOp_heckeT_comm : ∀ (N l q r : ℕ) (k : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → q ∣ N * l →
    r.Prime → ¬ r ∣ N * l → GlobalTheory.Hk.IsDia N l r σ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k,
    GlobalTheory.Hk.uOp q (GlobalTheory.Hk.heckeT k r σ ⇑f) = GlobalTheory.Hk.heckeT k r σ (GlobalTheory.Hk.uOp q ⇑f) := by
  intro N l q r k σ hN hl hq hqd hr hrd hσ f
  have hq0 : 0 < q := hq.pos
  have hr0 : 0 < r := hr.pos
  have hne : q ≠ r := fun h => hrd (h ▸ hqd)
  have hcop : Nat.Coprime q r := (Nat.coprime_primes hq hr).2 hne
  have hinv : ∀ γ ∈ lev N l, (⇑f) ∣[k] γ = ⇑f := fun γ hγ => by
    rw [SL_slash]; exact f.slash_action_eq' _ ⟨γ, hγ, rfl⟩
  have hper : ∀ τ : ℍ, ((⇑f) ∣[k] σ) ((1 : ℝ) +ᵥ τ) = ((⇑f) ∣[k] σ) τ := by
    intro τ
    have h1 : ((⇑f) ∣[k] σ) ∣[k] ModularGroup.T = (⇑f) ∣[k] σ := by
      have e : σ * ModularGroup.T = (σ * ModularGroup.T * σ⁻¹) * σ := by group
      rw [← SlashAction.slash_mul, e, SlashAction.slash_mul,
        hinv _ (isDia_conj_mem_lev N l r σ _ hσ (T_mem_lev N l))]
    have h2 := congr_fun h1 τ
    have hden : denom (ModularGroup.T : GL (Fin 2) ℝ) τ = 1 := by
      rw [denom]; simp [ModularGroup.coe_T]
    rw [SL_slash_apply, modular_T_smul] at h2
    simpa [hden] using h2
  have hd := GlobalTheory.T.heckeUOperatorExplicit_comm_diamondOperatorOfMatrix N l q k r σ hN hl hq hqd hσ f
  unfold GlobalTheory.Hk.dia at hd
  simp only [GlobalTheory.Hk.heckeT]
  rw [uOp_add, uOp_smul, uOp_comm _ q r hq0 hr0, uOp_vOp _ q r hq0 hr0 hcop hper, hd]

end GlobalTheory.Hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDiamondCommuteModCoboundariesGamma1Gamma0
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.Comm

open CongruenceSubgroup

theorem cj_sub {Γ : Type} (u v : Γ → ℂ[X]) : cj (u - v) = cj u - cj v := by
  funext γ
  simp [cj, Polynomial.map_sub]

theorem intCast_of_dvd {m n : ℕ} (h : m ∣ n) {x a : ℤ} (hx : ((x : ℤ) : ZMod n) = a) :
    ((x : ℤ) : ZMod m) = a := by
  have := congrArg (ZMod.castHom h (ZMod m)) hx
  simpa using this

theorem isDia_mul {N l : ℕ} {d e : ℤ} {σ τ : SL(2, ℤ)} (hσ : GlobalTheory.Hk.IsDia N l d σ)
    (hτ : GlobalTheory.Hk.IsDia N l e τ) : GlobalTheory.Hk.IsDia N l (d * e) (σ * τ) := by
  obtain ⟨h1, h2⟩ := hσ
  obtain ⟨h3, h4⟩ := hτ
  have h1' : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using intCast_of_dvd (dvd_mul_right N l) (a := 0) (by simpa using h1)
  refine ⟨?_, ?_⟩
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1, h3]
    ring
  · simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [h1', h2, h4]
    ring

theorem gamma_le_lev (N l : ℕ) : Gamma (N * l) ≤ Lev N l := by
  intro γ hγ
  rw [Gamma_mem] at hγ
  obtain ⟨h00, h01, h10, h11⟩ := hγ
  refine ⟨?_, ?_⟩
  · change γ ∈ Gamma1 N
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 1) (by simpa using h00)
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 1) (by simpa using h11)
    · simpa using intCast_of_dvd (dvd_mul_right N l) (a := 0) (by simpa using h10)
  · change γ ∈ Gamma0 l
    rw [Gamma0_mem]
    simpa using intCast_of_dvd (dvd_mul_left l N) (a := 0) (by simpa using h10)

theorem comm_of_decomp {Γ : Subgroup SL(2, ℤ)} {w : ℕ} (A B : Module.End ℂ (Γ → ℂ[X]))
    (hA : ∀ z ∈ B1 Γ w, A z ∈ B1 Γ w) (hB : ∀ z ∈ B1 Γ w, B z ∈ B1 Γ w)
    (hAc : ∀ z, cj (A z) = A (cj z)) (hBc : ∀ z, cj (B z) = B (cj z))
    (x y b : Γ → ℂ[X]) (hx : A (B x) - B (A x) ∈ B1 Γ w) (hy : A (B y) - B (A y) ∈ B1 Γ w)
    (hb : b ∈ B1 Γ w) :
    A (B (x + cj y + b)) - B (A (x + cj y + b)) ∈ B1 Γ w := by
  have hcj : ∀ z ∈ B1 Γ w, cj z ∈ B1 Γ w := (cj_mem_Z1_cj_mem_B1_per_smul Γ w).2.1
  have e : A (B (x + cj y + b)) - B (A (x + cj y + b)) =
      (A (B x) - B (A x)) + cj (A (B y) - B (A y)) + (A (B b) - B (A b)) := by
    simp only [cj_sub, hAc, hBc, map_add (f := _)]
    abel
  rw [e]
  exact add_mem (add_mem hx (hcj _ hy)) (sub_mem (hA _ (hB _ hb)) (hB _ (hA _ hb)))

theorem per_comm {Γ : Subgroup SL(2, ℤ)} {w : ℕ} {k : ℤ} (A B : Module.End ℂ (Γ → ℂ[X]))
    (FA FB : (ℍ → ℂ) → ℍ → ℂ)
    (hA : ∀ z ∈ B1 Γ w, A z ∈ B1 Γ w) (hB : ∀ z ∈ B1 Γ w, B z ∈ B1 Γ w)
    (mA : ∀ f : ModularForm Γ k, ∃ g : ModularForm Γ k, ⇑g = FA ⇑f)
    (mB : ∀ f : ModularForm Γ k, ∃ g : ModularForm Γ k, ⇑g = FB ⇑f)
    (eA : ∀ f : ModularForm Γ k, per Γ w (FA ⇑f) - A (per Γ w ⇑f) ∈ B1 Γ w)
    (eB : ∀ f : ModularForm Γ k, per Γ w (FB ⇑f) - B (per Γ w ⇑f) ∈ B1 Γ w)
    (hc : ∀ f : ModularForm Γ k, FA (FB ⇑f) = FB (FA ⇑f)) (f : ModularForm Γ k) :
    A (B (per Γ w ⇑f)) - B (A (per Γ w ⇑f)) ∈ B1 Γ w := by
  obtain ⟨g, hg⟩ := mB f
  obtain ⟨g', hg'⟩ := mA f
  have h1 := eB f
  have h2 := eA g
  have h3 := eA f
  have h4 := eB g'
  rw [hg] at h2
  rw [hg'] at h4
  have e : A (B (per Γ w ⇑f)) - B (A (per Γ w ⇑f)) =
      -A (per Γ w (FB ⇑f) - B (per Γ w ⇑f)) - (per Γ w (FA (FB ⇑f)) - A (per Γ w (FB ⇑f))) +
        (per Γ w (FB (FA ⇑f)) - B (per Γ w (FA ⇑f))) + B (per Γ w (FA ⇑f) - A (per Γ w ⇑f)) := by
    rw [hc f]
    simp only [map_sub]
    abel
  rw [e]
  exact add_mem (add_mem (sub_mem (neg_mem (hA _ h1)) h2) h4) (hB _ h3)

theorem heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → Odd k →
  ∀ (q q' : ℕ) (σ σ' τ τ' : SL(2, ℤ)) (d d' : ZMod N), q.Prime → ¬ q ∣ N * l → q'.Prime → ¬ q' ∣ N * l →
   IsDiam N l (q : ZMod N) σ → IsDiam N l (q' : ZMod N) σ' → IsDiam N l d τ → IsDiam N l d' τ' →
   ∀ z ∈ Z1 (Lev N l) (k - 2),
    TqZ (Lev N l) (k - 2) q σ (TqZ (Lev N l) (k - 2) q' σ' z) - TqZ (Lev N l) (k - 2) q' σ' (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (UlZ (Lev N l) (k - 2) l z) - UlZ (Lev N l) (k - 2) l (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    UlZ (Lev N l) (k - 2) l (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (UlZ (Lev N l) (k - 2) l z) ∈ B1 (Lev N l) (k - 2) ∧
    DdZ (Lev N l) (k - 2) τ (DdZ (Lev N l) (k - 2) τ' z) - DdZ (Lev N l) (k - 2) τ' (DdZ (Lev N l) (k - 2) τ z) ∈ B1 (Lev N l) (k - 2) := by
  intro N l k hN hl hlN hk hodd q q' σ σ' τ τ' d d' hq hqNl hq' hq'Nl hσ hσ' hτ hτ' z hz
  have hN0 : 0 < N := by omega
  have hl0 : 0 < l := hl.pos
  obtain ⟨bUl, bDd, bTq, bDia, -⟩ := GlobalTheory.SlashUpperTriangularMatrices.bridge
  obtain ⟨rT, rU, rD⟩ := GlobalTheory.HeckeFamilyMatrices.CosetReps.dcReps_level N l hN hl hlN
  have eqv := fun f => GlobalTheory.HeckeFamilyMatrices.HeckeEqv.period_map_equivariant N l k hN hl hlN hk f

  have opT : ∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
      GlobalTheory.Hk.IsDia N l q σ ∧
      (∀ z ∈ B1 (Lev N l) (k - 2), TqZ (Lev N l) (k - 2) q σ z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (TqZ (Lev N l) (k - 2) q σ z) = TqZ (Lev N l) (k - 2) q σ (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = TqF (k : ℤ) q σ ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (TqF (k : ℤ) q σ ⇑f) - TqZ (Lev N l) (k - 2) q σ (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    intro q σ hq hqn hs
    have dq : GlobalTheory.Hk.IsDia N l q σ := (bDia N l q σ).1 (by rwa [Int.cast_natCast])
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) (Fin (q + 1)) (dg 1 q) (tqFam q σ)
      (by simp [dg, Matrix.det_fin_two, hq.pos]) (rT q σ hq hqn hs)
    refine ⟨dq, H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).1 q σ hq hqn hs⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.heckeT_modularForm N l q k σ hN0 hq hqn dq f
    exact ⟨g, hg.trans (bTq _ _ _ _ hq.pos).symm⟩

  have opU :
      (∀ z ∈ B1 (Lev N l) (k - 2), UlZ (Lev N l) (k - 2) l z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (UlZ (Lev N l) (k - 2) l z) = UlZ (Lev N l) (k - 2) l (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = UlF (k : ℤ) l ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (UlF (k : ℤ) l ⇑f) - UlZ (Lev N l) (k - 2) l (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) (Fin l) (dg 1 l) (ulFam l)
      (by simp [dg, Matrix.det_fin_two, hl.pos]) rU
    refine ⟨H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).2.1⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.uOp_modularForm N l l k hN0 hl0 hl (dvd_mul_left l N) f
    exact ⟨g, hg.trans (bUl _ _ _ hl0).symm⟩

  have opD : ∀ (d : ZMod N) (τ : SL(2, ℤ)), IsDiam N l d τ →
      GlobalTheory.Hk.IsDia N l (mat τ 1 1) τ ∧
      (∀ z ∈ B1 (Lev N l) (k - 2), DdZ (Lev N l) (k - 2) τ z ∈ B1 (Lev N l) (k - 2)) ∧
      (∀ z, cj (DdZ (Lev N l) (k - 2) τ z) = DdZ (Lev N l) (k - 2) τ (cj z)) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ),
        ⇑g = DdF (k : ℤ) τ ⇑f) ∧
      (∀ f : ModularForm (Lev N l) (k : ℤ),
        per (Lev N l) (k - 2) (DdF (k : ℤ) τ ⇑f) - DdZ (Lev N l) (k - 2) τ (per (Lev N l) (k - 2) ⇑f)
          ∈ B1 (Lev N l) (k - 2)) := by
    intro d τ hs
    have dτ : GlobalTheory.Hk.IsDia N l (mat τ 1 1) τ := (bDia N l (mat τ 1 1) τ).1 ⟨hs.1, rfl⟩
    have H := GlobalTheory.HeckeFamilyMatrices.HkC.hk_cocycle_coboundary_conj (Lev N l) (k - 2) Unit (mat τ) (fun _ => mat τ)
      (by simp [mat]) (rD d τ hs)
    refine ⟨dτ, H.2.1, H.2.2, fun f => ?_, fun f => (eqv f).2.2 d τ hs⟩
    obtain ⟨g, hg⟩ := GlobalTheory.Hk.dia_modularForm N l k (mat τ 1 1) τ hN0 dτ f
    exact ⟨g, hg.trans (bDd _ _ _).symm⟩

  obtain ⟨f, h, hES⟩ := GlobalTheory.T.exists_eichlerShimura_decomposition_cocycle N (N * l) (Lev N l) k hN (Nat.mul_pos hN0 hl0)
    (gamma_le_lev N l) inf_le_left hodd hk z hz
  obtain ⟨b, hb, rfl⟩ : ∃ b ∈ B1 (Lev N l) (k - 2),
      z = per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b :=
    ⟨_, hES, by abel⟩
  have hh : ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = ⇑h := ⟨ModularFormClass.modularForm h, rfl⟩
  obtain ⟨hm, hhm⟩ := hh
  have pair : ∀ (A B : Module.End ℂ (Lev N l → ℂ[X])) (FA FB : (ℍ → ℂ) → ℍ → ℂ),
      (∀ z ∈ B1 (Lev N l) (k - 2), A z ∈ B1 (Lev N l) (k - 2)) ∧
        (∀ z, cj (A z) = A (cj z)) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = FA ⇑f) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ),
          per (Lev N l) (k - 2) (FA ⇑f) - A (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) →
      (∀ z ∈ B1 (Lev N l) (k - 2), B z ∈ B1 (Lev N l) (k - 2)) ∧
        (∀ z, cj (B z) = B (cj z)) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ), ∃ g : ModularForm (Lev N l) (k : ℤ), ⇑g = FB ⇑f) ∧
        (∀ f : ModularForm (Lev N l) (k : ℤ),
          per (Lev N l) (k - 2) (FB ⇑f) - B (per (Lev N l) (k - 2) ⇑f) ∈ B1 (Lev N l) (k - 2)) →
      (∀ f : ModularForm (Lev N l) (k : ℤ), FA (FB ⇑f) = FB (FA ⇑f)) →
      A (B (per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b)) -
        B (A (per (Lev N l) (k - 2) ⇑f + cj (per (Lev N l) (k - 2) ⇑h) + b)) ∈ B1 (Lev N l) (k - 2) := by
    rintro A B FA FB ⟨hA, hAc, mA, eA⟩ ⟨hB, hBc, mB, eB⟩ hc
    have hy := per_comm A B FA FB hA hB mA mB eA eB hc hm
    rw [hhm] at hy
    exact comm_of_decomp A B hA hB hAc hBc _ _ b (per_comm A B FA FB hA hB mA mB eA eB hc f) hy hb

  have eT : ∀ (q : ℕ) (σ : SL(2, ℤ)), 0 < q → ∀ g, TqF (k : ℤ) q σ g = GlobalTheory.Hk.heckeT k q σ g :=
    fun q σ hq g => bTq _ q σ g hq
  have eU : ∀ g, UlF (k : ℤ) l g = GlobalTheory.Hk.uOp l g := fun g => bUl _ l g hl0
  have eD : ∀ (τ : SL(2, ℤ)) g, DdF (k : ℤ) τ g = GlobalTheory.Hk.dia k τ g := fun τ g => bDd _ τ g
  obtain ⟨dq, oTq⟩ := opT q σ hq hqNl hσ
  obtain ⟨dq', oTq'⟩ := opT q' σ' hq' hq'Nl hσ'
  obtain ⟨dτ, oDτ⟩ := opD d τ hτ
  obtain ⟨dτ', oDτ'⟩ := opD d' τ' hτ'
  refine ⟨pair _ _ _ _ oTq oTq' ?_, pair _ _ _ _ oTq opU ?_, pair _ _ _ _ oTq oDτ ?_,
    pair _ _ _ _ opU oDτ ?_, pair _ _ _ _ oDτ oDτ' ?_⟩
  · intro f
    simp only [eT q σ hq.pos, eT q' σ' hq'.pos]
    exact GlobalTheory.Hk.heckeT_comm N l q q' k σ σ' hN0 hq hq' hqNl hq'Nl dq dq' f
  · intro f
    simp only [eT q σ hq.pos, eU]
    exact (GlobalTheory.Hk.uOp_heckeT_comm N l l q k σ hN0 hl0 hl (dvd_mul_left l N) hq hqNl dq f).symm
  · intro f
    simp only [eT q σ hq.pos, eD]
    exact GlobalTheory.Hk.heckeT_dia_comm N l q k (mat τ 1 1) σ τ hN0 hq hqNl dq dτ f
  · intro f
    simp only [eU, eD]
    exact GlobalTheory.Hk.uOp_dia_comm N l l k (mat τ 1 1) τ hN0 hl0 hl (dvd_mul_left l N) dτ f
  · intro f
    simp only [eD]
    exact (GlobalTheory.Hk.dia_mul N l k _ _ τ' τ (τ' * τ) hN0 dτ' dτ (isDia_mul dτ' dτ) f).trans
      (GlobalTheory.Hk.dia_mul N l k _ _ τ τ' (τ' * τ) hN0 dτ dτ'
        (by rw [mul_comm (mat τ 1 1)]; exact isDia_mul dτ' dτ) f).symm

end GlobalTheory.HeckeFamilyMatrices.Comm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeDiamondCommuteModCoboundariesGamma1Gamma0Statement
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0 : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → Odd k →
  ∀ (q q' : ℕ) (σ σ' τ τ' : SL(2, ℤ)) (d d' : ZMod N), q.Prime → ¬ q ∣ N * l → q'.Prime → ¬ q' ∣ N * l →
   IsDiam N l (q : ZMod N) σ → IsDiam N l (q' : ZMod N) σ' → IsDiam N l d τ → IsDiam N l d' τ' →
   ∀ z ∈ Z1 (Lev N l) (k - 2),
    TqZ (Lev N l) (k - 2) q σ (TqZ (Lev N l) (k - 2) q' σ' z) - TqZ (Lev N l) (k - 2) q' σ' (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (UlZ (Lev N l) (k - 2) l z) - UlZ (Lev N l) (k - 2) l (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    TqZ (Lev N l) (k - 2) q σ (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (TqZ (Lev N l) (k - 2) q σ z) ∈ B1 (Lev N l) (k - 2) ∧
    UlZ (Lev N l) (k - 2) l (DdZ (Lev N l) (k - 2) τ z) - DdZ (Lev N l) (k - 2) τ (UlZ (Lev N l) (k - 2) l z) ∈ B1 (Lev N l) (k - 2) ∧
    DdZ (Lev N l) (k - 2) τ (DdZ (Lev N l) (k - 2) τ' z) - DdZ (Lev N l) (k - 2) τ' (DdZ (Lev N l) (k - 2) τ z) ∈ B1 (Lev N l) (k - 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt | exact GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt | (intros; apply GlobalTheory.HeckeFamilyMatrices.Comm.heckeDiamond_commute_mod_coboundaries_gamma1Gamma0_alt <;> assumption)
end
