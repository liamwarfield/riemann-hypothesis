module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.LemmaN
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColAbelD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DifferentiableZeroModeLiftOf

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusC
namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

def ctU (q : ℕ) (b : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) : EuclideanSpace ℂ ι → ℂ :=
  fun t => cexp (q * Real.pi * Hf t b - q * Real.pi * Hf b b / 2) * F (t - b)

def ctY (Y : GT ι) (w : EuclideanSpace ℂ ι) : GT ι where
  b := Y.b
  integral := Y.integral
  perfect := Y.perfect
  ka := fun t => Y.ka t * cexp (2 * Real.pi * (Hf t w).im * I)
  ka_abs := by
    intro x hx
    rw [norm_mul, Y.ka_abs x hx, one_mul, Complex.norm_exp]
    simp

private theorem Hf_add_left_euclidean (a b c : EuclideanSpace ℂ ι) : Hf (a + b) c = Hf a c + Hf b c := by
  simp [Hf, add_mul, Finset.sum_add_distrib]

private theorem Hf_sub_leftSquareIntegrability (a b c : EuclideanSpace ℂ ι) : Hf (a - b) c = Hf a c - Hf b c := by
  simp [Hf, sub_mul, Finset.sum_sub_distrib]

private theorem Hf_add_right_euclidean (a b c : EuclideanSpace ℂ ι) : Hf a (b + c) = Hf a b + Hf a c := by
  simp [Hf, mul_add, Finset.sum_add_distrib]

private theorem Hf_sub_right' (a b c : EuclideanSpace ℂ ι) : Hf a (b - c) = Hf a b - Hf a c := by
  simp [Hf, mul_sub, Finset.sum_sub_distrib]

private theorem Hf_smul_right' (a b : EuclideanSpace ℂ ι) (c : ℂ) :
    Hf a (c • b) = (starRingEnd ℂ) c * Hf a b := by
  simp only [Hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp <;> ring

private theorem Hf_swap_eq_conj' (a b : EuclideanSpace ℂ ι) : Hf b a = (starRingEnd ℂ) (Hf a b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_sum, map_mul, Complex.conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem norm_sq_eq_re_Hf_self (v : EuclideanSpace ℂ ι) : ‖v‖ ^ 2 = (Hf v v).re := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Hf, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  all_goals rfl

private theorem Hf_neg_left' (a c : EuclideanSpace ℂ ι) : Hf (-a) c = -Hf a c := by
  simp [Hf, Finset.sum_neg_distrib]

private theorem Hf_neg_right' (a c : EuclideanSpace ℂ ι) : Hf a (-c) = -Hf a c := by
  simp [Hf, Finset.sum_neg_distrib]

private theorem Hf_eq_inner_swap_euclidean (v w : EuclideanSpace ℂ ι) : Hf v w = @inner ℂ _ _ w v := by
  simp [Hf, PiLp.inner_apply, mul_comm]

private theorem Hf_finset_sum_right {κ : Type} (s : Finset κ) (v : EuclideanSpace ℂ ι)
    (f : κ → EuclideanSpace ℂ ι) : Hf v (∑ k ∈ s, f k) = ∑ k ∈ s, Hf v (f k) :=
  map_sum (AddMonoidHom.mk' (fun w => Hf v w) (Hf_add_right_euclidean v)) f s

private theorem Hf_real_smul_right (v w : EuclideanSpace ℂ ι) (r : ℝ) :
    Hf v (r • w) = (r : ℂ) * Hf v w := by
  simp only [Hf, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp <;> ring

theorem ctY_coc (Y : GT ι) (w : EuclideanSpace ℂ ι) (q : ℕ) (h : Y.Coc q) : (ctY Y w).Coc q := by
  intro γ hγ γ' hγ'
  show Y.ka (γ + γ') * cexp (2 * Real.pi * (Hf (γ + γ') w).im * I) =
    Y.ka γ * cexp (2 * Real.pi * (Hf γ w).im * I) * (Y.ka γ' * cexp (2 * Real.pi * (Hf γ' w).im * I)) *
      cexp (-(Real.pi * q * (Hf γ γ').im) * I)
  rw [h γ hγ γ' hγ', Col.Hf_add_l, Complex.add_im]
  have e : cexp (2 * Real.pi * (((Hf γ w).im + (Hf γ' w).im : ℝ) : ℂ) * I) =
      cexp (2 * Real.pi * (Hf γ w).im * I) * cexp (2 * Real.pi * (Hf γ' w).im * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  rw [e]; ring

theorem ctU_mem (Y : GT ι) (w : EuclideanSpace ℂ ι) {q : ℕ} (hq : 1 ≤ q) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ (ctY Y w).Sec q) : ctU q (-((1 / (q : ℂ)) • w)) F ∈ Y.Sec q := by
  obtain ⟨hFd, hFe⟩ := hF
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  generalize hb : -((1 / (q : ℂ)) • w) = b
  change Differentiable ℂ (ctU q b F) ∧ ∀ γ ∈ lat Y.b, ∀ v, ctU q b F (v + γ) =
    Y.ka γ * cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) * ctU q b F v
  refine ⟨?_, ?_⟩
  · have hd : Differentiable ℂ (fun t : EuclideanSpace ℂ ι => Hf t b) := by
      have hfun : (fun t : EuclideanSpace ℂ ι => Hf t b) = fun t => innerSL ℂ b t := by
        funext t
        simp [Hf_eq_inner_swap_euclidean]
      rw [hfun]
      exact (innerSL ℂ b).differentiable
    unfold ctU
    exact (((hd.const_mul _).sub_const _).cexp).mul (hFd.comp (differentiable_id.sub_const _))
  · intro γ hγ v
    have hγb : Hf γ b = -(1 / (q : ℂ)) * Hf γ w := by
      rw [← hb, Hf_neg_right', Hf_smul_right']
      simp
    have hbγ : Hf b γ = -(1 / (q : ℂ)) * (starRingEnd ℂ) (Hf γ w) := by
      rw [Hf_swap_eq_conj' γ b, hγb]
      simp
    have hsub : Hf γ w - (starRingEnd ℂ) (Hf γ w) = 2 * ((Hf γ w).im : ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    have hc : (q : ℂ) * (1 / (q : ℂ)) = 1 := mul_one_div_cancel hq0
    have key : cexp (q * Real.pi * Hf (v + γ) b - q * Real.pi * Hf b b / 2) *
        cexp (2 * Real.pi * (Hf γ w).im * I) *
        cexp (q * Real.pi * Hf (v - b) γ + q * Real.pi * Hf γ γ / 2) =
        cexp (q * Real.pi * Hf v γ + q * Real.pi * Hf γ γ / 2) *
        cexp (q * Real.pi * Hf v b - q * Real.pi * Hf b b / 2) := by
      simp only [← Complex.exp_add]
      congr 1
      rw [Hf_add_left_euclidean, Hf_sub_leftSquareIntegrability, hγb, hbγ]
      linear_combination (-(Real.pi : ℂ) * (Hf γ w - (starRingEnd ℂ) (Hf γ w))) * hc +
        (-(Real.pi : ℂ)) * hsub
    have hka : (ctY Y w).ka γ = Y.ka γ * cexp (2 * Real.pi * (Hf γ w).im * I) := rfl
    have hv : v + γ - b = (v - b) + γ := by abel
    simp only [ctU]
    rw [hv, hFe γ hγ (v - b), hka]
    linear_combination (Y.ka γ * F (v - b)) * key

theorem pointNormSq_translate (Y : GT ι) (q : ℕ) (b : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ)
    (t : EuclideanSpace ℂ ι) : Y.ptN2 q (ctU q b F) t = Y.ptN2 q F (t - b) := by
  have e1 : ‖t - b‖ ^ 2 = ‖t‖ ^ 2 - 2 * (Hf t b).re + ‖b‖ ^ 2 := by
    rw [norm_sq_eq_re_Hf_self (t - b), norm_sq_eq_re_Hf_self t, norm_sq_eq_re_Hf_self b, Hf_sub_leftSquareIntegrability, Hf_sub_right', Hf_sub_right',
      Hf_swap_eq_conj' t b]
    simp only [Complex.sub_re, Complex.conj_re]
    ring
  have hA : ((q : ℂ) * (Real.pi : ℂ) * Hf t b - (q : ℂ) * (Real.pi : ℂ) * Hf b b / 2) =
      ((q * Real.pi : ℝ) : ℂ) * Hf t b - ((q * Real.pi / 2 : ℝ) : ℂ) * Hf b b := by
    push_cast
    ring
  simp only [GT.ptN2, ctU]
  rw [hA, norm_mul, Complex.norm_exp, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    ← norm_sq_eq_re_Hf_self b, e1]
  rw [mul_pow, mul_comm (Real.exp _ ^ 2), mul_assoc]
  congr 1
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem pointNormSq_periodic (Y : GT ι) {q : ℕ} {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec q)
    {γ : EuclideanSpace ℂ ι} (hγ : γ ∈ lat Y.b) (t : EuclideanSpace ℂ ι) :
    Y.ptN2 q F (t + γ) = Y.ptN2 q F t := by
  obtain ⟨_, hFe⟩ := hF
  have e1 : ‖t + γ‖ ^ 2 = ‖t‖ ^ 2 + 2 * (Hf t γ).re + ‖γ‖ ^ 2 := by
    rw [norm_sq_eq_re_Hf_self (t + γ), norm_sq_eq_re_Hf_self t, norm_sq_eq_re_Hf_self γ, Hf_add_left_euclidean, Hf_add_right_euclidean, Hf_add_right_euclidean,
      Hf_swap_eq_conj' t γ]
    simp only [Complex.add_re, Complex.conj_re]
    ring
  have hA : ((q : ℂ) * (Real.pi : ℂ) * Hf t γ + (q : ℂ) * (Real.pi : ℂ) * Hf γ γ / 2) =
      ((q * Real.pi : ℝ) : ℂ) * Hf t γ + ((q * Real.pi / 2 : ℝ) : ℂ) * Hf γ γ := by
    push_cast
    ring
  simp only [GT.ptN2]
  rw [hFe γ hγ t, hA, norm_mul, norm_mul, Y.ka_abs γ hγ, one_mul, Complex.norm_exp, Complex.add_re,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, ← norm_sq_eq_re_Hf_self γ, e1]
  rw [mul_pow, mul_comm (Real.exp _ ^ 2), mul_assoc]
  congr 1
  rw [sq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

instance ctCnt (Y : GT ι) : Countable (Submodule.span ℤ (Set.range Y.b)).toAddSubgroup :=
  inferInstanceAs (Countable (Submodule.span ℤ (Set.range Y.b)))

theorem ct_avg_trans (Y : GT ι) (g : EuclideanSpace ℂ ι → ℝ)
    (hper : ∀ γ ∈ lat Y.b, ∀ v, g (v + γ) = g v) (a : EuclideanSpace ℂ ι) :
    (⨍ v in ZSpan.fundamentalDomain Y.b, g (v - a)) = ⨍ v in ZSpan.fundamentalDomain Y.b, g v := by
  have hD := ZSpan.isAddFundamentalDomain Y.b volume
  have hT : IsAddFundamentalDomain (Submodule.span ℤ (Set.range Y.b)).toAddSubgroup
      ((fun u => u + a) ⁻¹' ZSpan.fundamentalDomain Y.b) volume :=
    hD.preimage_of_equiv (measurePreserving_add_right volume a).quasiMeasurePreserving
      Function.bijective_id fun _ _ => add_assoc _ _ _
  have hg : ∀ (γ : (Submodule.span ℤ (Set.range Y.b)).toAddSubgroup) (x : EuclideanSpace ℂ ι),
      g (γ +ᵥ x) = g x := by
    rintro ⟨γ, hγ⟩ x
    have h := hper γ hγ x
    rw [add_comm] at h
    exact h
  simp only [MeasureTheory.setAverage_eq]
  congr 1
  have h1 := (measurePreserving_add_right volume a).setIntegral_preimage_emb
    (MeasurableEquiv.addRight a).measurableEmbedding (fun y => g (y - a)) (ZSpan.fundamentalDomain Y.b)
  simp only [add_sub_cancel_right] at h1
  rw [← h1]
  exact hT.setIntegral_eq hD hg

theorem l2_ctU_eq_l2_ctY (Y : GT ι) (w : EuclideanSpace ℂ ι) {q : ℕ} {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ (ctY Y w).Sec q) :
    Y.l2 q (ctU q (-((1 / (q : ℂ)) • w)) F) = (ctY Y w).l2 q F := by
  have hper : ∀ γ ∈ lat Y.b, ∀ v, Y.ptN2 q F (v + γ) = Y.ptN2 q F v :=
    fun γ hγ v => pointNormSq_periodic (ctY Y w) hF hγ v
  simp only [GT.l2, pointNormSq_translate]
  exact ct_avg_trans Y _ hper _

end

end ReciprocityTheory.ChartRestriction.G.I2

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

theorem ctU_cancel (q : ℕ) (b : EuclideanSpace ℂ ι) (F : EuclideanSpace ℂ ι → ℂ) :
    ctU q b (ctU q (-b) F) = F := by
  funext t
  have e : (q * Real.pi * Hf t b - q * Real.pi * Hf b b / 2 : ℂ) +
      (q * Real.pi * Hf (t - b) (-b) - q * Real.pi * Hf (-b) (-b) / 2) = 0 := by
    simp only [Hf_sub_leftSquareIntegrability, Hf_neg_right', Hf_neg_left', neg_neg]
    ring
  simp only [ctU]
  rw [← mul_assoc, ← Complex.exp_add, e, Complex.exp_zero, one_mul, sub_neg_eq_add, sub_add_cancel]

variable {K : Submodule ℝ (EuclideanSpace ℂ ι)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
include hK

theorem ct_Hf_uc (v a : EuclideanSpace ℂ ι) :
    Hf v (Col.uc K a) = ∑ k, ((Col.z K k a).im : ℂ) * Col.z K k v := by
  simp only [Col.uc]
  rw [Hf_finset_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Hf_real_smul_right]
  rfl

theorem translate_zeroModeLift_formula (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB K)) → ℂ) (a v : EuclideanSpace ℂ ι) :
    cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) *
        (cexp ((q * Real.pi / 2 : ℂ) * Col.S K (v - a)) * β (Col.wmap K (v - a))) =
      cexp ((q * Real.pi / 2 : ℂ) * Col.S K a - q * Real.pi * Hf a a / 2 +
          q * Real.pi * Hf (Col.wmap K a) (Col.wmap K a) / 2) *
        cexp (-(2 * Real.pi * q : ℂ) * I * Hf v (Col.uc K a)) *
        (cexp ((q * Real.pi / 2 : ℂ) * Col.S K v) * ctU q (Col.wmap K a) β (Col.wmap K v)) := by
  have hz : ∀ k, Col.z K k (v - a) = Col.z K k v - Col.z K k a := fun k => Col.Hf_sub_l _ _ _
  have hS : Col.S K (v - a) = ∑ k, (Col.z K k v - Col.z K k a) ^ 2 := by
    unfold Col.S; simp only [hz]
  have hk : ∀ k, (q : ℂ) * Real.pi * (Col.z K k v * (starRingEnd ℂ) (Col.z K k a)) +
      (q * Real.pi / 2 : ℂ) * (Col.z K k v - Col.z K k a) ^ 2 =
      (q * Real.pi / 2 : ℂ) * Col.z K k a ^ 2 + (q * Real.pi / 2 : ℂ) * Col.z K k v ^ 2 +
        (-(2 * Real.pi * q : ℂ) * I) * (((Col.z K k a).im : ℂ) * Col.z K k v) := by
    intro k
    have hc : (starRingEnd ℂ) (Col.z K k a) = Col.z K k a - 2 * ((Col.z K k a).im : ℂ) * I := by
      apply Complex.ext <;> simp <;> ring
    rw [hc]; ring_nf
  have hsum := Finset.sum_congr rfl (fun k (_ : k ∈ Finset.univ) => hk k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hdec := Col.Hf_decomp hK v a
  have hw : Col.wmap K (v - a) = Col.wmap K v - Col.wmap K a := map_sub _ _ _
  have hww := Col.Hf_wmap hK v a
  unfold ctU
  rw [hw, ct_Hf_uc hK]
  have E : (q : ℂ) * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 +
      (q * Real.pi / 2 : ℂ) * Col.S K (v - a) =
      ((q * Real.pi / 2 : ℂ) * Col.S K a - q * Real.pi * Hf a a / 2 +
          q * Real.pi * Hf (Col.wmap K a) (Col.wmap K a) / 2) +
        -(2 * Real.pi * q : ℂ) * I * ∑ k, ((Col.z K k a).im : ℂ) * Col.z K k v +
        ((q * Real.pi / 2 : ℂ) * Col.S K v +
          ((q : ℂ) * Real.pi * Hf (Col.wmap K v) (Col.wmap K a) -
            q * Real.pi * Hf (Col.wmap K a) (Col.wmap K a) / 2)) := by
    rw [hS, hdec, hww]
    unfold Col.S
    linear_combination hsum
  calc _ = cexp ((q : ℂ) * Real.pi * Hf v a - q * Real.pi * Hf a a / 2 +
        (q * Real.pi / 2 : ℂ) * Col.S K (v - a)) * β (Col.wmap K v - Col.wmap K a) := by
        rw [Complex.exp_add]; ring
    _ = _ := by rw [E]; simp only [Complex.exp_add, Complex.exp_sub]; ring

end

end ReciprocityTheory.ChartRestriction.G.I2
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusB
namespace ReciprocityTheory.ChartRestriction.G.I2

open Real

theorem ct_expo_num (q c : ℕ) (hq : 1 ≤ q) {U y M1 r : ℝ} (hU : 0 ≤ U) (hy : 0 ≤ y)
    (hM : M1 ≤ q / 2) (hr0 : 0 ≤ r) (hr : r * (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ≤ c)
    (ht : 28 * (c : ℝ) ≤ q * y ^ 2) :
    q * π * r ^ 2 / 2 + 2 * π * r * (U + q * y) - π * (q - M1) * y ^ 2 ≤
      1.07 * c - 1.33 * (q * y ^ 2) := by
  have hπ1 : (3.14 : ℝ) < π := Real.pi_gt_d2
  have hπ2 : π < 3.15 := Real.pi_lt_d2
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hS0 : 0 ≤ Real.sqrt (q * (c + 1)) := Real.sqrt_nonneg _
  have hS2 : Real.sqrt (q * (c + 1)) ^ 2 = q * (c + 1) := Real.sq_sqrt (by positivity)
  have hA : 0 ≤ 2 * π * r * U := by positivity
  have h1 : 2 * π * r * U + 5 * (r * Real.sqrt (q * (c + 1))) ≤ c := by
    have e : r * (2 * π * U + 5 * Real.sqrt (q * (c + 1))) =
        2 * π * r * U + 5 * (r * Real.sqrt (q * (c + 1))) := by ring
    linarith
  have ha0 : 0 ≤ r * Real.sqrt (q * (c + 1)) := mul_nonneg hr0 hS0
  have ha : r * Real.sqrt (q * (c + 1)) ≤ c / 5 := by linarith
  have hX : (q * r ^ 2) * (c + 1) = (r * Real.sqrt (q * (c + 1))) ^ 2 := by
    rw [mul_pow, hS2]; ring
  have hX0 : 0 ≤ q * r ^ 2 := by positivity
  have hXa : q * r ^ 2 ≤ (r * Real.sqrt (q * (c + 1))) / 5 := by
    have h2 : (q * r ^ 2) * (c + 1) ≤ (r * Real.sqrt (q * (c + 1))) / 5 * (c + 1) := by
      rw [hX]; nlinarith
    exact le_of_mul_le_mul_right h2 (by positivity)
  have ht0 : 0 ≤ q * y ^ 2 := by positivity
  have hP0 : 0 ≤ r * q * y := by positivity
  have hPsq : (r * q * y) ^ 2 = (q * r ^ 2) * (q * y ^ 2) := by ring
  have hP : 2 * (r * q * y) ≤ 20 * (q * r ^ 2) + (q * y ^ 2) / 20 := by
    nlinarith [sq_nonneg (20 * (q * r ^ 2) - (q * y ^ 2) / 20)]
  have F1 : π * (q * r ^ 2) ≤ 3.15 * (q * r ^ 2) := mul_le_mul_of_nonneg_right hπ2.le hX0
  have F2 : π * (2 * (r * q * y)) ≤ π * (20 * (q * r ^ 2) + (q * y ^ 2) / 20) :=
    mul_le_mul_of_nonneg_left hP Real.pi_pos.le
  have F3 : π * (q * y ^ 2) ≤ 3.15 * (q * y ^ 2) := mul_le_mul_of_nonneg_right hπ2.le ht0
  have F3' : 3.14 * (q * y ^ 2) ≤ π * (q * y ^ 2) := mul_le_mul_of_nonneg_right hπ1.le ht0
  have F4 : π * (q / 2) * y ^ 2 ≤ π * (q - M1) * y ^ 2 := by
    have : (q : ℝ) / 2 ≤ q - M1 := by linarith
    have hy2 := sq_nonneg y
    have := mul_le_mul_of_nonneg_left this Real.pi_pos.le
    nlinarith
  linarith [F1, F2, F3, F3', F4, h1, hXa, ha, ht, hA]

theorem ct_base_num (q c : ℕ) (hq : 1 ≤ q) {t0 : ℝ}
    (hC5 : 4 * (c : ℝ) * (7 + Real.log (q * c)) ≤ t0) :
    (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c ≤ Real.exp (0.14 * t0) := by
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rcases Nat.eq_zero_or_pos c with hc | hc
  · subst hc
    simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero] at hC5 ⊢
    exact Real.one_le_exp (by linarith)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hqc1 : (1 : ℝ) ≤ q * c := by nlinarith
  have hL0 : 0 ≤ Real.log (q * c) := Real.log_nonneg hqc1
  have hS : 0 < Real.sqrt (q * (c + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < 6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1)) := by positivity
  have hlogB : Real.log (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) =
      Real.log 6.5 + 1.07 + Real.log (q * (c + 1)) / 2 := by
    rw [Real.log_mul (by positivity) hS.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
      Real.log_exp, Real.log_sqrt (by positivity)]
  have h65 : Real.log 6.5 ≤ 3 * Real.log 2 := by
    have e : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [← e]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have h2 := Real.log_two_lt_d9
  have hqc : Real.log (q * (c + 1)) ≤ Real.log 2 + Real.log (q * c) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have key : Real.log (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ≤
      0.56 * (7 + Real.log (q * c)) := by
    rw [hlogB]; linarith
  rw [← Real.exp_log hB, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have := mul_le_mul_of_nonneg_left key hc0
  linarith

theorem ct_B_num (gA gB dK dst : ℕ) {t0 Bsq : ℝ} (hBsq0 : 0 ≤ Bsq) (hBsq : Bsq ≤ 12 * (5.12 : ℝ) ^ gB)
    (hgB : gB ≤ gA) (hdK : dK ≤ dst) (hC6 : (gA : ℝ) * Real.log 2 ≤ t0) :
    Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0)) ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst := by
  have hsq : Real.sqrt Bsq ≤ 3.4642 * 2.263 ^ gA := by
    have hm : 12 * (5.12 : ℝ) ^ gB ≤ (3.4642 * 2.263 ^ gA) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm gA 2, pow_mul]
      apply mul_le_mul (by norm_num) _ (by positivity) (by norm_num)
      calc (5.12 : ℝ) ^ gB ≤ (2.263 ^ 2) ^ gB := pow_le_pow_left₀ (by norm_num) (by norm_num) gB
        _ ≤ (2.263 ^ 2) ^ gA := pow_le_pow_right₀ (by norm_num) hgB
    calc Real.sqrt Bsq ≤ Real.sqrt ((3.4642 * 2.263 ^ gA) ^ 2) := Real.sqrt_le_sqrt (hBsq.trans hm)
      _ = 3.4642 * 2.263 ^ gA := Real.sqrt_sq (by positivity)
  have h3 : (2.263 : ℝ) ^ gA * Real.exp (-(0.19 * t0)) ≤ 2 ^ gA := by
    have hl : Real.log 2.263 * 100 ≤ Real.log 2 * 119 := by
      have h := Real.log_le_log (by positivity) (show (2.263 : ℝ) ^ 100 ≤ 2 ^ 119 by norm_num)
      rw [Real.log_pow, Real.log_pow] at h
      push_cast at h
      linarith
    have hg0 : (0 : ℝ) ≤ gA := Nat.cast_nonneg gA
    have hm := mul_le_mul_of_nonneg_left hl hg0
    rw [← Real.exp_log (show (0 : ℝ) < 2.263 by norm_num), ← Real.exp_nat_mul,
      ← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have h4 : (3 : ℝ) ^ dK ≤ 4.3 ^ dst :=
    (pow_le_pow_left₀ (by norm_num) (by norm_num) dK).trans (pow_le_pow_right₀ (by norm_num) hdK)
  calc Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0))
      ≤ (3.4642 * 2.263 ^ gA) * (2 * 4.3 ^ dst) * Real.exp (-(0.19 * t0)) := by gcongr
    _ = 6.9284 * ((2.263 : ℝ) ^ gA * Real.exp (-(0.19 * t0))) * 4.3 ^ dst := by ring
    _ ≤ 6.9284 * 2 ^ gA * 4.3 ^ dst := by gcongr
    _ ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst := by gcongr; norm_num

theorem jet_product_le (q c dK gA dst : ℕ) (hq : 1 ≤ q) {n U t0 Bsq : ℝ} (hn : 1 ≤ n) (hU0 : 0 ≤ U)
    (hU : 2 * π * U ≤ 1.5 * n) (hC5 : 4 * (c : ℝ) * (7 + Real.log (q * c)) ≤ t0)
    (hB : Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0)) ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst) :
    (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0)))) ≤
      7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * n ^ c := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hS1 : 1 ≤ Real.sqrt (q * (c + 1)) := Real.one_le_sqrt.mpr (by nlinarith)
  have hn0 : 0 ≤ n := by linarith
  have hbase : 2 * π * U + 5 * Real.sqrt (q * (c + 1)) ≤ 6.5 * Real.sqrt (q * (c + 1)) * n := by
    nlinarith
  have hpow : (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c ≤
      (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) * n ^ c := by
    have e : (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) =
        (6.5 * Real.sqrt (q * (c + 1))) ^ c := by
      rw [mul_comm (6.5 : ℝ) (Real.exp 1.07), mul_assoc, mul_pow, ← Real.exp_nat_mul, mul_comm,
        ← mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase c
  have hbn := ct_base_num q c hq hC5
  have hX0 : 0 ≤ Real.sqrt Bsq * (2 * 3 ^ dK) := by positivity
  calc (2 * π * U + 5 * Real.sqrt (q * (c + 1))) ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0))))
      ≤ (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * Real.exp (-(1.07 * c)) * n ^ c *
        (Real.sqrt Bsq * Real.exp (1.07 * c) * (2 * 3 ^ dK * Real.exp (-(1.33 * t0)))) := by
        gcongr
    _ = (6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * n ^ c *
        (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0)) := by
        have : Real.exp (-(1.07 * c)) * Real.exp (1.07 * c) = 1 := by
          rw [← Real.exp_add]; simp
        linear_combination ((6.5 * Real.exp 1.07 * Real.sqrt (q * (c + 1))) ^ c * n ^ c *
          (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0))) * this
    _ ≤ Real.exp (0.14 * t0) * n ^ c * (Real.sqrt Bsq * (2 * 3 ^ dK)) * Real.exp (-(1.33 * t0)) := by
        gcongr
    _ = (Real.sqrt Bsq * (2 * 3 ^ dK) * Real.exp (-(0.19 * t0))) * Real.exp (-t0) * n ^ c := by
        have : Real.exp (0.14 * t0) * Real.exp (-(1.33 * t0)) =
            Real.exp (-(0.19 * t0)) * Real.exp (-t0) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        linear_combination (n ^ c * (Real.sqrt Bsq * (2 * 3 ^ dK))) * this
    _ ≤ 7 * 2 ^ gA * (4.3 : ℝ) ^ dst * Real.exp (-t0) * n ^ c := by gcongr

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex MeasureTheory

noncomputable section

theorem ct_expo_vec {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (w ua y : V)
    {q M1 r : ℝ} (hq : 0 < q) (hw : ‖w‖ ≤ r)
    (hc6 : |2 * inner ℝ (q • ua) y| ≤ M1 * ‖y‖ ^ 2) :
    Real.pi * q * ‖ua‖ ^ 2 - Real.pi * q * ‖w - (ua + y)‖ ^ 2 ≤
      2 * Real.pi * r * (q * ‖ua‖ + q * ‖y‖) - Real.pi * (q - M1) * ‖y‖ ^ 2 := by
  have e1 : ‖w - (ua + y)‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w ua - 2 * inner ℝ w y + ‖ua‖ ^ 2 +
      2 * inner ℝ ua y + ‖y‖ ^ 2 := by
    rw [@norm_sub_sq_real, @norm_add_sq_real, inner_add_right]
    ring
  have hua := norm_nonneg ua
  have hy := norm_nonneg y
  have hpq : 0 ≤ Real.pi * q := by positivity
  have t1 : Real.pi * q * inner ℝ w ua ≤ Real.pi * q * (r * ‖ua‖) :=
    mul_le_mul_of_nonneg_left ((real_inner_le_norm w ua).trans (mul_le_mul_of_nonneg_right hw hua)) hpq
  have t2 : Real.pi * q * inner ℝ w y ≤ Real.pi * q * (r * ‖y‖) :=
    mul_le_mul_of_nonneg_left ((real_inner_le_norm w y).trans (mul_le_mul_of_nonneg_right hw hy)) hpq
  have h3 : -(2 * inner ℝ (q • ua) y) ≤ M1 * ‖y‖ ^ 2 := (neg_le_abs _).trans hc6
  rw [real_inner_smul_left] at h3
  have t3 : Real.pi * (-(2 * (q * inner ℝ ua y))) ≤ Real.pi * (M1 * ‖y‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h3 Real.pi_pos.le
  have t4 : 0 ≤ Real.pi * q * ‖w‖ ^ 2 := by positivity
  rw [e1]
  nlinarith [t1, t2, t3, t4]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
  {I : Submodule ℤ (Vsp X.dim)}

theorem ct_cabPoly_zero {ι : Type} [Fintype ι] : cabPoly (0 : EuclideanSpace ℂ ι) 0 = 1 := by
  simp [cabPoly]

theorem ct_beta (hA : PropAStatement) (hS : GSupStatement) (hI : IsSplit P I) (hP : Ext.PackingCount)
    (w : EuclideanSpace ℂ (Fin (Col.gB (IR I)))) (c : ℕ) (hc : c ≤ DF) :
    ∃ βt ∈ (ctY (Col.YB hI hP P.q) w).Sec P.q,
      βt 0 = 1 ∧ (∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j βt 0 = 0) ∧
      (ctY (Col.YB hI hP P.q) w).l2 P.q βt ≤ 6 ∧
      ∀ t, (ctY (Col.YB hI hP P.q) w).ptN2 P.q βt t ≤ 12 * (5.12 : ℝ) ^ Col.gB (IR I) := by
  classical
  have hq2 : (2 : ℝ) ≤ P.q := cab_q_ge P
  have hq2n : 2 ≤ P.q := by exact_mod_cast hq2
  have hR0sq := P.hR0
  have hR0ne : P.R0 ≠ 0 := by intro h; rw [h] at hR0sq; norm_num at hR0sq
  have hR0pos : 0 < |P.R0| := abs_pos.mpr hR0ne
  have hlat : ∀ γ ∈ lat (ctY (Col.YB hI hP P.q) w).b, γ ≠ 0 →
      |P.R0| ≤ Real.sqrt (P.q * Real.pi) * ‖γ‖ := cab_YB_abs hI hP P.q
  have hGle : Col.gB (IR I) ≤ X.gA := cab_gB_le (IR I)
  have hGle' : (Col.gB (IR I) : ℝ) ≤ X.gA := by exact_mod_cast hGle
  have hcD : (c : ℝ) ≤ DF := by exact_mod_cast hc
  have h90 : 90 * ((Fintype.card (Fin (Col.gB (IR I))) : ℝ) + c) ≤ |P.R0| ^ 2 := by
    rw [sq_abs, Fintype.card_fin]; nlinarith [hR0sq.2]
  obtain ⟨β, hβ, hjet, hl2⟩ := hA (Fin (Col.gB (IR I))) (ctY (Col.YB hI hP P.q) w) P.q c |P.R0| P.hq
    (ctY_coc _ _ _ (Col.YB_coc hI hP P.q)) hR0pos hlat
    (by rw [sq_abs]; exact hR0sq.1) h90 (cabPoly 0 0) (by rw [ct_cabPoly_zero]; simp)
  rw [ct_cabPoly_zero] at hjet hl2
  have hJ := cab_J_le (0 : EuclideanSpace ℂ (Fin (Col.gB (IR I)))) (by simp) 0 P.q P.hq
  rw [ct_cabPoly_zero, Fintype.card_fin] at hJ
  have hl2' : (ctY (Col.YB hI hP P.q) w).l2 P.q β ≤
      6 * ((Nat.factorial 0 : ℕ) * (2 / (P.q * Real.pi)) ^ 0 * (2 / P.q) ^ Fintype.card (Fin (Col.gB (IR I)))) := by
    rw [Fintype.card_fin]; simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul] at hJ ⊢
    linarith
  have h90' : 90 * (Fintype.card (Fin (Col.gB (IR I))) : ℝ) ≤ |P.R0| ^ 2 := by
    have : (0 : ℝ) ≤ 90 * c := by positivity
    linarith
  have hβc : ContDiff ℂ (⊤ : ℕ∞) β := (cab_contDiff_top hβ.1).of_le (by exact_mod_cast le_top)
  obtain ⟨hb0, hbj⟩ := ct_jet_one_iter β hβc c hjet
  refine ⟨β, hβ, hb0, hbj, ?_, fun t => ?_⟩
  · refine hl2'.trans ?_
    simp only [Nat.factorial_zero, Nat.cast_one, pow_zero, one_mul, Fintype.card_fin]
    have : (2 / (P.q : ℝ)) ^ Col.gB (IR I) ≤ 1 :=
      pow_le_one₀ (by positivity) ((div_le_one (by linarith)).2 hq2)
    linarith
  · have := cab_sup hS (ctY (Col.YB hI hP P.q) w) P.q 0 hq2n |P.R0| hR0pos hlat h90' β hβ hl2' t
    simpa [Fintype.card_fin] using this

def ctA {dim : (E →+* ℂ) → ℕ} (x0 : Vsp dim) (q : ℕ) : Vsp dim := (1 / (q : ℂ)) • x0

def ctC {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (q : ℕ) (a : Vsp dim) : ℂ :=
  cexp ((q * Real.pi / 2 : ℂ) * Col.S (IR I) a - q * Real.pi * Hf a a / 2 +
    q * Real.pi * Hf (Col.wmap (IR I) a) (Col.wmap (IR I) a) / 2)

def ctS (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ)
    (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (a : Vsp X.dim) : (Fin 1 → Vsp X.dim) → ℂ :=
  (ctC I q a)⁻¹ • X.U q (fun _ => a) (Col.colS X I q β)

theorem ct_uc_A (x0 : Vsp X.dim) (q : ℕ) :
    Col.uc (IR I) (ctA x0 q) = (1 / (q : ℝ)) • Col.uc (IR I) x0 := by
  unfold Col.uc Col.z ctA
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Col.Hf_smul_l, smul_smul]
  congr 1
  rw [show (1 / (q : ℂ)) = ((1 / (q : ℝ) : ℝ) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]

theorem ct_norm_C (hI : IsSplit P I) (q : ℕ) (a : Vsp X.dim) :
    ‖ctC I q a‖ = Real.exp (-(q * Real.pi * ‖Col.uc (IR I) a‖ ^ 2)) := by
  have hK := Col.hK_of hI
  unfold ctC
  rw [Complex.norm_exp]
  congr 1
  have h1 := Col.norm_sq_decomp hK a
  have h2 := Col.norm_wmap hK a
  have h3 := Col.norm_uc_sq (IR I) a
  rw [Col.Hf_self a, Col.Hf_self (Col.wmap (IR I) a), h2, h3]
  have hS : (Col.S (IR I) a).re = ∑ k, ((Col.z (IR I) k a).re ^ 2 - (Col.z (IR I) k a).im ^ 2) := by
    unfold Col.S; rw [Complex.re_sum]; refine Finset.sum_congr rfl fun k _ => ?_
    rw [sq, Complex.mul_re]; ring
  have hn : ∀ k, ‖Col.z (IR I) k a‖ ^ 2 = (Col.z (IR I) k a).re ^ 2 + (Col.z (IR I) k a).im ^ 2 := by
    intro k; rw [Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.natCast_re, Complex.natCast_im]
  rw [hS, h1]
  simp only [hn, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  norm_num
  ring

theorem l2_U_eq_l2 {q : ℕ} {F : (Fin 1 → Vsp X.dim) → ℂ} (hF : F ∈ X.Sec q 1) (a : Fin 1 → Vsp X.dim) :
    X.l2 q (X.U q a F) = X.l2 q F := by
  unfold PT.l2
  simp_rw [pointwiseNormSq_translate X]
  have hc : Continuous (fun v => X.ptN2 q F v) := by
    have := hF.1.continuous
    unfold PT.ptN2 HC Hf
    fun_prop
  exact TiledBoundaries.stepT E X 1 ℝ (fun v => X.ptN2 q F v) hc (fun γ hγ v => pointwiseNormSq_add_period X hF hγ v) a

theorem ct_fun (q : ℕ) (β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (a : Vsp X.dim) :
    ctS X I q β a = fun w => (ctC I q a)⁻¹ *
      (cexp (q * Real.pi * Hf (w 0) a - q * Real.pi * Hf a a / 2) * Col.sP X I q β (w 0 - a)) := by
  funext w
  simp [ctS, PT.U, HC, Col.colS]

theorem ct_main (hI : IsSplit P I) (σ : E →+* ℂ) (q c : ℕ)
    (βt : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (hβt : Differentiable ℂ βt) (hb0 : βt 0 = 1)
    (hbj : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j βt 0 = 0) (ua : Vsp X.dim)
    (xs : Fin c → Vsp X.dim) (hxs : ∀ k, InPart σ (xs k)) :
    iteratedFDeriv ℂ c (fun v => cexp (-(2 * Real.pi * q : ℂ) * Complex.I * Hf v ua) * Col.F0 I q βt v) 0 xs =
      ∏ k, (-(2 * Real.pi * q : ℂ) * Complex.I * Hf (xs k) ua) := by
  set c0 : ℂ := -(2 * Real.pi * q : ℂ) * Complex.I with hc0
  set ℓL : Vsp X.dim →L[ℂ] ℂ := c0 • innerSL ℂ ua with hℓ
  have hℓv : ∀ v, ℓL v = c0 * Hf v ua := by
    intro v; rw [hℓ, ContinuousLinearMap.smul_apply, innerSL_apply_apply, Col.Hf_eq_inner, smul_eq_mul]
  have hf1 : (fun v => cexp (c0 * Hf v ua) * Col.F0 I q βt v) =
      fun v => cexp (ℓL v) * Col.F0 I q βt v := by funext v; rw [hℓv]
  rw [hf1]
  set W := Col.wmap (IR I) with hW
  have hexpc : ContDiff ℂ (⊤ : ℕ∞) (fun v => cexp (ℓL v)) := ℓL.contDiff.cexp
  have hgc : ContDiff ℂ (⊤ : ℕ∞) (fun v => βt (W v)) :=
    (cab_contDiff_top (hβt.comp W.differentiable)).of_le (by exact_mod_cast le_top)
  have hF0c : ContDiff ℂ (⊤ : ℕ∞) (Col.F0 I q βt) :=
    (cab_contDiff_top (differentiable_zeroModeLift I q βt hβt)).of_le (by exact_mod_cast le_top)
  have hle : ((c : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by exact_mod_cast le_top
  have hr := cab_restrict (cabVP σ) (c := c) (f := fun v => cexp (ℓL v) * Col.F0 I q βt v)
    (g := fun v => cexp (ℓL v) * βt (W v)) ((hexpc.mul hF0c).of_le hle) ((hexpc.mul hgc).of_le hle)
    (fun v hv => by simp only [zeroModeLift_on_part hI q βt σ v hv, hW]) xs hxs
  rw [hr]
  have hj : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j (fun v => βt (W v)) 0 = 0 := by
    intro j hj1 hjc
    have hβj : ContDiff ℂ j βt := contDiff_of_differentiable_fd hβt j
    have := W.iteratedFDeriv_comp_right hβj (0 : Vsp X.dim) le_rfl
    show iteratedFDeriv ℂ j (βt ∘ W) 0 = 0
    rw [this, map_zero, hbj j hj1 hjc]
    ext x; simp
  have hm := ct_iter_mul_jet_one (fun v => cexp (ℓL v)) (fun v => βt (W v)) hexpc hgc c
    (by simp [hb0]) hj
  rw [hm, ct_iter_cexp_apply]
  have h0 : Hf (0 : Vsp X.dim) ua = 0 := by simp [Hf]
  simp [hℓv, h0]

end

end ReciprocityTheory.ChartRestriction.G.I2
