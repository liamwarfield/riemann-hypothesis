module

public import GroundTheory.LocalFields.DifferentGalois

@[expose] public section

section -- merged from GroundTheory.LocalFields.LocalZetaIntegral
noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

section Laurent



theorem differentiable_qpow : Differentiable ℂ fun s : ℂ => (residueCard K : ℂ) ^ (-s) :=
  differentiable_neg.const_cpow (Or.inl residueCard_ne_zero_complex)

end Laurent

section Sums


omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
theorem hasSum_int_of_shift {E : Type*} [AddCommMonoid E] [TopologicalSpace E] {a : ℤ → E}
    (M : ℤ) (h : ∀ k, k < M → a k = 0) {x : E} (hx : HasSum (fun n : ℕ => a (M + n)) x) :
    HasSum a x := by
  have hinj : Function.Injective (fun n : ℕ => M + (n : ℤ)) := fun m n hmn => by
    simpa using hmn
  refine (hinj.hasSum_iff fun k hk => h k ?_).mp hx
  by_contra hle
  push Not at hle
  exact hk ⟨(k - M).toNat, by simp only; omega⟩

end Sums

section LFactor

variable (χ : Kˣ →* ℂˣ)


open Classical in
def localLFactor (s : ℂ) : ℂ :=
  if IsUnramifiedChar χ then (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
  else 1

variable {χ}

theorem localLFactor_of_isUnramified (h : IsUnramifiedChar χ) (s : ℂ) :
    localLFactor χ s = (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹ := by
  simp [localLFactor, h]

theorem localLFactor_of_not_isUnramified (h : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localLFactor χ s = 1 := by
  simp [localLFactor, h]

variable (hχ : Continuous χ)
include hχ

theorem norm_quasiChar_unifUnit :
    ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ = (residueCard K : ℝ) ^ (-quasiCharExponent χ) := by
  rw [norm_quasiChar_apply hχ, modulus_of_ne_zero (unifUnit K).ne_zero, ord_unifUnit,
    NNReal.coe_zpow, NNReal.coe_natCast, ← Real.rpow_intCast,
    ← Real.rpow_mul residueCard_pos_real.le]
  congr 1
  push_cast
  ring

theorem norm_quasiChar_unifUnit_mul_qpow_lt_one {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, norm_quasiChar_unifUnit hχ, norm_qpow, ← Real.rpow_add residueCard_pos_real]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast one_lt_residueCard) (by linarith)

theorem one_sub_quasiChar_unifUnit_mul_qpow_ne_zero {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  rw [← sub_eq_zero.mp h, norm_one] at this
  exact lt_irrefl _ this

theorem localLFactor_ne_zero {s : ℂ} (hs : -quasiCharExponent χ < s.re) :
    localLFactor χ s ≠ 0 := by
  by_cases h : IsUnramifiedChar χ
  · rw [localLFactor_of_isUnramified h]
    exact inv_ne_zero (one_sub_quasiChar_unifUnit_mul_qpow_ne_zero hχ hs)
  · rw [localLFactor_of_not_isUnramified h]
    exact one_ne_zero

theorem norm_quasiChar_mul_modulus_cpow (u : Kˣ) (s : ℂ) :
    ‖((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s‖ =
      ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ ^ ord (u : K) := by
  have hχu : ‖((χ u : ℂˣ) : ℂ)‖ = ‖((χ (unifUnit K) : ℂˣ) : ℂ)‖ ^ ord (u : K) := by
    have e := congrArg (fun v => ‖((χ v : ℂˣ) : ℂ)‖) (eq_unifUnit_zpow_mul u)
    rw [e, map_mul, Units.val_mul, norm_mul,
      norm_quasiChar_apply_eq_one hχ (unifUnit_zpow_neg_mul_mem u), mul_one, map_zpow,
      Units.val_zpow_eq_zpow_val, norm_zpow]
  rw [norm_mul, hχu, modulus_cpow_eq_zpow, norm_zpow, ← mul_zpow, ← norm_mul]

end LFactor

section ZetaNonvanishing₂

variable [MeasurableSpace K] [BorelSpace K]

def localZeta (f : K → ℂ) (χ : Kˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ u, f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s ∂multHaar K

variable {f : K → ℂ} {χ : Kˣ →* ℂˣ}

omit [MeasurableSpace K] [BorelSpace K] in
theorem continuous_localZeta_integrand (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) (s : ℂ) :
    Continuous fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s := by
  refine ((hf.1.continuous.comp Units.continuous_val).mul (Units.continuous_val.comp hχ)).mul ?_
  refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
    (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
  exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)

theorem integrable_localZeta (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    Integrable (fun u : Kˣ => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s)
      (multHaar K) := by
  obtain ⟨-, M, -, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  obtain ⟨C, hC⟩ := hf.1.continuous.bounded_above_of_compact_support hf.2
  set ρ := ‖((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)‖ with hρ
  have hρ1 : ρ < 1 := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  have hρ0 : 0 < ρ := norm_pos_iff.mpr (mul_ne_zero (χ _).ne_zero (qpow_ne_zero s))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine ⟨(continuous_localZeta_integrand hf hχ s).aestronglyMeasurable, ?_⟩
  let a : ℤ → ℝ := fun k => if M ≤ k then C * ρ ^ k else 0
  have ha0 : ∀ k, 0 ≤ a k := fun k => by
    simp only [a]
    split_ifs
    · exact mul_nonneg hC0 (zpow_nonneg hρ0.le _)
    · exact le_rfl
  have hsum : HasSum a (C * ρ ^ M * (1 - ρ)⁻¹) := by
    refine hasSum_int_of_shift M (fun k hk => by simp [a, not_le.mpr hk]) ?_
    have e : (fun n : ℕ => a (M + n)) = fun n : ℕ => C * ρ ^ M * ρ ^ n := by
      funext n
      simp only [a, le_add_iff_nonneg_right, Nat.cast_nonneg, if_true]
      rw [zpow_add₀ hρ0.ne', zpow_natCast, mul_assoc]
    rw [e]
    exact (hasSum_geometric_of_lt_one hρ0.le hρ1).mul_left _
  have hbound : ∀ u : Kˣ,
      ‖f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s‖ₑ ≤
        ENNReal.ofReal (a (ord (u : K))) := by
    intro u
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc, norm_mul, norm_quasiChar_mul_modulus_cpow hχ]
    simp only [a]
    split_ifs with hk
    · exact mul_le_mul_of_nonneg_right (hC _) (zpow_nonneg hρ0.le _)
    · have : f u = 0 := by
        by_contra h0
        exact hk ((mem_valBall_iff_le_ord u.ne_zero).mp (hM _ h0))
      rw [this, norm_zero, zero_mul]
  refine (lintegral_multHaar_le_tsum _ (fun k => ENNReal.ofReal (a k)) hbound).trans_lt ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg ha0 hsum.summable]
  exact ENNReal.ofReal_lt_top


open scoped Classical in
theorem localZeta_eq_sum (hf : f ∈ schwartzBruhat K) (hχ : Continuous χ) {M N : ℤ} (hMN : M ≤ N)
    (hM : ∀ x, f x ≠ 0 → x ∈ valBall K M) (hN : ∀ x ∈ valBall K N, f x = f 0) {s : ℂ}
    (hs : -quasiCharExponent χ < s.re) :
    localZeta f χ s =
      ∑ k ∈ Finset.Ico M N, (∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K) *
          ((residueCard K : ℂ) ^ (-s)) ^ k +
        if IsUnramifiedChar χ then
          f 0 * (((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s)) ^ N *
            (1 - ((χ (unifUnit K) : ℂˣ) : ℂ) * (residueCard K : ℂ) ^ (-s))⁻¹
        else 0 := by
  set T := (residueCard K : ℂ) ^ (-s) with hT
  set α := ((χ (unifUnit K) : ℂˣ) : ℂ) with hα
  let Z : ℤ → ℂ := fun k => ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) ∂multHaar K
  have hsum := hasSum_setIntegral_ordShell (integrable_localZeta hf hχ hs)
  have hterm : ∀ k, ∫ u in ordShell K k, f u * ((χ u : ℂˣ) : ℂ) *
      ((modulus (u : K) : ℝ) : ℂ) ^ s ∂multHaar K = Z k * T ^ k := by
    intro k
    simp only [Z]
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_
    rw [modulus_cpow_eq_zpow, mem_ordShell.mp hu]
  simp only [hterm] at hsum
  have hlow : ∀ k, k < M → Z k = 0 := by
    intro k hk
    refine setIntegral_eq_zero_of_forall_eq_zero fun u hu => ?_
    have : f u = 0 := by
      by_contra h0
      have := (mem_valBall_iff_le_ord u.ne_zero).mp (hM _ h0)
      rw [mem_ordShell.mp hu] at this
      omega
    rw [this, zero_mul]
  have hhigh : ∀ k, N ≤ k → Z k = f 0 * (if IsUnramifiedChar χ then α ^ k else 0) := by
    intro k hk
    rw [← setIntegral_ordShell_quasiChar hχ k, ← integral_const_mul]
    refine setIntegral_congr_fun (measurableSet_ordShell k) fun u hu => ?_
    rw [hN u ((mem_valBall_iff_le_ord u.ne_zero).mpr (by rw [mem_ordShell.mp hu]; exact hk))]
  have hαT : ‖α * T‖ < 1 := norm_quasiChar_unifUnit_mul_qpow_lt_one hχ hs
  have hαT0 : α * T ≠ 0 := mul_ne_zero (χ _).ne_zero (qpow_ne_zero s)
  have h1 : HasSum (fun k => if k < N then Z k * T ^ k else 0)
      (∑ k ∈ Finset.Ico M N, Z k * T ^ k) := by
    have : HasSum (fun k => if k < N then Z k * T ^ k else 0)
        (∑ k ∈ Finset.Ico M N, if k < N then Z k * T ^ k else 0) :=
      hasSum_sum_of_ne_finset_zero (fun k hk => by
        rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hk
        rcases hk with hk | hk
        · simp [hlow k hk]
        · simp [not_lt.mpr hk])
    convert this using 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_Ico.mp hk).2]
  have h2 : HasSum (fun k => if k < N then 0 else Z k * T ^ k)
      (if IsUnramifiedChar χ then f 0 * (α * T) ^ N * (1 - α * T)⁻¹ else 0) := by
    by_cases hu : IsUnramifiedChar χ
    · rw [if_pos hu]
      refine hasSum_int_of_shift N (fun k hk => by simp [hk]) ?_
      have e : (fun n : ℕ => if N + (n : ℤ) < N then 0 else Z (N + n) * T ^ (N + (n : ℤ))) =
          fun n : ℕ => f 0 * (α * T) ^ N * (α * T) ^ n := by
        funext n
        rw [if_neg (by omega), hhigh _ (by omega), if_pos hu, mul_assoc, ← mul_zpow,
          zpow_add₀ hαT0, zpow_natCast, mul_assoc]
      rw [e]
      exact (hasSum_geometric_of_norm_lt_one hαT).mul_left _
    · rw [if_neg hu]
      convert hasSum_zero with k
      split_ifs with hk
      · rfl
      · rw [hhigh k (not_lt.mp hk), if_neg hu, mul_zero, zero_mul]
  have h12 := h1.add h2
  have e : (fun k => (if k < N then Z k * T ^ k else 0) + (if k < N then 0 else Z k * T ^ k)) =
      fun k => Z k * T ^ k := by
    funext k
    split_ifs <;> simp
  rw [e] at h12
  exact hsum.unique h12



end ZetaNonvanishing₂

end GroundTheory.LocalField
end
end

noncomputable section

namespace GroundTheory.LocalField

open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

section Symmetric

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ

theorem integral_mul_localFourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) (y : K) :
    ∫ x, f x * localFourier μ ψ g (x * y) ∂μ = ∫ x, g x * localFourier μ ψ f (x * y) ∂μ := by
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have hfi := integrable_of_mem_schwartzBruhat μ hf
  have hgi := integrable_of_mem_schwartzBruhat μ hg
  let G : K → K → ℂ := fun x z => f x * (g z * (ψ (z * (x * y)) : ℂ))
  have hG : Integrable (Function.uncurry G) (μ.prod μ) := by
    have hdom : Integrable (fun p : K × K => ‖f p.1‖ * ‖g p.2‖) (μ.prod μ) :=
      hfi.norm.mul_prod hgi.norm
    refine hdom.mono' (Continuous.aestronglyMeasurable ?_) (Eventually.of_forall fun p => ?_)
    · exact (hf.1.continuous.comp continuous_fst).mul ((hg.1.continuous.comp continuous_snd).mul
        (hψc.comp (continuous_snd.mul (continuous_fst.mul continuous_const))))
    · simp [G, Function.uncurry, Circle.norm_coe]
  have e1 : ∫ x, f x * localFourier μ ψ g (x * y) ∂μ = ∫ x, ∫ z, G x z ∂μ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [localFourier, G]
    rw [integral_const_mul]
  have e2 : ∫ x, g x * localFourier μ ψ f (x * y) ∂μ = ∫ z, ∫ x, G x z ∂μ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [localFourier, G]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [show x * (z * y) = z * (x * y) by ring]
    ring
  rw [e1, e2, integral_integral_swap hG]

end Symmetric

section Multiplicative

theorem haarIntegers_singleton_zero : haarIntegers K {0} = 0 := by
  have hq : (1 : ℝ≥0) < (residueCard K : ℝ≥0) := one_lt_residueCard_nnreal
  have ht : Tendsto (fun n : ℕ => (((residueCard K : ℝ≥0) ^ (-(n : ℤ)) : ℝ≥0) : ℝ≥0∞)) atTop
      (𝓝 0) := by
    rw [← ENNReal.coe_zero, ENNReal.tendsto_coe]
    have e : (fun n : ℕ => (residueCard K : ℝ≥0) ^ (-(n : ℤ))) =
        fun n : ℕ => ((residueCard K : ℝ≥0)⁻¹) ^ n := by
      funext n
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [e]
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (inv_lt_one_of_one_lt₀ hq)
  refine le_antisymm (ge_of_tendsto' ht fun n => ?_) (by simp)
  rw [← haarIntegers_valBall]
  exact measure_mono (Set.singleton_subset_iff.mpr (zero_mem _))

theorem integral_multHaar_mul_modulus (h : K → ℂ) :
    ∫ u, h u * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      (multHaarConst K).toReal * ∫ x, h x ∂haarIntegers K := by
  rw [integral_multHaar (fun x => h x * ((modulus x : ℝ) : ℂ)), Complex.real_smul]
  congr 1
  have hae : ∀ᵐ x ∂haarIntegers K, x ∈ ({0}ᶜ : Set K) := by
    rw [ae_iff]
    simpa using haarIntegers_singleton_zero (K := K)
  conv_rhs => rw [← Measure.restrict_eq_self_of_ae_mem hae]
  refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have hm : ((modulus x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos hx).ne'
  rw [Complex.real_smul, Complex.ofReal_inv, mul_comm, mul_assoc, mul_inv_cancel₀ hm, mul_one]

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ

theorem integral_multHaar_mul_localFourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) (y : K) :
    ∫ u, f u * localFourier μ ψ g ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      ∫ u, g u * localFourier μ ψ f ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K := by
  rw [integral_multHaar_mul_modulus (fun x => f x * localFourier μ ψ g (x * y)),
    integral_multHaar_mul_modulus (fun x => g x * localFourier μ ψ f (x * y))]
  congr 1
  have hμ := eq_smul_haarIntegers μ
  have key := integral_mul_localFourier_comm μ hψ hf hg y
  have hc : (μ (𝒪[K] : Set K)).toReal ≠ 0 := by
    refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
    · rw [← coe_valBall_zero]
      exact ((isOpen_valBall 0).measure_pos μ ⟨0, zero_mem _⟩).ne'
    · rw [← coe_valBall_zero]
      exact (isCompact_valBall 0).measure_lt_top.ne
  have hJ : ∀ F : K → ℂ, ∫ x, F x ∂μ = ((μ (𝒪[K] : Set K)).toReal : ℂ) * ∫ x, F x ∂haarIntegers K :=
    fun F => by
      conv_lhs => rw [hμ]
      rw [integral_smul_measure, Complex.real_smul]
  rw [hJ, hJ] at key
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc) key

end Multiplicative

section Tate

variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
  (hψ1 : ψ ≠ 1) {χ : Kˣ →* ℂˣ} (hχ : Continuous χ)
include hψ hψ1 hχ

theorem localZeta_mul_localZeta_fourier_eq {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s) =
      ∫ y, ((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
        ∫ x, f x * localFourier μ ψ g ((x : K) * (y : K)) * ((modulus (x : K) : ℝ) : ℂ)
          ∂multHaar K ∂multHaar K := by
  set F₁ : Kˣ → ℂ := fun u => f u * ((χ u : ℂˣ) : ℂ) * ((modulus (u : K) : ℝ) : ℂ) ^ s
  set G₁ : Kˣ → ℂ := fun u => localFourier μ ψ g u * (((χ⁻¹) u : ℂˣ) : ℂ) *
    ((modulus (u : K) : ℝ) : ℂ) ^ (1 - s)
  have hF₁ : Integrable F₁ (multHaar K) := integrable_localZeta hf hχ hs1
  have hG₁ : Integrable G₁ (multHaar K) :=
    integrable_localZeta (localFourier_mem_schwartzBruhat μ hψ hψ1 hg) (continuous_quasiChar_inv hχ)
      (by rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]; linarith)
  have hP : Integrable (fun p : Kˣ × Kˣ => F₁ p.1 * G₁ p.2) ((multHaar K).prod (multHaar K)) :=
    hF₁.mul_prod hG₁
  have hH : Integrable (Function.uncurry fun x y : Kˣ => F₁ x * G₁ (x * y))
      ((multHaar K).prod (multHaar K)) :=
    (measurePreserving_prod_mul (multHaar K) (multHaar K)).integrable_comp_of_integrable hP
  have hpt : ∀ x y : Kˣ, F₁ x * G₁ (x * y) =
      ((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
        (f x * localFourier μ ψ g ((x : K) * (y : K)) * ((modulus (x : K) : ℝ) : ℂ)) := by
    intro x y
    have hx0 : ((modulus (x : K) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos x.ne_zero).ne'
    have e1 : (((χ⁻¹) (x * y) : ℂˣ) : ℂ) = ((χ x : ℂˣ) : ℂ)⁻¹ * ((χ y : ℂˣ) : ℂ)⁻¹ := by
      rw [MonoidHom.inv_apply, map_mul, mul_inv, Units.val_mul, Units.val_inv_eq_inv_val,
        Units.val_inv_eq_inv_val]
    have e2 : ((modulus ((x * y : Kˣ) : K) : ℝ) : ℂ) ^ (1 - s) =
        ((modulus (x : K) : ℝ) : ℂ) ^ (1 - s) * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) := by
      rw [Units.val_mul, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    have e3 : ((modulus (x : K) : ℝ) : ℂ) ^ s * ((modulus (x : K) : ℝ) : ℂ) ^ (1 - s) =
        ((modulus (x : K) : ℝ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hx0, add_sub_cancel, Complex.cpow_one]
    have hχx : ((χ x : ℂˣ) : ℂ) * ((χ x : ℂˣ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (χ x).ne_zero
    simp only [F₁, G₁]
    rw [e1, e2, Units.val_mul]
    calc f x * ((χ x : ℂˣ) : ℂ) * ((modulus (x : K) : ℝ) : ℂ) ^ s *
          (localFourier μ ψ g ((x : K) * (y : K)) * (((χ x : ℂˣ) : ℂ)⁻¹ * ((χ y : ℂˣ) : ℂ)⁻¹) *
            (((modulus (x : K) : ℝ) : ℂ) ^ (1 - s) * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s)))
        = (((χ x : ℂˣ) : ℂ) * ((χ x : ℂˣ) : ℂ)⁻¹) *
            (((modulus (x : K) : ℝ) : ℂ) ^ s * ((modulus (x : K) : ℝ) : ℂ) ^ (1 - s)) *
            (((χ y : ℂˣ) : ℂ)⁻¹ * ((modulus (y : K) : ℝ) : ℂ) ^ (1 - s) *
              (f x * localFourier μ ψ g ((x : K) * (y : K)))) := by ring
      _ = _ := by rw [hχx, e3]; ring
  calc localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s)
      = (∫ x, F₁ x ∂multHaar K) * ∫ y, G₁ y ∂multHaar K := rfl
    _ = ∫ x, F₁ x * ∫ y, G₁ y ∂multHaar K ∂multHaar K := (integral_mul_const _ _).symm
    _ = ∫ x, ∫ y, F₁ x * G₁ (x * y) ∂multHaar K ∂multHaar K := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [integral_const_mul, integral_mul_left_eq_self (μ := multHaar K) G₁ x]
    _ = ∫ y, ∫ x, F₁ x * G₁ (x * y) ∂multHaar K ∂multHaar K := integral_integral_swap hH
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [hpt]
        rw [integral_const_mul]

theorem localZeta_mul_localZeta_fourier_comm {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) {s : ℂ} (hs1 : -quasiCharExponent χ < s.re)
    (hs2 : s.re < 1 - quasiCharExponent χ) :
    localZeta f χ s * localZeta (localFourier μ ψ g) χ⁻¹ (1 - s) =
      localZeta g χ s * localZeta (localFourier μ ψ f) χ⁻¹ (1 - s) := by
  rw [localZeta_mul_localZeta_fourier_eq μ hψ hψ1 hχ hf hg hs1 hs2,
    localZeta_mul_localZeta_fourier_eq μ hψ hψ1 hχ hg hf hs1 hs2]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [integral_multHaar_mul_localFourier_comm μ hψ hf hg]

end Tate

end GroundTheory.LocalField
