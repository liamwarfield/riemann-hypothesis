module

public import Formalism.JumpKernelCokernel.JumpShiftProofs.RowDJoint
public import Formalism.TruncatedSeriesCounting.EtaDeterminantPolynomialIdentities
public import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.PadicValNatFactorialLeReal
public import Formalism.EisensteinCokernelLengths.FactorialValuationBounds.RationalTailBoundCubic

@[expose] public section

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.ColThmC
noncomputable section

namespace Formalism.KernelCokernelLengths

theorem column_theorem_C : ColThmC := by
  intro O _ _ _ M _ _ _ _ ℓ P k F gen n r m e e' S cD hn hrk hgen hk hF0 hF hsub hG hN hE
  have h := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.column_assembly_bound O M ℓ P k F gen m e e' (r * S + 2 * m * cD) hF0 hF hsub hG hN hE
  refine h.trans ?_
  have hAB : Module.finrank O M * e + gen.card * m * e' + (k - gen.card) * (r * S + 2 * m * cD) ≤
      (n + 1) * r * e + 4 * n * m * e' + (3 * n / 2) * (r * S + 2 * m * cD) := by
    gcongr
  gcongr

end Formalism.KernelCokernelLengths
end
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKer
noncomputable section

namespace Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

open PowerSeries

theorem len_quot_pow {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (v : ℕ) :
    Module.length O (O ⧸ Ideal.span {(u : O) * ϖ ^ v}) = v := by
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hϖ.maximalIdeal_eq]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal (R := O) v

theorem ker_eq_coker {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) :
    Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f) := by
  have h1 : Module.length O M =
      Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
      (Submodule.subtype_injective _) f.surjective_rangeRestrict
      (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length O M =
      Module.length O (LinearMap.range f) + Module.length O (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
      (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have hR : Module.length O (LinearMap.range f) ≠ ⊤ :=
    ne_top_of_le_ne_top hM
      (Module.length_le_of_injective _ (Submodule.subtype_injective (LinearMap.range f)))
  have h5 : Module.length O (LinearMap.ker f) + Module.length O (LinearMap.range f) =
      Module.length O (M ⧸ LinearMap.range f) + Module.length O (LinearMap.range f) := by
    rw [← h1, h2, add_comm]
  exact WithTop.add_right_cancel hR h5

variable {O : Type} [CommRing O] (ℓ : O) (n k : ℕ)

abbrev J : Ideal (PowerSeries O) := Ideal.span {(X : PowerSeries O) ^ n, C (ℓ ^ k)}

noncomputable abbrev ψ : Polynomial O →+* (PowerSeries O ⧸ J ℓ n k) :=
  Polynomial.eval₂RingHom (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X)

theorem psi_apply (P : Polynomial O) :
    ψ ℓ n k P = P.eval₂ (algebraMap O (PowerSeries O ⧸ J ℓ n k)) (Ideal.Quotient.mk (J ℓ n k) X) := rfl

theorem alg_eq (a : O) :
    algebraMap O (PowerSeries O ⧸ J ℓ n k) a = Ideal.Quotient.mk (J ℓ n k) (C a) := rfl

theorem psi_eq (P : Polynomial O) : ψ ℓ n k P = Ideal.Quotient.mk (J ℓ n k) (P : PowerSeries O) := by
  have h : ψ ℓ n k = (Ideal.Quotient.mk (J ℓ n k)).comp (Polynomial.coeToPowerSeries.ringHom) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [alg_eq]
    · simp
  rw [h]
  rfl

theorem mk_eq_psi (p : PowerSeries O) :
    Ideal.Quotient.mk (J ℓ n k) p = ψ ℓ n k (trunc n p) := by
  rw [psi_eq, Ideal.Quotient.eq]
  obtain ⟨q, hq⟩ : (X : PowerSeries O) ^ n ∣ p - (trunc n p : PowerSeries O) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [Polynomial.coeff_coe, PowerSeries.coeff_trunc, hm]
  rw [hq]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem algebraMap_pow_k :
    algebraMap O (PowerSeries O ⧸ J ℓ n k) (ℓ ^ k) = 0 := by
  rw [alg_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

theorem smul_pow_k (b : PowerSeries O ⧸ J ℓ n k) : ℓ ^ k • b = 0 := by
  rw [Algebra.smul_def, algebraMap_pow_k, zero_mul]

theorem len_B_le :
    Module.length O (PowerSeries O ⧸ J ℓ n k) ≤
      Module.length O (Fin n → O ⧸ Ideal.span {ℓ ^ k}) := by
  let e : Fin n → (PowerSeries O ⧸ J ℓ n k) := fun j => (Ideal.Quotient.mk (J ℓ n k) X) ^ (j : ℕ)
  have hker : ∀ j, Ideal.span {ℓ ^ k} ≤ LinearMap.ker (LinearMap.toSpanSingleton O _ (e j)) := by
    intro j
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact smul_pow_k ℓ n k _
  let Φ : (Fin n → O ⧸ Ideal.span {ℓ ^ k}) →ₗ[O] (PowerSeries O ⧸ J ℓ n k) :=
    ∑ j : Fin n, (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j)).comp
      (LinearMap.proj j)
  have hΦ : Function.Surjective Φ := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨fun j => Ideal.Quotient.mk _ (coeff (j : ℕ) p), ?_⟩
    rw [mk_eq_psi, psi_apply, eval₂_trunc_eq_sum_range,
      ← Fin.sum_univ_eq_sum_range]
    simp only [Φ]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show (Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (e j)) (hker j))
      (Submodule.Quotient.mk (coeff (j : ℕ) p)) = _
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, Algebra.smul_def]
  exact Module.length_le_of_surjective Φ hΦ

theorem len_coker_le :
    Module.length O ((PowerSeries O ⧸ J ℓ n k) ⧸ LinearMap.range (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))) ≤
      Module.length O (O ⧸ Ideal.span {ℓ ^ k}) := by
  set R := LinearMap.range (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ))) with hR
  have hker : Ideal.span {ℓ ^ k} ≤
      LinearMap.ker (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k))) := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, LinearMap.toSpanSingleton_apply,
      ← LinearMap.map_smul, smul_pow_k, map_zero]
  let Ψ := Submodule.liftQ _ (LinearMap.toSpanSingleton O _ (R.mkQ (1 : PowerSeries O ⧸ J ℓ n k)))
    hker
  have hΨ : Function.Surjective Ψ := by
    intro z
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective R z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    obtain ⟨Q, hQ⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (a := ℓ) (p := trunc n p)
    refine ⟨Submodule.Quotient.mk ((trunc n p).eval ℓ), ?_⟩
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, ← LinearMap.map_smul,
      Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine ⟨-ψ ℓ n k Q, ?_⟩
    have hX : Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ) =
        ψ ℓ n k (Polynomial.X - Polynomial.C ℓ) := by
      rw [psi_eq, Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C]
    rw [map_neg, LinearMap.mulLeft_apply, hX, ← map_mul, ← hQ, map_sub, mk_eq_psi ℓ n k p,
      psi_apply ℓ n k (Polynomial.C _), Polynomial.eval₂_C,
      Algebra.algebraMap_eq_smul_one, neg_sub]
  exact Module.length_le_of_surjective Ψ hΨ

end Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas

open Formalism.KernelCokernelLengths.TorsionKernelLengthLemmas in
theorem Formalism.KernelCokernelLengths.torsion_kernel_length : Formalism.KernelCokernelLengths.TorsKer := by
  intro O _ _ _ ℓ hℓ n k
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hℓ hϖ
  have hl1 : Module.length O (O ⧸ Ideal.span {ℓ}) = v := by
    rw [hu]; exact len_quot_pow hϖ u v
  have hlk : Module.length O (O ⧸ Ideal.span {ℓ ^ k}) = ((v * k : ℕ) : ℕ∞) := by
    rw [hu, mul_pow, ← pow_mul, ← Units.val_pow_eq_pow_val]
    exact len_quot_pow hϖ (u ^ k) (v * k)
  have hB : Module.length O (PowerSeries O ⧸ J ℓ n k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (len_B_le ℓ n k)
    rw [Module.length_pi, hlk, ENat.card_eq_coe_fintype_card, Fintype.card_fin, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  rw [ker_eq_coker hB, hl1]
  refine (len_coker_le ℓ n k).trans ?_
  rw [hlk]
  push_cast
  rw [mul_comm]
end
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.HCoefLim
noncomputable section

namespace Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

def P (s : ℝ) : ℝ := 25 + 57 * s + 40 * s ^ 2 + 8 * s ^ 3

lemma hCoef_eq (x : ℝ) (hx : 1 < x) : Formalism.KernelCokernelLengths.hCoef x = P (1 / (x - 1)) := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h0 : x ≠ 0 := by linarith
  unfold Formalism.KernelCokernelLengths.hCoef P
  field_simp
  ring

lemma P_mono {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) : P t ≤ P s := by
  unfold P
  have hs : 0 ≤ s := le_trans ht hts
  nlinarith [mul_le_mul hts hts ht hs, pow_le_pow_left₀ ht hts 3, pow_le_pow_left₀ ht hts 2]

lemma P_ge {s : ℝ} (hs : 0 ≤ s) : 25 ≤ P s := by
  unfold P
  nlinarith [pow_nonneg hs 2, pow_nonneg hs 3]

end Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

open Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas in
theorem Formalism.KernelCokernelLengths.coefficient_height_limit : Formalism.KernelCokernelLengths.HCoefLim := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    rw [hCoef_eq x (by linarith), hCoef_eq y (by linarith)]
    apply P_mono
    · have : 0 < y - 1 := by linarith
      positivity
    · exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · intro x hx
    rw [hCoef_eq x (by linarith)]
    apply P_ge
    have : 0 < x - 1 := by linarith
    positivity
  · have hs : Filter.Tendsto (fun x : ℝ => 1 / (x - 1)) Filter.atTop (nhds 0) := by
      have h := tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) Filter.tendsto_id)
      refine h.congr ?_
      intro x
      simp [sub_eq_add_neg]
    have hP : Continuous P := by unfold P; fun_prop
    have h25 : P 0 = 25 := by unfold P; norm_num
    have hlim : Filter.Tendsto (fun x : ℝ => P (1 / (x - 1))) Filter.atTop (nhds 25) := by
      rw [← h25]; exact (hP.tendsto 0).comp hs
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact (hCoef_eq x hx).symm
end
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.JumpShift
namespace Formalism.KernelCokernelLengths

theorem jump_shift_holds : JumpShift := by
  intro s S η t a ht
  refine ⟨fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

end Formalism.KernelCokernelLengths
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.RelZero
namespace Formalism.KernelCokernelLengths

theorem relation_vanishes : RelZero := by
  intro R _ u π₀ q ℓ h η y hℓ hη hy
  apply Formalism.TruncatedSeriesCounting.R9.pow_mem_span_pow_mul R u π₀ q ℓ (h / (ℓ - 1) + 1) η y hy
  have hpos : 0 < ℓ - 1 := by omega
  have h1 : h < (ℓ - 1) * (h / (ℓ - 1) + 1) := Nat.lt_mul_div_succ h hpos
  have h2 : (ℓ - 1) * (h / (ℓ - 1) + 1) ≤ (ℓ - 1) * y := Nat.mul_le_mul_left _ hy
  omega

end Formalism.KernelCokernelLengths
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.ThickA
namespace Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

open Filter

lemma coef_le (x : ℝ) (hx : 11 ≤ x) : (2 * x - 1) / (x - 1) ^ 2 ≤ 21 / 100 := by
  rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < (x - 1) ^ 2)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hx) (by linarith : (0 : ℝ) ≤ x - 11 / 21)]

lemma coef_nonneg (x : ℝ) (hx : 11 ≤ x) : 0 ≤ (2 * x - 1) / (x - 1) ^ 2 := by
  exact div_nonneg (by linarith) (sq_nonneg _)

lemma one_le_log (x : ℝ) (hx : 11 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

lemma logb_le (x y : ℝ) (hx : 11 ≤ x) (hy : 1 ≤ y) : Real.logb x y ≤ Real.log y := by
  rw [Real.logb]
  exact div_le_self (Real.log_nonneg hy) (one_le_log x hx)

lemma logb_nonneg' (x y : ℝ) (hx : 11 ≤ x) (hy : 1 ≤ y) : 0 ≤ Real.logb x y := by
  rw [Real.logb]
  exact div_nonneg (Real.log_nonneg hy) (by linarith [one_le_log x hx])

lemma eventually_log (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 13 + 2 * Real.log (4 * (n : ℝ)) ≤ c * n := by
  refine ⟨⌈256 / c ^ 2 + 26 / c⌉₊ + 1, fun n hn => ?_⟩
  have hA : 0 ≤ 256 / c ^ 2 := by positivity
  have hB : 0 ≤ 26 / c := by positivity
  have hnR : 256 / c ^ 2 + 26 / c + 1 ≤ (n : ℝ) := by
    have h1 := Nat.le_ceil (256 / c ^ 2 + 26 / c)
    have h2 : ((⌈256 / c ^ 2 + 26 / c⌉₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    push_cast at h2
    linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log (4 * n) ≤ 2 * Real.sqrt (4 * n) := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 4 * n))
    rw [Real.log_sqrt (by positivity)] at h
    linarith [Real.sqrt_nonneg (4 * (n : ℝ))]
  have hsq : Real.sqrt (4 * n) = 2 * Real.sqrt n := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hs16 : 16 / c ≤ Real.sqrt n := by
    have h1 : (16 / c) ^ 2 ≤ (n : ℝ) := by
      have : (16 / c) ^ 2 = 256 / c ^ 2 := by ring
      linarith
    calc 16 / c = Real.sqrt ((16 / c) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h1
  have h16 : 16 ≤ c * Real.sqrt n := by
    rw [div_le_iff₀ hc] at hs16
    linarith
  have h26 : 26 ≤ c * n := by
    have : 26 / c ≤ (n : ℝ) := by linarith
    rw [div_le_iff₀ hc] at this
    linarith
  have hcn : c * n = (c * Real.sqrt n) * Real.sqrt n := by rw [mul_assoc, hss]
  nlinarith [mul_le_mul_of_nonneg_right h16 hs0]

end Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas

open Formalism.KernelCokernelLengths.ThicknessFirstBoundLogLemmas in
theorem Formalism.KernelCokernelLengths.thickness_first_bound : Formalism.KernelCokernelLengths.ThickA := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_log (ε / 2) (by linarith)
  refine ⟨min (1 / 10) (ε / 10), by positivity, max N 4, ?_⟩
  intro ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3
  have hδ1 : min (1 / 10) (ε / 10) ≤ 1 / 10 := min_le_left _ _
  have hδε : min (1 / 10) (ε / 10) ≤ ε / 10 := min_le_right _ _
  have hbN : N ≤ b := le_trans (le_max_left _ _) hb
  have hb4 : 4 ≤ b := le_trans (le_max_right _ _) hb
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg _
  have hb4R : (4 : ℝ) ≤ b := by exact_mod_cast hb4
  have hℓ' : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hH1 : (1 : ℝ) ≤ 2 * ((h + (η + t + 1) : ℕ) : ℝ) := by
    have : 1 ≤ h + (η + t + 1) := by omega
    have : (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hHle : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2 := by
    have : h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2 := by omega
    exact_mod_cast this
  have hδb : min (1 / 10) (ε / 10) * (b : ℝ) ≤ ε / 10 * b := mul_le_mul_of_nonneg_right hδε hb0
  have hδb1 : min (1 / 10) (ε / 10) * (b : ℝ) ≤ 1 / 10 * b := mul_le_mul_of_nonneg_right hδ1 hb0
  have hcoef := coef_le ℓ hℓ'
  have hcoef0 := coef_nonneg ℓ hℓ'
  have hlogb := logb_le ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1
  have hlogb0 := logb_nonneg' ℓ (2 * ((h + (η + t + 1) : ℕ) : ℝ)) hℓ' hH1
  have h2H : 2 * ((h + (η + t + 1) : ℕ) : ℝ) ≤ 4 * b := by
    have hη' : (η : ℝ) ≤ 1 / 10 * b := le_trans hη hδb1
    have hS' : (S : ℝ) ≤ 1 / 10 * b := le_trans hS hδb1
    have ht' : (t : ℝ) ≤ 1 / 10 * b := le_trans ht hδb1
    linarith
  have hlog2H : Real.log (2 * ((h + (η + t + 1) : ℕ) : ℝ)) ≤ Real.log (4 * b) :=
    Real.log_le_log (by linarith) h2H
  have hlogN := hN b hbN
  have haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) =
      ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) + 3 +
        (Real.logb (ℓ : ℝ) (2 * ((h + (η + t + 1) : ℕ) : ℝ)) + 1) := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    rw [mul_div_assoc]
  have hHc : ((h + (η + t + 1) : ℕ) : ℝ) * ((2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2) ≤
      ((h + (η + t + 1) : ℕ) : ℝ) * (21 / 100) :=
    mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg _)
  have haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) := by
    rw [haR]
    have := mul_nonneg (Nat.cast_nonneg (h + (η + t + 1))) hcoef0
    linarith
  have hceil : (⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1))⌉₊ : ℝ) ≤
      Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ (h + (η + t + 1)) + 1 := (Nat.ceil_lt_add_one haR0).le
  have hεb : 0 ≤ ε * (b : ℝ) := mul_nonneg hε.le hb0
  push_cast
  push_cast at hHle hHc hceil haR hlogb hlog2H
  linarith
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.ColumnDegreeBound
namespace Formalism.KernelCokernelLengths

theorem column_degree_bound : CDge := by
  intro ℓ hℓ bi S η h hh
  have h2 : bi + S + η ≤ h + η := by omega
  gcongr
  all_goals first
    | exact_mod_cast h2
    | (rw [sub_nonneg]; exact_mod_cast (by omega : 1 ≤ ℓ))
    | (rw [sub_pos]; exact_mod_cast (by omega : 1 < ℓ))

end Formalism.KernelCokernelLengths
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.PdFacts
noncomputable section

namespace Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

open Polynomial

variable {O : Type} [CommRing O] {V : Type} [AddCommGroup V] [Module O V]

theorem decomp (d : Module.End O V) (P : O[X]) (v : V) :
    aeval d P v = P.eval 0 • v + aeval d P.divX (d v) := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add P]
  rw [map_add (f := _), map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, ← Polynomial.coeff_zero_eq_eval_zero, add_comm]

theorem aeval_mem (d : Module.End O V) (M : Submodule O V) (hM : M.map d ≤ M) :
    ∀ (Q : O[X]) (v : V), v ∈ M → aeval d Q v ∈ M := by
  have hd : ∀ v ∈ M, d v ∈ M := fun v hv => hM (Submodule.mem_map_of_mem hv)
  have hpow : ∀ (n : ℕ) (v : V), v ∈ M → (d ^ n) v ∈ M := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hd v hv)
  intro Q
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [map_add (f := _), LinearMap.add_apply]
    exact M.add_mem (hp v hv) (hq v hv)
  | monomial n a =>
    intro v hv
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact M.smul_mem a (hpow n v hv)

end Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

open Polynomial Formalism.KernelCokernelLengths.PolynomialDegreeLemmas in
theorem Formalism.KernelCokernelLengths.polynomial_degree_facts : Formalism.KernelCokernelLengths.PdFacts := by
  intro O _ V _ _ d P M hM
  refine ⟨fun h0 => ?_, fun h0 u hu => ?_⟩
  · have ha : ∀ v : V, d (aeval d P v) = 0 := by
      intro v
      have h1 := congrArg (fun f : Module.End O V => f v) h0
      simpa [map_mul, aeval_X] using h1
    refine ⟨ha, fun v hv => ?_, fun w hw u hu => ?_⟩
    · rw [decomp d P v, hv, map_zero, add_zero]
    · have h1 := decomp d P u
      have h2 : P.eval 0 • w = d (-(aeval d P.divX w)) := by
        have h3 : P.eval 0 • u = aeval d P u - aeval d P.divX (d u) := eq_sub_of_add_eq h1.symm
        rw [← hu, ← map_smul, h3, map_sub, ha, zero_sub, map_neg]
      rw [h2]
      exact Submodule.mem_map_of_mem (M.neg_mem (aeval_mem d M hM _ w hw))
  · have h1 := decomp d P u
    rw [h0, LinearMap.zero_apply] at h1
    have h3 : P.eval 0 • u = -(aeval d P.divX (d u)) := eq_neg_of_add_eq_zero_left h1.symm
    rw [h3]
    exact M.neg_mem (aeval_mem d M hM _ _ hu)
end
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.IdealPowerSumMem
namespace Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem add_pow_mem_span_pow_pow (R : Type) [CommRing R] (π₀ ℓ : R) (A r : ℕ) :
    (π₀ + ℓ) ^ (A + r - 1) ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := by
  have hπ : π₀ ^ A ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := Ideal.subset_span (Set.mem_insert _ _)
  have hℓ : ℓ ^ r ∈ Ideal.span {π₀ ^ A, ℓ ^ r} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [add_pow]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ A + r - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hA : A ≤ i
  · have e : π₀ ^ i = π₀ ^ A * π₀ ^ (i - A) := by rw [← pow_add, Nat.add_sub_cancel' hA]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ))
  · have hr : r ≤ A + r - 1 - i := by omega
    have e : ℓ ^ (A + r - 1 - i) = ℓ ^ r * ℓ ^ (A + r - 1 - i - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hℓ))

end Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem Formalism.KernelCokernelLengths.ideal_power_sum_mem : Formalism.KernelCokernelLengths.QPow := by
  intro R _ π₀ ℓ A r
  exact Formalism.KernelCokernelLengths.IdealPowerSumLemmas.add_pow_mem_span_pow_pow R π₀ ℓ A r
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.FiltrationExponentHolds
theorem Formalism.KernelCokernelLengths.filtration_exponent_holds : Formalism.KernelCokernelLengths.FExp := by
  intro R _ u π₀ q ℓ hℓ Mi h hMi
  set m := h / (ℓ - 1) with hm
  have hpos : 0 < ℓ - 1 := by omega
  have hk : Mi + 1 ≤ (ℓ - 1) * (m + 1) := by
    have := Nat.lt_mul_div_succ h hpos
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hMi this)
  obtain ⟨d, hd⟩ : ∃ d, (ℓ - 1) * (m + 1) = Mi + 1 + d := ⟨_, (Nat.add_sub_cancel' hk).symm⟩
  rw [Ideal.mem_span_singleton]
  refine ⟨u ^ (m + 1) * q ^ d, ?_⟩
  rw [mul_pow, mul_pow, ← pow_mul, hd, pow_add]
  ring
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.DetLen
namespace Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module

theorem ord_prod {O : Type} [CommRing O] [IsDomain O] {ι : Type} (s : Finset ι) (a : ι → O)
    (ha : ∀ i, a i ≠ 0) :
    Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]

end Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module in
theorem Formalism.KernelCokernelLengths.determinant_length_formula : Formalism.KernelCokernelLengths.DetLen := by
  intro O _ _ _ M _ _ _ _ d hdet
  classical
  have hinj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  let e : M ≃ₗ[O] LinearMap.range d := LinearEquiv.ofInjective d hinj
  have h : finrank O (LinearMap.range d) = finrank O M := e.finrank_eq.symm
  let b := Free.chooseBasis O M
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : M) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h

  have hL : Module.length O (M ⧸ LinearMap.range d) = ∑ i, Ring.ord O (a i) := by
    rw [((LinearMap.range d).quotientEquivPiSpan b h).length_eq,
      Module.length_pi_of_fintype]
    rfl

  let u : M ≃ₗ[O] LinearMap.range d := b'.equiv ab (Equiv.refl _)
  let D : M →ₗ[O] M := (LinearMap.range d).subtype ∘ₗ u.toLinearMap
  have hD : LinearMap.det D = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' D = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      simp only [D, u, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Basis.equiv_apply, Equiv.refl_apply, Submodule.coe_subtype, hab, map_smul,
        Basis.repr_self, Finsupp.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
        Finsupp.single_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [this, Matrix.det_diagonal]
  have hd : d = D ∘ₗ (e.trans u.symm).toLinearMap := by
    ext x
    simp [D, e]
  have hdet' : LinearMap.det d = (∏ i, a i) * LinearMap.det (e.trans u.symm).toLinearMap := by
    rw [congrArg LinearMap.det hd, LinearMap.det_comp, hD]
  rw [hL]
  change _ = Ring.ord O (LinearMap.det d)
  rw [hdet', Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' _),
    Formalism.KernelCokernelLengths.DeterminantLengthLemmas.ord_prod _ _ ha]
end

section -- merged from Formalism.EisensteinCokernelLengths.FactorialValuationBounds.DistinguishedPowMemSpanOfTrichotomy
noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

section Key

variable {A : Type} [CommRing A]

theorem rel_mem_of_le {X l : A} {M η E : ℕ} (c a i : ℕ) (h : E ≤ c) :
    l ^ c * X ^ a * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  have e : l ^ (E + d) * X ^ a * (X + l) ^ i = (l ^ d * X ^ a * (X + l) ^ i) * l ^ E := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _))

theorem rel_mem_of_ge {X l : A} {M η E : ℕ} (c a i : ℕ) (ha : M ≤ a) (hi : η ≤ i) :
    l ^ c * X ^ a * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  obtain ⟨a', rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hi
  have e : l ^ c * X ^ (M + a') * (X + l) ^ (η + i') =
      (l ^ c * X ^ a' * (X + l) ^ i') * (X ^ M * (X + l) ^ η) := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

theorem rel_key_high (X l : A) (M η E : ℕ) :
    ∀ j c i : ℕ, (E ≤ c ∨ η ≤ i ∨ E + η ≤ c + j + i + 1) →
      l ^ c * X ^ (M + j) * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  intro j
  induction j with
  | zero =>
    intro c i h
    by_cases hc : E ≤ c
    · exact rel_mem_of_le c _ i hc
    by_cases hi : η ≤ i
    · exact rel_mem_of_ge c _ i (Nat.le_add_right M 0) hi
    exfalso
    omega
  | succ j ih =>
    intro c i h
    by_cases hc : E ≤ c
    · exact rel_mem_of_le c _ i hc
    by_cases hi : η ≤ i
    · exact rel_mem_of_ge c _ i (Nat.le_add_right M (j + 1)) hi
    have e : l ^ c * X ^ (M + (j + 1)) * (X + l) ^ i =
        l ^ c * X ^ (M + j) * (X + l) ^ (i + 1) - l ^ (c + 1) * X ^ (M + j) * (X + l) ^ i := by
      ring
    rw [e]
    exact Ideal.sub_mem _ (ih c (i + 1) (by omega)) (ih (c + 1) i (by omega))

theorem rel_key (X l : A) (M η E : ℕ) :
    ∀ i a c : ℕ, (E ≤ c ∨ (M ≤ a ∧ η ≤ i) ∨ E + η + M ≤ c + a + i + 1) →
      l ^ c * X ^ a * (X + l) ^ i ∈ Ideal.span {l ^ E, X ^ M * (X + l) ^ η} := by
  intro i
  induction i with
  | zero =>
    intro a c h
    by_cases ha : M ≤ a
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ha
      exact rel_key_high X l M η E j c 0 (by omega)
    · exact rel_mem_of_le c a 0 (by omega)
  | succ i ih =>
    intro a c h
    by_cases ha : M ≤ a
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le ha
      exact rel_key_high X l M η E j c (i + 1) (by omega)
    have e : l ^ c * X ^ a * (X + l) ^ (i + 1) =
        l ^ c * X ^ (a + 1) * (X + l) ^ i + l ^ (c + 1) * X ^ a * (X + l) ^ i := by ring
    rw [e]
    exact Ideal.add_mem _ (ih (a + 1) c (by omega)) (ih a (c + 1) (by omega))

end Key

theorem rel_ceil_le (m r K : ℕ) (hm : 1 ≤ m) (h : r * (m + 1) ≤ K * m) :
    ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ ≤ K := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  rw [Nat.ceil_le, div_le_iff₀ hm']
  exact_mod_cast h

theorem le_div_add_one_or_add_le (m r T L : ℕ) (hm : 1 ≤ m) (hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K) :
    L ≤ T / m + 1 ∨ L + T ≤ T / m + 1 + (m * r + r) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  by_cases h : L ≤ T / (n + 1) + 1
  · exact Or.inl h
  right
  have hT := Nat.div_add_mod T (n + 1)
  have ht := Nat.mod_lt T (show n + 1 > 0 by omega)
  set q := T / (n + 1) with hq0
  set t := T % (n + 1) with ht0
  have hq : (q + 1) * (n + 1) + 1 ≤ r * (n + 1 + 1) := by
    by_contra hc
    have := hL (q + 1) (by omega)
    omega
  have hK := Nat.div_add_mod (r * (n + 1 + 1) + n) (n + 1)
  have hKm := Nat.mod_lt (r * (n + 1 + 1) + n) (show n + 1 > 0 by omega)
  set K := (r * (n + 1 + 1) + n) / (n + 1) with hK0
  set ρ := (r * (n + 1 + 1) + n) % (n + 1) with hρ0
  have hLK : L ≤ K := hL K (by nlinarith)
  have a1 := Nat.mul_le_mul_left (n + 1) hLK
  have a2 := Nat.mul_le_mul_left (n + 1) (show t ≤ n by omega)
  have a3 := Nat.mul_le_mul_left n hq
  have a4 : (n + 1) * T = (n + 1) * ((n + 1) * q + t) := by rw [hT]
  apply le_of_mul_le_mul_left _ (show 0 < n + 1 by omega)
  nlinarith [a1, a2, a3, a4, hK]

theorem mul_succ_le_of_sq_mul_le (m r s b e : ℕ) (hm : 2 ≤ m) (hb : b < s * m ^ 2)
    (he : (m + 1) ^ 2 * r ≤ (m + 1) * e + b) : r * (m + 1) ≤ (s + e) * m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  apply le_of_mul_le_mul_left _ (show 0 < n + 2 + 1 by omega)
  nlinarith [Nat.zero_le (e * n * n), Nat.zero_le (e * n), Nat.zero_le (s * n), Nat.zero_le e,
    Nat.zero_le s]

theorem exponent_trichotomy (m r s b L k : ℕ) (hm : 2 ≤ m) (hb : b < s * m ^ 2)
    (hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K) (hL0 : r = 0 → L = 0) (hk : k ≤ m * r) :
    L ≤ s + k ∨ (1 ≤ r ∧ b ≤ m * r + (m + 1) * (m * r - k)) ∨
      L + b + 1 ≤ s + k + r + (m * r + (m + 1) * (m * r - k)) + 1 := by
  set D := m * r + (m + 1) * (m * r - k) with hD
  obtain ⟨j, hj⟩ : ∃ j, m * r = k + j := ⟨m * r - k, by omega⟩
  have hj' : m * r - k = j := by omega
  have h2 : m * (m * r) = m * (k + j) := by rw [hj]
  have key : (m + 1) ^ 2 * r = D + r + (m + 1) * k := by
    rw [hD, hj']
    nlinarith [hj, h2]
  by_cases hbig : r + D ≤ b
  · left
    exact hL _ (mul_succ_le_of_sq_mul_le m r s b k hm hb (by omega))
  · right; right
    set x := r + D - b with hx0
    have hx : x + b = r + D := by omega
    have hxm : x ≤ (m + 1) * x := by nlinarith [Nat.zero_le (m * x)]
    have he : (m + 1) ^ 2 * r ≤ (m + 1) * (k + x) + b := by nlinarith [hxm, key, hx]
    have := hL _ (mul_succ_le_of_sq_mul_le m r s b (k + x) hm hb he)
    omega

theorem linearFactorPowMemSpanXPow : FirstRelationModule := by
  intro A _ ℓ _ hℓ X u M η r hM
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have hcast : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  have hfl : ⌊((M : ℝ) + η) / (m : ℝ)⌋₊ = (M + η) / m := by
    have := Nat.floor_div_eq_div (K := ℝ) (M + η) m
    push_cast at this
    exact this
  rw [hcast, hfl]
  simp only [Nat.add_sub_cancel]
  set L := ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ with hLdef
  have hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K := fun K h => rel_ceil_le m r K (by omega) h
  have e : ((m + 1 : ℕ) : A) ^ ((M + η) / m + 1) * (u * X * (X + ((m + 1 : ℕ) : A)) ^ m) ^ r =
      u ^ r * (((m + 1 : ℕ) : A) ^ ((M + η) / m + 1) * X ^ r *
        (X + ((m + 1 : ℕ) : A)) ^ (m * r)) := by
    rw [pow_mul]; ring
  rw [e]
  apply Ideal.mul_mem_left
  apply rel_key X _ M η L (m * r) r ((M + η) / m + 1)
  have := le_div_add_one_or_add_le m r (M + η) L (by omega) hL
  omega

theorem linearFactorPowMemSpan : FirstRelationTorsion := by
  intro A _ ℓ _ hℓ X u B r
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hm : 2 ≤ m := by omega
  have hcast : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  have hfl : ⌊(B : ℝ) / (m : ℝ)⌋₊ = B / m := Nat.floor_div_eq_div B m
  rw [hcast, hfl]
  simp only [Nat.add_sub_cancel]
  set L := ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ with hLdef
  have hL : ∀ K, r * (m + 1) ≤ K * m → L ≤ K := fun K h => rel_ceil_le m r K (by omega) h
  have e : ((m + 1 : ℕ) : A) ^ (B / m + 1) * (u * X * (X + ((m + 1 : ℕ) : A)) ^ m) ^ r =
      u ^ r * (((m + 1 : ℕ) : A) ^ (B / m + 1) * X ^ r * (X + ((m + 1 : ℕ) : A)) ^ (m * r)) := by
    rw [pow_mul]; ring
  rw [e]
  apply Ideal.mul_mem_left
  have key := rel_key X ((m + 1 : ℕ) : A) 1 B L (m * r) r (B / m + 1) (by
    have := le_div_add_one_or_add_le m r B L (by omega) hL
    omega)
  rwa [pow_one] at key

theorem distinguished_pow_mem_span_of_trichotomy {R : Type} [CommRing R] (Q l ε u' w : R) (ℓ b r σ L : ℕ)
    (hterm : ∀ k ≤ (ℓ - 1) * r, L ≤ σ + k ∨
      (1 ≤ r ∧ b ≤ (ℓ - 1) * r + ℓ * ((ℓ - 1) * r - k)) ∨
        L + b + 1 ≤ σ + k + r + ((ℓ - 1) * r + ℓ * ((ℓ - 1) * r - k)) + 1) :
    l ^ σ * (w * (Q - l) * Q ^ (ℓ - 1) * (l * ε + u' * Q ^ ℓ) ^ (ℓ - 1)) ^ r ∈
      Ideal.span {l ^ L, (Q - l) * Q ^ b} := by
  obtain ⟨n, hn⟩ : ∃ n, n = (ℓ - 1) * r := ⟨_, rfl⟩
  rw [← hn] at hterm
  have h1 : ∀ P : R, l ^ σ * (w * (Q - l) * Q ^ (ℓ - 1) * P ^ (ℓ - 1)) ^ r =
      w ^ r * (l ^ σ * (Q - l) ^ r * Q ^ n * P ^ n) := by
    intro P
    rw [hn, pow_mul, pow_mul, mul_pow, mul_pow, mul_pow]
    ring
  rw [h1, add_pow, Finset.mul_sum, Finset.mul_sum]
  apply Ideal.sum_mem
  intro k hk
  have hk' : k ≤ n := by simp at hk; omega
  have e : l ^ σ * (Q - l) ^ r * Q ^ n * ((l * ε) ^ k * (u' * Q ^ ℓ) ^ (n - k) * (n.choose k : R)) =
      (ε ^ k * u' ^ (n - k) * (n.choose k : R)) *
        (l ^ (σ + k) * (Q - l) ^ r * Q ^ (n + ℓ * (n - k))) := by
    rw [mul_pow, mul_pow, ← pow_mul, pow_add, pow_add]
    ring
  rw [e]
  have key := rel_key (Q - l) l 1 b L (n + ℓ * (n - k)) r (σ + k) (by
    have := hterm k hk'
    omega)
  rw [sub_add_cancel, pow_one] at key
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ key)

theorem distinguishedPowMemSpan : SecondRelationTorsion := by
  unfold SecondRelationTorsion
  intro O _ ℓ _ hℓ ε u' w b r
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  have hden : ((m + 1 : ℕ) : ℝ) - 1 = (m : ℝ) := by push_cast; ring
  have hfl : ⌊(b : ℝ) / (m : ℝ) ^ 2⌋₊ = b / m ^ 2 := by
    rw [← Nat.cast_pow]
    exact Nat.floor_div_eq_div _ _
  rw [hden, hfl]
  have hL : ∀ K, r * (m + 1) ≤ K * m → ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ ≤ K :=
    fun K hK => rel_ceil_le m r K (by omega) hK
  have hL0 : r = 0 → ⌈(r : ℝ) * ((m + 1 : ℕ) : ℝ) / (m : ℝ)⌉₊ = 0 := by
    rintro rfl
    simp
  have hb : b < (b / m ^ 2 + 1) * m ^ 2 := by
    have h1 := Nat.div_add_mod b (m ^ 2)
    have h2 := Nat.mod_lt b (pow_pos (by omega : 0 < m) 2)
    nlinarith [h1, h2]
  simp only [map_pow, Formalism.WindowSums.p1]
  apply distinguished_pow_mem_span_of_trichotomy
  intro k hk
  simp only [Nat.add_sub_cancel] at hk ⊢
  exact exponent_trichotomy m r (b / m ^ 2 + 1) b _ k (by omega) hb hL hL0 hk

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria
end
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.KerCokerEq
section -- merged from Formalism.JumpKernelCokernel.KerCokerEq
namespace Formalism.KernelCokernelLengths

def KerCokerEq : Prop :=
  ∀ (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M], Module.length O M ≠ ⊤ →
    ∀ f : Module.End O M, Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f)

def CokerSurj : Prop :=
  ∀ (O : Type) [CommRing O] (M M' : Type) [AddCommGroup M] [Module O M] [AddCommGroup M']
    [Module O M'] (f : Module.End O M) (f' : Module.End O M') (g : M →ₗ[O] M'),
    Function.Surjective g → g ∘ₗ f = f' ∘ₗ g →
      Module.length O (M' ⧸ LinearMap.range f') ≤ Module.length O (M ⧸ LinearMap.range f)

end Formalism.KernelCokernelLengths
end

namespace Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas

theorem main (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) :
    Module.length O (LinearMap.ker f) = Module.length O (M ⧸ LinearMap.range f) := by
  have h1 : Module.length O M =
      Module.length O (LinearMap.ker f) + Module.length O (M ⧸ LinearMap.ker f) :=
    Module.length_eq_add_of_exact _ _ (LinearMap.ker f).injective_subtype
      (LinearMap.ker f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  have h2 : Module.length O (M ⧸ LinearMap.ker f) = Module.length O (LinearMap.range f) :=
    (f.quotKerEquivRange).length_eq
  have h3 : Module.length O M =
      Module.length O (LinearMap.range f) + Module.length O (M ⧸ LinearMap.range f) :=
    Module.length_eq_add_of_exact _ _ (LinearMap.range f).injective_subtype
      (LinearMap.range f).mkQ_surjective (LinearMap.exact_subtype_mkQ _)
  rw [h2] at h1
  have hk : Module.length O (LinearMap.ker f) ≠ ⊤ := by
    intro h; apply hM; rw [h1, h]; exact top_add _
  have hr : Module.length O (LinearMap.range f) ≠ ⊤ := by
    intro h; apply hM; rw [h1, h]; exact add_top _
  have hc : Module.length O (M ⧸ LinearMap.range f) ≠ ⊤ := by
    intro h; apply hM; rw [h3, h]; exact add_top _
  lift Module.length O M to ℕ using hM with m hm
  lift Module.length O (LinearMap.ker f) to ℕ using hk with a ha
  lift Module.length O (LinearMap.range f) to ℕ using hr with b hb
  lift Module.length O (M ⧸ LinearMap.range f) to ℕ using hc with c hc'
  norm_cast at h1 h3 ⊢
  omega

theorem coker (O : Type) [CommRing O] (M M' : Type) [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (f : Module.End O M) (f' : Module.End O M')
    (g : M →ₗ[O] M') (hg : Function.Surjective g) (hc : g ∘ₗ f = f' ∘ₗ g) :
    Module.length O (M' ⧸ LinearMap.range f') ≤ Module.length O (M ⧸ LinearMap.range f) := by
  have hle : LinearMap.range f ≤ (LinearMap.range f').comap g := by
    rintro _ ⟨m, rfl⟩
    exact ⟨g m, (LinearMap.congr_fun hc m).symm⟩
  have hs : Function.Surjective (Submodule.mapQ (LinearMap.range f) (LinearMap.range f') g hle) := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨m, rfl⟩ := hg y
      exact ⟨Submodule.Quotient.mk m, rfl⟩
  exact Module.length_le_of_surjective _ hs

end Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas

theorem Formalism.KernelCokernelLengths.endKernelCokernelLengthEq : Formalism.KernelCokernelLengths.KerCokerEq :=
  fun O _ M _ _ hM f => Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas.main O M hM f

theorem Formalism.KernelCokernelLengths.cokernelLengthLeOfSurjective : Formalism.KernelCokernelLengths.CokerSurj :=
  fun O _ M M' _ _ _ _ f f' g hg hc => Formalism.KernelCokernelLengths.KernelCokernelEqualityLemmas.coker O M M' f f' g hg hc
end

section -- restored from Formalism.JumpKernelCokernel.JumpShiftProofs.CokerTors
open Polynomial Module

namespace Formalism.KernelCokernelLengths.CokernelTorsionLemmas

theorem charpoly_of_range_le {R : Type} [CommRing R] [IsDomain R] {M : Type} [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M]
    (S : Submodule R M) [Module.Free R S] [Module.Finite R S] [Module.Free R (M ⧸ S)]
    [Module.Finite R (M ⧸ S)] (d : Module.End R M) (hd : ∀ m, d m ∈ S) :
    d.charpoly = (d.restrict (p := S) (q := S) (fun x _ => hd x)).charpoly *
      X ^ finrank R (M ⧸ S) := by
  classical
  obtain ⟨g, hg⟩ := Module.projective_lifting_property S.mkQ LinearMap.id
    (Submodule.mkQ_surjective S)
  have hg' : ∀ x, S.mkQ (g x) = x := fun x => LinearMap.congr_fun hg x
  let pr : M →ₗ[R] M := LinearMap.id - g ∘ₗ S.mkQ
  have hmem : ∀ m, pr m ∈ S := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero]
    simp only [pr, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [Submodule.Quotient.mk_sub]
    have := hg' (S.mkQ m)
    simp only [Submodule.mkQ_apply] at this ⊢
    rw [this, sub_self]
  let F : M →ₗ[R] S × (M ⧸ S) :=
    LinearMap.prod (pr.codRestrict S hmem) S.mkQ
  let G : S × (M ⧸ S) →ₗ[R] M := S.subtype.coprod g
  have h1 : F ∘ₗ G = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨s, c⟩
    have hs : S.mkQ (s : M) = 0 := by simp
    have hs' : (Submodule.Quotient.mk (s : M) : M ⧸ S) = 0 := hs
    have hg'' : (Submodule.Quotient.mk (g c) : M ⧸ S) = c := hg' c
    apply Prod.ext
    · apply Subtype.ext
      simp [F, G, pr, hg', hs]
    · simp [F, G, pr, hs', hg'']
  have h2 : G ∘ₗ F = LinearMap.id := by
    apply LinearMap.ext
    intro m
    simp [F, G, pr]
  let e : M ≃ₗ[R] S × (M ⧸ S) := LinearEquiv.ofLinearMap (f := F) (g := G) h1 h2
  let dS := d.restrict (p := S) (q := S) (fun x _ => hd x)
  let bS := Module.Free.chooseBasis R S
  let bQ := Module.Free.chooseBasis R (M ⧸ S)
  let b := bS.prod bQ
  have hconj : ∀ x, e.conj d x = (⟨d (G x), hd _⟩, 0) := by
    intro x
    rw [LinearEquiv.conj_apply]
    have hq : S.mkQ (d (G x)) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hd _
    apply Prod.ext
    · apply Subtype.ext
      simp [e, F, pr, hq]
    · simp [e, F, pr, hq]
  have hM : LinearMap.toMatrix b b (e.conj d) =
      Matrix.fromBlocks (LinearMap.toMatrix bS bS dS) (LinearMap.toMatrix b b (e.conj d)).toBlocks₁₂
        0 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks (LinearMap.toMatrix b b (e.conj d))]
    congr 1
    · ext i j
      simp only [Matrix.toBlocks₁₁, Matrix.of_apply, LinearMap.toMatrix_apply, b,
        Module.Basis.prod_apply, Sum.elim_inl, hconj, Module.Basis.prod_repr_inl]
      congr 2
      apply Subtype.ext
      simp [G, dS]
    · ext i j
      simp [Matrix.toBlocks₂₁, LinearMap.toMatrix_apply, b, hconj]
    · ext i j
      simp [Matrix.toBlocks₂₂, LinearMap.toMatrix_apply, b, hconj]
  rw [← e.charpoly_conj d, ← LinearMap.charpoly_toMatrix (e.conj d) b, hM,
    Matrix.charpoly_fromBlocks_zero₂₁, LinearMap.charpoly_toMatrix, Matrix.charpoly_zero,
    Module.finrank_eq_card_chooseBasisIndex]

end Formalism.KernelCokernelLengths.CokernelTorsionLemmas

namespace Formalism.KernelCokernelLengths.CokernelTorsionLemmas

theorem eq_of_mul_X_pow {R : Type} [CommRing R] [IsDomain R] (P Q : R[X]) (k r : ℕ)
    (hP : P.coeff 0 ≠ 0) (hQ : Q.coeff 0 ≠ 0) (h : P * X ^ r = X ^ k * Q) : P = Q := by
  have hP0 : P ≠ 0 := fun h0 => hP (by simp [h0])
  have hQ0 : Q ≠ 0 := fun h0 => hQ (by simp [h0])
  have tP : P.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hP)
  have tQ : Q.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hQ)
  have hrk : r = k := by
    have h1 := congrArg Polynomial.natTrailingDegree h
    rw [mul_comm (X ^ k) Q, Polynomial.natTrailingDegree_mul_X_pow hP0,
      Polynomial.natTrailingDegree_mul_X_pow hQ0, tP, tQ] at h1
    omega
  subst hrk
  rw [mul_comm (X ^ r) Q] at h
  exact mul_right_cancel₀ (pow_ne_zero _ Polynomial.X_ne_zero) h

end Formalism.KernelCokernelLengths.CokernelTorsionLemmas

theorem Formalism.KernelCokernelLengths.cokernel_torsion_holds : Formalism.KernelCokernelLengths.CokerTors := by
  intro O _ _ _ M _ _ _ _ d k Q hQ0 hchar hann
  classical
  have hQc : Q.coeff 0 ≠ 0 := by rwa [Polynomial.coeff_zero_eq_eval_zero]

  have hdQ : ∀ m, d (aeval d Q m) = 0 := by
    intro m
    have := LinearMap.congr_fun hann m
    simpa [map_mul, aeval_X] using this
  have hQd : ∀ m, aeval d Q (d m) = 0 := by
    intro m
    have h0 : aeval d (Q * X) = 0 := by rw [mul_comm]; exact hann
    have := LinearMap.congr_fun h0 m
    simpa [map_mul, aeval_X] using this

  have hsplit : ∀ m, aeval d Q m = Q.coeff 0 • m + d (aeval d Q.divX m) := by
    intro m
    conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
    rw [map_add (f := _), map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, add_comm]
  have hcommR : ∀ m, d (aeval d Q.divX m) = aeval d Q.divX (d m) := by
    intro m
    have h0 : aeval d (X * Q.divX) = aeval d (Q.divX * X) := by rw [mul_comm]
    have := LinearMap.congr_fun h0 m
    simpa [map_mul, aeval_X] using this
  let S : Submodule O M := LinearMap.ker (aeval d Q)
  have hdS : ∀ m, d m ∈ S := fun m => hQd m

  have htf : Module.IsTorsionFree O (M ⧸ S) := by
    refine Module.IsTorsionFree.of_smul_eq_zero (fun a x hx => ?_)
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
      by_cases ha : a = 0
      · exact Or.inl ha
      · right
        rw [Submodule.Quotient.mk_eq_zero]
        have : a • aeval d Q m = 0 := by
          rw [← map_smul]; exact hx
        exact (smul_eq_zero.mp this).resolve_left ha
  have : Module.Free O (M ⧸ S) := Module.free_of_finite_type_torsion_free'
  let dS := d.restrict (p := S) (q := S) (fun x _ => hdS x)
  have hc := Formalism.KernelCokernelLengths.CokernelTorsionLemmas.charpoly_of_range_le S d hdS

  have hker : LinearMap.ker dS = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro s hs
    have hs1 : d (s : M) = 0 := by
      have := congrArg Subtype.val hs
      simpa [dS] using this
    have hs2 : aeval d Q (s : M) = 0 := s.2
    rw [hsplit, hcommR, hs1, map_zero (aeval d Q.divX), add_zero] at hs2
    exact Subtype.ext ((smul_eq_zero.mp hs2).resolve_left hQc)
  have hdet : LinearMap.det dS ≠ 0 := fun h => (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) hker
  have hPc : dS.charpoly.coeff 0 ≠ 0 := by
    intro h; apply hdet; rw [LinearMap.det_eq_sign_charpoly_coeff, h, mul_zero]
  have hPQ : dS.charpoly = Q :=
    Formalism.KernelCokernelLengths.CokernelTorsionLemmas.eq_of_mul_X_pow _ _ k _ hPc hQc (hc.symm.trans hchar)
  have hspan : Ideal.span {LinearMap.det dS} = Ideal.span {Q.eval 0} := by
    rw [LinearMap.det_eq_sign_charpoly_coeff, hPQ, Polynomial.coeff_zero_eq_eval_zero]
    exact Ideal.span_singleton_mul_left_unit ((isUnit_neg_one).pow _) _
  have hlen := Formalism.KernelCokernelLengths.determinant_length_formula O S dS hdet
  rw [hspan] at hlen
  rw [← hlen]

  have hmemT : ∀ s : S, (LinearMap.range d).mkQ (s : M) ∈
      Submodule.torsion O (M ⧸ LinearMap.range d) := by
    intro s
    rw [Submodule.mem_torsion_iff]
    refine ⟨⟨Q.coeff 0, mem_nonZeroDivisors_of_ne_zero hQc⟩, ?_⟩
    show Q.coeff 0 • (Submodule.Quotient.mk (s : M) : M ⧸ LinearMap.range d) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have hs2 : aeval d Q (s : M) = 0 := s.2
    rw [hsplit] at hs2
    rw [eq_neg_of_add_eq_zero_left hs2]
    exact Submodule.neg_mem _ (LinearMap.mem_range_self d _)
  let φ : S →ₗ[O] Submodule.torsion O (M ⧸ LinearMap.range d) :=
    ((LinearMap.range d).mkQ ∘ₗ S.subtype).codRestrict _ hmemT
  have hφ : LinearMap.range dS ≤ LinearMap.ker φ := by
    rintro _ ⟨s, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show (LinearMap.range d).mkQ (d (s : M)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range_self d _
  refine Module.length_le_of_surjective ((LinearMap.range dS).liftQ φ hφ) ?_
  rintro ⟨x, hx⟩
  induction x using Submodule.Quotient.induction_on with
  | H m =>
    rw [Submodule.mem_torsion_iff] at hx
    obtain ⟨a, ha⟩ := hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at ha
    obtain ⟨m', hm'⟩ := ha
    have h1 : (a : O) • aeval d Q m = 0 := by
      rw [← map_smul]
      show aeval d Q ((a : O) • m) = 0
      rw [show (a : O) • m = d m' from hm'.symm]; exact hQd m'
    have hmS : m ∈ S := (smul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero a)
    refine ⟨Submodule.Quotient.mk ⟨m, hmS⟩, ?_⟩
    rw [Submodule.liftQ_apply]
    rfl
end

namespace Formalism.KernelCokernelLengths

theorem length_theorems_all_hold : Formalism.KernelCokernelLengths.DetLen ∧ Formalism.KernelCokernelLengths.RelZero ∧ Formalism.KernelCokernelLengths.CDge ∧ Formalism.KernelCokernelLengths.RowD ∧ Formalism.KernelCokernelLengths.ExpRowD ∧ Formalism.KernelCokernelLengths.InvConst ∧ Formalism.KernelCokernelLengths.KerCoker ∧ Formalism.KernelCokernelLengths.JumpShift ∧ Formalism.KernelCokernelLengths.PowBinom ∧ Formalism.KernelCokernelLengths.HCoefLim ∧ Formalism.KernelCokernelLengths.QPow ∧ Formalism.KernelCokernelLengths.ColThmC ∧ Formalism.KernelCokernelLengths.FExp ∧ Formalism.KernelCokernelLengths.ThickB ∧ Formalism.KernelCokernelLengths.KerCokerEq ∧ Formalism.KernelCokernelLengths.CokerSurj ∧ Formalism.KernelCokernelLengths.ThickA ∧ Formalism.KernelCokernelLengths.PdFacts ∧ Formalism.KernelCokernelLengths.LenSplit ∧ Formalism.KernelCokernelLengths.TorsKerSum ∧ Formalism.KernelCokernelLengths.TorsKer ∧ Formalism.KernelCokernelLengths.RowDJoint ∧ Formalism.KernelCokernelLengths.LemmaDJoint ∧ Formalism.KernelCokernelLengths.CokerTors := by
  exact ⟨determinant_length_formula, relation_vanishes, column_degree_bound, row_degree_bound, row_degree_exponent, exists_fixed_add_of_sub_mem, kernel_cokernel_lengths, jump_shift_holds, power_binomial_bound, coefficient_height_limit, ideal_power_sum_mem, column_theorem_C, filtration_exponent_holds, thickness_second_bound, endKernelCokernelLengthEq, cokernelLengthLeOfSurjective, thickness_first_bound, polynomial_degree_facts, length_splits_additively, torsion_kernel_sum_length, torsion_kernel_length, row_degree_joint_form, lemma_D_joint_form, cokernel_torsion_holds⟩

theorem length_theorems_with_earlier :
    (Formalism.KernelCokernelLengths.DetLen ∧ Formalism.KernelCokernelLengths.RelZero ∧ Formalism.KernelCokernelLengths.CDge ∧ Formalism.KernelCokernelLengths.RowD ∧ Formalism.KernelCokernelLengths.ExpRowD ∧ Formalism.KernelCokernelLengths.InvConst ∧ Formalism.KernelCokernelLengths.KerCoker ∧ Formalism.KernelCokernelLengths.JumpShift ∧ Formalism.KernelCokernelLengths.PowBinom ∧ Formalism.KernelCokernelLengths.HCoefLim ∧ Formalism.KernelCokernelLengths.QPow ∧ Formalism.KernelCokernelLengths.ColThmC ∧ Formalism.KernelCokernelLengths.FExp ∧ Formalism.KernelCokernelLengths.ThickB ∧ Formalism.KernelCokernelLengths.KerCokerEq ∧ Formalism.KernelCokernelLengths.CokerSurj ∧ Formalism.KernelCokernelLengths.ThickA ∧ Formalism.KernelCokernelLengths.PdFacts ∧ Formalism.KernelCokernelLengths.LenSplit ∧ Formalism.KernelCokernelLengths.TorsKerSum ∧ Formalism.KernelCokernelLengths.TorsKer ∧ Formalism.KernelCokernelLengths.RowDJoint ∧ Formalism.KernelCokernelLengths.LemmaDJoint ∧ Formalism.KernelCokernelLengths.CokerTors) ∧
    (Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.HCoef ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ExpBound ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.MaxZeroExponentInequality ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.TwoIntervalValuationSumBound ∧
      Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.LemmaGVal ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.LemmaGIdeal ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.RamifiedValuationInequality ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.LenPi0 ∧
      Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ColChain ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.SubGen ∧ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ColAssembly) ∧
    (Formalism.TruncatedSeriesCounting.R9.LengthQuotientLeOfPowSMul ∧ Formalism.TruncatedSeriesCounting.R9.CancelQ ∧ Formalism.TruncatedSeriesCounting.R9.CancelC ∧ Formalism.TruncatedSeriesCounting.R9.TruncZero) ∧
    (Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.FirstRelationTorsion ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.FirstRelationModule ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.SecondRelationTorsion ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.GapG ∧
      Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.RRVal ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.ExponentChainBound ∧ Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.NumC) := by
  exact ⟨length_theorems_all_hold, ⟨Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.h_coefficient_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.expBound_statement, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.second_exponent_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.first_sigma_valuation_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.g_coeff_valuation_statement, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.g_ideal_valuation_statement, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.ramified_valuation_inequality, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.length_pi_zero_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.column_chain_bound, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.submodule_generator_count, Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.column_assembly_bound⟩, ⟨Formalism.TruncatedSeriesCounting.R9.length_quotient_le_of_pow_smul, Formalism.TruncatedSeriesCounting.R9.mem_span_of_X_pow_mul, Formalism.TruncatedSeriesCounting.R9.mem_span_of_C_pow_mul, Formalism.TruncatedSeriesCounting.R9.pow_mem_span_pow_mul⟩, ⟨Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.linearFactorPowMemSpan, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.linearFactorPowMemSpanXPow, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.distinguishedPowMemSpan, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.gapG_proof, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.rRVal_proof, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.exponentChainBound, Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria.rationalTailBoundCubic⟩⟩

end Formalism.KernelCokernelLengths
