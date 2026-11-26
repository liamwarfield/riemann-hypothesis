module

public import Formalism.JumpKernelCokernel.Statement

@[expose] public section

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.RowDegreeBound
namespace Formalism.KernelCokernelLengths

theorem row_degree_bound : RowD := by
  unfold RowD
  intro h h1 η hη
  have key : 32 * (h1 + η) ≤ 50 * h1 := by omega
  gcongr ?_ / _
  exact_mod_cast key

end Formalism.KernelCokernelLengths
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.InvConst
namespace Formalism.KernelCokernelLengths

theorem fil_eq_of_noJump {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (Fil : ℤ → Submodule K D) (b η : ℕ)
    (hj : ∀ j : ℤ, -(b : ℤ) < j → j < -(η : ℤ) → Fil j = Fil (j + 1)) :
    ∀ k : ℕ, ∀ j : ℤ, -(b : ℤ) < j → j + k = -(η : ℤ) → Fil j = Fil (-(η : ℤ)) := by
  intro k
  induction k with
  | zero =>
    intro j _ hjk
    simp only [Nat.cast_zero, add_zero] at hjk
    rw [hjk]
  | succ k ih =>
    intro j hjb hjk
    have hlt : j < -(η : ℤ) := by push_cast at hjk; omega
    rw [hj j hjb hlt]
    exact ih (j + 1) (by omega) (by push_cast at hjk ⊢; omega)

theorem exists_fixed_add_of_sub_mem : InvConst := by
  intro K _ D _ _ Fil hA χ hχ b η w hj hw
  have h1 : ∀ i : ℤ, i ≠ 0 → w i ∈ Fil (-i) := by
    intro i hi
    have hne : χ ^ i - 1 ≠ 0 := sub_ne_zero.mpr (hχ i hi)
    have h2 := (Fil (-i)).smul_mem (χ ^ i - 1)⁻¹ (hw i)
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  refine ⟨h1, fun i hi hib => ?_⟩
  by_cases hη : (η : ℤ) ≤ i
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, -i + k = -(η : ℤ) := ⟨(i - η).toNat, by omega⟩
    rw [← fil_eq_of_noJump Fil b η hj k (-i) (by omega) hk]
    exact h1 i hi
  · exact hA (by omega : -(η : ℤ) ≤ -i) (h1 i hi)

end Formalism.KernelCokernelLengths
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.KerCoker
namespace Formalism.KernelCokernelLengths.KernelCokernelLemmas

theorem main (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) (N : Submodule O M) (hN : N.map f ≤ N) :
    Module.length O (↥N ⧸ (N.map f).comap N.subtype) ≤ Module.length O (LinearMap.ker f) := by
  have hNf : ∀ x ∈ N, f x ∈ N := fun x hx => hN (Submodule.mem_map_of_mem hx)
  let g : N →ₗ[O] ↥((N.map f).comap N.subtype) :=
    LinearMap.codRestrict ((N.map f).comap N.subtype) (f.restrict hNf)
      (fun x => Submodule.mem_comap.2 (Submodule.mem_map_of_mem x.2))
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_comap.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxy)⟩
  have hNfin : Module.length O N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective N.subtype N.injective_subtype)
  have hQfin : Module.length O ((N.map f).comap N.subtype) ≠ ⊤ :=
    ne_top_of_le_ne_top hNfin (Module.length_le_of_injective _ (Submodule.injective_subtype _))
  have e1 := Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype ((N.map f).comap N.subtype))
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ ((N.map f).comap N.subtype))
  have e2 := Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype (LinearMap.ker g)) hgs
    (LinearMap.exact_subtype_ker_map g)
  have e3 : Module.length O (↥N ⧸ (N.map f).comap N.subtype) = Module.length O (LinearMap.ker g) := by
    rw [e1, add_comm] at e2
    exact WithTop.add_right_cancel hQfin e2
  rw [e3]
  refine Module.length_le_of_injective
    (LinearMap.codRestrict (LinearMap.ker f) (N.subtype.comp (LinearMap.ker g).subtype) ?_) ?_
  · intro x
    exact LinearMap.mem_ker.2
      (congrArg (fun z : ↥((N.map f).comap N.subtype) => ((z : N) : M)) (LinearMap.mem_ker.1 x.2))
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    exact h

end Formalism.KernelCokernelLengths.KernelCokernelLemmas

theorem Formalism.KernelCokernelLengths.kernel_cokernel_lengths : Formalism.KernelCokernelLengths.KerCoker := by
  intro O _ M _ _ hM f N hN
  exact Formalism.KernelCokernelLengths.KernelCokernelLemmas.main O M hM f N hN
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.LenSplit
namespace Formalism.KernelCokernelLengths.LengthSplittingLemmas

theorem main (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R]
    (π : Module.End O R) (R' R'' : Submodule O R) (h : R' ≤ R'') :
    Module.length O (R ⧸ (R' ⊔ LinearMap.range π)) ≤
      Module.length O (R ⧸ (R'' ⊔ LinearMap.range π)) +
        Module.length O (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) := by
  set A := R' ⊔ LinearMap.range π with hA
  set B := R'' ⊔ LinearMap.range π with hB
  have hAB : A ≤ B := sup_le_sup_right h _
  let f : (B ⧸ A.comap B.subtype) →ₗ[O] (R ⧸ A) := Submodule.mapQ (A.comap B.subtype) A B.subtype le_rfl
  let g : (R ⧸ A) →ₗ[O] (R ⧸ B) := Submodule.mapQ A B LinearMap.id (by simpa using hAB)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.subtype_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hx
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk r, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact ⟨Submodule.Quotient.mk ⟨r, hy⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      simp only [f, g, Submodule.mapQ_apply, Submodule.subtype_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero]
      exact b.2
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  have hRB : R'' ≤ B := le_sup_left
  let k : (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) →ₗ[O] (B ⧸ A.comap B.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hRB) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact sup_le_sup_left (LinearMap.map_le_range) R' hx)
  have hk : Function.Surjective k := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨r, hr, p, hp, rfl⟩ := Submodule.mem_sup.mp hb
    refine ⟨Submodule.Quotient.mk ⟨r, hr⟩, ?_⟩
    simp only [k, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
    have : r - (r + p) = -p := by abel
    rw [this]
    exact A.neg_mem (Submodule.mem_sup_right hp)
  have hle := Module.length_le_of_surjective k hk
  rw [hlen, add_comm]
  gcongr

end Formalism.KernelCokernelLengths.LengthSplittingLemmas

theorem Formalism.KernelCokernelLengths.length_splits_additively : Formalism.KernelCokernelLengths.LenSplit := by
  intro O _ R _ _ π R' R'' h
  exact Formalism.KernelCokernelLengths.LengthSplittingLemmas.main O R π R' R'' h
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.ThickB
namespace Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

lemma coef_le (ℓ : ℕ) (hℓ : 11 ≤ ℓ) :
    (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ 21 / 100 := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hpos : 0 < ((ℓ : ℝ) - 1) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hpos (by norm_num)]
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : (0 : ℝ) ≤ 21 * ℓ - 11)]

lemma log_two_le (x : ℝ) (hx : 0 < x) : Real.log x ≤ x / 100 + 98 := by
  have h1 := Real.log_le_sub_one_of_pos (show 0 < x / 100 by positivity)
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 100 by norm_num)
  have h3 : Real.log x = Real.log (x / 100) + Real.log 100 := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    congr 1
    field_simp
  linarith

lemma one_le_log (ℓ : ℕ) (hℓ : 11 ≤ ℓ) : 1 ≤ Real.log (ℓ : ℝ) := by
  have h : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma logb_le (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (x : ℝ) (hx : 1 ≤ x) :
    Real.logb (ℓ : ℝ) x ≤ Real.log x := by
  exact div_le_self (Real.log_nonneg hx) (one_le_log ℓ hℓ)

lemma logb_nonneg' (ℓ : ℕ) (hℓ : 11 ≤ ℓ) (x : ℝ) (hx : 1 ≤ x) :
    0 ≤ Real.logb (ℓ : ℝ) x := by
  have h : (1 : ℝ) < ℓ := by
    have : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    linarith
  exact Real.logb_nonneg h hx

end Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas

open Formalism.KernelCokernelLengths.ThicknessSecondBoundLogLemmas in
theorem Formalism.KernelCokernelLengths.thickness_second_bound : Formalism.KernelCokernelLengths.ThickB := by
  refine ⟨1 / 100, by norm_num, 10000, ?_⟩
  intro ℓ hℓ b η S t bi h hb hη hS ht h1 h2 h3
  have hbR : (10000 : ℝ) ≤ b := by exact_mod_cast hb
  have hη' : 100 * η ≤ b := by
    have : ((100 * η : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  have hS' : 100 * S ≤ b := by
    have : ((100 * S : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  have ht' : 100 * t ≤ b := by
    have : ((100 * t : ℕ) : ℝ) ≤ b := by push_cast; linarith
    exact_mod_cast this
  refine ⟨by omega, by omega, ?_⟩
  have hHn : h + (η + t + 1) ≤ b + 2 * η + 2 * t + S + 2 := by omega
  have hH1 : 1 ≤ h + (η + t + 1) := by omega
  have hHR : ((h + (η + t + 1) : ℕ) : ℝ) ≤ b + 2 * η + 2 * t + S + 2 := by exact_mod_cast hHn
  have hH1R : (1 : ℝ) ≤ ((h + (η + t + 1) : ℕ) : ℝ) := by exact_mod_cast hH1
  have hbi : b ≤ bi + t + 1 := h1
  have hbiR : (b : ℝ) ≤ bi + t + 1 := by exact_mod_cast hbi
  set H : ℕ := h + (η + t + 1) with hHdef
  have hx1 : (1 : ℝ) ≤ 2 * (H : ℝ) := by linarith
  have hlb := logb_le ℓ hℓ (2 * (H : ℝ)) hx1
  have hlb0 := logb_nonneg' ℓ hℓ (2 * (H : ℝ)) hx1
  have hlog := log_two_le (2 * (H : ℝ)) (by linarith)
  have hc := coef_le ℓ hℓ
  have hcoef0 : 0 ≤ (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    have hl : (11 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
    apply div_nonneg <;> nlinarith
  have hH0 : (0 : ℝ) ≤ H := by positivity
  have hA : (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 ≤ (H : ℝ) * (21 / 100) := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hc hH0
  have hA0 : 0 ≤ (H : ℝ) * (2 * (ℓ : ℝ) - 1) / ((ℓ : ℝ) - 1) ^ 2 := by
    rw [mul_div_assoc]; positivity
  have haR0 : 0 ≤ Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    linarith
  have haR : Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H ≤ (H : ℝ) * (21 / 100) + 4 + ((2 * (H : ℝ)) / 100 + 98) := by
    unfold Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.lam
    linarith
  have hceil := Nat.ceil_lt_add_one haR0
  have hηR : (100 : ℝ) * η ≤ b := by exact_mod_cast hη'
  have hSR : (100 : ℝ) * S ≤ b := by exact_mod_cast hS'
  have htR : (100 : ℝ) * t ≤ b := by exact_mod_cast ht'
  have key : ((2 * ⌈Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.aR ℓ H⌉₊ + (η + t + 1) + 1 : ℕ) : ℝ) ≤ (bi : ℝ) := by
    push_cast
    nlinarith
  exact_mod_cast key
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.PowBinom
namespace Formalism.KernelCokernelLengths

theorem power_binomial_bound : PowBinom := by
  intro A _ ℓ u ε q b Y hℓ hY
  set k := (Y - 1) / ℓ with hk
  set I : Ideal A := Ideal.span {(ℓ : A), q ^ ℓ} with hI
  have hYle : Y ≤ ℓ * (k + 1) := by
    have h := Nat.lt_mul_div_succ (Y - 1) (show 0 < ℓ by omega)
    rw [← hk] at h
    omega
  have hmem : (u * q ^ ℓ + (ℓ : A) * ε) ^ b ∈
      Ideal.span {(ℓ : A) ^ (b - k)} ⊔ Ideal.span {q ^ Y} * I ^ (b - k - 1) := by
    rw [add_pow]
    refine Ideal.sum_mem _ (fun m hm => ?_)
    rw [Finset.mem_range] at hm
    by_cases hmk : m ≤ k
    · apply Ideal.mem_sup_left
      rw [Ideal.mem_span_singleton]
      have h1 : (ℓ : A) ^ (b - k) ∣ ((ℓ : A) * ε) ^ (b - m) := by
        rw [mul_pow]; exact Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left h1 _) _
    · apply Ideal.mem_sup_right
      obtain ⟨e, rfl⟩ : ∃ e, m = k + 1 + e := ⟨m - (k + 1), by omega⟩
      have hℓI : (ℓ : A) ∈ I := Ideal.subset_span (by simp)
      have hqI : q ^ ℓ ∈ I := Ideal.subset_span (by simp)
      have hin : (q ^ ℓ) ^ e * (ℓ : A) ^ (b - (k + 1 + e)) ∈ I ^ (b - k - 1) := by
        have := Ideal.mul_mem_mul (Ideal.pow_mem_pow hqI e)
          (Ideal.pow_mem_pow hℓI (b - (k + 1 + e)))
        rw [← pow_add] at this
        exact Ideal.pow_le_pow_right (by omega) this
      have hp : q ^ (ℓ * (k + 1)) = q ^ Y * q ^ (ℓ * (k + 1) - Y) := by
        rw [← pow_add]; congr 1; omega
      have heq : (u * q ^ ℓ) ^ (k + 1 + e) * ((ℓ : A) * ε) ^ (b - (k + 1 + e)) *
            (b.choose (k + 1 + e) : A) =
          q ^ Y * ((q ^ ℓ) ^ e * (ℓ : A) ^ (b - (k + 1 + e)) *
            (u ^ (k + 1 + e) * q ^ (ℓ * (k + 1) - Y) * ε ^ (b - (k + 1 + e)) *
              (b.choose (k + 1 + e) : A))) := by
        have hq : (q ^ ℓ) ^ (k + 1 + e) = q ^ Y * q ^ (ℓ * (k + 1) - Y) * (q ^ ℓ) ^ e := by
          rw [pow_add, ← pow_mul, hp]
        rw [mul_pow, mul_pow, hq]
        ring
      rw [heq]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ hin)
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨α, rfl⟩ := Ideal.mem_span_singleton'.mp ha
  obtain ⟨β, hβ, rfl⟩ := Ideal.mem_span_singleton_mul.mp hc
  exact ⟨α, β, by rw [← hac]; ring, hβ⟩

end Formalism.KernelCokernelLengths
end

section -- merged from Formalism.JumpKernelCokernel.JumpShiftProofs.TorsKerSum
noncomputable section

namespace Formalism.KernelCokernelLengths.TorsionKernelSumLemmas

open PowerSeries

variable {O : Type} [CommRing O]

theorem len_pow [IsDomain O] (ℓ : O) (hℓ : ℓ ≠ 0) (k : ℕ) :
    Module.length O (O ⧸ Ideal.span {ℓ ^ k}) = (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  induction k with
  | zero =>
    have hs : Subsingleton (O ⧸ Ideal.span {ℓ ^ 0}) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.span_singleton_one])
    rw [Module.length_eq_zero, Nat.cast_zero, zero_mul]
  | succ k ih =>

    have hle : Ideal.span {ℓ} ≤ Submodule.comap (LinearMap.mulLeft O (ℓ ^ k)) (Ideal.span {ℓ ^ (k + 1)}) := by
      intro x hx
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      exact Ideal.mem_span_singleton.mpr ⟨y, by ring⟩
    have hge : Ideal.span {ℓ ^ (k + 1)} ≤ Ideal.span {ℓ ^ k} :=
      Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow ℓ k.le_succ)
    have hk : ℓ ^ k ≠ 0 := pow_ne_zero k hℓ
    have hf : Function.Injective (Submodule.mapQ _ _ (LinearMap.mulLeft O (ℓ ^ k)) hle) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker, Submodule.mapQ_apply, LinearMap.mulLeft_apply,
        Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at hx
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
      obtain ⟨c, hc⟩ := hx
      refine ⟨c, mul_left_cancel₀ hk ?_⟩
      rw [hc]
      ring
    have hg : Function.Surjective (Submodule.factor hge) := by
      intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk a, rfl⟩
    have hex : Function.Exact (Submodule.mapQ _ _ (LinearMap.mulLeft O (ℓ ^ k)) hle) (Submodule.factor hge) := by
      intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      constructor
      · intro h
        have h' : a ∈ Ideal.span {ℓ ^ k} := by
          rw [← Submodule.Quotient.mk_eq_zero]
          exact h
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp h'
        exact ⟨Submodule.Quotient.mk c, by rw [Submodule.mapQ_apply, LinearMap.mulLeft_apply, hc]⟩
      · rintro ⟨x, hx⟩
        obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
        rw [← hx, Submodule.mapQ_apply, LinearMap.mulLeft_apply]
        show (Submodule.Quotient.mk (ℓ ^ k * c) : O ⧸ Ideal.span {ℓ ^ k}) = 0
        rw [Submodule.Quotient.mk_eq_zero]
        exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
    rw [Module.length_eq_add_of_exact _ _ hf hg hex, ih]
    push_cast
    ring

abbrev J (ℓ : O) (n k : ℕ) : Ideal (PowerSeries O) :=
  Ideal.span {(X : PowerSeries O) ^ n, C (ℓ ^ k)}

theorem coeff_dvd_of_mem (ℓ : O) (n k : ℕ) {r : PowerSeries O} (hr : r ∈ J ℓ n k) :
    ∀ i < n, ℓ ^ k ∣ coeff i r := by
  intro i hi
  obtain ⟨a, c, rfl⟩ := Ideal.mem_span_pair.mp hr
  rw [map_add (f := _), coeff_mul_X_pow', if_neg (by omega), zero_add, coeff_mul_C]
  exact dvd_mul_left _ _

theorem mem_of_coeff_dvd (ℓ : O) (n k : ℕ) (p : PowerSeries O)
    (hp : ∀ i < n, ℓ ^ k ∣ coeff i p) : p ∈ J ℓ n k := by
  have hp' : ∀ i < n, ∃ c, coeff i p = ℓ ^ k * c := fun i hi => hp i hi
  choose! c hc using hp'
  refine Ideal.mem_span_pair.mpr
    ⟨PowerSeries.mk fun j => coeff (j + n) p, PowerSeries.mk fun i => if i < n then c i else 0, ?_⟩
  ext i
  rw [map_add (f := _), coeff_mul_X_pow', coeff_mul_C, coeff_mk, coeff_mk]
  split_ifs with h1 h2 h2
  · omega
  · rw [Nat.sub_add_cancel h1]
    ring
  · rw [hc i h2]
    ring
  · omega

theorem coeff_step (ℓ : O) (p : PowerSeries O) (i : ℕ) :
    coeff i p = coeff (i + 1) ((X - C ℓ) * p) + ℓ * coeff (i + 1) p := by
  rw [sub_mul, map_sub, coeff_succ_X_mul, coeff_C_mul]
  ring

theorem all_coeff_dvd (ℓ : O) (n k : ℕ) (p : PowerSeries O) (hp : (X - C ℓ) * p ∈ J ℓ n k)
    (htop : ℓ ^ k ∣ coeff (n - 1) p) : ∀ i < n, ℓ ^ k ∣ coeff i p := by

  have key : ∀ j i, i + j = n - 1 → i < n → ℓ ^ k ∣ coeff i p := by
    intro j
    induction j with
    | zero =>
      intro i hij _
      rw [show i = n - 1 by omega]
      exact htop
    | succ j ih =>
      intro i hij hi
      rw [Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_step ℓ p i]
      exact dvd_add (Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_dvd_of_mem ℓ n k hp (i + 1) (by omega))
        (dvd_mul_of_dvd_right (ih (i + 1) (by omega) (by omega)) _)
  intro i hi
  exact key (n - 1 - i) i (by omega) hi

def lift (ℓ : O) (n k : ℕ) : (PowerSeries O ⧸ J ℓ n k) → PowerSeries O :=
  Function.surjInv Ideal.Quotient.mk_surjective

theorem mk_lift (ℓ : O) (n k : ℕ) (b : PowerSeries O ⧸ J ℓ n k) :
    Ideal.Quotient.mk (J ℓ n k) (lift ℓ n k b) = b := Function.surjInv_eq Ideal.Quotient.mk_surjective b

def topFun (ℓ : O) (n k : ℕ) (b : PowerSeries O ⧸ J ℓ n k) : O ⧸ Ideal.span {ℓ ^ k} :=
  Ideal.Quotient.mk _ (coeff (n - 1) (lift ℓ n k b))

theorem topFun_mk (ℓ : O) (n k : ℕ) (hn : 0 < n) (p : PowerSeries O) :
    topFun ℓ n k (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (coeff (n - 1) p) := by
  unfold Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.topFun
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  have h := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.mk_lift ℓ n k (Ideal.Quotient.mk _ p)
  rw [Ideal.Quotient.eq] at h
  have h2 := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.coeff_dvd_of_mem ℓ n k h (n - 1) (by omega)
  rwa [map_sub] at h2

def topMap (ℓ : O) (n k : ℕ) (hn : 0 < n) :
    (PowerSeries O ⧸ J ℓ n k) →ₗ[O] O ⧸ Ideal.span {ℓ ^ k} where
  toFun := topFun ℓ n k
  map_add' a b := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_add (f := _), topFun_mk ℓ n k hn, topFun_mk ℓ n k hn, topFun_mk ℓ n k hn, map_add (f := _), map_add (f := _)]
  map_smul' c a := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
      topFun_mk ℓ n k hn, topFun_mk ℓ n k hn, PowerSeries.algebraMap_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, coeff_C_mul]
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]

theorem single (ℓ : O) (n k : ℕ) [IsDomain O] (hℓ : ℓ ≠ 0) :
    Module.length O (LinearMap.ker (LinearMap.mulLeft O
      (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))) ≤
      (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : (X : PowerSeries O) ^ 0 ∈ J ℓ 0 k := Ideal.subset_span (Set.mem_insert _ _)
    rw [pow_zero] at h1
    have hs : Subsingleton (PowerSeries O ⧸ J ℓ 0 k) :=
      Ideal.Quotient.subsingleton_iff.mpr ((Ideal.eq_top_iff_one _).mpr h1)
    rw [Module.length_eq_zero]
    exact zero_le
  ·
    have hinj : Function.Injective ((topMap ℓ n k hn).comp (LinearMap.ker (LinearMap.mulLeft O
        (Ideal.Quotient.mk (J ℓ n k) ((X : PowerSeries O) - C ℓ)))).subtype) := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      rintro ⟨b, hb⟩ hT
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hb' := hb
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hb'
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply] at hT
      have hT' : topFun ℓ n k (Ideal.Quotient.mk _ p) = 0 := hT
      rw [Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.topFun_mk ℓ n k hn, Ideal.Quotient.eq_zero_iff_mem,
        Ideal.mem_span_singleton] at hT'
      have hpJ := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.mem_of_coeff_dvd ℓ n k p
        (Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.all_coeff_dvd ℓ n k p hb' hT')
      apply Subtype.ext
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hpJ
    calc _ ≤ Module.length O (O ⧸ Ideal.span {ℓ ^ k}) := Module.length_le_of_injective _ hinj
      _ = _ := Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.len_pow ℓ hℓ k

theorem ker_pi_le {ι : Type} [Fintype ι] {R : Type} [CommRing R] (M : ι → Type)
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (f : ∀ i, M i →ₗ[R] M i) :
    Module.length R (LinearMap.ker (LinearMap.pi fun i => (f i).comp (LinearMap.proj (R := R)
      (φ := M) i))) ≤ ∑ i, Module.length R (LinearMap.ker (f i)) := by
  let Φ : LinearMap.ker (LinearMap.pi fun i => (f i).comp (LinearMap.proj (R := R) (φ := M) i)) →ₗ[R]
      (∀ i, LinearMap.ker (f i)) :=
    LinearMap.pi fun i => LinearMap.codRestrict (LinearMap.ker (f i))
      ((LinearMap.proj (R := R) (φ := M) i).comp (Submodule.subtype _)) (fun x => by
        have hx := x.2
        rw [LinearMap.mem_ker] at hx ⊢
        have h2 := congrFun hx i
        simpa using h2)
  have hΦ : Function.Injective Φ := by
    intro x y hxy
    apply Subtype.ext
    funext i
    have h2 := congrArg (fun z => (z i : M i)) hxy
    simpa [Φ] using h2
  calc _ ≤ Module.length R (∀ i, LinearMap.ker (f i)) := Module.length_le_of_injective Φ hΦ
    _ = _ := Module.length_pi_of_fintype R _

end Formalism.KernelCokernelLengths.TorsionKernelSumLemmas

open Formalism.KernelCokernelLengths.TorsionKernelSumLemmas in
theorem Formalism.KernelCokernelLengths.torsion_kernel_sum_length : Formalism.KernelCokernelLengths.TorsKerSum := by
  unfold Formalism.KernelCokernelLengths.TorsKerSum
  intro O _ _ _ ℓ hℓ m k n
  calc _ ≤ ∑ j : Fin m, Module.length O (LinearMap.ker (LinearMap.mulLeft O
        (Ideal.Quotient.mk (J ℓ (n j) k) ((PowerSeries.X : PowerSeries O) - PowerSeries.C ℓ)))) :=
        Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.ker_pi_le _ _
    _ ≤ ∑ _j : Fin m, (k : ℕ∞) * Module.length O (O ⧸ Ideal.span {ℓ}) :=
        Finset.sum_le_sum fun j _ => Formalism.KernelCokernelLengths.TorsionKernelSumLemmas.single ℓ (n j) k hℓ
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring
end
end
