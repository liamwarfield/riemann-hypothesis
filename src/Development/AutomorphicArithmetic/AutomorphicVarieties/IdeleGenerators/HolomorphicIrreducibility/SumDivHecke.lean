module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.UnitForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EigLift

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisChi
open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

private theorem eisChi_gauss_ne {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {ψ : AddChar (ZMod N) ℂ} (hχ : χ.IsPrimitive)
    (hψ : ψ.IsPrimitive) : gaussSum χ ψ ≠ 0 := by
  have h1 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹
      = ∑ b : ZMod N, ∑ a : ZMod N, χ a * ψ (b * (a - 1)) := by
    conv_lhs => rw [gaussSum.eq_1 χ⁻¹, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, mul_comm (gaussSum χ ψ), ← gaussSum_mulShift_of_isPrimitive ψ hχ b,
      gaussSum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [AddChar.mulShift_apply, AddChar.inv_apply, mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have h2 : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = (N : ℂ) := by
    rw [h1, Finset.sum_comm]
    simp_rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ, sub_eq_zero]
    rw [Finset.sum_eq_single (1 : ZMod N)]
    · simp
    · intro a _ ha
      simp [ha]
    · simp
  intro h0
  rw [h0, zero_mul] at h2
  exact (Nat.cast_ne_zero.2 (NeZero.ne N)) h2.symm

private theorem eisChi_coe_sum {N : ℕ} {k : ℤ} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → ModularForm (Gamma1 N) k) :
    ((∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) = ∑ a ∈ s, c a • (F a : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]; rfl

private theorem eisChi_coef_sum {N : ℕ} [NeZero N] {k : ℤ} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → ModularForm (Gamma1 N) k) (n : ℕ) :
    coef ((∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) n = ∑ a ∈ s, c a * coef (F a) n := by
  classical
  have hp : (1 : ℝ) ∈ (Gamma1 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp
  induction s using Finset.induction_on with
  | empty => simp [coef, qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    unfold coef
    have h1 := ModularForm.qExpansion_add one_pos hp (c a • F a) (∑ a ∈ s, c a • F a)
    have h2 := ModularForm.qExpansion_smul one_pos hp (c a) (F a)
    have h3 : ((c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) = c a • (F a : ℍ → ℂ) := rfl
    rw [h3, h2] at h1
    have h4 : ((c a • F a + ∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) =
      c a • (F a : ℍ → ℂ) + ((∑ a ∈ s, c a • F a : ModularForm (Gamma1 N) k) : ℍ → ℂ) := rfl
    rw [h4, h1]
    simp

private theorem eisChi_slash_sum {k : ℤ} {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (F : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ a ∈ s, c a • F a) ∣[k] γ = ∑ a ∈ s, c a • (F a ∣[k] γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih, SlashAction.add_slash, ModularForm.SL_smul_slash]

private theorem eisChi_gs {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (e : ZMod N) :
    ∑ a : ZMod N, χ⁻¹ a * (ZMod.stdAddChar (a * e) : ℂ) = χ e * gaussSum χ⁻¹ ZMod.stdAddChar := by
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := N)) hi e
  rw [inv_inv] at this
  rw [← this, gaussSum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [AddChar.mulShift_apply, mul_comm e a]

theorem UpperTheory.V.Sd.eisChi :
    UpperTheory.V.Sd.EisChi := by
  intro N k _ hN hk χ hχ hpar
  choose F hF using UpperTheory.V.Sd.eisMF N k hk
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have hg : gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)) ≠ 0 :=
    eisChi_gauss_ne hi (ZMod.isPrimitive_stdAddChar N)
  set g := gaussSum χ⁻¹ (ZMod.stdAddChar (N := N)) with hgdef
  haveI : Fact (1 < N) := ⟨hN⟩
  have h0 : χ⁻¹ (0 : ZMod N) = 0 := MulChar.map_nonunit _ not_isUnit_zero
  refine ⟨∑ a : ZMod N, ((2 * g)⁻¹ * χ⁻¹ a) • F a, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    rw [eisChi_coe_sum, eisChi_slash_sum, Finset.smul_sum]
    simp only [hF, UpperTheory.V.Sd.eisSlash N k hk _ γ hγ]
    have hd : IsUnit (((γ 1 1 : ℤ)) : ZMod N) := by
      have h1 := γ.det_coe
      rw [Matrix.det_fin_two] at h1
      have h2 : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 hγ
      have h3 := congrArg (Int.cast : ℤ → ZMod N) h1
      push_cast at h3
      rw [h2, mul_zero, sub_zero] at h3
      exact IsUnit.of_mul_eq_one_right _ h3
    obtain ⟨u, hu⟩ := hd
    rw [← hu]
    refine Fintype.sum_equiv (Units.mulRight u) _ _ fun a => ?_
    rw [smul_smul]
    congr 1
    have : χ (u : ZMod N) * χ⁻¹ (u : ZMod N) = 1 := by
      rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply_coe]
    simp only [Units.mulRight_apply, map_mul]
    linear_combination (-((2 * g)⁻¹ * χ⁻¹ a)) * this
  · intro γ hγ
    rw [eisChi_coe_sum, eisChi_slash_sum]
    refine Submodule.sum_mem (zeroAtImInftySubmodule ℂ) fun a _ => ?_
    by_cases ha : IsUnit a
    · refine Submodule.smul_mem _ _ ?_
      rw [hF]
      exact UpperTheory.V.Sd.eisVan N k hk a ha hN γ hγ
    · rw [MulChar.map_nonunit _ ha, mul_zero, zero_smul]
      exact Submodule.zero_mem _
  · intro n hn
    rw [eisChi_coef_sum]
    have h1 : ∀ a : ZMod N, (2 * g)⁻¹ * χ⁻¹ a * coef (F a) n = ∑ e ∈ n.divisors, (2 * g)⁻¹ * (e : ℂ) ^ (k - 1) *
        (χ⁻¹ a * (ZMod.stdAddChar (a * (e : ZMod N)) : ℂ) +
          (-1) ^ k * (χ⁻¹ a * (ZMod.stdAddChar (a * (-(e : ZMod N))) : ℂ))) := by
      intro a
      by_cases ha : a = 0
      · simp [ha, h0]
      · rw [hF, (UpperTheory.V.Sd.eisCoef N k hk a ha).2 n hn, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [mul_neg]; ring
    simp only [h1]
    rw [Finset.sum_comm, sigChi]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, eisChi_gs hχ, eisChi_gs hχ, ← hgdef,
      ← neg_one_mul (e : ZMod N), map_mul, hpar]
    have h2 : ((-1 : ℂ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
    have h3 : (2 * g)⁻¹ * (2 * g) = 1 := inv_mul_cancel₀ (mul_ne_zero two_ne_zero hg)
    linear_combination ((2 * g)⁻¹ * (e : ℂ) ^ (k - 1) * χ (e : ZMod N) * g) * h2 + ((e : ℂ) ^ (k - 1) * χ (e : ZMod N)) * h3
  · rw [eisChi_coef_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : a = 0
    · simp [ha, h0]
    · rw [hF, (UpperTheory.V.Sd.eisCoef N k hk a ha).1]
      have h3 : (2 * g)⁻¹ * (2 * g) = 1 := inv_mul_cancel₀ (mul_ne_zero two_ne_zero hg)
      linear_combination (χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ)) * h3
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.ConstSmall
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.LkDist
noncomputable section

open Polynomial

namespace UpperTheory.V.Sd

private lemma lk_deriv (k : ℕ) (x : ℂ) (hx : x ≠ 1) :
    ∃ d : ℂ, HasDerivAt (fun y : ℂ => Lk (k + 1) y) d x ∧ x * d = Lk (k + 2) x := by
  have hne : (1 - x) ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hp := Polynomial.hasDerivAt_aeval (numL (k + 1)) x
  have hq : HasDerivAt (fun y : ℂ => (1 - y) ^ (k + 1)) (((k + 1 : ℕ) : ℂ) * (1 - x) ^ k * (-1)) x := by
    have h1 : HasDerivAt (fun y : ℂ => 1 - y) (-1) x := by
      simpa using (hasDerivAt_id x).const_sub (1 : ℂ)
    have h2 := h1.pow (k + 1)
    simp only [Nat.add_sub_cancel] at h2
    exact h2
  refine ⟨_, hp.div hq (pow_ne_zero _ hne), ?_⟩
  have e : numL (k + 2) = X * (derivative (numL (k + 1)) * (1 - X) + C ((k : ℤ) + 1) * numL (k + 1)) := numL.eq_3 k
  unfold Lk
  rw [e]
  simp only [map_mul, map_add (f := _), map_sub, map_one, aeval_X, aeval_C]
  field_simp
  push_cast
  ring

private lemma lk_one (w : ℕ) (hw : 1 ≤ w) (ζ x : ℂ) (hζ : IsPrimitiveRoot ζ w) (hx : x ^ w ≠ 1) :
    ∑ j ∈ Finset.range w, Lk 1 (x * ζ ^ j) = (w : ℂ) ^ 1 * Lk 1 (x ^ w) := by
  have hy : ∀ j : ℕ, (x * ζ ^ j) ^ w = x ^ w := by
    intro j
    rw [mul_pow, ← pow_mul, mul_comm j w, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  have hxw : 1 - x ^ w ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hne : ∀ j : ℕ, 1 - x * ζ ^ j ≠ 0 := by
    intro j h
    apply hx
    rw [← hy j, ← sub_eq_zero.mp h, one_pow]
  have term : ∀ j : ℕ, Lk 1 (x * ζ ^ j) = (∑ m ∈ Finset.range w, (x * ζ ^ j) ^ m) / (1 - x ^ w) - 1 := by
    intro j
    have g := geom_sum_mul (x * ζ ^ j) w
    rw [hy j] at g
    unfold Lk
    simp only [numL.eq_2, aeval_X, pow_one]
    rw [eq_sub_iff_add_eq, div_add_one (hne j), div_eq_div_iff (hne j) hxw]
    linear_combination g
  have inner : ∀ m ∈ Finset.range w, ∑ j ∈ Finset.range w, (x * ζ ^ j) ^ m = if m = 0 then (w : ℂ) else 0 := by
    intro m hm
    split_ifs with h0
    · simp [h0]
    · have hm' : m < w := Finset.mem_range.mp hm
      have hq : ζ ^ m ≠ 1 := hζ.pow_ne_one_of_pos_of_lt h0 hm'
      have g := geom_sum_mul (ζ ^ m) w
      rw [← pow_mul, mul_comm m w, pow_mul, hζ.pow_eq_one, one_pow, sub_self] at g
      have hs : ∑ i ∈ Finset.range w, (ζ ^ m) ^ i = 0 := by
        rcases mul_eq_zero.mp g with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h) hq
      calc ∑ j ∈ Finset.range w, (x * ζ ^ j) ^ m = x ^ m * ∑ i ∈ Finset.range w, (ζ ^ m) ^ i := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j m]
        _ = 0 := by rw [hs, mul_zero]
  have total : ∑ j ∈ Finset.range w, ∑ m ∈ Finset.range w, (x * ζ ^ j) ^ m = w := by
    rw [Finset.sum_comm, Finset.sum_congr rfl inner, Finset.sum_ite_eq' (Finset.range w) 0]
    simp [Finset.mem_range.mpr (by omega : 0 < w)]
  rw [Finset.sum_congr rfl (fun j _ => term j), Finset.sum_sub_distrib, ← Finset.sum_div, total]
  unfold Lk
  simp only [numL.eq_2, aeval_X, pow_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  field_simp
  ring

theorem lkDist : LkDist := by
  intro w k hw hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro ζ x hζ hx
    exact lk_one w hw ζ x hζ hx
  | succ k hk ih =>
    intro ζ x hζ hx
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hy : ∀ j : ℕ, (x * ζ ^ j) ^ w = x ^ w := by
      intro j
      rw [mul_pow, ← pow_mul, mul_comm j w, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
    have hne : ∀ j : ℕ, x * ζ ^ j ≠ 1 := by
      intro j h
      apply hx
      rw [← hy j, h, one_pow]
    choose d hd hdx using fun j : ℕ => lk_deriv m (x * ζ ^ j) (hne j)
    obtain ⟨e, he, hex⟩ := lk_deriv m (x ^ w) hx
    have hj : ∀ j : ℕ, HasDerivAt (fun y : ℂ => Lk (m + 1) (y * ζ ^ j)) (d j * ζ ^ j) x := by
      intro j
      exact (hd j).comp x (hasDerivAt_mul_const (ζ ^ j))
    have hF : HasDerivAt (fun y : ℂ => ∑ j ∈ Finset.range w, Lk (m + 1) (y * ζ ^ j))
        (∑ j ∈ Finset.range w, d j * ζ ^ j) x :=
      HasDerivAt.fun_sum (u := Finset.range w) (A := fun j (y : ℂ) => Lk (m + 1) (y * ζ ^ j))
        (A' := fun j => d j * ζ ^ j) (fun j _ => hj j)
    have hG : HasDerivAt (fun y : ℂ => (w : ℂ) ^ (m + 1) * Lk (m + 1) (y ^ w))
        ((w : ℂ) ^ (m + 1) * (e * ((w : ℂ) * x ^ (w - 1)))) x :=
      (he.comp x (hasDerivAt_pow w x)).const_mul _
    have hev : (fun y : ℂ => ∑ j ∈ Finset.range w, Lk (m + 1) (y * ζ ^ j)) =ᶠ[nhds x]
        (fun y : ℂ => (w : ℂ) ^ (m + 1) * Lk (m + 1) (y ^ w)) := by
      have ho : IsOpen {y : ℂ | y ^ w ≠ 1} := isOpen_ne_fun (continuous_pow w) continuous_const
      filter_upwards [ho.mem_nhds hx] with y hy'
      exact ih ζ y hζ hy'
    have heq := hF.unique (hG.congr_of_eventuallyEq hev)
    have hw' : x * x ^ (w - 1) = x ^ w := by
      rw [← pow_succ']
      congr 1
      omega
    calc ∑ j ∈ Finset.range w, Lk (m + 1 + 1) (x * ζ ^ j)
        = x * ∑ j ∈ Finset.range w, d j * ζ ^ j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [← hdx j]
          ring
      _ = (w : ℂ) ^ (m + 1 + 1) * Lk (m + 1 + 1) (x ^ w) := by
          rw [heq, ← hex, ← hw']
          ring

end UpperTheory.V.Sd
end
end

open Formalism.ConjugateSelfDual Finset UpperTheory.V.Sd

private theorem gauss_mul_gauss_inv {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) :
    gaussSum χ ZMod.stdAddChar * gaussSum χ⁻¹ ZMod.stdAddChar * χ (-1) = N := by
  have hi : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have h1 : ZMod.dft (χ : ZMod N → ℂ) = fun k => χ⁻¹ (-k) * gaussSum χ ZMod.stdAddChar :=
    funext fun k => hχ.fourierTransform_eq_inv_mul_gaussSum k
  have h2 := congrFun (ZMod.dft_dft (χ : ZMod N → ℂ)) (-1)
  rw [h1, ZMod.dft_mul_const (fun k => χ⁻¹ (-k)), ZMod.dft_comp_neg (fun k => χ⁻¹ k)] at h2
  simp only [neg_neg, map_one, smul_eq_mul, mul_one] at h2
  have h3 := hi.fourierTransform_eq_inv_mul_gaussSum 1
  rw [inv_inv] at h3
  have h4 : ZMod.dft (fun k => χ⁻¹ k) 1 = χ (-1) * gaussSum χ⁻¹ ZMod.stdAddChar := h3
  rw [h4] at h2
  rw [← h2]; ring

section
variable {l : ℕ} [hl : Fact l.Prime]

private theorem root_le {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : ‖x‖ = 1 := by
  have : ‖x‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

private theorem nat_lt {n : ℕ} (h : l ∣ n) : ‖(n : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  have : ‖((n : ℤ) : ℚ_[l])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 h)
  simpa using this

private theorem nat_eq {n : ℕ} (h : ¬ l ∣ n) : ‖(n : Qbar l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 h

private theorem nadd_le {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x + y‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

private theorem add_lt {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

private theorem mul_le {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

private theorem mul_lt {x y : Qbar l} (hx : ‖x‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy

private theorem sum_le {I : Type} (s : Finset I) (f : I → Qbar l) (h : ∀ i ∈ s, ‖f i‖ ≤ 1) : ‖∑ i ∈ s, f i‖ ≤ 1 :=
  Finset.sum_induction f (fun x => ‖x‖ ≤ 1) (fun _ _ => nadd_le) (by simp) h

private theorem sum_lt {I : Type} (s : Finset I) (f : I → Qbar l) (h : ∀ i ∈ s, ‖f i‖ < 1) : ‖∑ i ∈ s, f i‖ < 1 :=
  Finset.sum_induction f (fun x => ‖x‖ < 1) (fun _ _ => add_lt) (by simp) h

private def intO (l : ℕ) [Fact l.Prime] : Subring (Qbar l) where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := mul_le
  one_mem' := by simp
  add_mem' := nadd_le
  zero_mem' := by simp
  neg_mem' := by simp

private theorem root_sub_one {x : Qbar l} (h : x ^ l = 1) : ‖x - 1‖ < 1 := by
  have h1 : ‖x - 1‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact nadd_le (root_le hl.out.ne_zero h).le (by simp)
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hl.out (⟨x - 1, h1⟩ : intO l) 1
  have h2 := congrArg (fun z : intO l => (z : Qbar l)) hr
  simp only [Subring.coe_add, SubmonoidClass.coe_pow, Subring.coe_mul, Subring.coe_one, sub_add_cancel, h, one_pow,
    Subring.coe_natCast, mul_one] at h2
  have h3 : (x - 1) ^ l = -((l : Qbar l) * (x - 1) * r) := by linear_combination -h2
  have h4 : ‖x - 1‖ ^ l < 1 := by
    rw [← norm_pow, h3, norm_neg]
    exact mul_lt (mul_lt (nat_lt dvd_rfl) h1) r.2
  exact lt_of_pow_lt_pow_left₀ l zero_le_one (by rwa [one_pow])

private theorem char_le (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    ‖ι.symm (χ a)‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    refine (root_le (n := Fintype.card (ZMod N)ˣ) Fintype.card_ne_zero ?_).le
    rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one]; simp
  · rw [χ.map_nonunit ha]; simp

private theorem add_pow_N {N : ℕ} [NeZero N] (a : ZMod N) : (ZMod.stdAddChar a : ℂ) ^ N = 1 := by
  rw [← AddChar.map_nsmul_eq_pow]; simp

private theorem gauss_le (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    ‖ι.symm (gaussSum χ ZMod.stdAddChar)‖ ≤ 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [gaussSum, map_sum]
  refine sum_le _ _ fun a _ => ?_
  rw [map_mul]
  refine mul_le (char_le ι χ a) (root_le (NeZero.ne N) ?_).le
  rw [← map_pow, add_pow_N, map_one]

private theorem gauss_eq (ι : Qbar l ≃+* ℂ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hN : ¬ l ∣ N) : ‖ι.symm (gaussSum χ⁻¹ ZMod.stdAddChar)‖ = 1 := by
  have h := congrArg (fun z => ‖ι.symm z‖) (gauss_mul_gauss_inv χ hχ)
  simp only [map_mul, map_natCast, nat_eq hN] at h
  refine le_antisymm (gauss_le ι _) (not_lt.1 fun hlt => ?_)
  rw [mul_comm (ι.symm (gaussSum χ _))] at h
  exact (mul_lt (mul_lt hlt (gauss_le ι _)) (char_le ι χ _)).ne h

private theorem map_Lk (ι : Qbar l ≃+* ℂ) (k : ℕ) (x : ℂ) : ι.symm (Lk k x) = Lk k (ι.symm x) := by
  unfold Lk
  rw [map_div₀, map_pow, map_sub, map_one]
  congr 1
  exact (Polynomial.aeval_algHom_apply (ι.symm.toRingHom.toIntAlgHom) x (numL k)).symm

private theorem Lk_le (h2 : l ≠ 2) (ι : Qbar l ≃+* ℂ) {N : ℕ} (hN0 : 0 < N) (hN : ¬ l ∣ N) {k : ℕ} (hk : 1 ≤ k) {x : ℂ}
    (hx : x ^ N = 1) : ‖ι.symm (Lk k x)‖ ≤ 1 := by
  by_cases h1 : x = 1
  · subst h1
    simp [Lk, zero_pow (Nat.one_le_iff_ne_zero.1 hk)]
  · rw [map_Lk]
    refine (lkSep l h2 N hN0 hN).1 k _ (by rw [← map_pow, hx, map_one]) fun h => h1 ?_
    exact ι.symm.injective (by rw [h, map_one])

end

private theorem sum_zmod {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : ∑ a : ZMod N, f a = ∑ n ∈ range N, f n := by
  symm
  refine Finset.sum_bij' (fun n _ => (n : ZMod N)) (fun a _ => a.val) (by simp) (fun a _ => by simp [ZMod.val_lt])
    (fun n hn => ZMod.val_cast_of_lt (mem_range.1 hn)) (fun a _ => ZMod.natCast_zmod_val a) (fun _ _ => rfl)

private theorem sum_mul_range (M w : ℕ) (f : ℕ → ℂ) :
    ∑ n ∈ range (M * w), f n = ∑ j ∈ range w, ∑ b ∈ range M, f (b + M * j) := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    simp only [add_comm (M * w)]

private theorem sum_multiples (M w : ℕ) (hw : 0 < w) (f : ℕ → ℂ) :
    ∑ n ∈ range (M * w), (if w ∣ n then f n else 0) = ∑ j ∈ range M, f (w * j) := by
  rw [mul_comm, sum_mul_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    rw [if_neg]
    intro h
    exact hb0 (Nat.eq_zero_of_dvd_of_lt ((Nat.dvd_add_left (dvd_mul_right w j)).1 h) (mem_range.1 hb))
  · intro h; exact absurd (mem_range.2 hw) h

private theorem sum_all {M w k : ℕ} (hM : 1 < M) (hw : 0 < w) (hk : 1 ≤ k) (ψ : DirichletCharacter ℂ M) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ (M * w)) :
    ∑ n ∈ range (M * w), ψ n * Lk k (ζ ^ n) = (w : ℂ) ^ k * ∑ b ∈ range M, ψ b * Lk k (ζ ^ (w * b)) := by
  rw [sum_mul_range, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  have h1 : IsPrimitiveRoot (ζ ^ M) w := hζ.pow (by positivity) rfl
  have h2 : ∀ j, ψ ((b + M * j : ℕ) : ZMod M) = ψ b := fun j => by simp
  simp only [h2]
  by_cases hb0 : b = 0
  · subst hb0
    haveI : Fact (1 < M) := ⟨hM⟩
    simp [ψ.map_zero]
  have h3 : (ζ ^ b) ^ w ≠ 1 := by
    rw [← pow_mul, Ne, hζ.pow_eq_one_iff_dvd]
    intro h
    exact hb0 (Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mul_dvd_mul_right hw h) (mem_range.1 hb))
  have h4 := lkDist w k hw hk _ _ h1 h3
  simp only [← pow_mul, ← pow_add] at h4
  rw [← Finset.mul_sum, h4, mul_comm b w]; ring

theorem UpperTheory.V.Sd.constSmall :
    UpperTheory.V.Sd.ConstSmall := by
  intro l hl ι M w _ φ θ χ h k hk c hc
  have hw0 : 0 < w := h.prime.pos
  have hM0 : 0 < M := zero_lt_one.trans h.one_lt
  haveI : NeZero M := ⟨hM0.ne'⟩
  haveI : Fact w.Prime := ⟨h.prime⟩
  have hlw : ¬ l ∣ w := fun hd => hl.out.one_lt.ne' (Nat.dvd_one.1 ((Nat.dvd_sub_iff_right hw0 hd).1 h.dvd))
  have hlN : ¬ l ∣ M * w := fun hd => (hl.out.dvd_mul.1 hd).elim h.cop hlw
  set ζ : ℂ := ZMod.stdAddChar (1 : ZMod (M * w)) with hζdef
  have hζn : ∀ n : ℕ, (ZMod.stdAddChar (n : ZMod (M * w)) : ℂ) = ζ ^ n := fun n => by
    rw [hζdef, ← AddChar.map_nsmul_eq_pow]; simp
  have hζ : IsPrimitiveRoot ζ (M * w) := by
    refine ⟨add_pow_N _, fun n hn => ?_⟩
    rw [← hζn, (ZMod.isPrimitive_stdAddChar (M * w)).zmod_char_eq_one_iff] at hn
    exact (ZMod.natCast_eq_zero_iff _ _).1 hn
  have hL : ∀ n : ℕ, ‖ι.symm (Lk k (ζ ^ n))‖ ≤ 1 := fun n =>
    Lk_le h.odd ι (by positivity) hlN hk (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow])
  have hmul : ∀ n : ℕ, χ⁻¹ (n : ZMod (M * w)) = φ⁻¹ (n : ZMod M) * θ⁻¹ (n : ZMod w) := fun n => by
    simp only [MulChar.inv_apply_eq_inv', h.mul, mul_inv]
  have hφw : φ⁻¹ (w : ZMod M) = 1 := by rw [MulChar.inv_apply_eq_inv', h.φw, inv_one]
  set T : ℂ := ∑ b ∈ range M, φ⁻¹ (b : ZMod M) * Lk k (ζ ^ (w * b)) with hT
  have hT1 : ‖ι.symm T‖ ≤ 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, map_sum]
    exact sum_le _ _ fun b _ => by rw [map_mul]; exact mul_le (char_le ι _ _) (hL _)
  have hA := sum_all h.one_lt hw0 hk φ⁻¹ hζ
  have hB := sum_multiples M w hw0 (fun n => φ⁻¹ (n : ZMod M) * Lk k (ζ ^ n))
  simp only [Nat.cast_mul, map_mul, hφw, one_mul] at hB
  rw [← hT] at hA hB
  have hS : ∑ a : ZMod (M * w), χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ) =
      ∑ n ∈ range (M * w), (if w ∣ n then 0 else (θ⁻¹ (n : ZMod w) - 1) * (φ⁻¹ (n : ZMod M) * Lk k (ζ ^ n))) +
        ((w : ℂ) ^ k - 1) * T := by
    rw [sub_mul, one_mul, ← hA, ← hB, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, sum_zmod]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hmul, hζn]
    split_ifs with hn
    · rw [(ZMod.natCast_eq_zero_iff _ _).2 hn, MulChar.map_zero]; ring
    · ring
  have hw1 : ‖ι.symm ((w : ℂ) ^ k - 1)‖ < 1 := by
    have h1 : l ∣ w ^ k - 1 := h.dvd.trans (Nat.sub_one_dvd_pow_sub_one w k)
    have h2 : ((w : ℂ) ^ k - 1) = ((w ^ k - 1 : ℕ) : ℂ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ hw0)]; simp
    rw [h2, map_natCast]; exact nat_lt h1
  have hSlt : ‖ι.symm (∑ a : ZMod (M * w), χ⁻¹ a * Lk k (ZMod.stdAddChar a : ℂ))‖ < 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_add (f := _), map_mul, map_sum]
    refine add_lt (sum_lt _ _ fun n _ => ?_) (mul_lt hw1 hT1)
    split_ifs with hn
    · simp
    · rw [map_mul, map_mul, map_sub, map_one]
      refine mul_lt (root_sub_one ?_) (mul_le (char_le ι _ _) (hL _))
      have hu : IsUnit (n : ZMod w) := Ne.isUnit (mt (ZMod.natCast_eq_zero_iff _ _).1 hn)
      rw [← map_pow, ← MulChar.pow_apply' _ hl.out.ne_zero, inv_pow, h.θpow, inv_one, MulChar.one_apply hu, map_one]
  have h2 : ‖(2 : Qbar l)‖ = 1 := by
    have : ¬ l ∣ 2 := fun hd => h.odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 hd)
    simpa using nat_eq (l := l) this
  rw [← hc, map_mul, map_mul, norm_mul, norm_mul, gauss_eq ι χ (ePrim l M w φ θ χ h) hlN, map_ofNat, h2] at hSlt
  simpa using hSlt
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.CuspOf
open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

theorem UpperTheory.V.Sd.cuspOf :
    UpperTheory.V.Sd.CuspOf := by
  intro N k _ χ f hχ hv h0
  have hT : (1:ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, ?_, ?_⟩
    · rw [SetLike.mem_coe, Gamma1_mem]
      simp [ModularGroup.T]
    · ext i j
      rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
  have hinf : IsZeroAtImInfty f := by
    apply ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero f
    rw [← qExpansion_coeff_zero one_pos (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hT)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hT)]
    exact h0
  refine ⟨⟨f.toSlashInvariantForm, f.holo', fun {c} hc => ?_⟩, rfl⟩
  have hc' : IsCusp c 𝒮ℒ := by
    rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
  intro γ _
  by_cases hd : (N:ℤ) ∣ γ 1 0
  · have hγ : γ ∈ Gamma0 N := Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hd)
    change IsZeroAtImInfty (⇑f ∣[(k:ℤ)] γ)
    rw [hχ γ hγ]
    exact hinf.smul _
  · exact hv γ hd
end

open Formalism.ConjugateSelfDual CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private theorem sum_div_split (g : ℕ → ℂ) (hg : ∀ a b, g (a * b) = g a * g b) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ (p * n).divisors with p ∣ j, g j = g p * ∑ j ∈ n.divisors, g j := by
  have hp0 : 0 < p := hp.pos
  rw [Finset.mul_sum]
  simp_rw [← hg]
  symm
  rw [← Finset.sum_image (g := fun j => p * j) (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp0 h)]
  congr 1
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨a, ⟨ha, hn0⟩, rfl⟩
    exact ⟨⟨mul_dvd_mul_left p ha, Nat.mul_ne_zero hp.ne_zero hn0⟩, dvd_mul_right p a⟩
  · rintro ⟨⟨hj, hpn⟩, ⟨b, rfl⟩⟩
    exact ⟨b, ⟨Nat.dvd_of_mul_dvd_mul_left hp0 hj, by omega⟩, rfl⟩

private theorem sum_div_hecke (g : ℕ → ℂ) (hg : ∀ a b, g (a * b) = g a * g b) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ (p * n).divisors, g j + g p * (if p ∣ n then ∑ j ∈ (n / p).divisors, g j else 0) =
      (1 + g p) * ∑ j ∈ n.divisors, g j := by
  have hn0 : n ≠ 0 := by omega
  rw [← Finset.sum_filter_add_sum_filter_not (p * n).divisors (fun j => p ∣ j), sum_div_split g hg hp n hn]
  have hB : ∑ j ∈ (p * n).divisors with ¬p ∣ j, g j = ∑ j ∈ n.divisors with ¬p ∣ j, g j := by
    congr 1
    ext j
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hj, _⟩, hpj⟩
      have hc : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpj).symm
      exact ⟨⟨hc.dvd_of_dvd_mul_left hj, hn0⟩, hpj⟩
    · rintro ⟨⟨hj, _⟩, hpj⟩
      exact ⟨⟨Dvd.dvd.mul_left hj p, Nat.mul_ne_zero hp.ne_zero hn0⟩, hpj⟩
  have hC : ∑ j ∈ n.divisors, g j = ∑ j ∈ n.divisors with ¬p ∣ j, g j +
      (if p ∣ n then g p * ∑ j ∈ (n / p).divisors, g j else 0) := by
    rw [← Finset.sum_filter_add_sum_filter_not n.divisors (fun j => p ∣ j), add_comm]
    congr 1
    split_ifs with h
    · obtain ⟨m, rfl⟩ := h
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · simp [h0] at hn0
        · exact h0
      rw [Nat.mul_div_cancel_left m hp.pos]
      exact sum_div_split g hg hp m hm
    · apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Nat.mem_divisors] at hj
      exact absurd (hj.2.trans hj.1.1) h
  rw [hB]
  split_ifs at hC ⊢
  · linear_combination (-1 : ℂ) * hC
  · linear_combination (-1 : ℂ) * hC

private theorem sig_hecke (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    sigChi k χ (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then sigChi k χ (n / p) else 0) =
      (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) * sigChi k χ n := by
  have h := sum_div_hecke (fun j => χ (j : ZMod N) * (j : ℂ) ^ (k - 1))
    (by intro a b; push_cast; rw [map_mul, mul_pow]; ring) hp n hn
  simpa only [sigChi] using h

section Int

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

private theorem int_add {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x + y)‖ ≤ 1 := by
  rw [map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

private theorem int_sub {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x - y)‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact int_add ι hx (by rwa [map_neg, norm_neg])

private theorem int_mul {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x * y)‖ ≤ 1 := by
  rw [map_mul, norm_mul]
  exact mul_le_one₀ hx (norm_nonneg _) hy

private theorem small_mul {x y : ℂ} (hx : ‖ι.symm x‖ < 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x * y)‖ < 1 := by
  rw [map_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans_lt hx

private theorem int_chi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a : ZMod N) : ‖ι.symm (χ a)‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · have hm : χ a ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← ha.unit_spec, ← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have h1 : ‖ι.symm (χ a)‖ ^ Fintype.card (ZMod N)ˣ = 1 := by
      rw [← norm_pow, ← map_pow, hm, map_one, norm_one]
    exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h1).le
  · rw [MulChar.map_nonunit χ ha, map_zero, norm_zero]
    exact zero_le_one

private theorem int_term (k : ℕ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (j : ℕ) :
    ‖ι.symm (χ (j : ZMod N) * (j : ℂ) ^ (k - 1))‖ ≤ 1 := by
  refine int_mul ι (int_chi ι χ _) ?_
  rw [map_pow, map_natCast, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ j)

private theorem int_sig (k : ℕ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖ι.symm (sigChi k χ n)‖ ≤ 1 := by
  unfold sigChi
  exact Finset.sum_induction _ (fun x => ‖ι.symm x‖ ≤ 1) (fun a b ha hb => int_add ι ha hb)
    (by simp) (fun j _ => int_term ι k χ j)

end Int

private theorem chi_neg_one {l M w : ℕ} (hl : l.Prime) {φ θ χ} (h : EDat l M w φ θ χ) : χ (-1) = φ (-1) := by
  have hM := h.one_lt
  have hw := h.prime.pos
  have h1 : 1 ≤ M * w := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  have key := h.mul (M * w - 1)
  have e1 : ((M * w - 1 : ℕ) : ZMod (M * w)) = -1 := by
    rw [Nat.cast_sub h1, ZMod.natCast_self]; simp
  have e2 : ((M * w - 1 : ℕ) : ZMod M) = -1 := by
    rw [Nat.cast_sub h1, Nat.cast_mul, ZMod.natCast_self]; simp
  have e3 : ((M * w - 1 : ℕ) : ZMod w) = -1 := by
    rw [Nat.cast_sub h1, Nat.cast_mul, ZMod.natCast_self]; simp
  rw [e1, e2, e3] at key
  have hθ : θ (-1) = 1 := by
    have hsq : θ (-1) ^ 2 = 1 := by
      rw [← map_pow]; simp
    have hθl : θ (-1) ^ l = 1 := by
      rw [← MulChar.pow_apply' θ hl.ne_zero, h.θpow, MulChar.one_apply isUnit_one.neg]
    obtain ⟨m, hm⟩ := Nat.Prime.odd_of_ne_two hl h.odd
    rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at hθl
    exact hθl
  rw [key, hθ, mul_one]

private theorem coef_comb {N k : ℕ} [NeZero N] (E G : ModularForm (Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ) :
    coef (E - c • G : ModularForm (Gamma1 N) (k : ℤ)) n = coef E n - c * coef G n := by
  have h1 : (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  unfold coef
  rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1 E (c • G), ModularForm.coe_smul,
    ModularForm.qExpansion_smul one_pos h1 c G]
  simp

private theorem slash_comb (k : ℕ) (E G : ℍ → ℂ) (c : ℂ) (γ : SL(2, ℤ)) :
    (E - c • G) ∣[(k : ℤ)] γ = E ∣[(k : ℤ)] γ - c • G ∣[(k : ℤ)] γ := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.SL_smul_slash, ← sub_eq_add_neg]

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.propE :
    UpperTheory.V.Sd.PropE := by
  intro l _ ι M w φ θ χ h
  have hl : l.Prime := Fact.out
  have hM := h.one_lt
  have hw2 := h.prime.two_le
  haveI : NeZero (M * w) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hN3 : 3 ≤ M * w := by nlinarith
  have hlN : ¬ l ∣ M * w := by
    intro hd
    rcases (Nat.Prime.dvd_mul hl).1 hd with h' | h'
    · exact h.cop h'
    · rcases Nat.Prime.eq_one_or_self_of_dvd h.prime l h' with h1 | h1
      · exact hl.one_lt.ne' h1
      · have hs : l ∣ w - (w - 1) := Nat.dvd_sub h' h.dvd
        have hw1 : w - (w - 1) = 1 := by omega
        rw [hw1] at hs
        exact hl.one_lt.ne' (Nat.dvd_one.1 hs)
  obtain ⟨k₁, hk₁⟩ := unitForm l h.odd ι (M * w) hN3 hlN
  refine ⟨max k₁ 3, fun k hk hφ => ?_⟩
  have hk1 : k₁ ≤ k := le_of_max_le_left hk
  have hk3 : 3 ≤ k := le_of_max_le_right hk
  have hχ : χ (-1) = (-1) ^ k := (chi_neg_one hl h).trans hφ
  obtain ⟨G, hGc, hGi, hGv, hG0⟩ := hk₁ k hk1 χ hχ
  obtain ⟨E, hEc, hEv, hEn, hE0⟩ := eisChi (M * w) k (by omega) hk3 χ (ePrim l M w φ θ χ h) hχ
  have hc : ‖ι.symm (coef E 0)‖ < 1 := constSmall l ι M w φ θ χ h k (by omega) _ hE0
  set c := coef (⇑E) 0 with hc_def
  have hF0 : coef (⇑(E - c • G)) 0 = 0 := by
    rw [coef_comb, hG0, mul_one, sub_self]
  have hFc : HasChar k χ ⇑(E - c • G) := by
    intro γ hγ
    rw [ModularForm.coe_sub, ModularForm.coe_smul, slash_comb, hEc γ hγ, hGc γ hγ, smul_sub, smul_comm c]
  have hFv : VanOff (M * w) k ⇑(E - c • G) := by
    intro γ hγ
    rw [ModularForm.coe_sub, ModularForm.coe_smul, slash_comb]
    have ht := (hEv γ hγ).sub ((hGv γ hγ).smul c)
    rw [sub_zero] at ht
    exact ht
  obtain ⟨f, hf⟩ := cuspOf (M * w) k χ (E - c • G) hFc hFv hF0
  have hcf : ∀ m, 1 ≤ m → coef (⇑f) m = sigChi k χ m - c * coef (⇑G) m := by
    intro m hm
    rw [hf, coef_comb, hEn m hm]
  have hfc : HasChar k χ ⇑f := by rw [hf]; exact hFc
  have hInt : IntQ ι ⇑f := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [hf, hF0, map_zero, norm_zero]
      exact zero_le_one
    · rw [hcf n hn]
      exact int_sub ι (int_sig ι k χ n) (int_mul ι hc.le (hGi n))
  have hOne : ‖ι.symm (coef (⇑f) 1)‖ = 1 := by
    have hy := small_mul ι hc (hGi 1)
    have hs1 : sigChi k χ 1 = 1 := by simp [sigChi]
    rw [hcf 1 le_rfl, hs1]
    refine le_antisymm (int_sub ι (by simp) hy.le) ?_
    have hmax := IsUltrametricDist.norm_add_le_max (ι.symm (1 - c * coef (⇑G) 1)) (ι.symm (c * coef (⇑G) 1))
    rw [← map_add (f := _), sub_add_cancel, map_one, norm_one] at hmax
    rcases le_max_iff.1 hmax with h' | h'
    · exact h'
    · exact absurd h' (not_le.2 hy)
  have hA : ∀ p : ℕ, p.Prime →
      ‖ι.symm (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1))‖ ≤ 1 ∧
      ∀ n : ℕ, 1 ≤ n →
        ‖ι.symm ((coef (⇑f) (p * n) + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then coef (⇑f) (n / p) else 0)) -
          (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)) * coef (⇑f) n)‖ < 1 := by
    intro p hp
    have ha : ‖ι.symm (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1))‖ ≤ 1 :=
      int_add ι (by simp) (int_term ι k χ p)
    refine ⟨ha, fun n hn => ?_⟩
    have hs := sig_hecke k χ hp n hn
    have hpn : 1 ≤ p * n := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hp.ne_zero (by omega))
    have key : (coef (⇑f) (p * n) + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then coef (⇑f) (n / p) else 0)) -
          (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)) * coef (⇑f) n =
        -(c * ((coef (⇑G) (p * n) + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1) *
            (if p ∣ n then coef (⇑G) (n / p) else 0)) -
          (1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)) * coef (⇑G) n)) := by
      split_ifs at hs ⊢ with hd
      · have hnp : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
        rw [hcf _ hpn, hcf _ hnp, hcf _ hn]
        linear_combination hs
      · rw [hcf _ hpn, hcf _ hn]
        linear_combination hs
    rw [key, map_neg, norm_neg]
    refine small_mul ι hc (int_sub ι (int_add ι (hGi _) (int_mul ι (int_term ι k χ p) ?_)) (int_mul ι ha (hGi n)))
    split_ifs
    · exact hGi _
    · simp
  obtain ⟨g, hg⟩ := eigLift l ι (M * w) k (by omega) χ f hfc hInt hOne
    (fun p => 1 + χ (p : ZMod (M * w)) * (p : ℂ) ^ (k - 1)) hA
  exact ⟨g, hg⟩
