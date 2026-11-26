module

public import Formalism.EllipticTorsion.EllipticTorsionProofs.LegendreInvariant
public import Formalism.EllipticTorsion.FormalGroupPointsTorsionFree
public import Formalism.FormalGroupLog.LogDeterminesLaw

@[expose] public section

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
namespace Formalism.ELL

namespace DeuringModel

open Polynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

lemma norm_add_eq_left {x y : K} (h : ‖y‖ < ‖x‖) : ‖x + y‖ = ‖x‖ := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne', max_eq_left h.le]

lemma norm_nat_le_one (n : ℕ) : ‖(n : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n

lemma exists_root_deuring [IsAlgClosed K] (j : K) :
    ∃ a : K, a ^ 3 * (a ^ 3 - 24) ^ 3 = j * (a ^ 3 - 27) := by
  let P : K[X] := X ^ 3 * (X ^ 3 - C 24) ^ 3 - C j * (X ^ 3 - C 27)
  have hdeg : P.degree = 12 := by
    simp only [P]
    compute_degree!
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root P (by rw [hdeg]; norm_num)
  refine ⟨a, ?_⟩
  simp only [P, IsRoot, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at ha
  exact sub_eq_zero.mp ha

end DeuringModel

open DeuringModel in
theorem deuring_model : ModelDeuring := by
  intro K _ _ _ h3 j hj
  obtain ⟨a, ha⟩ := exists_root_deuring j
  have hc4 : (deuring a).c₄ = a * (a ^ 3 - 24) := by
    simp [deuring, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hΔ : (deuring a).Δ = a ^ 3 - 27 := by
    simp [deuring, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have h27 : ‖(27 : K)‖ = 1 := by
    have e : (27 : K) = 3 ^ 3 := by norm_num
    rw [e, norm_pow, h3, one_pow]
  have ha1 : ‖a‖ ≤ 1 := by
    by_contra hlt
    push_neg at hlt
    have hA3 : ‖a ^ 3‖ = ‖a‖ ^ 3 := norm_pow a 3
    have hbig : 1 < ‖a‖ ^ 3 := one_lt_pow₀ hlt (by norm_num)
    have h24 : ‖(24 : K)‖ ≤ 1 := by exact_mod_cast norm_nat_le_one (K := K) 24
    have hn1 : ‖a ^ 3 - 24‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hn2 : ‖a ^ 3 - 27‖ = ‖a‖ ^ 3 := by
      rw [sub_eq_add_neg, norm_add_eq_left (by rw [norm_neg, hA3]; linarith), hA3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = ‖a‖ ^ 12 := by
      rw [norm_mul, hA3, norm_pow, hn1]
      ring
    have hR : ‖j * (a ^ 3 - 27)‖ ≤ ‖a‖ ^ 3 := by
      rw [norm_mul, hn2]
      calc ‖j‖ * ‖a‖ ^ 3 ≤ 1 * ‖a‖ ^ 3 := by gcongr
        _ = ‖a‖ ^ 3 := one_mul _
    rw [ha] at hL
    have hlt2 : ‖a‖ ^ 3 < ‖a‖ ^ 12 := pow_lt_pow_right₀ hlt (by norm_num)
    linarith
  have hA3le : ‖a ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha1
  have hΔle : ‖a ^ 3 - 27‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA3le (by rw [norm_neg, h27]))
  have hΔ1 : ‖a ^ 3 - 27‖ = 1 := by
    by_contra hne
    have hlt : ‖a ^ 3 - 27‖ < 1 := lt_of_le_of_ne hΔle hne
    have e1 : a ^ 3 = 27 + (a ^ 3 - 27) := by ring
    have hA : ‖a ^ 3‖ = 1 := by
      rw [e1, norm_add_eq_left (by rw [h27]; exact hlt), h27]
    have e2 : a ^ 3 - 24 = 3 + (a ^ 3 - 27) := by ring
    have hB : ‖a ^ 3 - 24‖ = 1 := by
      rw [e2, norm_add_eq_left (by rw [h3]; exact hlt), h3]
    have hL : ‖a ^ 3 * (a ^ 3 - 24) ^ 3‖ = 1 := by
      rw [norm_mul, hA, norm_pow, hB]
      norm_num
    rw [ha, norm_mul] at hL
    have h4 : ‖j‖ * ‖a ^ 3 - 27‖ < 1 := by
      calc ‖j‖ * ‖a ^ 3 - 27‖ ≤ 1 * ‖a ^ 3 - 27‖ := by gcongr
        _ < 1 := by rw [one_mul]; exact hlt
    linarith
  refine ⟨a, ha1, ?_, ?_⟩
  · rw [hc4, hΔ, ← ha]
    ring
  · rw [hΔ, hΔ1]

end Formalism.ELL
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.JetsTwo
universe u

noncomputable section

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type*} [CommRing K]

def ccd (i : Fin 2) (H : MvPowerSeries (Fin 2) K) : K :=
  MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := K) i H)

theorem hv {x y : MvPowerSeries (Fin 2) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    ∀ j, MvPowerSeries.constantCoeff (![x, y] j) = 0 := by
  intro j
  fin_cases j <;> simp [hx, hy]

theorem ccd_F (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (i : Fin 2) :
    ccd i (F.subst ![x, y]) = ccd 0 F * ccd i x + ccd 1 F * ccd i y := by
  unfold ccd
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pderiv_subst (hv hx hy), map_sum, Fin.sum_univ_two]
  simp only [map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy), Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

theorem ccd_single (F : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    ccd i F = MvPowerSeries.coeff (Finsupp.single i 1) F := by
  unfold ccd
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL

open Formalism.G Formalism.ELL.FormalGroupQuadraticJets Formalism.G.LogCR

end Formalism.ELL
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.TorInt
universe u

noncomputable section

namespace Formalism.ELL.TorsionIntegralEllipticTorsion

open WeierstrassCurve Formalism.ELL

lemma y_int {K : Type u} [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (hW : IntegralModel W) {x y : K} (h : W.toAffine.Equation x y) (hx : ‖x‖ ≤ 1) :
    ‖y‖ ≤ 1 := by
  have hW' := hW
  unfold IntegralModel at hW'
  have h' := h
  rw [WeierstrassCurve.Affine.equation_iff] at h'
  obtain ⟨h1, h2, h3, h4, h6⟩ := hW'
  have hadd : ∀ a b : K, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a + b‖ ≤ 1 := fun a b ha hb =>
    (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  have hmul : ∀ a b : K, ‖a‖ ≤ 1 → ‖b‖ ≤ 1 → ‖a * b‖ ≤ 1 := fun a b ha hb => by
    rw [norm_mul]
    first
    | exact mul_le_one₀ ha (norm_nonneg _) hb
    | nlinarith [norm_nonneg a, norm_nonneg b]
  have hx2 : ‖x ^ 2‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | nlinarith [norm_nonneg x]
  have hx3 : ‖x ^ 3‖ ≤ 1 := by
    rw [norm_pow]
    first
    | exact pow_le_one₀ (norm_nonneg _) hx
    | nlinarith [norm_nonneg x, hx2]
  have hR : ‖x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆‖ ≤ 1 :=
    hadd _ _ (hadd _ _ (hadd _ _ hx3 (hmul _ _ h2 hx2)) (hmul _ _ h4 hx)) h6
  by_contra hy
  push_neg at hy
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hm : ‖W.a₁ * x * y + W.a₃ * y‖ ≤ ‖y‖ := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      calc ‖W.a₁ * x‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (hmul _ _ h1 hx) hy0
        _ = ‖y‖ := one_mul _
    · rw [norm_mul]
      calc ‖W.a₃‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right h3 hy0
        _ = ‖y‖ := one_mul _
  have hy2 : y ^ 2 = (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) - (W.a₁ * x * y + W.a₃ * y) := by
    first
    | linear_combination h'
    | (rw [← h']; ring)
  have hsub : ‖(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) - (W.a₁ * x * y + W.a₃ * y)‖ ≤ ‖y‖ := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hR.trans hy.le) ?_)
    rw [norm_neg]
    exact hm
  have hn : ‖y‖ ^ 2 ≤ ‖y‖ := by
    rw [← norm_pow, hy2]
    exact hsub
  nlinarith

end Formalism.ELL.TorsionIntegralEllipticTorsion

namespace Formalism.ELL

open WeierstrassCurve

theorem torsionIntegral_of (h : Formalism.ELL.FormalGroupPointsTorsionFree.{u}) : Formalism.ELL.TorsionIntegral.{u} := by
  intro K _ _ W hW hΔ n hn x y hxy hnP
  have hx : ‖x‖ ≤ 1 := by
    by_contra hx
    push Not at hx
    exact Affine.Point.some_ne_zero hxy (h K W hW hΔ n hn _ hx hnP)
  exact ⟨hx, TorsionIntegralEllipticTorsion.y_int W hW hxy.1 hx⟩

end Formalism.ELL
end
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.Legendre
namespace Formalism.ELL

namespace LegendreModelEllipticTorsion

open Polynomial

noncomputable def legPoly {K : Type*} [Field K] (j : K) : K[X] :=
  C 256 * (X ^ 2 - X + 1) ^ 3 - C j * (X * (X - 1)) ^ 2

theorem legPoly_natDegree {K : Type*} [Field K] (h : (256 : K) ≠ 0) (j : K) :
    (legPoly j).natDegree = 6 := by
  unfold legPoly
  compute_degree!

theorem norm_one_add {K : Type*} [NormedField K] [IsUltrametricDist K] {t : K} (ht : ‖t‖ ≠ 1) :
    ‖1 + t‖ = max 1 ‖t‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : K)) (y := t)
    (by rw [norm_one]; exact fun h => ht h.symm)
  simpa using this

end LegendreModelEllipticTorsion

open LegendreModelEllipticTorsion Polynomial in
theorem legendre_model : ModelLegendre := by
  intro K _ _ _ h2 j hj
  have h16 : ‖(16 : K)‖ = 1 := by
    have : (16 : K) = 2 ^ 4 := by norm_num
    rw [this, norm_pow, h2, one_pow]
  have h256 : ‖(256 : K)‖ = 1 := by
    have : (256 : K) = 2 ^ 8 := by norm_num
    rw [this, norm_pow, h2, one_pow]
  have h256ne : (256 : K) ≠ 0 := by
    intro h; rw [h, norm_zero] at h256; exact zero_ne_one h256
  have hdeg : (legPoly j).degree ≠ 0 := by
    rw [degree_eq_natDegree, legPoly_natDegree h256ne]
    · decide
    · intro h0
      have := legPoly_natDegree h256ne j
      rw [h0, natDegree_zero] at this
      exact absurd this (by decide)
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_root _ hdeg
  have hroot : (256 : K) * (l ^ 2 - l + 1) ^ 3 = j * (l * (l - 1)) ^ 2 := by
    have := hl.eq_zero
    simp only [legPoly, eval_sub, eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one] at this
    exact sub_eq_zero.mp this
  set t := l * (l - 1) with ht
  have hu : l ^ 2 - l + 1 = 1 + t := by rw [ht]; ring
  rw [hu] at hroot
  have hnorm := congrArg norm hroot
  simp only [norm_mul, norm_pow, h256, one_mul] at hnorm

  have htn : ‖t‖ = 1 := by
    by_contra hne
    have e := norm_one_add hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [e, max_eq_left hlt.le, one_pow] at hnorm
      have : ‖j‖ * ‖t‖ ^ 2 < 1 := by
        calc ‖j‖ * ‖t‖ ^ 2 ≤ 1 * ‖t‖ ^ 2 := by gcongr
          _ < 1 := by rw [one_mul]; exact pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)
      linarith
    · rw [e, max_eq_right hgt.le] at hnorm
      have hpos : 0 < ‖t‖ ^ 2 := by positivity
      have : ‖t‖ ^ 3 ≤ ‖t‖ ^ 2 := by
        rw [hnorm]; calc ‖j‖ * ‖t‖ ^ 2 ≤ 1 * ‖t‖ ^ 2 := by gcongr
          _ = ‖t‖ ^ 2 := one_mul _
      have : ‖t‖ ^ 2 * ‖t‖ ≤ ‖t‖ ^ 2 * 1 := by nlinarith
      have := le_of_mul_le_mul_left this hpos
      linarith
  have hprod : ‖l‖ * ‖l - 1‖ = 1 := by rw [← norm_mul, ← ht, htn]
  have hle1 : ‖l - 1‖ ≤ max ‖l‖ 1 := by
    have := IsUltrametricDist.norm_add_le_max l (-1 : K)
    simpa [← sub_eq_add_neg] using this
  have hle2 : ‖l‖ ≤ max ‖l - 1‖ 1 := by
    have := IsUltrametricDist.norm_add_le_max (l - 1) (1 : K)
    simpa using this
  have hl1 : ‖l‖ = 1 := by
    rcases lt_trichotomy ‖l‖ 1 with h | h | h
    · exfalso
      rw [max_eq_right h.le] at hle1
      have : ‖l‖ * ‖l - 1‖ < 1 := by
        calc ‖l‖ * ‖l - 1‖ ≤ ‖l‖ * 1 := by gcongr
          _ < 1 := by rw [mul_one]; exact h
      linarith
    · exact h
    · exfalso
      have hpos : 0 < ‖l‖ := by linarith
      have hlt : ‖l - 1‖ < 1 := by
        by_contra hc
        rw [not_lt] at hc
        nlinarith
      rw [max_eq_right hlt.le] at hle2
      linarith
  have hl2 : ‖l - 1‖ = 1 := by rw [hl1, one_mul] at hprod; exact hprod
  obtain ⟨hΔ, hc4⟩ := legendre_invariant K l
  refine ⟨l, hl1, hl2, ?_, ?_⟩
  · rw [hΔ, hc4]
    have : (l ^ 2 - l + 1) = 1 + t := hu
    rw [this]
    have e2 : (16 : K) * l ^ 2 * (l - 1) ^ 2 = 16 * t ^ 2 := by rw [ht]; ring
    rw [e2]
    linear_combination 16 * hroot
  · rw [hΔ, norm_mul, norm_mul, h16, norm_pow, norm_pow, hl1, hl2]
    norm_num

end Formalism.ELL
end

section -- merged from Formalism.EllipticTorsion.EllipticTorsionProofs.LogWeight
open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL.LogarithmWeight

open Formalism.G

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem norm_sum_mul_le {ι : Type*} (s : Finset ι) (f : ι → K) {w B : ℝ} (hw : 0 < w)
    (hB : 0 ≤ B) (h : ∀ i ∈ s, ‖f i‖ * w ≤ B) : ‖∑ i ∈ s, f i‖ * w ≤ B := by
  rw [← le_div_iff₀ hw]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hB hw.le)
  intro i hi
  rw [le_div_iff₀ hw]
  exact h i hi

theorem coeff_mul_le {f g : PowerSeries K} {c A B : ℝ} (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ n, ‖coeff n f‖ * c ^ n ≤ A) (hg : ∀ n, ‖coeff n g‖ * c ^ n ≤ B) (n : ℕ) :
    ‖coeff n (f * g)‖ * c ^ n ≤ A * B := by
  rw [PowerSeries.coeff_mul]
  apply norm_sum_mul_le _ _ (pow_pos hc n) (mul_nonneg hA hB)
  intro x hx
  have hx : x.1 + x.2 = n := by simpa using hx
  rw [norm_mul, ← hx, pow_add]
  calc ‖coeff x.1 f‖ * ‖coeff x.2 g‖ * (c ^ x.1 * c ^ x.2)
      = (‖coeff x.1 f‖ * c ^ x.1) * (‖coeff x.2 g‖ * c ^ x.2) := by ring
    _ ≤ A * B := mul_le_mul (hf _) (hg _) (by positivity) hA

theorem coeff_pow_le {f : PowerSeries K} {c A : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (hf : ∀ n, ‖coeff n f‖ * c ^ n ≤ A) (m n : ℕ) :
    ‖coeff n (f ^ m)‖ * c ^ n ≤ A ^ m := by
  induction m generalizing n with
  | zero =>
    rw [pow_zero, pow_zero]
    rcases n with _ | n
    · simp
    · simp [PowerSeries.coeff_one]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact coeff_mul_le hc (pow_nonneg hA _) hA ih hf n

theorem coeff_pow_of_cc {e : PowerSeries K} (he : constantCoeff e = 0) :
    ∃ g : PowerSeries K, constantCoeff g = coeff 1 e ∧
      ∀ m n : ℕ, coeff n (e ^ m) = if m ≤ n then coeff (n - m) (g ^ m) else 0 := by
  obtain ⟨g, hg⟩ := (PowerSeries.X_dvd_iff).mpr he
  refine ⟨g, ?_, fun m n => ?_⟩
  · rw [hg, show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · rw [hg, mul_pow, PowerSeries.coeff_X_pow_mul']

theorem coeff_pow_eq_zero {e : PowerSeries K} (he : constantCoeff e = 0) {m n : ℕ} (h : n < m) :
    coeff n (e ^ m) = 0 := by
  obtain ⟨g, -, hg⟩ := coeff_pow_of_cc he
  rw [hg, if_neg (by omega)]

theorem coeff_pow_self {e : PowerSeries K} (he : constantCoeff e = 0) (n : ℕ) :
    coeff n (e ^ n) = coeff 1 e ^ n := by
  obtain ⟨g, hg1, hg⟩ := coeff_pow_of_cc he
  rw [hg, if_pos le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hg1]

theorem coeff_subst_eq_sum {l e : PowerSeries K} (he : constantCoeff e = 0) (n : ℕ) :
    coeff n (l.subst e) = ∑ m ∈ Finset.range (n + 1), coeff m l * coeff n (e ^ m) := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' he)]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) ?_]
  · simp [smul_eq_mul]
  · intro m hm
    simp only [Function.mem_support] at hm
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply hm
    rw [coeff_pow_eq_zero he (by omega), smul_zero]

theorem subst_ga_eq {R : Type*} [CommRing R] (f : PowerSeries R) (hf0 : constantCoeff f = 0) :
    (FormalGroup.𝔾ₐ (R := R)).toPowerSeries.subst ![atX f, atY f] = atX f + atY f := by
  have hv := Formalism.G.LogP.hs2 (R := R) (u := atX f) (v := atY f)
    (PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0)
    (PowerSeries.constantCoeff_subst_eq_zero (by simp) f hf0)
  rw [FormalGroup.𝔾ₐ_toPowerSeries, MvPowerSeries.subst_add hv, MvPowerSeries.subst_X hv,
    MvPowerSeries.subst_X hv]
  rfl

theorem log_comp_hom [CharZero K] {F : FormalGroup K} {e l : PowerSeries K} (p : K) (hp : p ≠ 0)
    (he : IsHom F F e) (he1 : coeff 1 e = p) (hl : IsLog F l) :
    l.subst e = p • l := by
  have hlh : IsHom F FormalGroup.𝔾ₐ l := ((Formalism.G.log_iff_hom_additive K F l).mp hl).1
  have hh := Formalism.G.homComp_statement K F F FormalGroup.𝔾ₐ e l he hlh
  have h1 : coeff 1 (l.subst e) = p := by
    rw [coeff_subst_eq_sum he.1]
    simp [Finset.sum_range_succ, hl.2.1, he1]
  have hF : PowerSeries.HasSubst F.toPowerSeries :=
    PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff
  have hg : IsLog F (p⁻¹ • l.subst e) := by
    refine ⟨?_, ?_, ?_⟩
    · simp [hh.1]
    · rw [map_smul, h1, smul_eq_mul, inv_mul_cancel₀ hp]
    · simp only [atX, atY]
      rw [PowerSeries.subst_smul hF, hh.2, subst_ga_eq _ hh.1,
        PowerSeries.subst_smul (PowerSeries.HasSubst.X 0),
        PowerSeries.subst_smul (PowerSeries.HasSubst.X 1), smul_add]
  have := (Formalism.G.log_exists_unique K F).unique hg hl
  calc l.subst e = p • (p⁻¹ • l.subst e) := by rw [smul_smul, mul_inv_cancel₀ hp, one_smul]
    _ = p • l := by rw [this]

end Formalism.ELL.LogarithmWeight

namespace Formalism.ELL

theorem logarithm_coeff_weight : Formalism.ELL.LogWeight := by
  intro K _ _ _ p q hp hp0 hp1 hq F e l he heI he1 he0 hl n hn
  set P : K := (p : K) with hPdef
  have hP0 : P ≠ 0 := norm_pos_iff.mp hp0
  have hle := Formalism.ELL.LogarithmWeight.log_comp_hom P hP0 he he1 hl
  have hq1 : (0:ℝ) < (q:ℝ) - 1 := by
    have : (2:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  set c : ℝ := ‖P‖ ^ (1 / ((q:ℝ) - 1)) with hc
  have cpos : 0 < c := Real.rpow_pos_of_pos hp0 _
  have cle : c ≤ 1 := Real.rpow_le_one (norm_nonneg _) hp1.le (div_nonneg zero_le_one hq1.le)
  have cpow : c ^ (q - 1) = ‖P‖ := by
    rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_one, one_div, inv_mul_cancel₀ hq1.ne', Real.rpow_one]
  have cq : c ^ q = ‖P‖ * c := by
    rw [← cpow, ← pow_succ]
    congr 1
    omega
  have heB : ∀ d, ‖coeff d e‖ * c ^ d ≤ c ^ q := by
    intro d
    rcases Nat.lt_or_ge d q with hd | hd
    · rcases (show d = 0 ∨ d = 1 ∨ 2 ≤ d by omega) with rfl | rfl | hd2
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, he.1]
        simp only [norm_zero, zero_mul]
        positivity
      · rw [he1, pow_one, cq]
      · rw [he0 d hd2 hd]
        simp only [norm_zero, zero_mul]
        positivity
    · calc ‖coeff d e‖ * c ^ d ≤ 1 * c ^ d := by
            gcongr
            exact heI d
        _ = c ^ d := one_mul _
        _ ≤ c ^ q := pow_le_pow_of_le_one cpos.le cle hd
  have hpow : ∀ m k, ‖coeff k (e ^ m)‖ * c ^ k ≤ (c ^ q) ^ m :=
    Formalism.ELL.LogarithmWeight.coeff_pow_le cpos (by positivity) heB
  have hdiff : ∀ k, 2 ≤ k → ‖P‖ ≤ ‖P - P ^ k‖ := by
    intro k hk
    have hlt : ‖P ^ k‖ < ‖P‖ := by
      rw [norm_pow]
      exact pow_lt_self_of_lt_one₀ hp0 hp1 (by omega)
    have := IsUltrametricDist.norm_add_le_max (P - P ^ k) (P ^ k)
    rw [sub_add_cancel] at this
    rcases le_max_iff.mp this with h | h
    · exact h
    · exact absurd h (not_le.mpr hlt)
  have main : ∀ k, 1 ≤ k → ‖coeff k l‖ * c ^ k ≤ c := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
    intro hk
    rcases (show k = 1 ∨ 2 ≤ k by omega) with rfl | hk2
    · rw [hl.2.1]
      simp
    have hcoef := congrArg (coeff k) hle
    rw [Formalism.ELL.LogarithmWeight.coeff_subst_eq_sum he.1, Finset.sum_range_succ,
      Formalism.ELL.LogarithmWeight.coeff_pow_self he.1, he1, map_smul, smul_eq_mul] at hcoef
    have hS : coeff k l * (P - P ^ k) = ∑ m ∈ Finset.range k, coeff m l * coeff k (e ^ m) := by
      rw [mul_sub, mul_comm (coeff k l) P, ← hcoef]
      ring
    have hSb : ‖∑ m ∈ Finset.range k, coeff m l * coeff k (e ^ m)‖ * c ^ k ≤ c ^ q := by
      apply Formalism.ELL.LogarithmWeight.norm_sum_mul_le _ _ (pow_pos cpos k) (by positivity)
      intro m hm
      rw [Finset.mem_range] at hm
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hl.1]
        simp only [zero_mul, norm_zero]
        positivity
      · have h1 := ih m hm hm0
        have h2 := hpow m k
        rw [norm_mul]
        have hqm : q + m ≤ 1 + q * m := by nlinarith
        have key : ‖coeff m l‖ * ‖coeff k (e ^ m)‖ * c ^ k * c ^ m ≤ c ^ q * c ^ m := by
          calc ‖coeff m l‖ * ‖coeff k (e ^ m)‖ * c ^ k * c ^ m
              = (‖coeff m l‖ * c ^ m) * (‖coeff k (e ^ m)‖ * c ^ k) := by ring
            _ ≤ c * (c ^ q) ^ m := mul_le_mul h1 h2 (by positivity) cpos.le
            _ = c ^ (1 + q * m) := by rw [← pow_mul, ← pow_succ', add_comm]
            _ ≤ c ^ (q + m) := pow_le_pow_of_le_one cpos.le cle hqm
            _ = c ^ q * c ^ m := pow_add _ _ _
        exact le_of_mul_le_mul_right key (pow_pos cpos m)
    have : ‖coeff k l‖ * c ^ k * ‖P‖ ≤ c * ‖P‖ := by
      calc ‖coeff k l‖ * c ^ k * ‖P‖ ≤ ‖coeff k l‖ * c ^ k * ‖P - P ^ k‖ := by
            gcongr
            exact hdiff k hk2
        _ = ‖coeff k l * (P - P ^ k)‖ * c ^ k := by rw [norm_mul]; ring
        _ ≤ c ^ q := by rw [hS]; exact hSb
        _ = c * ‖P‖ := by rw [cq, mul_comm]
    exact le_of_mul_le_mul_right this hp0
  have hm := main n hn
  have hcn : 0 < c ^ n := pow_pos cpos n
  have hfin : ‖coeff n l‖ ≤ c / c ^ n := by
    rw [le_div_iff₀ hcn]
    exact hm
  refine hfin.trans (le_of_eq ?_)
  rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_sub hp0]
  congr 1
  ring

end Formalism.ELL

end
end
