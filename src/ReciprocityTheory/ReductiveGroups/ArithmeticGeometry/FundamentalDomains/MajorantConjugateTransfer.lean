module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealEmbeddingCharacters
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer
namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace MajorantConjugateTransfer

variable {r : ℕ} (X : Data E r)

theorem maj_transfer {x y : Frame X.Ψ r} (hx : x ∈ X.dom) (hy : y ∈ X.dom) (τ : X.Ψ)
    (g g' : Matrix (Fin r) (Fin r) ℂ) (hgg' : ∀ w, Matrix.mulVec g (Matrix.mulVec g' w) = w)
    (hiso : ∀ u v, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g v) = hermC τ.1 X.Gm u v)
    (H1 : ∀ c, ∃ K : Fin X.p0 → ℂ, Matrix.mulVec g (X.colP x τ c) = ∑ a, K a • X.colP y τ a)
    (H2 : ∀ a, ∃ L : Fin X.p0 → ℂ, X.colP y τ a = ∑ c, L c • Matrix.mulVec g (X.colP x τ c))
    (w : Fin r → ℂ) : X.maj y τ w = X.maj x τ (Matrix.mulVec g' w) := by
  have pp : ∀ (x' : Frame X.Ψ r) (v : Fin r → ℂ),
      X.posPart x' τ v = (hermC τ.1 X.Gm (X.ppos x' τ v) v).re := by
    intro x' v
    rw [X.hermC_ppos_self]
    rfl
  set u := Matrix.mulVec g' w with hu
  set p := Matrix.mulVec g (X.ppos x τ u) with hp
  set z := Matrix.mulVec g u with hz
  have hA : ∀ d : Fin r → ℂ, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) →
      ∀ c, hermC τ.1 X.Gm d (Matrix.mulVec g (X.colP x τ c)) = 0 := by
    intro d hd c
    obtain ⟨K, hK⟩ := H1 c
    rw [hK, hermC_sum_right]
    exact Finset.sum_eq_zero fun a _ => by rw [hermC_smul_right, hd, mul_zero]
  have hB : ∀ b, hermC τ.1 X.Gm z (X.colP y τ b) = hermC τ.1 X.Gm p (X.colP y τ b) := by
    intro b
    rw [← sub_eq_zero, ← hermC_sub_left]
    obtain ⟨L, hL⟩ := H2 b
    rw [hL, hermC_sum_right]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [hermC_smul_right, hz, hp, ← Matrix.mulVec_sub, hiso, hermC_sub_left,
      X.hermC_ppos_colP hx, sub_self, mul_zero]
  have h1 : X.ppos y τ z = X.ppos y τ p := by
    rw [X.ppos_eq, X.ppos_eq]
    simp only [hB]
  have h2 : ∀ c', hermC τ.1 X.Gm (X.ppos y τ p - p) (X.colP y τ c') = 0 := by
    intro c'
    rw [hermC_sub_left, X.hermC_ppos_colP hy, sub_self]
  have h3 : ∀ d, (∀ c', hermC τ.1 X.Gm d (X.colP y τ c') = 0) → hermC τ.1 X.Gm d p = 0 := by
    intro d hd
    rw [hp, X.ppos_eq x τ u, Matrix.mulVec_sum, hermC_sum_right]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Matrix.mulVec_smul, hermC_smul_right, hA d hd a, mul_zero]
  have key : hermC τ.1 X.Gm (X.ppos y τ z) z = hermC τ.1 X.Gm (X.ppos x τ u) u := by
    have e := h3 _ h2
    rw [hermC_sub_left, sub_eq_zero] at e
    rw [X.hermC_ppos_left hy τ z z, h1, ← X.hermC_ppos_left hy τ p p, e, hp, hiso,
      ← X.hermC_ppos_left hx τ u u]
  have hwz : w = z := (hgg' w).symm
  rw [hwz]
  simp only [Data.maj]
  rw [pp, pp, key, hz, hiso]

theorem maj_zero (x : Frame X.Ψ r) (τ : X.Ψ) : X.maj x τ 0 = 0 := by
  simp [Data.maj, Data.posPart, hermC_zero_left]

theorem maj_nonneg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj x τ v := by
  by_cases hv : v = 0
  · rw [hv, maj_zero X x τ]
  · exact (X.maj_pos hx τ hv).le

theorem Hf_sub_left (x : Frame X.Ψ r) (τ : X.Ψ) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u - u') w = X.Hf x τ u w - X.Hf x τ u' w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_sub, hermC_sub_left,
    hermC_sub_left]
  ring

theorem Hf_smul_left (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (k • u) w = k * X.Hf x τ u w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.ppos_smul_eq, hermC_smul_left, hermC_smul_left]
  ring

theorem Hf_sub_right (x : Frame X.Ψ r) (τ : X.Ψ) (u w w' : Fin r → ℂ) :
    X.Hf x τ u (w - w') = X.Hf x τ u w - X.Hf x τ u w' := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hermC_sub_right, hermC_sub_right]
  ring

theorem Hf_smul_right (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ u (k • w) = conj k * X.Hf x τ u w := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, hermC_smul_right, hermC_smul_right]
  ring

theorem Hf_conj {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf x τ u w) = X.Hf x τ w u := by
  rw [X.Hf_eq_two_ppos, X.Hf_eq_two_ppos, map_sub, map_mul, map_ofNat, hermC_conj _ X.Gm_herm,
    hermC_conj _ X.Gm_herm, X.ppos_selfadj hx τ w u]

theorem cs {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    ‖X.Hf x τ u v‖ ^ 2 ≤ X.maj x τ u * X.maj x τ v := by
  by_cases hv : v = 0
  · have h0 : X.Hf x τ u 0 = 0 := by
      have := Hf_sub_right X x τ u 0 0
      simpa using this
    rw [hv, h0, maj_zero X x τ]
    simp
  have hm : 0 < X.maj x τ v := X.maj_pos hx τ hv
  have hmu := maj_nonneg X hx τ u

  set H := X.Hf x τ u v with hH
  have hw := X.Hf_self hx τ ((X.maj x τ v : ℂ) • u - H • v)
  have hn := maj_nonneg X hx τ ((X.maj x τ v : ℂ) • u - H • v)
  simp only [Hf_sub_left, Hf_sub_right, Hf_smul_left, Hf_smul_right] at hw
  rw [X.Hf_self hx τ u, X.Hf_self hx τ v, ← Hf_conj X hx τ u v, ← hH, Complex.conj_ofReal] at hw
  have hHH : H * conj H = (Complex.normSq H : ℂ) := Complex.mul_conj H
  have e : ((X.maj x τ ((X.maj x τ v : ℂ) • u - H • v) : ℝ) : ℂ) =
      ((X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) : ℝ) : ℂ) := by
    rw [← hw]
    push_cast
    linear_combination (-(X.maj x τ v : ℂ)) * hHH
  have e' := Complex.ofReal_injective e
  rw [e'] at hn
  have hle : Complex.normSq H ≤ X.maj x τ v * X.maj x τ u := by
    by_contra hc
    push_neg at hc
    have : X.maj x τ v * (X.maj x τ v * X.maj x τ u - Complex.normSq H) < 0 :=
      mul_neg_of_pos_of_neg hm (by linarith)
    linarith
  rw [Complex.sq_norm]
  linarith [mul_comm (X.maj x τ u) (X.maj x τ v)]

end MajorantConjugateTransfer

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentCoefficientShift
namespace ReciprocityTheory.ChartRestriction.G.FD

namespace UnipotentCoefficientShift

open NumberField Complex
open scoped ComplexConjugate ComplexOrder

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_zero_of_conj_lt_one {a : E} (ha : IsIntegral ℤ a) (h : ∀ σ : E →+* ℂ, ‖σ a‖ < 1) :
    a = 0 := by
  classical
  by_contra ha0
  have hint : IsIntegral ℤ (Algebra.norm ℚ a) := Algebra.isIntegral_norm ℚ ha
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hN : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.mpr ha0
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hN
    rw [← hn, map_zero]
  have hne : (Finset.univ : Finset (E →ₐ[ℚ] ℂ)).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff, AlgHom.card]
    exact Module.finrank_pos
  have hlt : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ < ∏ _σ : E →ₐ[ℚ] ℂ, (1 : ℝ) :=
    Finset.prod_lt_prod_of_nonempty₀
      (fun σ _ => norm_pos_iff.mpr ((map_ne_zero σ).mpr ha0))
      (fun σ _ => h (σ : E →+* ℂ)) hne
  rw [Finset.prod_const_one, ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ a, ← hn] at hlt
  have h1 : ‖((n : ℚ) : ℂ)‖ < 1 := by simpa using hlt
  have h2 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hn0
  have h3 : ‖((n : ℚ) : ℂ)‖ = |(n : ℝ)| := by
    rw [Rat.cast_intCast, Complex.norm_intCast]
  linarith

variable {r : ℕ} {X : Data E r}

theorem Hf_add_left (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ (u + v) w = X.Hf z τ u w + X.Hf z τ v w := by
  simp only [Data.Hf, Data.ppos_add, smul_add, hermC_sub_left, hermC_add_left, hermC_smul_left]
  ring

theorem Hf_sub_left (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ (u - v) w = X.Hf z τ u w - X.Hf z τ v w := by
  simp only [Data.Hf, Data.ppos_sub, smul_sub, hermC_sub_left, hermC_smul_left]
  ring

private lemma ppos_smul' (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u : Fin r → ℂ) :
    X.ppos z τ (k • u) = k • X.ppos z τ u := by
  simp only [Data.ppos, hermC_smul_left, Finset.smul_sum, smul_smul, Finset.mul_sum, mul_assoc]

theorem Hf_smul_left (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf z τ (k • u) w = k * X.Hf z τ u w := by
  simp only [Data.Hf, ppos_smul', smul_comm (2 : ℂ) k, hermC_sub_left, hermC_smul_left]
  ring

theorem Hf_add_right (z : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf z τ u (v + w) = X.Hf z τ u v + X.Hf z τ u w := by
  simp only [Data.Hf, hermC_add_right]

theorem Hf_smul_right (z : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf z τ u (k • w) = conj k * X.Hf z τ u w := by
  simp only [Data.Hf, hermC_smul_right]

theorem Hf_conj {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (u w : Fin r → ℂ) :
    conj (X.Hf z τ u w) = X.Hf z τ w u := by
  have key : hermC τ.1 X.Gm w (X.ppos z τ u) = hermC τ.1 X.Gm (X.ppos z τ w) u := by
    rw [← hermC_conj τ.1 X.Gm_herm (X.ppos z τ u) w, X.hermC_ppos_left hz τ u w,
      hermC_conj τ.1 X.Gm_herm, X.hermC_ppos_left hz τ w u]
  simp only [Data.Hf]
  rw [hermC_conj τ.1 X.Gm_herm, hermC_sub_right, hermC_smul_right, hermC_sub_left, hermC_smul_left,
    key, map_ofNat]

private lemma maj_nonneg_of_mem_dom {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    0 ≤ X.maj z τ v := by
  rcases eq_or_ne v 0 with h | h
  · subst h
    simp [Data.maj, Data.posPart, hermC]
  · exact (X.maj_pos hz τ h).le

theorem norm_hermC_le_maj {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    ‖hermC τ.1 X.Gm v v‖ ≤ X.maj z τ v := by
  have hv : v = X.ppos z τ v + (v - X.ppos z τ v) := by abel
  have hPq : X.ppos z τ (v - X.ppos z τ v) = 0 := by
    rw [Data.ppos_sub, X.ppos_ppos hz, sub_self]
  have hpq : hermC τ.1 X.Gm (X.ppos z τ v) (v - X.ppos z τ v) = 0 := by
    rw [hermC_sub_right, X.hermC_ppos_left hz τ v v, sub_self]
  have hqp : hermC τ.1 X.Gm (v - X.ppos z τ v) (X.ppos z τ v) = 0 := by
    rw [← hermC_conj τ.1 X.Gm_herm (X.ppos z τ v) (v - X.ppos z τ v), hpq, map_zero]
  have hA : X.Hf z τ (X.ppos z τ v) (X.ppos z τ v) = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) := by
    rw [Data.Hf, X.ppos_ppos hz, two_smul, add_sub_cancel_right]
  have hB : X.Hf z τ (v - X.ppos z τ v) (v - X.ppos z τ v) =
      -hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    rw [Data.Hf, hPq, smul_zero, hermC_sub_left, hermC_zero_left, zero_sub]
  have hV : X.Hf z τ v v = 2 * hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) - hermC τ.1 X.Gm v v := by
    rw [Data.Hf, hermC_sub_left, hermC_smul_left, X.hermC_ppos_left hz τ v v]
  have hvv : hermC τ.1 X.Gm v v = hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) +
      hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) := by
    conv_lhs => rw [hv]
    rw [hermC_add_left, hermC_add_right, hermC_add_right, hpq, hqp]
    ring
  have eA : hermC τ.1 X.Gm (X.ppos z τ v) (X.ppos z τ v) = (X.maj z τ (X.ppos z τ v) : ℂ) := by
    rw [← hA]; exact X.Hf_self hz τ _
  have eB : hermC τ.1 X.Gm (v - X.ppos z τ v) (v - X.ppos z τ v) = -(X.maj z τ (v - X.ppos z τ v) : ℂ) := by
    rw [← X.Hf_self hz τ, hB, neg_neg]
  have eC : ((X.maj z τ v : ℝ) : ℂ) = ((X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [← X.Hf_self hz τ, hV, hvv, eA, eB]
    push_cast
    ring
  have eC' : X.maj z τ v = X.maj z τ (X.ppos z τ v) + X.maj z τ (v - X.ppos z τ v) := by
    exact_mod_cast eC
  have ha := maj_nonneg_of_mem_dom hz τ (X.ppos z τ v)
  have hb := maj_nonneg_of_mem_dom hz τ (v - X.ppos z τ v)
  have e : hermC τ.1 X.Gm v v = ((X.maj z τ (X.ppos z τ v) - X.maj z τ (v - X.ppos z τ v) : ℝ) : ℂ) := by
    rw [hvv, eA, eB]
    push_cast
    ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, eC']
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

theorem maj_smul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj z τ ((k : ℂ) • v) = k ^ 2 * X.maj z τ v := by
  have hS : (∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm ((k : ℂ) • v) (col (mat z τ) (Fin.castLE X.p0_le b)))) =
      ((k ^ 2 : ℝ) : ℂ) * ∑ a : Fin X.p0, ∑ b : Fin X.p0,
        hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le a)) * (X.gramPos z τ)⁻¹ a b *
          conj (hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b))) := by
    simp only [hermC_smul_left, map_mul, Complex.conj_ofReal, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have hh : hermC τ.1 X.Gm ((k : ℂ) • v) ((k : ℂ) • v) = ((k ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_left, hermC_smul_right, Complex.conj_ofReal]
    push_cast
    ring
  simp only [Data.maj, Data.posPart]
  rw [hS, hh, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem coef_shift (z : Frame X.Ψ r) (τ : X.Ψ) (u e : Fin r → ℂ) (c : ℂ) (he : X.Hf z τ e e ≠ 0) :
    X.Hf z τ (u + c • e) e / X.Hf z τ e e = X.Hf z τ u e / X.Hf z τ e e + c := by
  rw [Hf_add_left, Hf_smul_left, add_div, mul_div_assoc, div_self he, mul_one]

theorem ucomp_shift (z : Frame X.Ψ r) (τ : X.Ψ) (u e : Fin r → ℂ) (c : ℂ) (he : X.Hf z τ e e ≠ 0) :
    (u + c • e) - (X.Hf z τ (u + c • e) e / X.Hf z τ e e) • e =
      u - (X.Hf z τ u e / X.Hf z τ e e) • e := by
  rw [coef_shift z τ u e c he, add_smul]
  abel

theorem maj_decomp {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v e : Fin r → ℂ)
    (he : X.Hf z τ e e ≠ 0) :
    X.maj z τ v = X.maj z τ (v - (X.Hf z τ v e / X.Hf z τ e e) • e) +
      ‖X.Hf z τ v e / X.Hf z τ e e‖ ^ 2 * X.maj z τ e := by
  set K := X.Hf z τ v e / X.Hf z τ e e with hKdef
  have hK : K * X.Hf z τ e e = X.Hf z τ v e := div_mul_cancel₀ _ he
  have h1 : X.Hf z τ (v - K • e) e = 0 := by
    rw [Hf_sub_left, Hf_smul_left, hK, sub_self]
  have h2 : X.Hf z τ e (v - K • e) = 0 := by
    rw [← Hf_conj hz τ (v - K • e) e, h1, map_zero]
  have hv : v = (v - K • e) + K • e := (sub_add_cancel v (K • e)).symm
  have hexp : X.Hf z τ v v = X.Hf z τ (v - K • e) (v - K • e) + K * conj K * X.Hf z τ e e := by
    conv_lhs => rw [hv]
    rw [Hf_add_left, Hf_add_right, Hf_add_right, Hf_smul_left, Hf_smul_left, Hf_smul_right,
      Hf_smul_right, h1, h2]
    ring
  rw [X.Hf_self hz, X.Hf_self hz, X.Hf_self hz, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hexp
  exact_mod_cast hexp

end UnipotentCoefficientShift

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMeanContinuity
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
  ReciprocityTheory.ChartRestriction.G.FD.AdmissibleHermitianColumns ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma mean_smul {α : Type*} [MeasurableSpace α] (μ : Measure α) (c : ENNReal) (hc0 : c ≠ 0)
    (hct : c ≠ ⊤) (s : Set α) (F : α → ℂ) :
    (((c • μ) s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂(c • μ) = ((μ s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂μ := by
  have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩
  have hc' : ((c.toReal : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [Measure.restrict_smul, integral_smul_measure, Measure.smul_apply, smul_eq_mul,
    ENNReal.toReal_mul, Complex.ofReal_mul, mul_inv, Complex.real_smul]
  calc _ = ((μ s).toReal : ℂ)⁻¹ * (∫ y in s, F y ∂μ) *
        (((c.toReal : ℝ) : ℂ)⁻¹ * ((c.toReal : ℝ) : ℂ)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hc', mul_one]

lemma mean_haar {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
    [MeasurableSpace G] [BorelSpace G] (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (s : Set G) (F : G → ℂ) :
    ((μ s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂μ = ((ν s).toReal : ℂ)⁻¹ * ∫ y in s, F y ∂ν := by
  haveI : ProperSpace G := FiniteDimensional.proper_real G
  have h := Measure.isAddLeftInvariant_eq_smul ν μ
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν μ
  rw [h, ENNReal.smul_def]
  exact (mean_smul μ _ (ENNReal.coe_ne_zero.mpr hpos.ne') ENNReal.coe_ne_top s F).symm

variable (X : Data E r) (la : Wt X.Ψ r)

noncomputable def fjI (ξ : Fin r → E) (ν : X.Ψ → ℝ) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r)
    (s : X.Ψ → ℝ) : ℂ :=
  P (X.flow ξ (fun τ => (s τ : ℂ)) x) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)

lemma flow_differentiable (ξ : Fin r → E) (x : Frame X.Ψ r) :
    Differentiable ℂ (fun s : X.Ψ → ℂ => X.flow ξ s x) := by
  rw [differentiable_pi]
  intro τ
  rw [differentiable_pi]
  intro a
  rw [differentiable_pi]
  intro b
  intro s
  simp only [Data.flow, Matrix.mul_apply, Data.flowMat, Matrix.of_apply, mat]
  refine DifferentiableAt.fun_sum fun k _ => ?_
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_sub
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.mul_const
  apply DifferentiableAt.const_mul
  exact (differentiable_apply τ) s

lemma fjI_continuous (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E}
    (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    Continuous (fjI X ξ ν P x) := by
  have hflow0 : X.flow ξ (fun _ => (0 : ℂ)) x = x := by
    funext τ
    change X.flowMat ξ τ 0 * mat x τ = x τ
    rw [flowMat_eq]
    simp only [mul_zero, neg_zero, zero_smul, add_zero, one_mul]
    rfl
  have hmaps : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := by
    intro s
    have h0 := (flow_mem_dom_iff (X := X) hξ x hx (fun _ => (0 : ℂ))).mp (by rw [hflow0]; exact hx)
    rw [flow_mem_dom_iff (X := X) hξ x hx]
    simpa using h0
  have hc1 : Continuous (fun s : X.Ψ → ℝ => X.flow ξ (fun τ => (s τ : ℂ)) x) :=
    (flow_differentiable X ξ x).continuous.comp
      (continuous_pi fun τ => Complex.continuous_ofReal.comp (continuous_apply τ))
  have hc2 : Continuous (fun s : X.Ψ → ℝ => P (X.flow ξ (fun τ => (s τ : ℂ)) x)) :=
    hP.1.continuousOn.comp_continuous hc1 hmaps
  unfold fjI
  exact hc2.mul (by fun_prop)

lemma fjI_periodic (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E} (hξΛ : ξ ∈ X.Λ)
    (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ)
    (hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (p : X.Ψ → ℝ) (hp : p ∈ X.periods la) (s : X.Ψ → ℝ) :
    fjI X ξ ν P x (p + s) = fjI X ξ ν P x s := by
  have hflow0 : X.flow ξ (fun _ => (0 : ℂ)) x = x := by
    funext τ
    change X.flowMat ξ τ 0 * mat x τ = x τ
    rw [flowMat_eq]
    simp only [mul_zero, neg_zero, zero_smul, add_zero, one_mul]
    rfl
  have hmaps : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := by
    intro s
    have h0 := (flow_mem_dom_iff (X := X) hξ x hx (fun _ => (0 : ℂ))).mp (by rw [hflow0]; exact hx)
    rw [flow_mem_dom_iff (X := X) hξ x hx]
    simpa using h0
  have hadd : X.flow ξ (fun τ => (((p + s) τ : ℝ) : ℂ)) x =
      X.flow ξ (cR X p) (X.flow ξ (fun τ => (s τ : ℂ)) x) := by
    funext τ
    change X.flowMat ξ τ _ * mat x τ = X.flowMat ξ τ _ * mat (X.flow ξ _ x) τ
    rw [mat_flow, ← mul_assoc, flowMat_mul (X := X) hξ]
    congr 2
    simp [cR]
  unfold fjI
  rw [hadd, sec_periodic (X := X) la P hP hξΛ hξ hp _ (hmaps s)]
  congr 1
  obtain ⟨k, hk⟩ := hν p hp
  have hsplit : ∑ τ, (ν τ : ℂ) * (((p + s) τ : ℝ) : ℂ) =
      ∑ τ, (ν τ : ℂ) * (p τ : ℂ) + ∑ τ, (ν τ : ℂ) * (s τ : ℂ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Pi.add_apply]
    push_cast
    ring
  rw [hsplit, mul_add, Complex.exp_add]
  have hk' : cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * (p τ : ℂ)) = 1 := by
    have h1 : ∑ τ, (ν τ : ℂ) * (p τ : ℂ) = (k : ℂ) / 2 := by
      have h2 := congrArg (fun t : ℝ => (t : ℂ)) hk
      push_cast at h2
      linear_combination h2 / 2
    rw [h1, show -(4 * (Real.pi : ℂ) * I) * ((k : ℂ) / 2) = ((-k : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I (-k)
  rw [hk', one_mul]

lemma exists_basis : ∃ ω : Module.Basis (Fin (Fintype.card X.Ψ)) ℝ (X.Ψ → ℝ),
    Submodule.span ℤ (Set.range ω) = perL X la := by
  classical
  let b := Module.Free.chooseBasis ℤ (perL X la)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (perL X la)) = Fintype.card X.Ψ := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, perL_rank]
  refine ⟨(b.ofZLatticeBasis ℝ (perL X la)).reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

theorem fj_eq_fourCoeff (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) {n : ℕ} (ω : Module.Basis (Fin n) ℝ (X.Ψ → ℝ))
    (hω : Submodule.span ℤ (Set.range ω) = perL X la) (ν : X.Ψ → ℝ) (k : Fin n → ℤ)
    (hk : ∀ j, 2 * ∑ τ, ν τ * ω j τ = k j) :
    X.fj la ξ ν P x = ReciprocityTheory.L2DbarEstimates.Y.fourCoeff
      (fun t => P (X.flow ξ (fun τ => ∑ j, t j * (ω j τ : ℂ)) x)) 0 k := by
  classical

  have hper : X.periods la = (Submodule.span ℤ (Set.range ω)).toAddSubgroup := by
    rw [hω]
    rfl
  have hcond : ∀ p ∈ X.periods la, ∃ k' : ℤ, 2 * ∑ τ, ν τ * p τ = k' := by
    intro p hp
    rw [hper] at hp
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
    refine ⟨∑ j, c j * k j, ?_⟩
    have hc : ∀ τ, (∑ j, c j • ω j) τ = ∑ j, (c j : ℝ) * ω j τ := fun τ => by
      simp [Finset.sum_apply, zsmul_eq_mul]
    simp only [hc]
    push_cast
    simp only [← hk, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hF0 : IsAddFundamentalDomain (X.periods la) (ZSpan.fundamentalDomain ω) volume := by
    rw [hper]
    exact ZSpan.isAddFundamentalDomain ω volume
  have hex : ∃ D : Set (X.Ψ → ℝ), MeasurableSet D ∧ IsAddFundamentalDomain (X.periods la) D volume ∧
      0 < volume D ∧ volume D < ⊤ :=
    ⟨_, ZSpan.fundamentalDomain_measurableSet ω, hF0,
      pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero ω),
      (ZSpan.fundamentalDomain_isBounded ω).measure_lt_top⟩
  have hcount : ((X.periods la : Set (X.Ψ → ℝ))).Countable :=
    (Set.countable_range (fun c : Fin n → ℤ => ∑ j, c j • ω j)).mono fun p hp => by
      rw [hper] at hp
      exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp hp
  haveI : Countable (X.periods la) := hcount.to_subtype
  unfold Data.fj
  rw [if_pos hcond, dite_eq_left hex]
  obtain ⟨-, hD, -, -⟩ := hex.choose_spec
  show ((volume hex.choose).toReal : ℂ)⁻¹ * ∫ s in hex.choose, fjI X ξ ν P x s = _

  rw [hD.measure_eq hF0, hD.setIntegral_eq hF0 (f := fjI X ξ ν P x)
    (fun g s => fjI_periodic X la P hP hξ.1 hξ.2.1 ν hcond hx g g.2 s)]

  set T := ω.equivFunL.symm with hTdef
  haveI : (Measure.map T volume).IsAddHaarMeasure := T.isAddHaarMeasure_map volume
  rw [mean_haar volume (Measure.map T volume) (ZSpan.fundamentalDomain ω) (fjI X ξ ν P x)]
  have hmp : MeasurePreserving T volume (Measure.map T volume) :=
    T.continuous.measurable.measurePreserving volume
  have hemb : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  rw [← hmp.setIntegral_preimage_emb hemb _ (ZSpan.fundamentalDomain ω),
    Measure.map_apply T.continuous.measurable (ZSpan.fundamentalDomain_measurableSet ω)]
  have hpre : T ⁻¹' ZSpan.fundamentalDomain ω = Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1) := by
    ext t
    have hTt : T t = ω.equivFun.symm t := rfl
    have hrep : ∀ i, ω.repr (ω.equivFun.symm t) i = t i := fun i => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [Set.mem_preimage, ZSpan.mem_fundamentalDomain, Set.mem_univ_pi, hTt]
    simp only [hrep]
  have hvol : volume (Set.univ.pi (fun _ : Fin n => Set.Ico (0 : ℝ) 1)) = 1 := by
    rw [Real.volume_pi_Ico]
    simp
  have hae : (Set.univ.pi fun _ : Fin n => Set.Ico (0 : ℝ) 1) =ᵐ[volume]
      (Set.univ.pi fun _ : Fin n => Set.Ioc (0 : ℝ) 1) := by
    rw [MeasureTheory.volume_pi]
    exact Measure.univ_pi_Ico_ae_eq_Icc.trans Measure.univ_pi_Ioc_ae_eq_Icc.symm
  rw [hpre, hvol, ENNReal.toReal_one, Complex.ofReal_one, inv_one, one_mul,
    setIntegral_congr_set hae]
  unfold ReciprocityTheory.L2DbarEstimates.Y.fourCoeff
  congr 1
  funext t
  have hT : ∀ τ, (T t) τ = ∑ j, t j * ω j τ := fun τ => by
    rw [show T t = ω.equivFun.symm t from rfl, Module.Basis.equivFun_symm_apply, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have hk' : ∀ j, (k j : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * (ω j τ : ℂ) := fun j => by
    have h2 := congrArg (fun r : ℝ => (r : ℂ)) (hk j)
    push_cast at h2
    exact h2.symm
  unfold fjI
  simp only [hT, Pi.zero_apply, Complex.ofReal_zero, zero_mul, add_zero, hk']
  push_cast
  congr 1
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end ReciprocityTheory.ChartRestriction.G.FD.FlowMeanContinuity
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds
section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RingOfIntegersCovering
namespace ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering

open NumberField InfinitePlace Module Submodule TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cover_OE (Z : VS E) :
    ∃ α : 𝓞 E, ‖Z - iota E (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
  set f : ℝ := (Fintype.card (CP E) : ℝ) with hf_def
  have hf : 0 < f := Nat.cast_pos.mpr card_complexPlaces_pos
  set D := dE E with hD_def
  have hD : 0 < D := dE_pos
  set t := D ^ (1 / f) with ht_def
  have ht : 0 < t := Real.rpow_pos_of_pos hD _
  have htinv : D ^ (-(1 / f)) = t⁻¹ := Real.rpow_neg hD.le _
  set lam := Real.sqrt (4 * f * t⁻¹) with hlam_def
  have hlam : 0 < lam := Real.sqrt_pos.mpr (by positivity)
  have hlam2 : lam ^ 2 = 4 * f * t⁻¹ := Real.sq_sqrt (by positivity)
  have hmin : ∀ x ∈ span ℤ (Set.range (bd E)), x ≠ 0 → lam ≤ ‖x‖ := by
    intro x hx hx0
    have hnorm := norm_bd_ge x hx hx0
    rw [← hf_def, ← hD_def, htinv] at hnorm
    rw [hlam_def, ← Real.sqrt_sq (norm_nonneg x)]
    exact Real.sqrt_le_sqrt hnorm
  obtain ⟨x, hx, hxb⟩ := BabaiCovering.cover (bas E) (bd E) inner_bas_bd lam hlam hmin Z
  obtain ⟨α, rfl⟩ := mem_span_bas hx
  refine ⟨α, ?_⟩
  have hn : (finrank ℝ (VS E) : ℝ) = 2 * f := by
    rw [finrank_VS, (card_CP (E := E)).2]
    push_cast
    ring
  have hfdeg : (fdeg E : ℝ) = f := by rw [← (card_CP (E := E)).1]
  have hrd : rdE E ^ 2 = t := by
    rw [rdE, ← hD_def, (card_CP (E := E)).2, ← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1
    push_cast
    rw [← hf_def]
    field_simp
  rw [hn] at hxb
  have hbound : (2 * f) / 4 * ((2 * f) ^ 2 / lam) ^ 2 = 2 * f ^ 4 * t := by
    rw [div_pow, hlam2]
    field_simp
    ring
  rw [hbound] at hxb
  have hB : 0 ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have : 0 ≤ rdE E := Real.rpow_nonneg (abs_nonneg _) _
    positivity
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hB (by norm_num : (2 : ℕ) ≠ 0)]
  calc ‖Z - iota E (α : E)‖ ^ 2 ≤ 2 * f ^ 4 * t := hxb
    _ ≤ 4 * f ^ 4 * t := by nlinarith [pow_pos hf 4]
    _ = (2 * (fdeg E : ℝ) ^ 2 * rdE E) ^ 2 := by
        rw [mul_pow, mul_pow, hrd, hfdeg]
        ring

end ReciprocityTheory.ChartRestriction.G.FD.RingOfIntegersCovering
end

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField InfinitePlace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem integerApproximationCount_holds : IntegerApproximationCount (E := E) := by
  intro r X
  refine ⟨fun w' => ?_, fun R hR => PackingSeparation.count R hR⟩
  classical
  have hconjmem : ∀ φ : E →+* ℂ, φ ∉ X.Ψ → ComplexEmbedding.conjugate φ ∈ X.Ψ := by
    intro φ h
    have := X.cmType (ComplexEmbedding.conjugate φ)
    rw [TraceIntegralBasis.conj_conj] at this
    exact this.mpr h
  let Z : TraceIntegralBasis.VS E := WithLp.toLp 2 (fun w : TraceIntegralBasis.CP E =>
    if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
    else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩))
  obtain ⟨α, hα⟩ := RingOfIntegersCovering.cover_OE Z
  refine ⟨α, fun τ => ?_⟩
  set w : TraceIntegralBasis.CP E := ⟨InfinitePlace.mk τ.1, IsTotallyComplex.isComplex _⟩ with hw
  have hcoord : ‖Z w - w.1.embedding (α : E)‖ ≤ 2 * (fdeg E : ℝ) ^ 2 * rdE E := by
    have h := PiLp.norm_apply_le (Z - TraceIntegralBasis.iota E (α : E)) w
    rw [PiLp.sub_apply, TraceIntegralBasis.iota_apply] at h
    exact h.trans hα
  have hZw : Z w = if h : w.1.embedding ∈ X.Ψ then w' ⟨w.1.embedding, h⟩
      else conj (w' ⟨ComplexEmbedding.conjugate w.1.embedding, hconjmem _ h⟩) := rfl
  have hmk : InfinitePlace.mk w.1.embedding = InfinitePlace.mk τ.1 := mk_embedding _
  rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
  · have hmem : w.1.embedding ∈ X.Ψ := h ▸ τ.2
    have hZ : Z w = w' τ := by
      rw [hZw, dite_eq_left hmem]
      congr 1
      exact Subtype.ext h
    rw [hZ, h] at hcoord
    rwa [norm_sub_rev] at hcoord
  · have hnot : w.1.embedding ∉ X.Ψ := by
      intro hm
      exact ((X.cmType _).mp hm) (h ▸ τ.2)
    have hZ : Z w = conj (w' τ) := by
      rw [hZw, dite_eq_right hnot]
      congr 2
      exact Subtype.ext h
    have hemb : w.1.embedding (α : E) = conj (τ.1 (α : E)) := by
      rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]
    rw [hZ, hemb, ← map_sub, Complex.norm_conj] at hcoord
    rwa [norm_sub_rev] at hcoord

end ReciprocityTheory.ChartRestriction.G.FD
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowMajorantFlags
namespace ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem Hf_sub_left (x : Frame X.Ψ r) (τ : X.Ψ) (u v w : Fin r → ℂ) :
    X.Hf x τ (u - v) w = X.Hf x τ u w - X.Hf x τ v w := by
  simp only [Data.Hf_eq_jp, Data.jp_sub, hermC_sub_left]

theorem Hf_smul_left (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ (k • u) w = k * X.Hf x τ u w := by
  simp only [Data.Hf_eq_jp, Data.jp_smul, hermC_smul_left]

theorem Hf_smul_right (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u w : Fin r → ℂ) :
    X.Hf x τ u (k • w) = conj k * X.Hf x τ u w := by
  simp only [Data.Hf_eq_jp, hermC_smul_right]

theorem maj_smul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((k : ℂ) • v) = k ^ 2 * X.maj x τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hx τ, Hf_smul_left, Hf_smul_right, X.Hf_self hx τ, Complex.conj_ofReal]
  push_cast; ring

theorem ppos_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.ppos z' τ v = X.ppos z τ v := by
  have hspan := hf τ
  have hmem : X.ppos z τ v ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z' τ) (Fin.castLE X.p0_le a)) := by
    rw [← hspan]
    unfold Data.ppos
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  rw [← hβ]
  apply X.ppos_eq_of z' τ (X.gramPos_det_ne hz' τ) v β
  intro b
  rw [hβ]
  have hb : col (mat z' τ) (Fin.castLE X.p0_le b) ∈ Submodule.span ℂ
      (Set.range fun a : Fin X.p0 => col (mat z τ) (Fin.castLE X.p0_le a)) := by
    rw [hspan]; exact Submodule.subset_span ⟨b, rfl⟩
  obtain ⟨γ, hγ⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hb
  rw [← hγ, hermC_sum_right]
  exact Finset.sum_eq_zero fun a _ => by
    rw [hermC_smul_right, X.ppos_orth z τ (X.gramPos_det_ne hz τ) v a, mul_zero]

theorem Hf_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (u w : Fin r → ℂ) : X.Hf z' τ u w = X.Hf z τ u w := by
  simp only [Data.Hf, ppos_flag X hz hz' hf]

theorem maj_flag {z z' : Frame X.Ψ r} (hz : z ∈ X.dom) (hz' : z' ∈ X.dom) (hf : X.SameFlag z z')
    (τ : X.Ψ) (v : Fin r → ℂ) : X.maj z' τ v = X.maj z τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hz' τ, ← X.Hf_self hz τ, Hf_flag X hz hz' hf]

theorem flowMatV_mulVec (e : Fin r → ℂ) (τ : X.Ψ) (s : ℂ) (v : Fin r → ℂ) :
    Matrix.mulVec (X.flowMatV e τ s) v = v + (-(I * X.c τ * s) * hermC τ.1 X.Gm v e) • e := by
  funext a
  simp only [Data.flowMatV, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hermC, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sub_eq_add_neg]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem ppos_flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.ppos (X.flowV e s z) τ v = X.ppos z τ v := by
  have hcol : ∀ a, col (mat (X.flowV e s z) τ) a =
      Matrix.mulVec (X.flowMatV (e τ) τ (s τ)) (col (mat z τ) a) :=
    fun a => Data.col_mul (X.flowMatV (e τ) τ (s τ)) (mat z τ) a
  have hT := flowMatV_mulVec X (e τ) τ (s τ)
  set β : Fin X.p0 → ℂ := fun a => ∑ b, hermC τ.1 X.Gm v (col (mat z τ) (Fin.castLE X.p0_le b)) *
    (X.gramPos z τ)⁻¹ b a with hβ
  have hp : X.ppos z τ v = ∑ a, β a • col (mat z τ) (Fin.castLE X.p0_le a) := rfl
  have hcoef : ∑ a, β a * (-(I * X.c τ * s τ) *
      hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) = 0 := by
    have : ∑ a, β a * (-(I * X.c τ * s τ) *
        hermC τ.1 X.Gm (col (mat z τ) (Fin.castLE X.p0_le a)) (e τ)) =
        -(I * X.c τ * s τ) * hermC τ.1 X.Gm (X.ppos z τ v) (e τ) := by
      rw [hp, hermC_sum_left, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hermC_smul_left]; ring
    rw [this, hpe, mul_zero]
  have hsum : ∑ a, β a • col (mat (X.flowV e s z) τ) (Fin.castLE X.p0_le a) = X.ppos z τ v := by
    simp only [hcol, hT, smul_add, Finset.sum_add_distrib, smul_smul]
    rw [← hp, ← Finset.sum_smul, hcoef, zero_smul, add_zero]
  rw [← hsum]
  apply X.ppos_eq_of _ τ (X.gramPos_det_ne hTz τ) v β
  intro b
  rw [hsum, hcol, hT, hermC_add_right, hermC_smul_right,
    X.ppos_orth z τ (X.gramPos_det_ne hz τ) v b, zero_add, hermC_sub_left, hve, hpe, sub_zero,
    mul_zero]

theorem maj_flowV (e : X.Ψ → Fin r → ℂ) (s : X.Ψ → ℂ) {z : Frame X.Ψ r} (hz : z ∈ X.dom)
    (hTz : X.flowV e s z ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ)
    (hve : hermC τ.1 X.Gm v (e τ) = 0) (hpe : hermC τ.1 X.Gm (X.ppos z τ v) (e τ) = 0) :
    X.maj (X.flowV e s z) τ v = X.maj z τ v := by
  apply Complex.ofReal_injective
  rw [← X.Hf_self hTz τ, ← X.Hf_self hz τ]
  simp only [Data.Hf, ppos_flowV X e s hz hTz τ v hve hpe]

theorem hpe_of {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (v e : Fin r → ℂ)
    (hH : X.Hf z τ e v = 0) (hh : hermC τ.1 X.Gm e v = 0) :
    hermC τ.1 X.Gm (X.ppos z τ v) e = 0 := by
  have h1 : hermC τ.1 X.Gm (X.ppos z τ e) v = 0 := by
    rw [Data.Hf_eq_two_ppos, hh, sub_zero] at hH
    simpa using hH
  rw [X.ppos_selfadj hz, ← hermC_conj τ.1 X.Gm_herm, h1, map_zero]

end ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UMatUpper
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

open NumberField Complex Matrix
open scoped ComplexConjugate

noncomputable section

variable {n : ℕ}

def blk (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : Matrix (Fin c) (Fin c) ℂ :=
  G.submatrix (Fin.castLE c.isLt.le) (Fin.castLE c.isLt.le)

def rowc (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) : Fin c → ℂ := fun m => G c (Fin.castLE c.isLt.le m)

def uMat (G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j c => if j = c then 1 else
    if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ else 0

lemma uMat_diag (G : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : uMat G j j = 1 := by
  simp [uMat]

lemma uMat_upper (G : Matrix (Fin n) (Fin n) ℂ) : (uMat G).BlockTriangular id := by
  intro i j hij
  simp only [id] at hij
  simp only [uMat, Matrix.of_apply]
  rw [if_neg (ne_of_gt hij), dif_neg (not_lt.2 hij.le)]

lemma uMat_term (G : Matrix (Fin n) (Fin n) ℂ) (c m j : Fin n) :
    uMat G j c * G j m = (if j = c then G c m else 0) +
      (if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ * G j m else 0) := by
  simp only [uMat, Matrix.of_apply]
  by_cases h1 : j = c
  · subst h1
    simp
  · by_cases h2 : j < c
    · simp [h1, h2]
    · simp [h1, h2]

lemma uT_G_zero (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n) (hdet : (blk G c).det ≠ 0) (m : Fin n)
    (hm : m < c) : ((uMat G)ᵀ * G) c m = 0 := by
  have hinv : IsUnit (blk G c).det := isUnit_iff_ne_zero.2 hdet
  have key : ∀ m' : Fin c, ∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * blk G c j' m' =
      rowc G c m' := by
    intro m'
    have h := congrFun (Matrix.vecMul_vecMul (rowc G c) (blk G c)⁻¹ (blk G c)) m'
    rw [Matrix.nonsing_inv_mul _ hinv, Matrix.vecMul_one] at h
    rw [← h]
    rfl
  let g : Fin n → ℂ := fun j =>
    if h : j < c then -(Matrix.vecMul (rowc G c) (blk G c)⁻¹) ⟨j, h⟩ * G j m else 0
  have hmain : ((uMat G)ᵀ * G) c m = G c m + ∑ j : Fin n, g j := by
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply, uMat_term, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rfl
  have hA : ∑ j' : Fin c, g (Fin.castLE c.isLt.le j') =
      -∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * G (Fin.castLE c.isLt.le j') m := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have h : Fin.castLE c.isLt.le j' < c := j'.isLt
    simp only [g, dif_pos h]
    exact neg_mul _ _
  have hB : ∑ j : Fin n, g j = ∑ j' : Fin c, g (Fin.castLE c.isLt.le j') := by
    rw [show (∑ j' : Fin c, g (Fin.castLE c.isLt.le j')) =
        ∑ x ∈ Finset.univ.map (Fin.castLEEmb c.isLt.le), g x from
      (Finset.sum_map Finset.univ (Fin.castLEEmb c.isLt.le) g).symm]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hjc : ¬ j < c := by
      intro hlt
      exact hj (Finset.mem_map.2 ⟨⟨j, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    simp only [g, dif_neg hjc]
  have k2 : ∑ j' : Fin c, Matrix.vecMul (rowc G c) (blk G c)⁻¹ j' * G (Fin.castLE c.isLt.le j') m =
      G c m := key ⟨m, hm⟩
  rw [hmain, hB, hA, k2]
  ring

end

end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
end
