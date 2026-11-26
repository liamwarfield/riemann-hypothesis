module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem rank_const_absorb {x : ℝ} (hx : 1 < x) (hK : (1000 : ℝ) ≤ x ^ ((1 : ℝ) / 1000)) {a b C : ℝ}
    (hC : C ≤ 1000) (hab : a + 1 / 1000 ≤ b) : C * x ^ a ≤ x ^ b := by
  have hx0 : 0 < x := by linarith
  calc C * x ^ a ≤ x ^ ((1 : ℝ) / 1000) * x ^ a :=
        mul_le_mul_of_nonneg_right (hC.trans hK) (Real.rpow_nonneg hx0.le _)
    _ = x ^ (a + 1 / 1000) := by rw [Real.rpow_add hx0, mul_comm]
    _ ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx.le hab

theorem rank_mul_le {x : ℝ} (hx : 0 < x) {u v a b : ℝ} (hv : 0 ≤ v) (hu : u ≤ x ^ a) (hv' : v ≤ x ^ b) :
    u * v ≤ x ^ (a + b) := by
  rw [Real.rpow_add hx]
  exact mul_le_mul hu hv' hv (Real.rpow_nonneg hx.le _)

theorem rank_basic_bounds : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.f : ℝ) ≤ s.x ^ (3 : ℝ) ∧ (R.m : ℝ) ≤ s.x ∧ (R.r : ℝ) ≤ s.x ^ (5 : ℝ) ∧ R.k ≤ R.r ∧ R.r ≤ 2 * R.k ∧ s.L ≤ s.x ∧ 1 ≤ s.L ∧ s.x ^ ((13 : ℝ) / 2) ≤ (R.f : ℝ) * R.r * s.L ∧ (R.f : ℝ) * R.r * s.L ≤ s.x ^ ((687 : ℝ) / 100) ∧ ((R.f * R.r.choose 2 : ℕ) : ℝ) ≤ s.x ^ (12 : ℝ) ∧ (R.k : ℝ) * R.f / R.m ≤ s.x ^ (7 : ℝ) ∧ ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) ∧ s.x ^ (377 : ℝ) ≤ (R.t : ℝ) ∧ (R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ (R.N R.m : ℝ) ≤ s.x ^ (402 : ℝ) ∧ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
  intro eps he0 he1
  refine ⟨(1000 : ℝ) ^ (1000 : ℝ), fun s R hs hx0 hR => ?_⟩
  have hn2 := RankVal.n_le hR
  obtain ⟨⟨hn1, -⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, ht⟩ := hR
  have hx := s.one_lt_alt
  have hxp : 0 < s.x := lt_trans one_pos hx
  have e0 := s.eps_pos
  have e1 := s.eps_lt
  have hK : (1000 : ℝ) ≤ s.x ^ ((1 : ℝ) / 1000) := by
    calc (1000 : ℝ) = ((1000 : ℝ) ^ (1000 : ℝ)) ^ ((1 : ℝ) / 1000) := by
          rw [← Real.rpow_mul (by norm_num)]; norm_num
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hx0 (by norm_num)
  clear hx0
  have ab : ∀ {a b C : ℝ}, C ≤ 1000 → a + 1 / 1000 ≤ b → C * s.x ^ a ≤ s.x ^ b :=
    fun hC hab => rank_const_absorb hx hK hC hab
  have mono : ∀ {a b : ℝ}, a ≤ b → s.x ^ a ≤ s.x ^ b :=
    fun h => Real.rpow_le_rpow_of_exponent_le hx.le h
  have one : ∀ {a : ℝ}, 0 ≤ a → 1 ≤ s.x ^ a := fun h => Real.one_le_rpow hx.le h
  have hsq : Real.sqrt (s.x * s.delta1) = s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
    have : s.x * s.delta1 = s.x ^ (1 + -(s.eps / 8)) := by
      rw [Real.rpow_add hxp, Real.rpow_one]; rfl
    rw [this, Real.sqrt_eq_rpow, ← Real.rpow_mul hxp.le]
    congr 1; ring
  rw [hsq] at hm1 hm2
  have h2m := R.two_le_m
  have hmk := R.m_add_three_le_k
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hrk : R.r ≤ 2 * R.k := by unfold Ranks.r; omega
  have hkr' : (R.k : ℝ) ≤ R.r := by exact_mod_cast hkr
  have hrk' : (R.r : ℝ) ≤ 2 * R.k := by exact_mod_cast hrk
  have hfn : (R.f : ℝ) = 2 * R.n := by unfold Ranks.f; push_cast; ring
  have hf : (R.f : ℝ) ≤ s.x ^ ((2156 : ℝ) / 1000) := by
    have := ab (C := 4) (a := 2 + 8 * s.eps + s.eps / 100) (b := 2156 / 1000) (by norm_num) (by linarith)
    linarith
  have hr : (R.r : ℝ) ≤ s.x ^ ((4694 : ℝ) / 1000) := by
    have := ab (C := 4) (a := 9 / 2 + 10 * s.eps) (b := 4694 / 1000) (by norm_num) (by linarith)
    linarith
  have hk : (R.k : ℝ) ≤ s.x ^ ((4694 : ℝ) / 1000) := hkr'.trans hr
  have hL : s.L ≤ s.x ^ ((20 : ℝ) / 1000) := mono (by linarith)
  have hL1 : 1 ≤ s.L := one e0.le
  have hmu : (R.m : ℝ) ≤ s.x ^ ((501 : ℝ) / 1000) := by
    have := ab (C := 2) (a := 1 / 2 - s.eps / 16) (b := 501 / 1000) (by norm_num) (by linarith)
    linarith
  have hmp : (0 : ℝ) < R.m := by exact_mod_cast (by omega : 0 < R.m)
  have hmi : (R.m : ℝ)⁻¹ ≤ s.x ^ (-(498 : ℝ) / 1000) := by
    have h1 : s.x ^ ((498 : ℝ) / 1000) ≤ R.m := (mono (by linarith)).trans hm1
    rw [neg_div, Real.rpow_neg hxp.le]
    exact inv_anti₀ (by positivity) h1
  have f0 : (0 : ℝ) ≤ R.f := by positivity
  have r0 : (0 : ℝ) ≤ R.r := by positivity
  have k0 : (0 : ℝ) ≤ R.k := by positivity
  have L0 : (0 : ℝ) ≤ s.L := by linarith
  have mi0 : (0 : ℝ) ≤ (R.m : ℝ)⁻¹ := by positivity
  have k1 : (1 : ℝ) ≤ R.k := by exact_mod_cast (by omega : 1 ≤ R.k)
  have hf1 : 1 ≤ R.f := by
    have : R.m ≤ R.f := R.m_le_f
    omega
  have hf1' : (1 : ℝ) ≤ R.f := by exact_mod_cast hf1
  have hfr := rank_mul_le hxp r0 hf hr

  have hB0 : 0 ≤ (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by
    have : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    positivity
  have hApos : 0 < 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8 := by
    have : (0 : ℝ) < R.r := by linarith
    have : (0 : ℝ) < (R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m := by linarith
    positivity
  have hW1 : 1 ≤ nWv R s := by
    have := Nat.ceil_pos.mpr hApos
    unfold nWv; omega
  have hW : ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) := by
    have h1 := (Nat.ceil_lt_add_one hApos.le).le
    have hk' : (R.k : ℝ) - 1 ≤ s.x ^ ((4694 : ℝ) / 1000) := by linarith
    have k0' : (0 : ℝ) ≤ (R.k : ℝ) - 1 := by linarith
    have h2 := rank_mul_le hxp mi0 (rank_mul_le hxp L0 (rank_mul_le hxp L0 (rank_mul_le hxp k0'
      (rank_mul_le hxp k0' (rank_mul_le hxp k0' (rank_mul_le hxp f0 hfr hf) hk') hk') hk') hL) hL) hmi
    have h3 := h2.trans (mono (b := 227 / 10) (by norm_num))
    have h4 := hfr.trans (mono (b := 227 / 10) (by norm_num))
    have h5 : 1 ≤ s.x ^ ((227 : ℝ) / 10) := one (by norm_num)
    have h6 := ab (C := 28) (a := 227 / 10) (b := 229 / 10) (by norm_num) (by norm_num)
    have h7 : 10 * (R.r : ℝ) * ((R.f : ℝ) + (R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2 / R.m) / 8
        = (10 * ((R.f : ℝ) * R.r) + 10 * ((R.f : ℝ) * R.r * R.f * ((R.k : ℝ) - 1) * ((R.k : ℝ) - 1)
          * ((R.k : ℝ) - 1) * s.L * s.L * (R.m : ℝ)⁻¹)) / 8 := by
      rw [div_eq_mul_inv ((R.f : ℝ) ^ 2 * ((R.k : ℝ) - 1) ^ 3 * s.L ^ 2)]; ring
    unfold nWv
    push_cast
    linarith
  have hT1 : s.x ^ (377 : ℝ) ≤ (TOv s : ℝ) := Nat.le_ceil _
  have hT2 : (TOv s : ℝ) ≤ s.x ^ (378 : ℝ) := by
    have h1 : (TOv s : ℝ) ≤ s.x ^ (377 : ℝ) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
    have h5 : 1 ≤ s.x ^ (377 : ℝ) := one (by norm_num)
    have h6 := ab (C := 2) (a := 377) (b := 378) (by norm_num) (by norm_num)
    linarith
  have ht1 : TOv s ≤ R.t := by
    have h1 : TOv s ≤ TOv s * nWv R s := Nat.le_mul_of_pos_right _ hW1
    have h2 : R.r ≤ 8 * R.f * R.r := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have ht2 : (R.t : ℝ) ≤ s.x ^ (401 : ℝ) := by
    have h1 : R.t ≤ 8 * R.f * R.r + 4 + TOv s * nWv R s := by omega
    have h2 : (R.t : ℝ) ≤ 8 * (R.f * R.r) + 4 + TOv s * nWv R s := by
      have : ((R.t : ℕ) : ℝ) ≤ ((8 * R.f * R.r + 4 + TOv s * nWv R s : ℕ) : ℝ) := by exact_mod_cast h1
      push_cast at this; linarith
    have h3 := (rank_mul_le hxp (by positivity) hT2 hW).trans (mono (b := 4009 / 10) (by norm_num))
    have h4 := hfr.trans (mono (b := 4009 / 10) (by norm_num))
    have h5 : 1 ≤ s.x ^ ((4009 : ℝ) / 10) := one (by norm_num)
    have h6 := ab (C := 13) (a := 4009 / 10) (b := 401) (by norm_num) (by norm_num)
    linarith
  refine ⟨hf.trans (mono (by norm_num)), ?_, hr.trans (mono (by norm_num)), hkr, hrk, ?_, hL1, ?_, ?_, ?_, ?_,
    hW, hT1.trans (by exact_mod_cast ht1), ht2, ?_, hm1, hm2⟩
  · simpa using hmu.trans (mono (b := 1) (by norm_num))
  · simpa using hL.trans (mono (b := 1) (by norm_num))
  · have h1 : s.x ^ (2 : ℝ) ≤ R.f := by
      have := mono (a := 2) (b := 2 + 8 * s.eps) (by linarith)
      have : (0 : ℝ) ≤ R.n := by positivity
      linarith
    have h2 : s.x ^ ((9 : ℝ) / 2) ≤ R.r := by
      have := mono (a := 9 / 2) (b := 9 / 2 + 10 * s.eps) (by linarith)
      linarith
    calc s.x ^ ((13 : ℝ) / 2) = s.x ^ (2 : ℝ) * s.x ^ ((9 : ℝ) / 2) * 1 := by
          rw [← Real.rpow_add hxp]; norm_num
      _ ≤ _ := by gcongr
  · exact (rank_mul_le hxp L0 hfr hL).trans (mono (by norm_num))
  · have h1 : ((R.r.choose 2 : ℕ) : ℝ) ≤ R.r * R.r := by
      have := Nat.choose_le_pow R.r 2
      rw [sq] at this
      exact_mod_cast this
    have h2 := (rank_mul_le hxp r0 hfr hr).trans (mono (b := 12) (by norm_num))
    push_cast
    calc (R.f : ℝ) * (R.r.choose 2 : ℕ) ≤ R.f * (R.r * R.r) := by gcongr
      _ ≤ _ := by rw [← mul_assoc]; exact h2
  · rw [div_eq_mul_inv]
    exact (rank_mul_le hxp mi0 (rank_mul_le hxp f0 hk hf) hmi).trans (mono (by norm_num))
  · have h3 := (rank_mul_le hxp (by positivity) hmu ht2).trans (mono (b := 4016 / 10) (by norm_num))
    have h4 := hk.trans (mono (b := 4016 / 10) (by norm_num))
    have h5 := hmu.trans (mono (b := 4016 / 10) (by norm_num))
    have h6 := ab (C := 3) (a := 4016 / 10) (b := 402) (by norm_num) (by norm_num)
    unfold Ranks.N
    push_cast
    linarith

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScaleStatement
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.explicitRanks_basic_bounds_large_scale : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → (R.f : ℝ) ≤ s.x ^ (3 : ℝ) ∧ (R.m : ℝ) ≤ s.x ∧ (R.r : ℝ) ≤ s.x ^ (5 : ℝ) ∧ R.k ≤ R.r ∧ R.r ≤ 2 * R.k ∧ s.L ≤ s.x ∧ 1 ≤ s.L ∧ s.x ^ ((13 : ℝ) / 2) ≤ (R.f : ℝ) * R.r * s.L ∧ (R.f : ℝ) * R.r * s.L ≤ s.x ^ ((687 : ℝ) / 100) ∧ ((R.f * R.r.choose 2 : ℕ) : ℝ) ≤ s.x ^ (12 : ℝ) ∧ (R.k : ℝ) * R.f / R.m ≤ s.x ^ (7 : ℝ) ∧ ((nWv R s : ℕ) : ℝ) ≤ s.x ^ ((229 : ℝ) / 10) ∧ s.x ^ (377 : ℝ) ≤ (R.t : ℝ) ∧ (R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ (R.N R.m : ℝ) ≤ s.x ^ (402 : ℝ) ∧ s.x ^ ((1 : ℝ) / 2 - s.eps / 16) ≤ (R.m : ℝ) ∧ (R.m : ℝ) ≤ 2 * s.x ^ ((1 : ℝ) / 2 - s.eps / 16) := by
  first | exact @GlobalTheory.EX.rank_basic_bounds | exact GlobalTheory.EX.rank_basic_bounds | (intros; apply GlobalTheory.EX.rank_basic_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFacts
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomDict

open GlobalTheory.MomOne

theorem root_eq (d : ℕ) (hd : d % 4 = 3) (t n : ℤ) (hD : t ^ 2 - 4 * n = -(d : ℤ)) (β : ℂ)
    (hβ : β ^ 2 = t * β - n) : ∃ k : ℤ, β = k + wK d ∨ β = k - wK d := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, t = 2 * k + 1 := by
    rcases Int.even_or_odd' t with ⟨k, rfl | rfl⟩
    · exfalso
      have : (2 * k) ^ 2 = 4 * (k * k) := by ring
      rw [this] at hD
      generalize k * k = m at hD
      omega
    · exact ⟨k, rfl⟩
  obtain ⟨s, hs2, hw⟩ : ∃ s : ℂ, s ^ 2 = -(d : ℂ) ∧ wK d = (1 + s) / 2 := by
    refine ⟨Complex.I * ((Real.sqrt d : ℝ) : ℂ), ?_, rfl⟩
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    push_cast; ring
  have hDc : (t : ℂ) ^ 2 - 4 * n = -(d : ℂ) := by exact_mod_cast hD
  have hprod : (2 * β - t - s) * (2 * β - t + s) = 0 := by
    linear_combination 4 * hβ + hDc - hs2
  have hkc : (t : ℂ) = 2 * k + 1 := by exact_mod_cast hk
  rcases mul_eq_zero.1 hprod with h | h
  · refine ⟨k, Or.inl ?_⟩
    rw [hw]; linear_combination h / 2 + hkc / 2
  · refine ⟨k + 1, Or.inr ?_⟩
    rw [hw]; push_cast; linear_combination h / 2 + hkc / 2

theorem inOK_iff_int_pair (d : ℕ) (β : ℂ) (k : ℤ) (hβ : β = k + wK d ∨ β = k - wK d) (z : ℂ) :
    InOK d z ↔ ∃ x y : ℤ, z = x + y * β := by
  rcases hβ with rfl | rfl
  · constructor
    · rintro ⟨u, v, rfl⟩; exact ⟨u - v * k, v, by push_cast; ring⟩
    · rintro ⟨x, y, rfl⟩; exact ⟨x + y * k, y, by push_cast; ring⟩
  · constructor
    · rintro ⟨u, v, rfl⟩; exact ⟨u + v * k, -v, by push_cast; ring⟩
    · rintro ⟨x, y, rfl⟩; exact ⟨x + y * k, -y, by push_cast; ring⟩

theorem inOK_iff (D : D7) (z : ℂ) :
    InOK D.host.d z ↔ ∃ x : 𝓞 D.host.K, z = D.host.φ₀ ((x : D.host.K) : D.host.E) := by
  obtain ⟨b, t, n, h0, hw, hdisc⟩ := GlobalTheory.QuadraticZeta.exists_basis (K := D.host.K) (GlobalTheory.CurveLattice.finrank_hostK D)
  rw [GlobalTheory.CurveLattice.discr_hostK D] at hdisc
  let σ : 𝓞 D.host.K →+* ℂ := D.host.φ₀.comp ((algebraMap D.host.K D.host.E).comp (algebraMap (𝓞 D.host.K) D.host.K))
  have hσ : ∀ x : 𝓞 D.host.K, σ x = D.host.φ₀ ((x : D.host.K) : D.host.E) := fun x => rfl
  have hβ : σ (b 1) ^ 2 = t * σ (b 1) - n := by
    rw [← map_pow, hw]; simp
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨k, hk⟩ := root_eq D.host.d hd4 t n hdisc.symm _ hβ
  rw [inOK_iff_int_pair D.host.d _ k hk z]
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨x + y * b 1, by rw [← hσ]; simp⟩
  · rintro ⟨x, rfl⟩
    refine ⟨b.repr x 0, b.repr x 1, ?_⟩
    rw [← hσ]
    conv_lhs => rw [GlobalTheory.QuadraticZeta.eq_coord b h0 x]
    simp

end GlobalTheory.MomDict

namespace GlobalTheory.MomDict

theorem area_bot : area (⊥ : AddSubgroup ℂ) = 0 := by
  unfold area
  have : {a : ℝ | 0 < a ∧ ∃ w₁ ∈ (⊥ : AddSubgroup ℂ), ∃ w₂ ∈ (⊥ : AddSubgroup ℂ), a = |((starRingEnd ℂ) w₁ * w₂).im|} = ∅ := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    rintro ha ⟨w₁, h1, w₂, h2, rfl⟩
    rw [AddSubgroup.mem_bot] at h1 h2
    simp [h1, h2] at ha
  rw [this, Real.sInf_empty]

theorem lamOf_zero (D : D7) (cc : Ideal (𝓞 D.host.K)) : lamOf D cc 0 = ⊥ := by
  ext w
  rw [GlobalTheory.CurveLattice.mem_lamOf, AddSubgroup.mem_bot]
  constructor
  · rintro ⟨c, -, rfl⟩; simp
  · rintro rfl; exact ⟨0, cc.zero_mem, by simp⟩

theorem area_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : cc ≠ ⊥) :
    area (lamOf D cc δ) = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 := by
  rcases eq_or_ne δ 0 with rfl | hδ
  · rw [lamOf_zero, area_bot]; simp
  obtain ⟨a, τ, ha, hN, h⟩ := GlobalTheory.CurveLattice.exists_tau D cc hcc
  have hda : δ * a ≠ 0 := mul_ne_zero hδ ha
  have hd : 0 < √(D.host.d : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  rw [GlobalTheory.CurveLattice.area_of_tau hda (h δ), hN, norm_mul, Complex.normSq_eq_norm_sq]
  field_simp

theorem main : ∀ (D : D7), D.host.d.Prime ∧ D.host.d % 16 = 7 ∧ (∀ z : ℂ, GlobalTheory.MomOne.InOK D.host.d z ↔ ∃ x : 𝓞 D.host.K, z = D.host.φ₀ ((x : D.host.K) : D.host.E)) ∧ (∀ x : D.host.K, D.host.φ₀ (D.host.conj (x : D.host.E)) = (starRingEnd ℂ) (D.host.φ₀ (x : D.host.E))) ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → area (lamOf D cc δ) = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ ∀ z : ℂ, z ∈ lamOf D cc δ ↔ ∃ x ∈ cc, z = δ * D.host.φ₀ ((x : D.host.K) : D.host.E) := by
  intro D
  refine ⟨D.host.hyp.2.1, D.host.hyp.2.2.2.1, inOK_iff D, fun x => D.host.conjE_apply _ _, fun cc δ hcc => ⟨area_lamOf D cc δ hcc, fun z => GlobalTheory.CurveLattice.mem_lamOf D cc δ z⟩⟩

end GlobalTheory.MomDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CmBaseFieldIntegersAndCurveIdealFactsStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts : ∀ (D : D7), D.host.d.Prime ∧ D.host.d % 16 = 7 ∧ (∀ z : ℂ, GlobalTheory.MomOne.InOK D.host.d z ↔ ∃ x : 𝓞 D.host.K, z = D.host.φ₀ ((x : D.host.K) : D.host.E)) ∧ (∀ x : D.host.K, D.host.φ₀ (D.host.conj (x : D.host.E)) = (starRingEnd ℂ) (D.host.φ₀ (x : D.host.E))) ∧ ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → area (lamOf D cc δ) = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 ∧ ∀ z : ℂ, z ∈ lamOf D cc δ ↔ ∃ x ∈ cc, z = δ * D.host.φ₀ ((x : D.host.K) : D.host.E) := by
  first | exact @GlobalTheory.MomDict.main | exact GlobalTheory.MomDict.main | (intros; apply GlobalTheory.MomDict.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem exists_even_between (A : ℝ) (hA : 2 ≤ A) : ∃ m : ℕ, Even m ∧ A ≤ m ∧ (m : ℝ) ≤ 2 * A := by
  refine ⟨2 * ⌈A / 2⌉₊, even_two_mul _, ?_, ?_⟩
  · have := Nat.le_ceil (A / 2)
    push_cast; linarith
  · have := Nat.ceil_lt_add_one (a := A / 2) (by linarith)
    push_cast; linarith

theorem exists_ranks_of_frame (φ : Formalism.HC.Frame) (k m T W : ℕ) (hk : Even k) (hm : Even m) (h2 : 2 ≤ m) (h3 : m + 3 ≤ k)
    (hmf : m ≤ 2 * φ.ord) (hfk : 2 * φ.ord ≤ k) :
    ∃ R : Ranks, R.toFrame = φ ∧ R.k = k ∧ R.m = m ∧ R.r + R.t = 8 * R.f * R.r + 4 + T * (8 * W) := by
  obtain ⟨r, hr⟩ : ∃ r, r = k + m - 1 := ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f, f = 2 * φ.ord := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, p = f * r := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = T * W := ⟨_, rfl⟩
  have hpr : r ≤ p := by
    rw [hp]; exact Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hmt : m ≤ 8 * p + 4 + 8 * q - r + 1 := by omega
  refine ⟨⟨φ, k, m, 8 * p + 4 + 8 * q - r, ⟨k', hk'⟩, ⟨m', hm'⟩, ?_, h2, h3, by omega, by omega, hmf, hfk, ?_⟩,
    rfl, rfl, rfl, ?_⟩
  · rw [Nat.odd_iff]; omega
  · rw [sq]
    exact (Nat.mul_le_mul_left m hmt).trans (Nat.le_add_left _ _)
  · show (k + m - 1) + (8 * p + 4 + 8 * q - r) = 8 * (2 * φ.ord) * (k + m - 1) + 4 + T * (8 * W)
    rw [← hr, ← hf, mul_assoc 8 f r, ← hp, mul_left_comm T 8 W, ← hq]
    omega

theorem exists_ranks_rankVal_frame : ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    ∀ φ : Formalism.HC.Frame, s.x ^ (2 + 8 * s.eps) ≤ (φ.ord : ℝ) → (φ.ord : ℝ) ≤ 2 * s.x ^ (2 + 8 * s.eps) →
      ∃ R : Ranks, R.toFrame = φ ∧ RankVal s R := by
  intro eps h0 h1
  refine ⟨16, fun s hs hx φ he1 hp2 => ?_⟩
  subst hs
  have hx1 : (1 : ℝ) ≤ s.x := by linarith
  have hx0 : (0 : ℝ) < s.x := by linarith
  have hH1 : s.x ^ 2 ≤ s.x ^ (2 + 8 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hH2 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ 3 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have he2 : (φ.ord : ℝ) ≤ 2 * s.x ^ 3 := by linarith
  have hB : s.x ^ 4 ≤ s.x ^ (9 / 2 + 10 * s.eps) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have hd : s.x * s.delta1 = s.x ^ (1 - s.eps / 8) := by
    unfold Scale.delta1
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hA1 : 2 ≤ Real.sqrt (s.x * s.delta1) := by
    apply Real.le_sqrt_of_sq_le
    rw [hd]
    have h1 : s.x ^ (1 / 2 : ℝ) ≤ s.x ^ (1 - s.eps / 8) :=
      Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have h2 : (4 : ℝ) ≤ s.x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      linarith
    linarith
  have hA2 : Real.sqrt (s.x * s.delta1) ≤ s.x := by
    rw [Real.sqrt_le_left hx0.le, hd, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
  have p2 : 16 * s.x ≤ s.x ^ 2 := by nlinarith
  have p3 : 16 * s.x ^ 2 ≤ s.x ^ 3 := by nlinarith
  have p4 : 16 * s.x ^ 3 ≤ s.x ^ 4 := by nlinarith
  obtain ⟨m, hm, hm1, hm2⟩ := exists_even_between _ hA1
  obtain ⟨k, hk, hk1, hk2⟩ := exists_even_between (s.x ^ (9 / 2 + 10 * s.eps)) (by linarith)
  have a1 : 2 ≤ m := by
    have : ((2 : ℕ) : ℝ) ≤ m := by push_cast; linarith
    exact_mod_cast this
  have a2 : m + 3 ≤ k := by
    have : (m : ℝ) + 3 ≤ k := by linarith
    exact_mod_cast this
  have a3 : m ≤ 2 * φ.ord := by
    have : (m : ℝ) ≤ 2 * (φ.ord : ℝ) := by linarith
    exact_mod_cast this
  have a4 : 2 * φ.ord ≤ k := by
    have : 2 * (φ.ord : ℝ) ≤ k := by linarith
    exact_mod_cast this
  obtain ⟨R, rfl, rfl, rfl, hR⟩ := exists_ranks_of_frame φ k m (TOv s)
    ⌈10 * ((k + m - 1 : ℕ) : ℝ) * (((2 * φ.ord : ℕ) : ℝ) +
      ((2 * φ.ord : ℕ) : ℝ) ^ 2 * ((k : ℝ) - 1) ^ 3 * s.L ^ 2 / m) / 8⌉₊ hk hm a1 a2 a3 a4
  exact ⟨R, rfl, ⟨he1, hp2⟩, ⟨hm1, hm2⟩, ⟨hk1, hk2⟩, hR⟩

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

def stdConst (CT2 C8 p m l : ℝ) : FC where
  Ct := 401
  Cc := 2
  CT2 := CT2
  CGam := m
  Csz := m
  Cr := 1
  CTu := 25
  Cdg := 1
  C5 := 1
  full := True
  GK := ⟨m, l, l, l, l, l, l, l, l, l, l, 5, 4, 1, l⟩
  cX := ⟨1, ⟨12, 3, m⟩⟩
  P :=
    { CkLow := l, Ck6 := l, CfL := l, cLL := l⁻¹, CnW := 10, Crho := l, CDelG := l, CLw := 11 * 405, Cj0 := 405,
      Cw := l, cw := 9 / 10, CDel := l, CCount := l, Ch0r := l, Ch0k := l, Ch0N := l, Cgap := l, CetaF := 6,
      CY := l, CYL := 9, Cpde := C8, CccK := 1, CF := m }
  T := { CP := p, eP := 12, Cp := 1, Cb := l, cTO := 377, ChT := l, CbN := l }

theorem stdConst_cPre (CT2 C8 p m l c : ℝ) (h : c ∈ (stdConst CT2 C8 p m l).cPre) : c = p := by
  simpa [FC.cPre, stdConst] using h

theorem stdConst_cMid (CT2 C8 p m l c : ℝ)
    (h : c ∈ (stdConst CT2 C8 p m l).cMid (stdConst CT2 C8 p m l).P.CF) : c = m := by
  simpa [FC.cMid, stdConst] using h

theorem stdConst_cLast (CT2 C8 p m l c : ℝ) (h : c ∈ (stdConst CT2 C8 p m l).cLast) : c = l := by
  simpa [FC.cLast, stdConst] using h

theorem exists_std_large (K K0 : TransportedAlt) (CT2 C8 : ℝ) (h8 : 1 ≤ C8) :
    ∃ C : FC, Std C ∧ C.CT2 = CT2 ∧ C.P.Cpde = C8 ∧ C.Large K C.P.CF ∧ C.Large K0 C.P.CF ∧ C.GK.Nonneg := by
  obtain ⟨p, hp1, hpK, hpK0⟩ : ∃ p : ℝ, 1000 ≤ p ∧ K.pre ≤ p ∧ K0.pre ≤ p :=
    ⟨max 1000 (max K.pre K0.pre), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨m, hm1, hmK, hmK0⟩ : ∃ m : ℝ, 1 ≤ m ∧ K.mid (stdConst CT2 C8 p 0 0).cOut ≤ m ∧
      K0.mid (stdConst CT2 C8 p 0 0).cOut ≤ m :=
    ⟨max 1 (max _ _), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨l, hl1, hlK, hlK0⟩ : ∃ l : ℝ, 1 ≤ l ∧
      K.last ((stdConst CT2 C8 p m 0).cOut ++ (stdConst CT2 C8 p m 0).cMid m) ≤ l ∧
      K0.last ((stdConst CT2 C8 p m 0).cOut ++ (stdConst CT2 C8 p m 0).cMid m) ≤ l :=
    ⟨max 1 (max _ _), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  have hm0 : 0 ≤ m := by linarith
  have hl0 : 0 ≤ l := by linarith
  refine ⟨stdConst CT2 C8 p m l, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, h8, hp1, ?_, ?_⟩,
    rfl, rfl, ⟨?_, trivial, ?_, ?_⟩, ⟨?_, trivial, ?_, ?_⟩, ?_⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, le_rfl, rfl⟩
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hm1
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hl1
  · intro c hc; rw [stdConst_cPre _ _ _ _ _ _ hc]; exact hpK
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hmK
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hlK
  · intro c hc; rw [stdConst_cPre _ _ _ _ _ _ hc]; exact hpK0
  · intro c hc; rw [stdConst_cMid _ _ _ _ _ _ hc]; exact hmK0
  · intro c hc; rw [stdConst_cLast _ _ _ _ _ _ hc]; exact hlK0
  · exact ⟨hm0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, hl0, by norm_num [stdConst], by norm_num [stdConst],
      by norm_num [stdConst], hl0⟩

end GlobalTheory.EX

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HostBoundsTwoMulRpowLogSqLe
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem hostBounds_two_mul_rpow_log_sq_le (eps : ℝ) (he : 0 < eps) :
    ∃ x0 : ℝ, ∀ x ≥ x0, 2 * x ^ (eps / 5) * Real.log x ^ 2 ≤ x ^ eps := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (s := 4 * eps / 5) (by positivity)).bound
    (c := 1 / 2) (by norm_num)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.mp (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx0 x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (Real.rpow_nonneg h2.le _)] at h1
  have e : x ^ eps = x ^ (eps / 5) * x ^ (4 * eps / 5) := by
    rw [← Real.rpow_add h2]; congr 1; ring
  have hp : 0 < x ^ (eps / 5) := Real.rpow_pos_of_pos h2 _
  rw [e]
  nlinarith

theorem hostBounds_log_of_sqrt_exp_lt {a y : ℝ} (h : Real.sqrt (Real.exp a) < y) :
    a / 2 ≤ Real.log y := by
  have h0 : 0 < Real.sqrt (Real.exp a) := Real.sqrt_pos.mpr (Real.exp_pos a)
  have h1 := Real.log_le_log h0 h.le
  rwa [Real.log_sqrt (Real.exp_pos a).le, Real.log_exp] at h1

private theorem hostBounds_rd (R : Ranks) (H : Host R) :
    1 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by
  have hq0 : (1 : ℝ) ≤ H.q := by exact_mod_cast H.hyp.1.one_le
  have hd0 : (1 : ℝ) ≤ H.d := by exact_mod_cast H.hyp.2.1.one_le
  have hS0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have hqd : (1 : ℝ) ≤ (H.q : ℝ) * H.d := one_le_mul_of_one_le_of_one_le hq0 hd0
  have hs1 : 1 ≤ Real.sqrt ((H.q : ℝ) * H.d) := Real.one_le_sqrt.mpr hqd
  have hs2 : Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.q : ℝ) * H.d := by
    have := Real.mul_self_sqrt (show (0 : ℝ) ≤ (H.q : ℝ) * H.d by positivity)
    nlinarith
  obtain ⟨hrd1, hrd2, -⟩ := factRd R H
  have he0 : (0 : ℝ) ≤ R.e := Nat.cast_nonneg _
  have hB : (2 : ℝ) ^ (-(R.e : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hlo : (1 : ℝ) ≤ (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ))) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  refine ⟨(one_le_mul_of_one_le_of_one_le hlo (Real.one_le_sqrt.mpr hd0)).trans hrd1, hrd2.trans ?_⟩
  have : (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.QS : ℝ) * ((H.q : ℝ) * H.d) :=
    mul_le_mul (by linarith) hs2 (Real.sqrt_nonneg _) hS0.le
  rwa [mul_assoc]

theorem hostBounds_ez {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H) : s.eps / C8 ≤ s.ez :=
  div_le_div_of_nonneg_left s.eps_pos.le (lt_of_lt_of_le one_pos s.one_le_J) h.2.2.2.2.2.2.2.2.1

theorem hostBounds_one_le_log_div {s : Scale} {C8 : ℝ} {R : Ranks} {H : Host R} (h : HostVal s C8 H)
    (hx : Real.exp C8 ≤ s.x) : 1 ≤ Real.log s.x / s.J := by
  rw [one_le_div (lt_of_lt_of_le one_pos s.one_le_J)]
  exact h.2.2.2.2.2.2.2.2.1.trans ((Real.le_log_iff_exp_le (by linarith [s.one_lt_alt])).mpr hx)

private theorem hostBounds_win {s : Scale} {Y : ℝ} (h : PairWin s Y) :
    s.x ^ (s.ez / 5) ≤ Y ^ (s.eps / 5) ∧ Y ^ (s.eps / 5) ≤ s.x ^ (s.eps / 5) ∧
      (Real.log s.x / s.J) ^ 2 ≤ Real.log Y ^ 2 ∧ Real.log Y ^ 2 ≤ Real.log s.x ^ 2 := by
  obtain ⟨h1, h2⟩ := h
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hJ : 0 < s.J := lt_of_lt_of_le one_pos s.one_le_J
  have he := s.eps_pos
  have hp : 0 < s.x ^ (1 / s.J) := Real.rpow_pos_of_pos hx0 _
  have hY : 0 < Y := hp.trans_le h1
  have hl : Real.log s.x / s.J ≤ Real.log Y := by
    have := Real.log_le_log hp h1
    rw [Real.log_rpow hx0] at this
    calc Real.log s.x / s.J = 1 / s.J * Real.log s.x := by ring
      _ ≤ _ := this
  have hl0 : 0 ≤ Real.log s.x / s.J := div_nonneg (Real.log_pos hx1).le hJ.le
  refine ⟨?_, Real.rpow_le_rpow hY.le h2 (by positivity), pow_le_pow_left₀ hl0 hl 2,
    pow_le_pow_left₀ (hl0.trans hl) (Real.log_le_log hY h2) 2⟩
  have e : s.x ^ (s.ez / 5) = (s.x ^ (1 / s.J)) ^ (s.eps / 5) := by
    rw [← Real.rpow_mul hx0.le]; congr 1; unfold Scale.ez; ring
  rw [e]
  exact Real.rpow_le_rpow hp.le h1 (by positivity)

theorem hostBounds : ∀ eps C8 : ℝ, 0 < eps → eps < 1 / 52 → 1 ≤ C8 → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R → HostVal s C8 H → s.x ^ (s.ez / 5) / 2 ≤ Real.log H.q ∧ Real.log H.q ≤ s.x ^ (s.eps / 5) ∧ s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 / 2 ≤ Real.log H.d ∧ Real.log H.d ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ 1 ≤ H.rdE ∧ H.rdE ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ∧ Real.log H.rdE ≤ s.L ∧ Real.log H.pde ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 ∧ Real.log H.pde' ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
  intro eps C8 he _ hC
  obtain ⟨x0, hx0⟩ := hostBounds_two_mul_rpow_log_sq_le eps he
  refine ⟨x0, fun s R H hse hx _ hH => ?_⟩
  subst hse
  obtain ⟨⟨Y, hW, hq, -, hq1, hq2, hd, -, hd1, hd2, -, -, hNY⟩, -, -, ⟨hp, hp'⟩, -⟩ := hH
  obtain ⟨w1, w2, w3, w4⟩ := hostBounds_win hW
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have p1 : 0 < s.x ^ (s.ez / 5) := Real.rpow_pos_of_pos hxp _
  have v1 : s.x ^ (s.ez / 5) * (Real.log s.x / s.J) ^ 2 ≤ Y ^ (s.eps / 5) * Real.log Y ^ 2 :=
    mul_le_mul w1 w3 (sq_nonneg _) (p1.le.trans w1)
  have v2 : Y ^ (s.eps / 5) * Real.log Y ^ 2 ≤ s.x ^ (s.eps / 5) * Real.log s.x ^ 2 :=
    mul_le_mul w2 w4 (sq_nonneg _) (Real.rpow_pos_of_pos hxp _).le
  have hq0 : (0 : ℝ) < H.q := by exact_mod_cast hq.pos
  have hd0 : (0 : ℝ) < H.d := by exact_mod_cast hd.pos
  have hS0 : (0 : ℝ) < H.QS := by exact_mod_cast H.QS_pos
  have lq : Real.log H.q ≤ Y ^ (s.eps / 5) := (Real.log_le_iff_le_exp hq0).mpr hq2
  have ld : Real.log H.d ≤ Y ^ (s.eps / 5) * Real.log Y ^ 2 := (Real.log_le_iff_le_exp hd0).mpr hd2
  have lq' : Y ^ (s.eps / 5) / 2 ≤ Real.log H.q := hostBounds_log_of_sqrt_exp_lt hq1
  have ld' : Y ^ (s.eps / 5) * Real.log Y ^ 2 / 2 ≤ Real.log H.d := hostBounds_log_of_sqrt_exp_lt hd1
  have hN : Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by linarith
  obtain ⟨hrd1, hrd3⟩ := hostBounds_rd R H
  have hNpos : (0 : ℝ) < (H.QS : ℝ) * H.q * H.d := by positivity
  have hpl : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ ((H.QS : ℝ) * H.q * H.d) ^ C8 →
      Real.log p ≤ 2 * C8 * s.x ^ (s.eps / 5) * Real.log s.x ^ 2 := by
    intro p hpp hle
    have h1 := Real.log_le_log (by exact_mod_cast hpp.pos) hle
    rw [Real.log_rpow hNpos] at h1
    have h2 := mul_le_mul_of_nonneg_left hN (show 0 ≤ C8 by linarith)
    linarith
  exact ⟨by linarith, lq.trans w2, by linarith, ld.trans v2, hN, hrd1, (factRd R H).2.1,
    ((Real.log_le_log (by linarith) hrd3).trans hN).trans (hx0 _ hx),
    hpl _ H.pde_prime hp, hpl _ H.pde'_prime hp'⟩

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MPowFiveMulFMulLLe
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem m_pow_five_mul_f_mul_L_le (s : Scale) (R : Ranks) (h : RankVal s R) :
    (R.m : ℝ) ^ 5 * R.f * s.L ≤ 128 * s.x ^ (9 / 2 + 9 * s.eps) := by
  have hn := h.n_le
  obtain ⟨-, ⟨-, hm⟩, -, -⟩ := h
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have he := s.eps_pos
  have hm2 : (R.m : ℝ) ≤ 2 * s.x ^ (1 / 2 - s.eps / 16) := by
    refine hm.trans (le_of_eq ?_)
    have hd : s.delta1 = s.x ^ (-(s.eps / 8)) := rfl
    rw [hd, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hx0.le (by linarith [s.eps_lt]), ← Real.rpow_mul hx0.le]
    congr 2; ring
  have hm5 : (R.m : ℝ) ^ 5 ≤ 32 * s.x ^ (5 / 2 - 5 * s.eps / 16) := by
    calc (R.m : ℝ) ^ 5 ≤ (2 * s.x ^ (1 / 2 - s.eps / 16)) ^ 5 := by gcongr
      _ = 32 * s.x ^ (5 / 2 - 5 * s.eps / 16) := by
        rw [mul_pow, ← Real.rpow_natCast (s.x ^ (1 / 2 - s.eps / 16)), ← Real.rpow_mul hx0.le]
        congr 1
        · norm_num
        · congr 1; push_cast; ring
  have hf : (R.f : ℝ) ≤ 4 * s.x ^ (2 + 8 * s.eps + s.eps / 100) := by
    simp only [Ranks.f]; push_cast; linarith
  have hL : s.L = s.x ^ s.eps := rfl
  have hL0 : 0 ≤ s.x ^ s.eps := by positivity
  calc (R.m : ℝ) ^ 5 * R.f * s.L
      ≤ (32 * s.x ^ (5 / 2 - 5 * s.eps / 16)) * (4 * s.x ^ (2 + 8 * s.eps + s.eps / 100)) * s.x ^ s.eps := by
        rw [hL]; gcongr
    _ = 128 * (s.x ^ (5 / 2 - 5 * s.eps / 16) * s.x ^ (2 + 8 * s.eps + s.eps / 100) * s.x ^ s.eps) := by ring
    _ ≤ 128 * s.x ^ (9 / 2 + 9 * s.eps) := by
        rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)) (by norm_num)

theorem exists_injective_words : ∀ eps CG CF : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ CG → 0 ≤ CF → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks), s.eps = eps → x0 ≤ s.x → RankVal s R → ∃ c : Fin ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊ → (Fin (R.k - 2) → Bool), Function.Injective c ∧ 0 < ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊ := by
  intro eps CG CF he _ hG hF
  set K : ℝ := 2 * (2 + 256 * CG + CF) + 2 with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K ^ (1 / eps), fun s R hs hx hR => ?_⟩
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hb := m_pow_five_mul_f_mul_L_le s R hR
  have hk := hR.2.2.1.1
  rw [hs] at hb hk
  have hKx : K ≤ s.x ^ eps := by
    calc K = (K ^ (1 / eps)) ^ eps := by
          rw [← Real.rpow_mul hK0, one_div_mul_cancel he.ne', Real.rpow_one]
      _ ≤ s.x ^ eps := by gcongr
  set X : ℝ := s.x ^ (9 / 2 + 9 * eps) with hX
  have hxX : s.x ≤ X := by
    calc s.x = s.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ X := Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith)
  have hX1 : 1 ≤ X := by linarith
  have hkX : K * X ≤ R.k := by
    refine le_trans ?_ hk
    have : s.x ^ (9 / 2 + 10 * eps) = s.x ^ eps * X := by
      rw [hX, ← Real.rpow_add hx0]; congr 1; ring
    rw [this]; gcongr
  have hk2 : 2 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hlog : Real.log s.x ≤ X := by
    have := Real.log_le_sub_one_of_pos hx0; linarith
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by have := Real.add_one_le_exp (2 : ℝ); linarith
  have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hA : CG * (R.m : ℝ) ^ 5 * R.f * s.L ≤ 128 * CG * X := by
    calc CG * (R.m : ℝ) ^ 5 * R.f * s.L = CG * ((R.m : ℝ) ^ 5 * R.f * s.L) := by ring
      _ ≤ CG * (128 * X) := by gcongr
      _ = _ := by ring
  have hFX : Real.log s.x * CF ≤ X * CF := by gcongr
  have hkc : ((R.k - 2 : ℕ) : ℝ) = (R.k : ℝ) - 2 := by rw [Nat.cast_sub hk2]; norm_num
  have hmain : 3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF ≤ ((2 ^ (R.k - 2) : ℕ) : ℝ) := by
    calc 3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF
        ≤ Real.exp 2 * Real.exp (128 * CG * X) ^ 2 * Real.exp (X * CF) := by
          rw [Real.rpow_def_of_pos hx0]; gcongr
      _ = Real.exp (2 + 256 * CG * X + X * CF) := by
          rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (((R.k - 2 : ℕ) : ℝ) * Real.log 2) := by
          apply Real.exp_le_exp.2
          have h1 : 2 + 256 * CG * X + X * CF ≤ ((R.k - 2 : ℕ) : ℝ) * (1 / 2) := by
            rw [hkc]; rw [hK] at hkX; nlinarith
          refine h1.trans ?_
          gcongr
      _ = ((2 ^ (R.k - 2) : ℕ) : ℝ) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]; push_cast; rfl
  have hle := Nat.ceil_le.2 hmain
  have hcard : Fintype.card (Fin ⌈3 * Real.exp (CG * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ CF⌉₊) ≤
      Fintype.card (Fin (R.k - 2) → Bool) := by
    simpa using hle
  obtain ⟨c⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨c, c.injective, Nat.ceil_pos.2 (by positivity)⟩

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobal
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobal
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.LatLocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {k : ℕ}

theorem mem_latS_adele_iff (Λ : Submodule (𝓞 E) (Fin k → E)) (hΛ : Module.Finite (𝓞 E) Λ)
    (u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔
      ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ := by
  obtain ⟨m, l, -, hl⟩ := GlobalTheory.T.exists_generators_mem_completedLattice_iff F E k Λ hΛ
  have hv : ∀ (v : HeightOneSpectrum (𝓞 F)) (w : Fin k → E ⊗[F] v.adicCompletion F),
      w ∈ locLat v Λ ↔ ∃ t : Fin m → v.adicCompletion F,
        (∀ j, t j ∈ (v.adicCompletionIntegers F).toSubring) ∧ w = fun i => ∑ j, l j i ⊗ₜ[F] t j :=
    fun v w => hl _ _ w
  rw [hl]
  constructor
  · rintro ⟨t, ht, rfl⟩ v
    refine (hv v _).2 ⟨fun j => t j v, fun j => ht j v, ?_⟩
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => Formalism.UG.P.afsplit_prV_tmul v _ _
  · intro h
    choose t ht hu using fun v => (hv v _).1 (h v)
    let s : Fin m → FiniteAdeleRing (𝓞 F) F := fun j =>
      ⟨fun v => t v j, Filter.Eventually.of_forall fun v => ht v j⟩
    refine ⟨s, fun j v => ht v j, ?_⟩
    funext i
    rw [← sub_eq_zero]
    refine Formalism.UG.P.afsplit_inj _ fun v => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, sub_eq_zero, map_sum]
    refine (congrFun (hu v) i).trans ?_
    exact Finset.sum_congr rfl fun j _ => (Formalism.UG.P.afsplit_prV_tmul v (l j i) (s j)).symm

theorem mem_of_forall_locLat (Λ : Submodule (𝓞 E) (Fin k → E)) (hΛ : Module.Finite (𝓞 E) Λ)
    (hspan : Submodule.span E (Λ : Set (Fin k → E)) = ⊤) (x : Fin k → E)
    (hx : ∀ v : HeightOneSpectrum (𝓞 F),
      (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) : x ∈ Λ := by
  rw [← Formalism.UG.P.global_lattice_one_holds F E (Fin k) Λ hΛ hspan]
  show ((1⁻¹ : GL (Fin k) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin k) (Fin k) _) *ᵥ
      (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
  rw [inv_one, Units.val_one, one_mulVec, mem_latS_adele_iff Λ hΛ]
  exact hx

theorem mem_range_of_forall_intV (a : E)
    (ha : ∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) :
    a ∈ (algebraMap (𝓞 E) E).range := by
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have h1 : (fun _ => 1 : Fin 1 → E) ∈ Λ := Submodule.subset_span rfl
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • (fun _ => 1 : Fin 1 → E) := by
      funext i
      rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have := mem_of_forall_locLat (F := F) Λ hfin hspan (fun _ => a) fun v => by
    have h2 : (fun _ => inclE (F := F) (v.adicCompletion F) (1 : E)) ∈ locLat v Λ :=
      Submodule.subset_span ⟨_, h1, rfl⟩
    have h3 := (locLat v Λ).smul_mem (⟨_, ha v⟩ : intV E v) h2
    convert h3 using 1
    funext i
    show _ = inclE (F := F) (v.adicCompletion F) a * inclE (F := F) (v.adicCompletion F) (1 : E)
    rw [map_one, mul_one]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
  refine ⟨c, ?_⟩
  have := congrFun hc 0
  simpa [Algebra.smul_def] using this

theorem latS_local_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → (∀ u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F, u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ) ∧ (Submodule.span E (Λ : Set (Fin k → E)) = ⊤ → ∀ x : Fin k → E, (∀ v : HeightOneSpectrum (𝓞 F), (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) → x ∈ Λ) ∧ ∀ a : E, (∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) → a ∈ (algebraMap (𝓞 E) E).range :=
  fun _ _ _ _ _ _ _ _ Λ hΛ =>
    ⟨mem_latS_adele_iff Λ hΛ, mem_of_forall_locLat Λ hΛ, mem_range_of_forall_intV⟩

end GlobalTheory.LatLocGlob
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicLatticeCompletionLocalGlobalStatement
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLatticeCompletion_local_global : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin k → E)), Module.Finite (𝓞 E) Λ → (∀ u : Fin k → E ⊗[F] FiniteAdeleRing (𝓞 F) F, u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ ↔ ∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (u i)) ∈ locLat v Λ) ∧ (Submodule.span E (Λ : Set (Fin k → E)) = ⊤ → ∀ x : Fin k → E, (∀ v : HeightOneSpectrum (𝓞 F), (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ locLat v Λ) → x ∈ Λ) ∧ ∀ a : E, (∀ v : HeightOneSpectrum (𝓞 F), inclE (F := F) (v.adicCompletion F) a ∈ intV E v) → a ∈ (algebraMap (𝓞 E) E).range := by
  first | exact @GlobalTheory.LatLocGlob.latS_local_global | exact GlobalTheory.LatLocGlob.latS_local_global | (intros; apply GlobalTheory.LatLocGlob.latS_local_global <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowAndImp
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField

namespace GlobalTheory.EX

theorem SzRow.and {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P) (hQ : SzRow Q) :
    SzRow (fun C D L => P C D L ∧ Q C D L) := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  obtain ⟨b1, hb1⟩ := hQ eps h0 h1 C hC
  refine ⟨max a1 b1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD (le_trans (le_max_left _ _) hcD)
  obtain ⟨b2, hb2⟩ := hb1 cD (le_trans (le_max_right _ _) hcD)
  refine ⟨max a2 b2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch (le_trans (le_max_left _ _) hch)
  obtain ⟨b3, hb3⟩ := hb2 ch (le_trans (le_max_right _ _) hch)
  refine ⟨max a3 b3, fun D L he hx hV => ⟨?_, ?_⟩⟩
  · exact ha3 D L he (le_trans (le_max_left _ _) hx) hV
  · exact hb3 D L he (le_trans (le_max_right _ _) hx) hV

theorem SzRow.imp {P Q : FC → ∀ D : D7, SizeData₂ D → Prop} (hP : SzRow P)
    (h : ∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) : SzRow Q := by
  intro eps h0 h1 C hC
  obtain ⟨a1, ha1⟩ := hP eps h0 h1 C hC
  refine ⟨a1, fun cD hcD => ?_⟩
  obtain ⟨a2, ha2⟩ := ha1 cD hcD
  refine ⟨a2, fun ch hch => ?_⟩
  obtain ⟨a3, ha3⟩ := ha2 ch hch
  exact ⟨a3, fun D L he hx hV => h C cD ch D L hC hV (ha3 D L he hx hV)⟩

theorem szRow_and_imp :
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P → SzRow Q → SzRow (fun C D L => P C D L ∧ Q C D L)) ∧
    (∀ P Q : FC → ∀ D : D7, SizeData₂ D → Prop, SzRow P →
      (∀ C cD ch D L, Std C → Val C cD ch L → P C D L → Q C D L) → SzRow Q) :=
  ⟨fun _ _ hP hQ => hP.and hQ, fun _ _ hP h => hP.imp h⟩

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSmulMemOfMemLocW
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

theorem exists_smul_mem_of_mem_locW (D : D7) (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (L : Submodule (𝓞 D.what₂.LL) V) {x : V}
    (hx : x ∈ locW D.what₂.places w L) : ∃ d : 𝓞 D.what₂.LL, d ∉ (D.plEq w).asIdeal ∧ d • x ∈ L := by
  have h1 : (1 : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal :=
    fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  unfold locW at hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, h1, by simpa using hy⟩
  | zero => exact ⟨1, h1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d, hd, hy⟩ := hy
    obtain ⟨e, he, hz⟩ := hz
    refine ⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact L.smul_mem _ hy
    · rw [mul_smul]; exact L.smul_mem _ hz
  | smul r y _ hy =>
    obtain ⟨d, hd, hy⟩ := hy
    have hr : (D.plEq w).valuation D.what₂.LL (r : D.what₂.LL) ≤ 1 := (D.val_nonneg_iff w r).1 r.2
    obtain ⟨n, e, hne⟩ := (D.plEq w).exists_primeCompl_mul_eq_of_integer (r : D.what₂.LL) hr
    refine ⟨d * e, fun h => ((D.plEq w).isPrime.mem_or_mem h).elim hd e.2, ?_⟩
    have : (d * (e : 𝓞 D.what₂.LL)) • r • y = n • d • y := by
      rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL (d * (e : 𝓞 D.what₂.LL)), ← algebraMap_smul D.what₂.LL n,
        ← algebraMap_smul D.what₂.LL d y, smul_smul, smul_smul, ← hne, map_mul]
      congr 1; ring
    rw [this]; exact L.smul_mem _ hy

theorem mem_of_forall_locW (D : D7) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (L : Submodule (𝓞 D.what₂.LL) V) {x : V}
    (hx : ∀ w, x ∈ locW D.what₂.places w L) : x ∈ L := by
  let I : Ideal (𝓞 D.what₂.LL) := L.comap (LinearMap.toSpanSingleton (𝓞 D.what₂.LL) V x)
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL) :=
      ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField _)⟩
    obtain ⟨d, hd, hdx⟩ := exists_smul_mem_of_mem_locW D (D.plEq.symm v) L (hx _)
    rw [Equiv.apply_symm_apply] at hd
    exact hd (hIM (show d ∈ I from hdx))
  have h1 : (1 : 𝓞 D.what₂.LL) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

variable {D : D7} {u : D.what₂.Word} {X : Ch D u}

end GlobalTheory.LvT
end
end
