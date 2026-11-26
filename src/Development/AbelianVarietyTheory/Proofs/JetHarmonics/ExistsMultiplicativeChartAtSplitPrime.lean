module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFormalGroupAdd
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUnitCoeffMulSeriesLeNorm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsIsoGmOfMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HeightOneOfSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrder
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.FormalMul

section General
variable {K : Type*} [CommRing K]

theorem hs {f : K⟦X⟧} (hf : constantCoeff f = 0) : HasSubst f := HasSubst.of_constantCoeff_zero' hf

theorem cc_subst {f g : K⟦X⟧} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    constantCoeff (f.subst g : K⟦X⟧) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (τ := Unit) hg f hf

theorem subst_C' (g : K⟦X⟧) (r : K) : ((C r : K⟦X⟧).subst g : K⟦X⟧) = C r := PowerSeries.subst_C r

theorem taylor_dvd (U f h : K⟦X⟧) (N : ℕ) (hf : constantCoeff f = 0) (hh0 : constantCoeff h = 0)
    (hh : X ^ N ∣ h) :
    (X : K⟦X⟧) ^ (2 * N) ∣ (U.subst (f + h) : K⟦X⟧) - U.subst f - (d⁄dX U).subst f * h := by
  have hfh : constantCoeff (f + h) = 0 := by rw [map_add (f := _), hf, hh0, add_zero]
  set M := 2 * N with hM
  obtain ⟨V, P, hU⟩ : ∃ (V : K⟦X⟧) (P : Polynomial K), U = X ^ (M + 1) * V + (P : K⟦X⟧) :=
    ⟨_, _, eq_X_pow_mul_shift_add_trunc (M + 1) U⟩
  have hD : d⁄dX U = X ^ M * (((M + 1 : ℕ) : K⟦X⟧) * V + X * d⁄dX V) +
      ((Polynomial.derivative P : Polynomial K) : K⟦X⟧) := by
    rw [hU, map_add (f := _), derivative_coe, Derivation.leibniz, Derivation.leibniz_pow, derivative_X]
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
    ring
  obtain ⟨k, hk⟩ := (P.map (algebraMap K K⟦X⟧)).binomExpansion f h
  rw [Polynomial.derivative_map, Polynomial.eval_map_algebraMap, Polynomial.eval_map_algebraMap,
    Polynomial.eval_map_algebraMap] at hk
  rw [hD]
  rw [hU, subst_add (hs hfh), subst_add (hs hf), subst_add (hs hf), subst_mul (hs hfh), subst_mul (hs hf),
    subst_mul (hs hf), subst_pow (hs hfh), subst_pow (hs hf), subst_pow (hs hf), subst_X (hs hfh), subst_X (hs hf),
    subst_coe (hs hfh), subst_coe (hs hf), subst_coe (hs hf)]
  have d1 : (X : K⟦X⟧) ^ M ∣ f ^ M := pow_dvd_pow_of_dvd (X_dvd_iff.2 hf) _
  have d2 : (X : K⟦X⟧) ^ M ∣ (f + h) ^ M := pow_dvd_pow_of_dvd (X_dvd_iff.2 hfh) _
  have d3 : (X : K⟦X⟧) ^ M ∣ h ^ 2 := by
    rw [hM, mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd hh _
  have key : ∀ a b c p0 p1 p2 : K⟦X⟧, p0 = p1 + p2 * h + k * h ^ 2 →
      (X : K⟦X⟧) ^ M ∣ (f + h) ^ (M + 1) * a + p0 - (f ^ (M + 1) * b + p1) - (f ^ M * c + p2) * h := by
    intro a b c p0 p1 p2 e
    have : (f + h) ^ (M + 1) * a + p0 - (f ^ (M + 1) * b + p1) - (f ^ M * c + p2) * h
        = (f + h) ^ M * ((f + h) * a) - f ^ M * (f * b + c * h) + h ^ 2 * k := by
      rw [e]; ring
    rw [this]
    exact dvd_add (dvd_sub (d2.mul_right _) (d1.mul_right _)) (d3.mul_right _)
  exact key _ _ _ _ _ _ hk

theorem add_law (G : MvPowerSeries (Fin 2) K) (U : K⟦X⟧) (hU : constantCoeff U = 0)
    (hG : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K) G
      = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U)
    (f g : K⟦X⟧) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (MvPowerSeries.subst (![U.subst f, U.subst g] : Fin 2 → MvPowerSeries Unit K) G : K⟦X⟧) = U.subst (f + g) := by
  have hb := GlobalTheory.ConvSer.nMul_hasSubst_pair hf hg
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 := by simp
  have comp : ∀ a : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit K) (PowerSeries.subst a U)
        = PowerSeries.subst (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit K) a) U := by
    intro a ha
    rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply (HasSubst.of_constantCoeff_zero ha).const hb]
    rfl
  have ha : MvPowerSeries.HasSubst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX 0) U hU
    · exact PowerSeries.constantCoeff_subst_eq_zero (hX 1) U hU
  have := congrArg (MvPowerSeries.subst (R := K) (![f, g] : Fin 2 → MvPowerSeries Unit K)) hG
  rw [MvPowerSeries.subst_comp_subst_apply ha hb, comp _ (by simp), MvPowerSeries.subst_add hb,
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at this
  refine Eq.trans ?_ this
  congr! 2 with s
  fin_cases s
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    rw [comp _ (hX 0), MvPowerSeries.subst_X hb]; rfl
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [comp _ (hX 1), MvPowerSeries.subst_X hb]; rfl

theorem deriv_mul_eq_one {U ℓ : K⟦X⟧} (hℓ : constantCoeff ℓ = 0) (h : U.subst ℓ = (X : K⟦X⟧)) :
    ((d⁄dX U).subst ℓ : K⟦X⟧) * d⁄dX ℓ = 1 := by
  rw [← derivative_subst (hs hℓ), h, derivative_X]

theorem subst_inv {U ℓ : K⟦X⟧} (hℓ : constantCoeff ℓ = 0) (h : U.subst ℓ = (X : K⟦X⟧)) :
    ℓ.subst U = (X : K⟦X⟧) := by
  have h1 := congrArg constantCoeff (deriv_mul_eq_one hℓ h)
  rw [map_mul, map_one, ← coeff_zero_eq_constantCoeff_apply (d⁄dX ℓ), coeff_derivative] at h1
  simp only [zero_add, Nat.cast_zero, mul_one] at h1
  have : Invertible (coeff 1 ℓ) := ⟨_, h1, by rw [mul_comm]; exact h1⟩
  have h2 := subst_substInv_right ℓ hℓ
  have hV : HasSubst ℓ.substInv := hs (by simp)
  have : U = ℓ.substInv := by
    have := subst_comp_subst_apply (hs hℓ) hV U
    rw [h, h2, subst_X hV] at this
    rw [this, ← PowerSeries.map_algebraMap_eq_subst_X]; simp
  rw [this, h2]

theorem coeff_subst_C_mul (U ℓ : K⟦X⟧) (hℓ : constantCoeff ℓ = 0) (n : ℕ) (a : K) :
    coeff n (U.subst (C a * ℓ) : K⟦X⟧) = ∑ d ∈ Finset.range (n + 1), coeff d U * (a ^ d * coeff n (ℓ ^ d)) := by
  rw [coeff_subst' (hs (by simp [hℓ])), finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
  · refine Finset.sum_congr rfl fun d _ => ?_
    rw [mul_pow, ← map_pow, coeff_C_mul, smul_eq_mul]
  · intro d hd
    by_contra hn
    apply hd
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    have : coeff n (ℓ ^ d) = 0 := X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hℓ) d) n (by omega)
    show _ • _ = _
    rw [mul_pow, ← map_pow, coeff_C_mul, this, mul_zero, smul_zero]

end General

section Padic
variable {q : ℕ} [Fact q.Prime]

theorem mem_int_iff (x : ℂ_[q]) : x ∈ 𝓞_ℂ_[q] ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm, Valuation.norm_def,
    (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl), Valuation.embedding_restrict]
  exact_mod_cast Iff.rfl

theorem bd_map (f : 𝓞_ℂ_[q]⟦X⟧) : Bd 1 (PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) f) := by
  intro n
  rw [coeff_map]
  exact (mem_int_iff _).1 (coeff n f).2

theorem norm_zc (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  rw [zc, norm_algebraMap']; rfl

theorem zc_natCast (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by simp [zc]

theorem zc_mul (a b : ℤ_[q]) : zc (a * b) = zc a * zc b := by simp [zc]

theorem continuous_zc : Continuous (zc : ℤ_[q] → ℂ_[q]) :=
  (continuous_algebraMap ℚ_[q] ℂ_[q]).comp continuous_subtype_val

def Van (m : ℕ) (f : ℂ_[q]⟦X⟧) : Prop := ∀ n < m, ‖coeff n f‖ < 1

theorem norm_add_lt {x y : ℂ_[q]} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_mul_lt_left {x y : ℂ_[q]} (hx : ‖x‖ < 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ < 1 := by
  rw [norm_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx hy

theorem van_mul {f g : ℂ_[q]⟦X⟧} {a b : ℕ} (hf : Bd 1 f) (hg : Bd 1 g) (ha : Van a f) (hb : Van b g) :
    Van (a + b) (f * g) := by
  intro n hn
  rw [coeff_mul]
  refine Finset.sum_induction _ (fun x => ‖x‖ < 1) (fun _ _ => norm_add_lt) (by simp) ?_
  intro p hp
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  by_cases h : p.1 < a
  · exact norm_mul_lt_left (ha _ h) (hg _)
  · rw [mul_comm]
    exact norm_mul_lt_left (hb _ (by omega)) (hf _)

theorem bd_pow {g : ℂ_[q]⟦X⟧} (hg : Bd 1 g) (d : ℕ) : Bd 1 (g ^ d) := by
  induction d with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ d ih =>
    have := ((sup_norm_laws q).1 _ _ _ _ ih hg).2
    rwa [one_mul, ← pow_succ] at this

theorem van_pow {g : ℂ_[q]⟦X⟧} {r : ℕ} (hg : Bd 1 g) (hr : Van r g) (d : ℕ) : Van (d * r) (g ^ d) := by
  induction d with
  | zero => intro n hn; omega
  | succ d ih =>
    rw [add_mul, one_mul, pow_succ]
    exact van_mul (bd_pow hg d) hg ih hr

theorem van_subst {f g : ℂ_[q]⟦X⟧} {m r : ℕ} (hf : Bd 1 f) (hg : Bd 1 g) (h0 : constantCoeff g = 0)
    (hm : Van m f) (hr : Van r g) : Van (m * r) (f.subst g) := by
  intro n hn
  rw [coeff_subst' (hs h0)]
  refine finsum_induction (fun x => ‖x‖ < 1) (by simp) (fun _ _ => norm_add_lt) fun d => ?_
  rw [smul_eq_mul]
  by_cases h : d < m
  · exact norm_mul_lt_left (hm _ h) (bd_pow hg d n)
  · rw [mul_comm]
    exact norm_mul_lt_left (van_pow hg hr d n (hn.trans_le (Nat.mul_le_mul_right r (by omega)))) (hf d)

theorem map_law (F : FormalGroup 𝓞_ℂ_[q]) (f g : 𝓞_ℂ_[q]⟦X⟧) (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    (MvPowerSeries.subst (![PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) f, PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) g] :
      Fin 2 → MvPowerSeries Unit ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) : ℂ_[q]⟦X⟧)
    = PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q])
      (MvPowerSeries.subst (![f, g] : Fin 2 → MvPowerSeries Unit 𝓞_ℂ_[q]) F.toPowerSeries) := by
  symm
  refine (MvPowerSeries.map_subst (GlobalTheory.ConvSer.nMul_hasSubst_pair hf hg) _).trans ?_
  congr! 2 with s
  fin_cases s <;> rfl

end Padic

theorem padic_multiplications : ∀ (q : ℕ) [Fact q.Prime] (F : FormalGroup 𝓞_ℂ_[q]) (U ℓ : ℂ_[q]⟦X⟧), constantCoeff U = 0 → constantCoeff ℓ = 0 → U.subst ℓ = X → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) U, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U → (∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ))) ∧ (∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1) ∧ (‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1 → ∀ (k : ℕ) (a : ℤ_[q]), ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) → ∀ n < (2 * q) ^ k, ‖coeff n (U.subst (C (zc a) * ℓ))‖ < 1) := by
  intro q hq F U ℓ hU hℓ hUℓ hG
  have law := add_law _ U hU hG
  have hinv := subst_inv hℓ hUℓ
  have hc : ∀ a : ℂ_[q], constantCoeff (C a * ℓ) = 0 := fun a => by simp [hℓ]
  have hB0 : ∀ a : ℂ_[q], constantCoeff (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) = 0 := fun a => cc_subst hU (hc a)
  have hℓB : ∀ a : ℂ_[q], (ℓ.subst (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧) = C a * ℓ := fun a => by
    rw [← subst_comp_subst_apply (hs hU) (hs (hc a)), hinv, subst_X (hs (hc a))]
  have hcomp : ∀ a b : ℂ_[q], (PowerSeries.subst (U.subst (C b * ℓ) : ℂ_[q]⟦X⟧) (U.subst (C a * ℓ) : ℂ_[q]⟦X⟧) : ℂ_[q]⟦X⟧)
      = U.subst (C (a * b) * ℓ) := fun a b => by
    rw [subst_comp_subst_apply (hs (hc a)) (hs (hB0 b)), subst_mul (hs (hB0 b)), subst_C', hℓB, map_mul, mul_assoc]

  have hnat : ∀ n : ℕ, (U.subst (C (n : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)
      = PowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) (GlobalTheory.ConvSer.nMul F n) := by
    intro n
    induction n with
    | zero =>
      ext m
      rw [coeff_subst_C_mul U ℓ hℓ, GlobalTheory.ConvSer.nMul_zero, map_zero, map_zero]
      refine Finset.sum_eq_zero fun d _ => ?_
      rcases d with _ | d
      · simp [hU]
      · simp
    | succ n ih =>
      rw [GlobalTheory.ConvSer.nMul_succ, ← map_law F _ _ (GlobalTheory.ConvSer.nMul_constantCoeff F n) constantCoeff_X, ← ih, map_X]
      have := law _ _ (hc n) hℓ
      rw [hUℓ] at this
      rw [this]
      congr 1
      push_cast
      rw [map_add (f := _), map_one]
      ring
  have hint : ∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ)) := by
    intro a m
    refine PadicInt.denseRange_natCast.induction_on (p := fun a => ‖coeff m (U.subst (C (zc a) * ℓ) : ℂ_[q]⟦X⟧)‖ ≤ 1)
      a ?_ fun n => ?_
    · simp only [coeff_subst_C_mul U ℓ hℓ]
      have := continuous_zc (q := q)
      exact isClosed_le (by fun_prop) continuous_const
    · rw [zc_natCast, hnat]
      exact bd_map _ m
  have hBq : Bd 1 (U.subst (C (q : ℂ_[q]) * ℓ)) := by
    have := hint q
    rwa [zc_natCast] at this

  have hone := deriv_mul_eq_one hℓ hUℓ
  set W : ℂ_[q]⟦X⟧ := C (coeff 1 ℓ) * (d⁄dX U).subst ℓ with hW
  have hW0 : constantCoeff W = 1 := by
    have h1 := congrArg constantCoeff hone
    rw [map_mul, map_one, ← coeff_zero_eq_constantCoeff_apply (d⁄dX ℓ), coeff_derivative] at h1
    simp only [zero_add, Nat.cast_zero, mul_one] at h1
    rw [hW, map_mul, constantCoeff_C, mul_comm, h1]
  have hWint : Bd 1 W := by
    intro m
    set N := m + 2 with hN
    have hXN : constantCoeff (X ^ N : ℂ_[q]⟦X⟧) = 0 := by simp [hN]
    set h : ℂ_[q]⟦X⟧ := ℓ.subst (X ^ N : ℂ_[q]⟦X⟧) with hh
    have hh0 : constantCoeff h = 0 := cc_subst hℓ hXN
    have hUh : (U.subst h : ℂ_[q]⟦X⟧) = X ^ N := by
      rw [hh, ← subst_comp_subst_apply (hs hℓ) (hs hXN), hUℓ, subst_X (hs hXN)]
    obtain ⟨V, hV⟩ : ∃ V : ℂ_[q]⟦X⟧, ℓ = C (coeff 1 ℓ) * X + X ^ 2 * V := by
      have : (X : ℂ_[q]⟦X⟧) ^ 2 ∣ ℓ - C (coeff 1 ℓ) * X := by
        rw [X_pow_dvd_iff]
        intro j hj
        interval_cases j
        · simp [hℓ]
        · simp
      obtain ⟨V, hV⟩ := this
      exact ⟨V, by rw [← hV]; ring⟩
    have hh' : h = C (coeff 1 ℓ) * X ^ N + X ^ (2 * N) * V.subst (X ^ N : ℂ_[q]⟦X⟧) := by
      rw [hh]
      conv_lhs => rw [hV]
      rw [subst_add (hs hXN), subst_mul (hs hXN), subst_mul (hs hXN), subst_pow (hs hXN), subst_C', subst_X (hs hXN),
        ← pow_mul, mul_comm N 2]
    have hd : (X : ℂ_[q]⟦X⟧) ^ N ∣ h := by
      rw [hh']
      exact dvd_add (dvd_mul_left _ _) ((pow_dvd_pow _ (by omega)).mul_right _)
    obtain ⟨T, hT⟩ := taylor_dvd U ℓ h N hℓ hh0 hd
    have hl := law _ _ hℓ hh0
    have hb := map_law F X (X ^ N) constantCoeff_X (by simp [hN])
    rw [map_pow, map_X] at hb
    rw [hUℓ, hUh, hb] at hl
    have hbd : Bd 1 (U.subst (ℓ + h)) := hl ▸ bd_map _
    have e : (U.subst (ℓ + h) : ℂ_[q]⟦X⟧) = X + X ^ N * W +
        X ^ (2 * N) * (T + (d⁄dX U).subst ℓ * V.subst (X ^ N : ℂ_[q]⟦X⟧)) := by
      rw [hUℓ] at hT
      rw [hW]
      linear_combination hT + ((d⁄dX U).subst ℓ : ℂ_[q]⟦X⟧) * hh'
    have := hbd (m + N)
    rw [e, map_add (f := _), map_add (f := _), coeff_X_pow_mul, coeff_X, if_neg (by omega), coeff_X_pow_mul', if_neg (by omega)] at this
    simpa using this
  have hq1 : ‖(q : ℂ_[q])‖ < 1 := by
    rw [← zc_natCast, norm_zc, PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hq.out.one_lt)
  have hder : Bd ‖(q : ℂ_[q])‖ (d⁄dX (U.subst (C (q : ℂ_[q]) * ℓ))) := by
    refine (sup_norm_laws q).2.2.2.2.2 _ W 0 _ hWint (by rw [hW0, norm_one]) ?_
    have e : X ^ 0 * W * d⁄dX (U.subst (C (q : ℂ_[q]) * ℓ))
        = C (q : ℂ_[q]) * W.subst (U.subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧) := by
      rw [derivative_subst (hs (hc q)), hW, subst_mul (hs (hB0 q)), subst_C',
        subst_comp_subst_apply (hs hℓ) (hs (hB0 q)), hℓB, Derivation.leibniz, derivative_C]
      simp only [smul_eq_mul]
      linear_combination (C (coeff 1 ℓ) * C (q : ℂ_[q]) *
        ((d⁄dX U).subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)) * hone
    rw [e]
    intro n
    rw [coeff_C_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) ((sup_norm_laws q).2.1 W _ 1 hWint hBq (hB0 q) n)
  have h2 : ∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ) : ℂ_[q]⟦X⟧)‖ < 1 := by
    intro k hk
    rcases k with _ | k
    · exact absurd (dvd_zero q) hk
    have := hder k
    rw [coeff_derivative, norm_mul] at this
    have hk1 : ‖((k : ℂ_[q]) + 1)‖ = 1 := by
      rw [← Nat.cast_succ, ← zc_natCast, norm_zc, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hq.out).2 hk
    rw [hk1, mul_one] at this
    exact this.trans_lt hq1
  refine ⟨hint, h2, fun hqq k a ha => ?_⟩
  have hv : Van (2 * q) (U.subst (C (q : ℂ_[q]) * ℓ)) := by
    intro n hn
    by_cases hd : q ∣ n
    · obtain ⟨c, rfl⟩ := hd
      have hc2 : c < 2 := by
        by_contra h
        have : q * 2 ≤ q * c := Nat.mul_le_mul_left q (by omega)
        omega
      interval_cases c
      · rw [mul_zero, coeff_zero_eq_constantCoeff_apply, hB0]; simp
      · rwa [mul_one]
    · exact h2 n hd
  obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 ((PadicInt.norm_le_pow_iff_mem_span_pow a k).1 ha)
  clear ha
  show Van _ _
  induction k with
  | zero =>
    intro n hn
    obtain rfl : n = 0 := by simpa using hn
    rw [coeff_zero_eq_constantCoeff_apply, hB0]; simp
  | succ k ih =>
    have := van_subst hBq (hint _) (hB0 _) hv ih
    rw [hcomp, ← zc_natCast, ← zc_mul, ← pow_succ'] at this
    convert this using 5
    ring

end GlobalTheory.MomOne.FormalMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupPadicMulIntegralVanishingOrderStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder : ∀ (q : ℕ) [Fact q.Prime] (F : FormalGroup 𝓞_ℂ_[q]) (U ℓ : ℂ_[q]⟦X⟧), constantCoeff U = 0 → constantCoeff ℓ = 0 → U.subst ℓ = X → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) U, PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) U → (∀ a : ℤ_[q], Bd 1 (U.subst (C (zc a) * ℓ))) ∧ (∀ k, ¬ q ∣ k → ‖coeff k (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1) ∧ (‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ < 1 → ∀ (k : ℕ) (a : ℤ_[q]), ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) → ∀ n < (2 * q) ^ k, ‖coeff n (U.subst (C (zc a) * ℓ))‖ < 1) := by
  first | exact @GlobalTheory.MomOne.FormalMul.padic_multiplications | exact GlobalTheory.MomOne.FormalMul.padic_multiplications | (intros; apply GlobalTheory.MomOne.FormalMul.padic_multiplications <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsSmallInPrimePow
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

theorem thue_normSq (d e : ℕ) (he : d + 1 = 4 * e) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + e * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have he' : (d : ℝ) + 1 = 4 * e := by exact_mod_cast he
  have h1 : ((u : ℂ) + (v : ℂ) * wK d).re = u + v / 2 := by
    simp [wK]; ring
  have h2 : ((u : ℂ) + (v : ℂ) * wK d).im = v * Real.sqrt d / 2 := by
    simp [wK]; ring
  rw [Complex.normSq_apply, h1, h2]
  push_cast
  linear_combination ((v : ℝ) ^ 2 / 4) * hs + ((v : ℝ) ^ 2 / 4) * he'

theorem thue_norm_zc {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.padic_norm_e_of_padicInt]

theorem thue_pigeon {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) (k : ℕ) :
    ∃ u v : ℤ, (u ≠ 0 ∨ v ≠ 0) ∧ u ^ 2 ≤ (q : ℤ) ^ k ∧ v ^ 2 ≤ (q : ℤ) ^ k ∧
      ‖(u : ℤ_[q]) + (v : ℤ_[q]) * a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
  have hq : q.Prime := Fact.out
  haveI : NeZero (q ^ k) := ⟨pow_ne_zero _ hq.ne_zero⟩
  set m := Nat.sqrt (q ^ k) with hm
  let f : Fin (m + 1) × Fin (m + 1) → ZMod (q ^ k) := fun p =>
    PadicInt.toZModPow k (((p.1 : ℕ) : ℤ_[q]) + ((p.2 : ℕ) : ℤ_[q]) * a)
  have hcard : Fintype.card (ZMod (q ^ k)) < Fintype.card (Fin (m + 1) × Fin (m + 1)) := by
    rw [ZMod.card, Fintype.card_prod, Fintype.card_fin]
    exact Nat.lt_succ_sqrt _
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  have hm2 : ((m : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    have := Nat.sqrt_le' (q ^ k)
    exact_mod_cast this
  have hb : ∀ i j : Fin (m + 1), (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) ^ 2 ≤ (q : ℤ) ^ k := by
    intro i j
    have hi := i.2
    have hj := j.2
    refine le_trans ?_ hm2
    apply sq_le_sq' <;> omega
  refine ⟨((x.1 : ℕ) : ℤ) - ((y.1 : ℕ) : ℤ), ((x.2 : ℕ) : ℤ) - ((y.2 : ℕ) : ℤ), ?_, hb _ _, hb _ _, ?_⟩
  · by_contra h
    push_neg at h
    apply hxy
    ext
    · have := h.1; omega
    · have := h.2; omega
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have : PadicInt.toZModPow k ((((x.1 : ℕ) : ℤ_[q]) + ((x.2 : ℕ) : ℤ_[q]) * a) -
        (((y.1 : ℕ) : ℤ_[q]) + ((y.2 : ℕ) : ℤ_[q]) * a)) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hf
    rw [← this]
    congr 1
    push_cast
    ring

theorem exists_small_in_prime_pow : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → ∀ k : ℕ, ∃ (β : ℂ) (N : ℕ), InOK d β ∧ β ≠ 0 ∧ ‖ι β‖ ≤ (q : ℝ) ^ (-(k : ℤ)) ∧ (N : ℂ) = β * conj β ∧ N ≤ (d + 3) * q ^ k := by
  intro d q _ ι hd h16 hs k
  obtain ⟨⟨-, hw, -⟩, h2, -⟩ := GlobalTheory.T.imagQuadraticMaximalOrder_arithmetic_at_split_prime d q ι hd h16 hs
  obtain ⟨⟨a, ha⟩, -⟩ := h2 _ hw
  obtain ⟨u, v, huv, hu, hv, hn⟩ := thue_pigeon a k
  obtain ⟨e, he⟩ : ∃ e : ℕ, d + 1 = 4 * e := ⟨(d + 1) / 4, by omega⟩
  have he1 : (1 : ℤ) ≤ e := by omega
  have hed : (e : ℤ) ≤ d := by omega
  have hpos : 0 < u ^ 2 + u * v + e * v ^ 2 := by
    have h3 : v ^ 2 ≤ e * v ^ 2 := by nlinarith [sq_nonneg v]
    have h4 : 0 < u ^ 2 + v ^ 2 := by
      rcases huv with h | h
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg v]
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg u]
    nlinarith [sq_nonneg (u + v)]
  have hN := thue_normSq d e he u v
  obtain ⟨N, hNe⟩ := Int.eq_ofNat_of_zero_le hpos.le
  refine ⟨(u : ℂ) + (v : ℂ) * wK d, N, ⟨u, v, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [h, map_zero] at hN
    have : u ^ 2 + u * v + e * v ^ 2 = 0 := by exact_mod_cast hN.symm
    omega
  · have : ι ((u : ℂ) + (v : ℂ) * wK d) = zc ((u : ℤ_[q]) + (v : ℤ_[q]) * a) := by
      rw [map_add (f := _), map_mul, ha]
      simp [zc]
    rw [this, thue_norm_zc]
    exact hn
  · rw [Complex.mul_conj, hN, hNe]
    simp
  · have h5 : (e : ℤ) * v ^ 2 ≤ d * (q : ℤ) ^ k :=
      mul_le_mul hed hv (sq_nonneg v) (by positivity)
    have h6 : (N : ℤ) ≤ (d + 3) * (q : ℤ) ^ k := by
      rw [← hNe]
      nlinarith [sq_nonneg (u - v), sq_nonneg u, sq_nonneg v]
    exact_mod_cast h6

end GlobalTheory.MomOne
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne

private theorem norm_zc_eq {q : ℕ} [Fact q.Prime] (a : ℤ_[q]) : ‖zc a‖ = ‖a‖ := by
  unfold zc
  exact (PadicComplex.norm_extends' (p := q) (a : ℚ_[q])).trans (PadicInt.norm_def).symm

private theorem zc_natCast_eq {q : ℕ} [Fact q.Prime] (n : ℕ) : zc (n : ℤ_[q]) = (n : ℂ_[q]) := by
  simp [zc]

theorem height_one_of_split : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (F : FormalGroup 𝓞_ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)), PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u))] : Fin 2 → MvPowerSeries (Fin 2) ℂ_[q]) (MvPowerSeries.map (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F.toPowerSeries) = PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[q]) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) → ∃ ℓ : ℂ_[q]⟦X⟧, constantCoeff ℓ = 0 ∧ PowerSeries.subst ℓ (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = X ∧ ‖coeff q (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ = 1 ∧ ∀ k < q, ‖coeff k (PowerSeries.subst (C (q : ℂ_[q]) * ℓ) (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)))‖ < 1 := by
  intro d q _ M F hd hd16 hs hOK hM hF
  set U : ℂ_[q]⟦X⟧ := PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u) with hUdef
  have flow := uw_elliptic_flow q M hM
  have hU0 : constantCoeff U = 0 := by
    rw [hUdef, ← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [flow.2.2.2.2.1]

  obtain ⟨ℓ, hchart, hℓX⟩ := Basic.exists_chart M hM
  have hℓ0 : constantCoeff ℓ = 0 := hchart.2.1
  have hUℓ : U.subst ℓ = X := hℓX
  obtain ⟨P1, P2, P3⟩ := GlobalTheory.T.formalGroup_padicMul_integral_vanishingOrder q F U ℓ hU0 hℓ0 hUℓ hF
  refine ⟨ℓ, hℓ0, hUℓ, ?_, ?_⟩
  ·

    have hle : ‖coeff q (U.subst (C (q : ℂ_[q]) * ℓ))‖ ≤ 1 := by
      have := P1 (q : ℤ_[q])
      rw [zc_natCast_eq] at this
      exact this q
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    have P3' := P3 hlt
    set k : ℕ := d + 3 with hk
    obtain ⟨β, N, hβ, hβ0, hβn, hN, hNle⟩ := exists_small_in_prime_pow d q M.ι hd hd16 hs k
    have ar := okArith d q M.ι hd hd16 hs
    obtain ⟨a, ha⟩ := (ar.2.1 β hβ).1
    have hanorm : ‖a‖ ≤ (q : ℝ) ^ (-(k : ℤ)) := by
      rw [← norm_zc_eq, ← ha]
      exact hβn
    have hlat : ∀ l ∈ M.L.lattice, β * l ∈ M.L.lattice := by
      intro l hl
      rw [hOK] at hl ⊢
      exact (ar.1.2.2 β l hβ hl).2.1
    have hu0 : AnalyticAt ℂ M.u 0 := (flow.2.2.2.2.2.2.2.2 0 (Or.inl ((hOK 0).2 ⟨0, 0, by simp⟩))).1
    have hhat : hat M.ι ℓ (fun z => M.u (β * z)) = U.subst (C (zc a) * ℓ) := by
      rw [(TaylorRead.hat_laws q M.ι ℓ hℓ0).2.2.2.2.2.1 M.u β hu0, ← ha]
      rfl
    have hbd : Bd 1 (hat M.ι ℓ (fun z => M.u (β * z))) := by
      rw [hhat]
      exact P1 a
    obtain ⟨n, hnN, hn1⟩ := GlobalTheory.T.exists_unit_coeff_mul_series_le_norm q M ℓ β N hchart hβ0 hlat hN hbd
    have hnlt : n < (2 * q) ^ k := by
      have hq : 0 < q ^ k := pow_pos (Fact.out : q.Prime).pos k
      have h2 : d + 3 < 2 ^ k := Nat.lt_two_pow_self
      calc n ≤ N := hnN
        _ ≤ (d + 3) * q ^ k := hNle
        _ < 2 ^ k * q ^ k := Nat.mul_lt_mul_of_pos_right h2 hq
        _ = (2 * q) ^ k := (mul_pow 2 q k).symm
    have := P3' k a hanorm n hnlt
    rw [← hhat, hn1] at this
    exact lt_irrefl _ this
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hc : constantCoeff (C (q : ℂ_[q]) * ℓ) = 0 := by simp [hℓ0]
      rw [coeff_zero_eq_constantCoeff_apply, TaylorRead.constantCoeff_subst_of hc, hU0, norm_zero]
      exact one_pos
    · exact P2 k (Nat.not_dvd_of_pos_of_lt hkpos hk)

end GlobalTheory.MomOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMultiplicativeChartAtSplitPrime
noncomputable section

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.SplitChart

open ChordLaw

section Algebra

variable {k : Type} [CommRing k] {σ : Type}

theorem law_two {U : k⟦X⟧} (hU : constantCoeff U = 0) {F : MvPowerSeries (Fin 2) k}
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U] : Fin 2 → MvPowerSeries (Fin 2) k) F =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U)
    {a b : MvPowerSeries σ k} (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst (![PowerSeries.subst a U, PowerSeries.subst b U] : Fin 2 → MvPowerSeries σ k) F =
      PowerSeries.subst (a + b) U := by
  have hab := hasSubst_two ha hb
  have c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) U) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU
  have h := congrArg (MvPowerSeries.subst ![a, b]) H
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_two (c0 0) (c0 1)) hab, subst_psubst hab (by simp),
    MvPowerSeries.subst_add hab, MvPowerSeries.subst_X hab, MvPowerSeries.subst_X hab] at h
  refine Eq.trans ?_ h
  congr 1
  funext i
  fin_cases i
  · simp [subst_psubst hab (MvPowerSeries.constantCoeff_X 0), MvPowerSeries.subst_X hab]
  · simp [subst_psubst hab (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X hab]

theorem constantCoeff_mulN {R : Type} [CommRing R] (F : FormalGroup R) (n : ℕ) :
    constantCoeff (JetMomFound.mulN F n) = 0 := by
  induction n with
  | zero => simp [JetMomFound.mulN]
  | succ n ih =>
    refine MvPowerSeries.constantCoeff_subst_eq_zero (hasSubst_two ih constantCoeff_X) ?_ F.zero_constantCoeff
    intro i
    fin_cases i
    · exact ih
    · exact constantCoeff_X

theorem map_mulN {R : Type} [CommRing R] (φ : R →+* k) (F : FormalGroup R) {U ℓ : k⟦X⟧}
    (hU : constantCoeff U = 0) (hℓ : constantCoeff ℓ = 0) (hUℓ : PowerSeries.subst ℓ U = (X : k⟦X⟧))
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U] : Fin 2 → MvPowerSeries (Fin 2) k)
      (MvPowerSeries.map φ F.toPowerSeries) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) U) (n : ℕ) :
    PowerSeries.map φ (JetMomFound.mulN F n) = PowerSeries.subst (C (n : k) * ℓ) U := by
  induction n with
  | zero =>
    simp only [JetMomFound.mulN, map_zero, Nat.cast_zero, zero_mul]
    exact (PowerSeries.subst_zero_of_constantCoeff_zero hU).symm
  | succ n ih =>
    have h := law_two hU H (a := (C (n : k) * ℓ : k⟦X⟧)) (b := ℓ)
      (show constantCoeff (C (n : k) * ℓ) = 0 by rw [map_mul, hℓ, mul_zero]) hℓ
    have e : (C ((n + 1 : ℕ) : k) * ℓ : k⟦X⟧) = C (n : k) * ℓ + ℓ := by
      rw [Nat.cast_succ, map_add (f := _), map_one]; ring
    rw [e]
    refine Eq.trans ?_ h
    rw [← ih, hUℓ]
    refine (MvPowerSeries.map_subst (hasSubst_two (constantCoeff_mulN F n) constantCoeff_X) _).trans ?_
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact PowerSeries.map_X φ

theorem deriv_of_mul {g : k⟦X⟧}
    (H : PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) g +
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g +
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) g *
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) g) :
    derivative g = C (coeff 1 g) * (1 + g) := by
  have HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) k) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have HS : PowerSeries.HasSubst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have h := congrArg (MvPowerSeries.pderiv (R := k) 1) H
  simp only [map_add (f := _), Derivation.leibniz, smul_eq_mul, GlobalTheory.FormalCalc.pderiv_powerSeries_subst (HX _),
    GlobalTheory.FormalCalc.pderiv_powerSeries_subst HS] at h
  have p0 : MvPowerSeries.pderiv (R := k) 1 (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) = 0 := by
    simp [MvPowerSeries.pderiv_X_of_ne]
  have p1 : MvPowerSeries.pderiv (R := k) 1 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) k) = 1 := by simp
  simp only [p0, p1, zero_add, mul_one, mul_zero, add_zero] at h
  have ha : MvPowerSeries.HasSubst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k) :=
    hasSubst_two constantCoeff_X (map_zero _)
  have h2 := congrArg (MvPowerSeries.subst (![(X : k⟦X⟧), 0] : Fin 2 → MvPowerSeries Unit k)) h
  rw [subst_psubst ha (by simp), MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
    MvPowerSeries.subst_mul ha, subst_psubst ha (MvPowerSeries.constantCoeff_X 0),
    subst_psubst ha (MvPowerSeries.constantCoeff_X 1), MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, add_zero] at h2
  have e : PowerSeries.subst (0 : MvPowerSeries Unit k) (derivative g) = (C (coeff 1 g) : k⟦X⟧) := by
    rw [PowerSeries.subst_zero_eq_C_constantCoeff, MvPowerSeries.map_C, ← coeff_zero_eq_constantCoeff_apply,
      coeff_derivative]
    simp [PowerSeries.C]
  rw [X_subst, X_subst, e] at h2
  rw [h2]
  ring

theorem subst_log_eq_X [IsAddTorsionFree k] {g L : k⟦X⟧} {γ ω : k} (hγ : γ * ω = 1) (hg : constantCoeff g = 0)
    (hd : derivative g = C γ * (1 + g)) (hL0 : constantCoeff L = 0) (hL : (1 + X) * derivative L = 1) :
    PowerSeries.subst (C ω * L) g = (X : k⟦X⟧) := by
  have h0 : constantCoeff (C ω * L) = 0 := by rw [map_mul, hL0, mul_zero]
  have Hs := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hh0 : constantCoeff (PowerSeries.subst (C ω * L) g : k⟦X⟧) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h0 _ hg
  have hD : derivative (PowerSeries.subst (C ω * L) g : k⟦X⟧) =
      C γ * (1 + PowerSeries.subst (C ω * L) g) * (C ω * derivative L) := by
    rw [PowerSeries.derivative_subst Hs, hd, PowerSeries.subst_mul Hs, PowerSeries.subst_add Hs,
      PowerSeries.subst_C, ← PowerSeries.coe_substAlgHom Hs, map_one, Derivation.leibniz, derivative_C]
    simp only [smul_eq_mul, mul_zero, add_zero]
    rfl
  generalize (PowerSeries.subst (C ω * L) g : k⟦X⟧) = h at hh0 hD
  have hC : (C γ : k⟦X⟧) * C ω = 1 := by rw [← map_mul, hγ, map_one]
  set r := derivative L with hr
  have hr' := congrArg (derivative (R := k)) hL
  rw [Derivation.leibniz, map_add (f := _), derivative_X, Derivation.map_one_eq_zero] at hr'
  simp only [smul_eq_mul] at hr'
  have hr0 : constantCoeff r = 1 := by simpa using congrArg constantCoeff hL
  have key : (1 + h) * r = 1 := by
    let _ : HasUniqueDiv k := IsAddTorsionFree.hasUniqueDiv
    apply derivative.ext
    · rw [Derivation.leibniz, map_add (f := _), Derivation.map_one_eq_zero, hD]
      simp only [smul_eq_mul]
      linear_combination (1 + h) * r * hr' - (1 + h) * derivative r * hL + (1 + h) * r ^ 2 * hC
    · simp [hh0, hr0]
  linear_combination (1 + X) * key - (1 + h) * hL

theorem exists_scale {R K : Type} [CommRing R] [Field K] [CharZero K] (φ : R →+* K) (F : FormalGroup R)
    {U ℓ L : K⟦X⟧} (hU : constantCoeff U = 0) (hℓ : constantCoeff ℓ = 0)
    (hUℓ : PowerSeries.subst ℓ U = (X : K⟦X⟧))
    (H : MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)
      (MvPowerSeries.map φ F.toPowerSeries) =
      PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U)
    {f : R⟦X⟧} (hf : JetMomFound.IsIsoGm F f) (hL0 : constantCoeff L = 0) (hL : (1 + X) * derivative L = 1) :
    ∃ (ω : K) (e : R⟦X⟧), IsUnit (coeff 1 e) ∧ PowerSeries.subst (C ω * L) U = PowerSeries.map φ e := by
  obtain ⟨f0, f1, hf⟩ := hf
  have HX : ∀ i, PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have c0 : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) f) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ f0
  have cU : ∀ i, MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) U) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hU
  have ha := hasSubst_two (c0 0) (c0 1)
  have hb := hasSubst_two (cU 0) (cU 1)
  rw [FormalGroup.𝔾ₘ_toPowerSeries, MvPowerSeries.subst_add ha, MvPowerSeries.subst_add ha,
    MvPowerSeries.subst_mul ha, MvPowerSeries.subst_X ha, MvPowerSeries.subst_X ha] at hf
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hf
  have h1 := congrArg (MvPowerSeries.map φ) hf
  rw [map_add (f := _), map_add (f := _), map_mul,
    PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero F.zero_constantCoeff),
    PowerSeries.map_subst (HX 0), PowerSeries.map_subst (HX 1), MvPowerSeries.map_X, MvPowerSeries.map_X] at h1
  set f' := PowerSeries.map φ f with hf'
  have f0' : constantCoeff f' = 0 := by
    rw [hf', ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, f0, map_zero]
  have h2 := congrArg (MvPowerSeries.subst (![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) U,
      PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) U] : Fin 2 → MvPowerSeries (Fin 2) K)) h1
  rw [subst_psubst hb (by rw [MvPowerSeries.constantCoeff_map, F.zero_constantCoeff, map_zero]), H,
    MvPowerSeries.subst_add hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_mul hb,
    subst_psubst hb (MvPowerSeries.constantCoeff_X 0), subst_psubst hb (MvPowerSeries.constantCoeff_X 1),
    MvPowerSeries.subst_X hb, MvPowerSeries.subst_X hb] at h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [← psubst_psubst (by simp) hU, ← psubst_psubst (MvPowerSeries.constantCoeff_X 0) hU,
    ← psubst_psubst (MvPowerSeries.constantCoeff_X 1) hU] at h2
  have hd := deriv_of_mul h2
  have g0 : constantCoeff (PowerSeries.subst U f' : K⟦X⟧) = 0 := PowerSeries.constantCoeff_subst_eq_zero hU _ f0'
  have hγ : coeff 1 (PowerSeries.subst U f' : K⟦X⟧) ≠ 0 := by
    intro hz
    have hg : (PowerSeries.subst U f' : K⟦X⟧) = 0 := by
      apply derivative.ext
      · rw [hd, hz]; simp
      · rw [g0, map_zero]
    have h3 := psubst_psubst (σ := Unit) hℓ hU f'
    rw [hg, hUℓ, X_subst, ← PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hℓ),
      map_zero] at h3
    have h4 := f1.map φ
    rw [← coeff_map, ← hf', ← h3, map_zero] at h4
    exact not_isUnit_zero h4
  have h5 := subst_log_eq_X (mul_inv_cancel₀ hγ) g0 hd hL0 hL
  set ω := (coeff 1 (PowerSeries.subst U f' : K⟦X⟧))⁻¹
  have h0 : constantCoeff (C ω * L) = 0 := by rw [map_mul, hL0, mul_zero]
  rw [psubst_psubst (σ := Unit) h0 hU] at h5
  have u0 : constantCoeff (PowerSeries.subst (C ω * L) U : K⟦X⟧) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero h0 _ hU
  refine ⟨ω, f.substInvOfIsUnit f1, by rw [coeff_one_substInvOfIsUnit]; exact Units.isUnit _, ?_⟩
  have h6 := congrArg (MvPowerSeries.map φ) (subst_substInvOfIsUnit_left f f0 f1)
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' f0)] at h6
  have h7 : PowerSeries.subst f' (PowerSeries.map φ (f.substInvOfIsUnit f1)) = (X : K⟦X⟧) :=
    h6.trans (PowerSeries.map_X φ)
  have h8 := psubst_psubst (σ := Unit) u0 f0' (PowerSeries.map φ (f.substInvOfIsUnit f1))
  rw [h7, h5, X_subst, PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' u0)] at h8
  exact h8

end Algebra

theorem exists_mChart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → IsAlgebraic ℚ M.W.a₁ → IsAlgebraic ℚ M.W.a₂ → IsAlgebraic ℚ M.W.a₃ → IsAlgebraic ℚ M.W.a₄ → IsAlgebraic ℚ M.W.a₆ → ∃ ω : ℂ_[q], M.MChart ω := by
  intro d q _ M hd hd16 hsp hL hOk b₁ b₂ b₃ b₄ b₆
  obtain ⟨F, hfin, H⟩ := exists_formalGroup_add q M hOk b₁ b₂ b₃ b₄ b₆
  obtain ⟨ℓ, hℓ, hUℓ, h1, h2⟩ := height_one_of_split d q M F hd hd16 hsp hL hOk H
  have hU : constantCoeff (PowerSeries.map (M.ι : ℂ →+* ℂ_[q]) (tay M.u)) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, tay, coeff_mk]
    simp [Mdl.u]
  rw [← map_mulN (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H q] at h1 h2
  obtain ⟨f, hf⟩ := GlobalTheory.ConvSer.HeightOneInt.htOneIsGm q F hfin ⟨h1, h2⟩
  have hL0 : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by simp [logS]
  obtain ⟨ω, e, he1, he⟩ := exists_scale (algebraMap 𝓞_ℂ_[q] ℂ_[q]) F hU hℓ hUℓ H hf hL0
    (MulSeries.mulS_laws q).2.2.2.2.1
  have hO : ∀ x : 𝓞_ℂ_[q], ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖ ≤ 1 := fun x => by
    have hx := (Valuation.mem_valuationSubring_iff _ _).1 x.2
    rw [PadicComplex.norm_eq_norm]
    exact Valued.toNormedField.norm_le_one_iff.2 hx
  refine ⟨ω, hOk, by rw [map_mul, hL0, mul_zero], fun n => ?_, ?_⟩
  · rw [hat, he, coeff_map]; exact hO _
  · rw [hat, he, coeff_map]
    obtain ⟨v, hv⟩ := he1.exists_right_inv
    have h3 := congrArg (fun x => ‖algebraMap 𝓞_ℂ_[q] ℂ_[q] x‖) hv
    simp only [map_mul, norm_mul, map_one, norm_one] at h3
    have h4 := hO (coeff 1 e)
    have h5 := hO v
    nlinarith [norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] (coeff 1 e)), norm_nonneg (algebraMap 𝓞_ℂ_[q] ℂ_[q] v)]

end GlobalTheory.MomOne.SplitChart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMultiplicativeChartAtSplitPrimeStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicativeChart_at_splitPrime : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.Ok → IsAlgebraic ℚ M.W.a₁ → IsAlgebraic ℚ M.W.a₂ → IsAlgebraic ℚ M.W.a₃ → IsAlgebraic ℚ M.W.a₄ → IsAlgebraic ℚ M.W.a₆ → ∃ ω : ℂ_[q], M.MChart ω := by
  first | exact @GlobalTheory.MomOne.SplitChart.exists_mChart | exact GlobalTheory.MomOne.SplitChart.exists_mChart | (intros; apply GlobalTheory.MomOne.SplitChart.exists_mChart <;> assumption)
end
