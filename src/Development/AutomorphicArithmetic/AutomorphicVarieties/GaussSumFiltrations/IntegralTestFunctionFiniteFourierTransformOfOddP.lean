module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntMatrixIsometryPrimeOrderLatticeStability
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertHolomorphicUnnormalizedSlashOfPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.DualLatticeIndexEqDiscrPowMulDetPow

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.WeilIndexConstantCongruentOneModPrime
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.DConst

variable {F : Type} [Field F] [NumberField F]

theorem absNorm_coprime_of_away {p : ℕ} (hp : p.Prime) (J : Ideal (𝓞 F))
    (hJ : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → ¬ J ≤ w.asIdeal) :
    (Ideal.absNorm J).Coprime p := by
  classical
  obtain ⟨w0, hw0⟩ := DenP.exists_place (F := F) hp
  have hJ0 : J ≠ ⊥ := by rintro rfl; exact hJ w0 hw0 bot_le
  have hsup : J ⊔ Ideal.span {((p : ℕ) : 𝓞 F)} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hpM : ((p : ℕ) : 𝓞 F) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hM0 : M ≠ ⊥ := by rintro rfl; exact hp.ne_zero (by simpa using hpM)
    exact hJ ⟨M, hM.isPrime, hM0⟩ hpM (le_sup_left.trans hle)
  obtain ⟨a, ha, z, hz, haz⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 hsup)
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  haveI : Fact p.Prime := ⟨hp⟩
  have hn0 : Ideal.absNorm J ≠ 0 := fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hn0
  haveI : Finite (𝓞 F ⧸ J) := Nat.finite_of_card_ne_zero hn0
  letI : Fintype (𝓞 F ⧸ J) := Fintype.ofFinite _
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd
  have h1 : (p : 𝓞 F ⧸ J) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
  have h2 : (Ideal.Quotient.mk J b) * (p : 𝓞 F ⧸ J) = 1 := by
    have := congrArg (Ideal.Quotient.mk J) haz
    rw [map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, map_mul, map_natCast, map_one] at this
    exact this
  have h3 : x = 0 := by
    calc x = (Ideal.Quotient.mk J b * (p : 𝓞 F ⧸ J)) * x := by rw [h2, one_mul]
      _ = 0 := by rw [mul_assoc, h1, mul_zero]
  rw [h3, addOrderOf_zero] at hx
  exact hp.one_lt.ne hx

theorem diff_cofactor {p : ℕ} (δ : F) (hδ : IsDel p δ) (d : 𝓞 F)
    (hd : d ∈ differentIdeal ℤ (𝓞 F)) (hu : PUnit p ((d : F) / δ)) :
    ∃ J : Ideal (𝓞 F), Ideal.span {d} = differentIdeal ℤ (𝓞 F) * J ∧
      ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → ¬ J ≤ w.asIdeal := by
  classical
  have hle : Ideal.span {d} ≤ differentIdeal ℤ (𝓞 F) := (Ideal.span_singleton_le_iff_mem _).2 hd
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  refine ⟨J, hJ, fun w hw hJw => ?_⟩
  have hv := hu w hw
  rw [map_div₀, hδ w hw, div_eq_one_iff_eq WithZero.exp_ne_zero] at hv
  have hv' : w.intValuation d = WithZero.exp (-(ordI w (differentIdeal ℤ (𝓞 F)) : ℤ)) := by
    rw [← hv]; exact (HeightOneSpectrum.valuation_of_algebraMap (K := F) w d).symm
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv'
    exact WithZero.exp_ne_zero hv'.symm
  have hJ0 : J ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hJ
    exact hd0 (Ideal.span_singleton_eq_bot.1 hJ)
  rw [w.intValuation_if_neg hd0, WithZero.exp_inj, neg_inj, Nat.cast_inj, hJ, ← Associates.mk_mul_mk,
    Associates.count_mul (Associates.mk_ne_zero.2 DenP.diff_ne) (Associates.mk_ne_zero.2 hJ0)
      w.associates_irreducible] at hv'
  have hc := (Associates.count_ne_zero_iff_dvd hJ0 w.irreducible).2 (Ideal.dvd_iff_le.2 hJw)
  unfold ordI at hv'
  exact hc (by omega)

theorem norm_intCast_eq_natAbs {p : ℕ} [Fact p.Prime] (z : ℤ) :
    ‖((z : ℚ) : ℚ_[p])‖ = ‖((z.natAbs : ℚ) : ℚ_[p])‖ := by
  rcases Int.natAbs_eq z with h | h
  · have e : ((z : ℚ) : ℚ_[p]) = ((z.natAbs : ℚ) : ℚ_[p]) := by
      conv_lhs => rw [h]
      simp only [Int.cast_natCast]
    rw [e]
  · have e : ((z : ℚ) : ℚ_[p]) = -((z.natAbs : ℚ) : ℚ_[p]) := by
      conv_lhs => rw [h]
      simp only [Int.cast_neg, Int.cast_natCast, Rat.cast_neg]
    rw [e, norm_neg]

theorem norm_norm_eq_one {p : ℕ} [Fact p.Prime] (x : F) (hx : PUnit p x) :
    ‖((Algebra.norm ℚ x : ℚ) : ℚ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨N, hN0, hNc, hN⟩ := DenP.exists_away hp x
  have hint : IsIntegral ℤ ((N : F) * x) := (DenP.isIntegral_iff_val _).2 fun w => by
    by_cases hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal
    · rw [map_mul, DenP.val_coprime hNc hw, hx w hw, one_mul]
    · exact hN w hw
  let a : 𝓞 F := ⟨_, hint⟩
  have haF : (a : F) = (N : F) * x := rfl
  have ha : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal →
      ¬ Ideal.span {a} ≤ w.asIdeal := by
    intro w hw hle
    have h1 : a ∈ w.asIdeal := hle (Ideal.mem_span_singleton_self a)
    have h2 : w.valuation F (algebraMap (𝓞 F) F a) = 1 := by
      show w.valuation F ((N : F) * x) = 1
      rw [map_mul, DenP.val_coprime hNc hw, hx w hw, one_mul]
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff] at h2
    exact h2 h1
  have hc := absNorm_coprime_of_away hp _ ha
  rw [Ideal.absNorm_span_singleton] at hc
  have h1 : ‖(((Algebra.norm ℤ a : ℤ) : ℚ) : ℚ_[p])‖ = 1 := by
    rw [norm_intCast_eq_natAbs, Rat.cast_natCast, Padic.norm_natCast_eq_one_iff]
    exact hc.symm
  have hNn : Algebra.norm ℚ (N : F) = (N : ℚ) ^ Module.finrank ℚ F := by
    rw [← map_natCast (algebraMap ℚ F), Algebra.norm_algebraMap]
  rw [Algebra.coe_norm_int, haF, map_mul, hNn, Rat.cast_mul, norm_mul, Rat.cast_pow, norm_pow,
    Rat.cast_natCast, Padic.norm_natCast_eq_one_iff.2 hNc.symm, one_pow, one_mul] at h1
  exact h1

theorem norm_norm_eq_disc {p : ℕ} [Fact p.Prime] (δ c : F) (hδ : IsDel p δ) (hc : PUnit p (c / δ)) :
    ‖((Algebra.norm ℚ c : ℚ) : ℚ_[p])‖ = ‖(((discr F).natAbs : ℚ) : ℚ_[p])‖ := by
  have hp : p.Prime := Fact.out
  obtain ⟨hδ0, -, -, d, -, hd, -, -, hdu⟩ := denominators_prime_to F p hp δ hδ
  obtain ⟨J, hJ, hJw⟩ := diff_cofactor δ hδ d hd hdu
  have hd0 : (d : F) ≠ 0 := by
    obtain ⟨w, hw⟩ := DenP.exists_place (F := F) hp
    intro h
    have := hdu w hw
    rw [h, zero_div, map_zero] at this
    exact zero_ne_one this
  have hcd : PUnit p (c / d) := fun w hw => by
    have e : c / (d : F) = (c / δ) / ((d : F) / δ) := by field_simp
    rw [e, map_div₀, hc w hw, hdu w hw, div_one]
  have h1 := norm_norm_eq_one (p := p) _ hcd
  have e2 : c = c / d * d := by field_simp
  have hJc := absNorm_coprime_of_away hp J hJw
  have hnd : (Algebra.norm ℤ d).natAbs = (discr F).natAbs * Ideal.absNorm J := by
    rw [← Ideal.absNorm_span_singleton, hJ, map_mul, NumberField.absNorm_differentIdeal (K := F)]
  have h2 : ‖((Algebra.norm ℚ (d : F) : ℚ) : ℚ_[p])‖ = ‖(((discr F).natAbs : ℚ) : ℚ_[p])‖ := by
    rw [← Algebra.coe_norm_int, norm_intCast_eq_natAbs, hnd, Nat.cast_mul, Rat.cast_mul, norm_mul,
      Rat.cast_natCast (Ideal.absNorm J : ℕ), Padic.norm_natCast_eq_one_iff.2 hJc.symm, mul_one]
  rw [e2, map_mul, Rat.cast_mul, norm_mul, h1, one_mul, h2]

theorem norm_le_one_of_near {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹) : ‖x‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  calc ‖x‖ = ‖(x - 1) + 1‖ := by ring_nf
    _ ≤ max ‖x - 1‖ ‖(1 : ℚ_[p])‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ 1 := max_le (hx.trans hp1) (by simp)

theorem near_mul {p : ℕ} [Fact p.Prime] {x y : ℚ_[p]} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹)
    (hy : ‖y - 1‖ ≤ (p : ℝ)⁻¹) : ‖x * y - 1‖ ≤ (p : ℝ)⁻¹ := by
  have h1 := norm_le_one_of_near hx
  calc ‖x * y - 1‖ = ‖x * (y - 1) + (x - 1)‖ := by ring_nf
    _ ≤ max ‖x * (y - 1)‖ ‖x - 1‖ := IsUltrametricDist.norm_add_le_max _ _
    _ ≤ (p : ℝ)⁻¹ := by
      refine max_le ?_ hx
      rw [norm_mul]
      calc ‖x‖ * ‖y - 1‖ ≤ 1 * (p : ℝ)⁻¹ := by gcongr
        _ = (p : ℝ)⁻¹ := one_mul _

theorem near_pow {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹) (n : ℕ) :
    ‖x ^ n - 1‖ ≤ (p : ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; exact near_mul ih hx

theorem near_inv {p : ℕ} [Fact p.Prime] {x : ℚ_[p]} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖x⁻¹ - 1‖ ≤ (p : ℝ)⁻¹ := by
  have hp : p.Prime := Fact.out
  have hlt : ‖x - 1‖ < ‖(1 : ℚ_[p])‖ := by
    rw [norm_one]; exact hx.trans_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
  have hn : ‖x‖ = 1 := by rw [Padic.norm_eq_of_norm_sub_lt_right hlt, norm_one]
  have hx0 : x ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  have e : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by field_simp; ring
  rw [e, norm_mul, norm_neg, norm_inv, hn, inv_one, mul_one]
  exact hx

theorem fermat {p : ℕ} [Fact p.Prime] (u : ℚ_[p]) (hu : ‖u‖ = 1) : ‖u ^ (p - 1) - 1‖ ≤ (p : ℝ)⁻¹ := by
  let v : ℤ_[p] := ⟨u, hu.le⟩
  have hv : ‖v‖ = 1 := hu
  have hz : PadicInt.toZMod v ≠ 0 := by
    intro h
    have h1 : v ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h
    have h2 := PadicInt.mem_nonunits.1 (IsLocalRing.mem_maximalIdeal _ |>.1 h1)
    rw [hv] at h2; exact lt_irrefl _ h2
  have h1 : PadicInt.toZMod (v ^ (p - 1) - 1) = 0 := by
    rw [map_sub, map_pow, ZMod.pow_card_sub_one_eq_one hz, map_one, sub_self]
  have h2 : ‖v ^ (p - 1) - 1‖ < 1 := by
    have h3 : v ^ (p - 1) - 1 ∈ IsLocalRing.maximalIdeal ℤ_[p] := by rw [← PadicInt.ker_toZMod]; exact h1
    exact PadicInt.mem_nonunits.1 (IsLocalRing.mem_maximalIdeal _ |>.1 h3)
  obtain ⟨y, hy⟩ := (PadicInt.norm_lt_one_iff_dvd _).1 h2
  have h4 : ‖v ^ (p - 1) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [hy, norm_mul, PadicInt.norm_p]
    calc (p : ℝ)⁻¹ * ‖y‖ ≤ (p : ℝ)⁻¹ * 1 := by gcongr; exact PadicInt.norm_le_one y
      _ = (p : ℝ)⁻¹ := mul_one _
  have e : ((v ^ (p - 1) - 1 : ℤ_[p]) : ℚ_[p]) = u ^ (p - 1) - 1 := by push_cast; rfl
  rw [← e]
  exact h4

end GlobalTheory.HilbertThetaSeries.DConst


open GlobalTheory.HilbertThetaSeries.DConst in
theorem GlobalTheory.HilbertThetaSeries.wC_near_one : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ c : F, IsDel p δ → PUnit p (c / δ) → ∀ t N : ℕ, N.Coprime p → (-1) ^ ((p - 1) / 2) * (t : ℤ) ≡ 1 [ZMOD p] → ‖ι.symm (wC (p - 1) t (N : F) c) - 1‖ ≤ (p : ℝ)⁻¹ := by
  intro F _ _ p _ ι hp2 δ c hδ hc t N hN ht
  have hp : p.Prime := Fact.out
  set n := Module.finrank ℚ F with hn
  set m := (p - 1) / 2 with hmdef
  have hm : p - 1 = 2 * m := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    omega
  set q : ℚ := Algebra.norm ℚ c / ((N : ℚ) ^ n) ^ 2 / ((discr F).natAbs : ℚ) with hq
  set R : ℚ := (-1) ^ (m * n) * (Algebra.norm ℚ c) ^ (p - 1) /
    (((N : ℚ) ^ n) ^ (2 * (p - 1)) * ((discr F).natAbs : ℚ) ^ (p - 1) * (t : ℚ) ^ n) with hR
  have hw : wC (p - 1) t (N : F) c = (R : ℂ) := by
    have hNn : Algebra.norm ℚ (N : F) = (N : ℚ) ^ n := by
      rw [← map_natCast (algebraMap ℚ F), Algebra.norm_algebraMap]
    have hI : (-Complex.I) ^ ((p - 1) * n) = (-1) ^ (m * n) := by
      rw [hm, mul_assoc, pow_mul, neg_sq, Complex.I_sq]
    unfold wC
    rw [hNn, hI, hR]
    push_cast
    ring
  have hQ : ι.symm (R : ℂ) - 1 = algebraMap ℚ_[p] (Qbar p) ((R : ℚ_[p]) - 1) := by
    rw [map_ratCast, map_sub, map_ratCast, map_one]
  rw [hw, hQ]
  show ‖algebraMap ℚ_[p] (PadicAlgCl p) ((R : ℚ_[p]) - 1)‖ ≤ (p : ℝ)⁻¹
  rw [PadicAlgCl.norm_extends]
  have ht0 : (t : ℚ) ≠ 0 := by
    rintro h
    have h' : t = 0 := by exact_mod_cast h
    subst h'
    have := (Int.ModEq.dvd ht)
    simp at this
    exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)
  have hN0 : (N : ℚ) ≠ 0 := by
    rintro h
    have h' : N = 0 := by exact_mod_cast h
    subst h'
    exact hp.one_lt.ne' (by simpa using hN)
  have hD0 : ((discr F).natAbs : ℚ) ≠ 0 := by
    exact_mod_cast Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero F)
  have hε : ((-1 : ℚ) ^ m)⁻¹ = (-1) ^ m := by rw [← inv_pow, inv_neg, inv_one]
  have hRe : R = (((-1 : ℚ) ^ m * t)⁻¹) ^ n * q ^ (p - 1) := by
    rw [hR, hq, mul_inv, hε]
    ring
  have hr : ‖((((-1 : ℚ) ^ m * t : ℚ) : ℚ_[p])) - 1‖ ≤ (p : ℝ)⁻¹ := by
    have hd := Int.ModEq.dvd ht
    have h1 := (Padic.norm_int_le_pow_iff_dvd (p := p) (1 - (-1) ^ m * (t : ℤ)) 1).2 (by simpa using hd)
    have e : ((((-1 : ℚ) ^ m * t : ℚ) : ℚ_[p])) - 1 = -(((1 - (-1) ^ m * (t : ℤ) : ℤ) : ℚ_[p])) := by
      push_cast; ring
    rw [e, norm_neg]
    simpa using h1
  have hqn : ‖((q : ℚ) : ℚ_[p])‖ = 1 := by
    have hDn : ‖((discr F).natAbs : ℚ_[p])‖ ≠ 0 := by
      rw [norm_ne_zero_iff, Nat.cast_ne_zero]; exact Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero F)
    rw [hq, Rat.cast_div, Rat.cast_div, norm_div, norm_div, norm_norm_eq_disc δ c hδ hc]
    simp only [Rat.cast_pow, Rat.cast_natCast, norm_pow, Padic.norm_natCast_eq_one_iff.2 hN.symm,
      one_pow, div_one]
    exact div_self hDn
  rw [hRe, Rat.cast_mul, Rat.cast_pow, Rat.cast_pow, Rat.cast_inv]
  exact near_mul (near_pow (near_inv hr) n) (fermat _ hqn)

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_index_constant_congruent_one_mod_prime : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ c : F, IsDel p δ → PUnit p (c / δ) → ∀ t N : ℕ, N.Coprime p → (-1) ^ ((p - 1) / 2) * (t : ℤ) ≡ 1 [ZMOD p] → ‖ι.symm (wC (p - 1) t (N : F) c) - 1‖ ≤ (p : ℝ)⁻¹ := by
  first | exact @GlobalTheory.HilbertThetaSeries.wC_near_one | exact GlobalTheory.HilbertThetaSeries.wC_near_one | (intros; apply GlobalTheory.HilbertThetaSeries.wC_near_one <;> assumption)
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GoodInv

theorem exists_place (F : Type) [Field F] [NumberField F] (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  have hu : ¬ IsUnit ((p : ℕ) : 𝓞 F) := by
    intro h
    have h1 : IsUnit (algebraMap ℤ (𝓞 F) (p : ℤ)) := by simpa using h
    have h2 : IsUnit (p : ℤ) := isUnit_of_map_unit _ _ h1
    exact (Nat.prime_iff_prime_int.mp hp).not_unit h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 F)}) (by
    rwa [Ne, Ideal.span_singleton_eq_top])
  have hmem : ((p : ℕ) : 𝓞 F) ∈ M := hle (Ideal.subset_span rfl)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  have : ((p : ℕ) : 𝓞 F) = 0 := by simpa using hmem
  exact hp.ne_zero (by exact_mod_cast this)

theorem val_nat {F : Type} [Field F] [NumberField F] {p n : ℕ} (h : n.Coprime p)
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) : w.valuation F (n : F) = 1 := by
  have h1 : (n : F) = algebraMap (𝓞 F) F (n : 𝓞 F) := by simp
  rw [h1, HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hn
  have hc : IsCoprime ((n : ℕ) : 𝓞 F) ((p : ℕ) : 𝓞 F) := Nat.Coprime.cast h
  obtain ⟨a, b, hab⟩ := hc
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (Ideal.mul_mem_left _ _ hn) (Ideal.mul_mem_left _ _ hw)))

theorem norm_et {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (x : F) :
    ‖ι.symm (et x)‖ = 1 := by
  set q : ℚ := Algebra.trace ℚ F x with hq
  have h : et x ^ q.den = 1 := by
    unfold et
    rw [← Complex.exp_nat_mul, ← hq]
    have h1 : (q.den : ℂ) * (q : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.den_mul_eq_num q
    have : (q.den : ℂ) * (2 * Real.pi * Complex.I * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [← h1]; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have h2 : ‖ι.symm (et x)‖ ^ q.den = 1 := by
    rw [← norm_pow, ← map_pow, h, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) q.den_nz).1 h2

theorem exists_perm {V : Type} [AddCommGroup V] {A B : AddSubgroup V} {T : Finset V} (hT : IsReps A B T)
    (s : V →+ V) (hA : ∀ x, s x ∈ A ↔ x ∈ A) (hB : ∀ x ∈ B, s x ∈ B) :
    ∃ σ : V → V, (∀ x ∈ T, σ x ∈ T ∧ s x - σ x ∈ A) ∧ Set.BijOn σ T T ∧
      ∀ n : ℕ, ∀ x ∈ T, s^[n] x = x → σ^[n] x = x := by
  classical
  have huniq : ∀ x ∈ T, ∀ y ∈ T, x - y ∈ A → x = y := fun x hx y hy h =>
    (hT.2 x (hT.1 x hx)).unique ⟨hx, by simpa using A.zero_mem⟩ ⟨hy, h⟩
  have hex : ∀ x, ∃ y, x ∈ T → y ∈ T ∧ s x - y ∈ A := fun x => by
    by_cases hx : x ∈ T
    · obtain ⟨y, hy, -⟩ := hT.2 _ (hB x (hT.1 x hx))
      exact ⟨y, fun _ => hy⟩
    · exact ⟨x, fun h => absurd h hx⟩
  choose σ hσ using hex
  have hit : ∀ n : ℕ, ∀ x ∈ T, σ^[n] x ∈ T ∧ s^[n] x - σ^[n] x ∈ A := by
    intro n x hx
    induction n with
    | zero => exact ⟨hx, by simpa using A.zero_mem⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      refine ⟨(hσ _ ih.1).1, ?_⟩
      have h1 := (hA _).2 ih.2
      have h2 := (hσ _ ih.1).2
      rw [map_sub] at h1
      simpa using A.add_mem h1 h2
  refine ⟨σ, hσ, ?_, fun n x hx h => ?_⟩
  · have hm : Set.MapsTo σ (T : Set V) T := fun x hx => (hσ x hx).1
    refine (T.finite_toSet.injOn_iff_bijOn_of_mapsTo hm).1 fun x hx y hy h => huniq x hx y hy ?_
    rw [← hA, map_sub]
    have := A.sub_mem (hσ x hx).2 (hσ y hy).2
    rw [h] at this
    simpa using this
  · have := hit n x hx
    rw [h] at this
    exact (huniq _ hx _ this.1 this.2).symm

section Lat

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smul_mem_LL {a : F} (ha : IsIntegral ℤ a) {x : κ → F} (hx : x ∈ LL F κ) : a • x ∈ LL F κ :=
  fun i hi => ha.mul (hx i hi)

theorem BF_smul_right (G : Matrix κ κ ℤ) (a : F) (x y : κ → F) : BF G x (a • y) = a * BF G x y := by
  simp only [BF, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem BF_add_right (G : Matrix κ κ ℤ) (x y z : κ → F) : BF G x (y + z) = BF G x y + BF G x z := by
  simp only [BF, Matrix.mulVec_add, dotProduct_add]

theorem isSB_wT {p : ℕ} (hp : p.Prime) {δ : F} (hδ : IsDel p δ) {G S : Matrix κ κ ℤ} {t : ℕ} (hL : LatD p G S t)
    (Φ : (κ → F) → ℂ) {N : ℕ} {T : Finset (κ → F)} {c : F} (hN : 0 < N) (hNp : N.Coprime p)
    (hT : ∀ x ∈ T, x ∈ aL κ (N : F)⁻¹) (hc : PUnit p (c / δ)) (k : ℕ) :
    ∃ M : ℕ, 0 < M ∧ M.Coprime p ∧ IsSB M (wT G k t (N : F) c T Φ) := by
  obtain ⟨hδ0, hint, htr, d, -, hd, -, -, hdu⟩ := GlobalTheory.T.isDel_ne_zero_coprime_denominators_different_generator F p hp δ hδ
  obtain ⟨-, hsm, hadd, hI, -, haL, het, -⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hL.pos
  obtain ⟨hlev, -⟩ := GlobalTheory.T.dualLattice_index_eq_discr_pow_mul_det_pow F κ G hL.pos
  obtain ⟨-, -, -, ht⟩ := GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability F p hp κ G S t hL
  have htp : t.Coprime p := ((Nat.Prime.coprime_iff_not_dvd hp).2 (by exact_mod_cast ht)).symm
  obtain ⟨w₀, hw₀⟩ := exists_place F p hp
  have hc0 : c ≠ 0 := by
    rintro rfl
    simpa using hc w₀ hw₀
  have hd0 : (d : F) ≠ 0 := by
    intro h
    simpa [h] using hdu w₀ hw₀
  have ht0 : (t : F) ≠ 0 := by
    intro h
    simpa [h] using val_nat htp w₀ hw₀
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  obtain ⟨N₁, h1, h1p, h1i⟩ := hint (c / ((t : F) ^ 2 * d * N)) (by
    intro w hw
    have e : c / ((t : F) ^ 2 * d * N) = (c / δ) / ((t : F) ^ 2 * (d / δ) * N) := by field_simp
    rw [e, map_div₀, map_mul, map_mul, map_pow, hc w hw, hdu w hw, val_nat htp w hw, val_nat hNp w hw]
    simp)
  obtain ⟨N₂, h2, h2p, h2i⟩ := htr c⁻¹ (by
    intro w hw
    have e : δ * c⁻¹ = (c / δ)⁻¹ := by field_simp
    rw [e, map_inv₀, hc w hw]
    simp)
  have hN1 : (N₁ : F) ≠ 0 := by exact_mod_cast h1.ne'
  have hN2 : (N₂ : F) ≠ 0 := by exact_mod_cast h2.ne'
  have hnat : ∀ n : ℕ, IsIntegral ℤ (n : F) := fun n => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := F) (x := (n : ℤ)))
  refine ⟨N₁ * N₂ * N, by positivity, Nat.Coprime.mul_left (Nat.Coprime.mul_left h1p h2p) hNp, fun y hy => ?_,
    fun y l hl => ?_⟩
  · have hyd : ((N : F) / c) • y ∈ dualL F G := by
      by_contra h
      exact hy (by simp [wT, h])
    have h3 := smul_mem_LL ((hnat (N₂ * N)).mul h1i) (hlev _ hyd d hd)
    refine (haL _ _).2 ⟨_, h3, ?_⟩
    rw [smul_smul, smul_smul, smul_smul, hL.det]
    have e : ((N₁ * N₂ * N : ℕ) : F)⁻¹ * (((N₂ * N : ℕ) : F) * (N₁ * (c / ((t : F) ^ 2 * d * N)))) *
        ((((t : ℤ) ^ 2 : ℤ) : F) * d) * (N / c) = 1 := by
      push_cast
      field_simp
    rw [e, one_smul]
  · obtain ⟨l₀, hl₀, rfl⟩ := (haL _ _).1 hl
    have hld : ((N : F) / c) • (((N₁ * N₂ * N : ℕ) : F) • l₀) ∈ dualL F G := by
      intro l' hl'
      obtain ⟨n, hn⟩ := h2i _ ((hnat (N₁ * N * N)).mul ((hI l₀ hl₀).2 l' hl'))
      refine ⟨n, ?_⟩
      rw [← hn, (hsm _ _ _).1, (hsm _ _ _).1]
      congr 1
      push_cast
      field_simp
    have hiff : ((N : F) / c) • (y + ((N₁ * N₂ * N : ℕ) : F) • l₀) ∈ dualL F G ↔ ((N : F) / c) • y ∈ dualL F G := by
      rw [smul_add]
      exact (dualL F G).add_mem_cancel_right hld
    unfold wT
    rw [hiff]
    split_ifs with h
    · congr 1
      refine Finset.sum_congr rfl fun x hx => ?_
      obtain ⟨x₀, hx₀, rfl⟩ := (haL _ _).1 (hT x hx)
      rw [hadd, add_div, (het _ _).1, ((het (BF _ (_ • l₀) _ / c) 0).2.2.1).2, mul_one]
      obtain ⟨n, hn⟩ := h2i _ ((hnat N₁).mul ((hI l₀ hl₀).2 x₀ hx₀))
      refine ⟨n, ?_⟩
      rw [← hn, (hsm _ _ _).1, BF_smul_right]
      congr 1
      push_cast
      field_simp
    · rfl

end Lat

theorem good_wT : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ (Φ : (κ → F) → ℂ) (N : ℕ) (T : Finset (κ → F)) (c : F), Good ι S Φ → 0 < N → N.Coprime p → IsSB N Φ → IsReps (aL κ (N : F)) (aL κ (N : F)⁻¹) T → 0 ∈ T → PUnit p (c / δ) → Good ι S (wT G (p - 1) t (N : F) c T Φ) := by
  intro F _ _ p hpf ι hp2 δ hδ κ _ _ G S t hL Φ N T c hΦ hN hNp hSB hT h0 hc
  classical
  have hp : p.Prime := hpf.out
  obtain ⟨-, hinv, hint, hzero⟩ := hΦ
  obtain ⟨-, hsm, -, -, -, haL, het, -⟩ := GlobalTheory.T.evenPos_gramForm_integral_lattice_properties F κ G hL.pos
  obtain ⟨hiso, hS, hfree, -⟩ := GlobalTheory.T.intMatrix_isometry_prime_order_lattice_stability F p hp κ G S t hL
  have hC := GlobalTheory.T.weil_index_constant_congruent_one_mod_prime F p ι hp2 δ c hδ hc t N hNp hL.cong
  have hp1 : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_le)
  have hC1 : ‖ι.symm (wC (p - 1) t (N : F) c)‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max (ι.symm (wC (p - 1) t (N : F) c) - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le (hC.trans hp1) le_rfl)
  let s : (κ → F) →+ (κ → F) := (Matrix.mulVecLin (S.map (Int.cast : ℤ → F))).toAddMonoidHom
  have hs : ∀ x, s x = (S.map (Int.cast : ℤ → F)) *ᵥ x := fun _ => rfl
  obtain ⟨σ, hσ, hbij, hit⟩ := exists_perm hT s (fun x => (hS x).2.2.2 _) (fun x hx => ((hS x).2.2.2 _).2 hx)
  have huniq : ∀ x ∈ T, ∀ y ∈ T, x - y ∈ aL κ (N : F) → x = y := fun x hx y hy h =>
    (hT.2 x (hT.1 x hx)).unique ⟨hx, by simpa using (aL κ (N : F)).zero_mem⟩ ⟨hy, h⟩
  have hΦσ : ∀ x ∈ T, Φ (σ x) = Φ x := fun x hx => by
    rw [← hinv x, ← hSB.2 (σ x) _ (hσ x hx).2, hs, add_sub_cancel]
  refine ⟨isSB_wT hp hδ hL Φ hN hNp hT.1 hc _, fun y => ?_, fun y => ?_, ?_⟩
  · have hiff : ((N : F) / c) • (S.map (Int.cast : ℤ → F) *ᵥ y) ∈ dualL F G ↔ ((N : F) / c) • y ∈ dualL F G := by
      rw [← Matrix.mulVec_smul]
      exact (hS _).2.2.1
    unfold wT
    rw [hiff]
    split_ifs with h
    · congr 1
      symm
      refine Finset.sum_nbij σ (fun x hx => (hσ x hx).1) hbij.injOn hbij.surjOn fun x hx => ?_
      obtain ⟨l, hl, e⟩ := (haL _ _).1 (hσ x hx).2
      have e' : S.map (Int.cast : ℤ → F) *ᵥ x = σ x + (N : F) • l := by rw [← e, hs, add_sub_cancel]
      rw [hΦσ x hx, ← (hiso y x).1, e', BF_add_right, add_div, (het _ _).1, ((het (BF _ _ (_ • l) / c) 0).2.2.1).2, mul_one]
      obtain ⟨n, hn⟩ := hiff.2 h l hl
      refine ⟨n, ?_⟩
      rw [← hn, (hsm _ _ _).1, BF_smul_right]
      congr 1
      ring
    · rfl
  · unfold wT
    split_ifs with h
    · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, norm_mul, map_sum]
      refine mul_le_one₀ hC1 (norm_nonneg _) ?_
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ => ?_
      rw [map_mul, norm_mul, norm_et, mul_one]
      exact hint x
    · simp
  · have e0 : wT G (p - 1) t (N : F) c T Φ 0 = wC (p - 1) t (N : F) c * (Φ 0 + ∑ x ∈ T.erase 0, Φ x) := by
      unfold wT
      rw [if_pos (by simpa using (dualL F G).zero_mem), Finset.add_sum_erase _ _ h0]
      congr 1
      refine Finset.sum_congr rfl fun x _ => ?_
      simp [BF, et]
    have hσ0 : σ 0 = 0 := (huniq _ h0 _ (hσ 0 h0).1 (by simpa using (hσ 0 h0).2)).symm
    have horb := GlobalTheory.T.norm_sum_free_orbits_le_inv_prime p ι _ σ (T.erase 0) Φ
      (fun x hx => by
        obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
        exact Finset.mem_erase.2 ⟨fun h => hx0 (hbij.injOn hx h0 (h.trans hσ0.symm)), (hσ x hx).1⟩)
      (fun x hx => hit p x (Finset.mem_of_mem_erase hx) (hS x).1)
      (fun x hx h => by
        obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
        have h1 := (hσ x hx).2
        rw [h] at h1
        exact hx0 (huniq x hx 0 h0 (by simpa using hfree N x hN hNp (hT.1 x hx) h1)))
      (fun x hx => hΦσ x (Finset.mem_of_mem_erase hx)) (fun x _ => hint x)
    rw [e0, map_mul, map_add (f := _)]
    set a := ι.symm (wC (p - 1) t (N : F) c)
    set b := ι.symm (Φ 0)
    set r := ι.symm (∑ x ∈ T.erase 0, Φ x)
    have e : a * (b + r) - 1 = (a - 1) + (a * (b - 1) + a * r) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hC ?_)
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hC1).trans hzero
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hC1).trans horb

end GlobalTheory.HilbertThetaSeries.GoodInv

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_test_function_finite_fourier_transform_of_odd_prime : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ (Φ : (κ → F) → ℂ) (N : ℕ) (T : Finset (κ → F)) (c : F), Good ι S Φ → 0 < N → N.Coprime p → IsSB N Φ → IsReps (aL κ (N : F)) (aL κ (N : F)⁻¹) T → 0 ∈ T → PUnit p (c / δ) → Good ι S (wT G (p - 1) t (N : F) c T Φ) := by
  first | exact @GlobalTheory.HilbertThetaSeries.GoodInv.good_wT | exact GlobalTheory.HilbertThetaSeries.GoodInv.good_wT | (intros; apply GlobalTheory.HilbertThetaSeries.GoodInv.good_wT <;> assumption)
