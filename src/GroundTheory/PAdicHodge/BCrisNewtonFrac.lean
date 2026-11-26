module

public import GroundTheory.PAdicHodge.BCrisNewtonSlope
public import GroundTheory.PAdicHodge.BCrisNewtonDom
public import GroundTheory.PAdicHodge.BCrisPlusInvariants

@[expose] public section

section -- merged from GroundTheory.PAdicHodge.BCrisNewtonKey
section -- merged from GroundTheory.PAdicHodge.BCrisNewtonValue
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

open _root_.WittVector Laurent Polynomial WittTilt

variable {p : ℕ} [hp : Fact p.Prime]


variable (p) in
def sig (ρ : ℝ) : ℝ := Real.log ρ / Real.log (p : ℝ)⁻¹

theorem inv_p_pos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 hp.out.pos)

theorem inv_p_lt_one : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hp.out.one_lt)

theorem log_inv_p_neg : Real.log (p : ℝ)⁻¹ < 0 := Real.log_neg inv_p_pos inv_p_lt_one

theorem rpow_sig {ρ : ℝ} (hρ : 0 < ρ) : ((p : ℝ)⁻¹) ^ sig p ρ = ρ := by
  rw [Real.rpow_def_of_pos inv_p_pos]
  have : Real.log (p : ℝ)⁻¹ * sig p ρ = Real.log ρ := by
    unfold sig
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ log_inv_p_neg.ne
  rw [this, Real.exp_log hρ]

theorem sig_pos {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : 0 < sig p ρ :=
  div_pos_of_neg_of_neg (Real.log_neg hρ0 hρ1) log_inv_p_neg

theorem sig_inv_p : sig p (p : ℝ)⁻¹ = 1 := div_self log_inv_p_neg.ne

theorem norm_p_Cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem norm_p_algCl : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem pow_rpow_comm {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (s : ℝ) : (x ^ n) ^ s = (x ^ s) ^ n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, mul_comm, Real.rpow_mul hx, Real.rpow_natCast]

theorem gn_padicInt {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : ℤ_[p]) :
    gn ℂ_[p] p ρ (algebraMap (AInf ℂ_[p] p) (Localization.Away (p : AInf ℂ_[p] p))
      (IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p c)) =
      ‖c‖ ^ sig p ρ := by
  by_cases hc : c = 0
  · subst hc
    rw [map_zero, map_zero, gn_zero, norm_zero, Real.zero_rpow (sig_pos hρ0 hρ1).ne']
  · have hn : ‖c‖ = ((p : ℝ)⁻¹) ^ c.valuation := by
      conv_lhs => rw [PadicInt.unitCoeff_spec hc]
      rw [norm_mul, PadicInt.norm_units, one_mul, norm_pow, PadicInt.norm_p]
    conv_lhs => rw [PadicInt.unitCoeff_spec hc]
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, gn_mul hρ0 hρ1,
      gn_unit hρ0 hρ1 ((PadicInt.unitCoeff hc).isUnit.map _), one_mul, gn_pow hρ0 hρ1,
      gn_natCast_p hρ0, hn, pow_rpow_comm inv_p_pos.le, rpow_sig hρ0]

theorem natDegree_minpoly_pos (y : PadicAlgCl p) : 0 < (minpoly ℚ_[p] y).natDegree :=
  minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y)

theorem norm_minpoly_coeff_le (y : PadicAlgCl p) {i : ℕ} (hi : i ≤ (minpoly ℚ_[p] y).natDegree) :
    ‖(minpoly ℚ_[p] y).coeff i‖ ≤ ‖y‖ ^ ((minpoly ℚ_[p] y).natDegree - i) := by
  set q := minpoly ℚ_[p] y with hq
  rcases hi.lt_or_eq with hi | hi
  · have h1 : ‖q.coeff i‖ ^ (1 / (q.natDegree - i : ℝ)) ≤ ‖y‖ := by
      have e : ‖y‖ = spectralValue q := rfl
      rw [e, ← spectralValueTerms_of_lt_natDegree _ hi]
      exact le_ciSup (spectralValueTerms_bddAbove _) i
    have hpos : (0 : ℝ) < (q.natDegree - i : ℝ) := by
      have : (i : ℝ) < q.natDegree := by exact_mod_cast hi
      linarith
    have hcast : ((q.natDegree - i : ℕ) : ℝ) = (q.natDegree - i : ℝ) := by
      rw [Nat.cast_sub hi.le]
    calc ‖q.coeff i‖ = (‖q.coeff i‖ ^ (1 / (q.natDegree - i : ℝ))) ^ ((q.natDegree - i : ℕ) : ℝ) := by
          rw [← Real.rpow_mul (norm_nonneg _), hcast, one_div, inv_mul_cancel₀ hpos.ne', Real.rpow_one]
      _ ≤ ‖y‖ ^ ((q.natDegree - i : ℕ) : ℝ) :=
          Real.rpow_le_rpow (by positivity) h1 (Nat.cast_nonneg _)
      _ = ‖y‖ ^ (q.natDegree - i) := Real.rpow_natCast _ _
  · rw [hi, Nat.sub_self, pow_zero, (minpoly.monic (Algebra.IsIntegral.isIntegral y)).coeff_natDegree,
      norm_one]

theorem norm_minpoly_coeff_zero (y : PadicAlgCl p) :
    ‖(minpoly ℚ_[p] y).coeff 0‖ = ‖y‖ ^ (minpoly ℚ_[p] y).natDegree := by
  have h := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := ℚ_[p]) (L := PadicAlgCl p) y
  rw [PadicAlgCl.spectralNorm_eq] at h
  have hd : (0 : ℝ) < (minpoly ℚ_[p] y).natDegree := by exact_mod_cast natDegree_minpoly_pos y
  rw [h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div, inv_mul_cancel₀ hd.ne',
    Real.rpow_one]

theorem eq_of_no_dominant {d : ℕ} (hd : 1 ≤ d) {Fa Fb μ ρk : ℝ} (hFa : 0 < Fa) (hFb : 0 < Fb)
    (hμ : 0 < μ) (hρk : 0 < ρk) (G : ℕ → ℝ) (hG : ∀ i ≤ d, 0 ≤ G i ∧ G i ≤ ρk * μ ^ (d - i))
    (hG0 : G 0 = ρk * μ ^ d) (hGd : G d = ρk)
    (hnd : ∀ j ∈ Finset.range (d + 1), 0 < G j * Fa ^ j * Fb ^ (d - j) →
      ¬ ∀ i ∈ Finset.range (d + 1), i ≠ j →
        G i * Fa ^ i * Fb ^ (d - i) < G j * Fa ^ j * Fb ^ (d - j)) :
    Fa = μ * Fb := by
  rcases lt_trichotomy Fa (μ * Fb) with hlt | heq | hgt
  · exfalso
    refine hnd 0 (Finset.mem_range.2 (by omega)) ?_ fun i hi hi0 => ?_
    · rw [hG0]; positivity
    · have hid : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      obtain ⟨hG1, hG2⟩ := hG i hid
      have hpow : Fa ^ i < (μ * Fb) ^ i := pow_lt_pow_left₀ hlt hFa.le hi0
      have e1 : ρk * μ ^ (d - i) * (μ * Fb) ^ i * Fb ^ (d - i) = ρk * μ ^ d * Fb ^ d := by
        rw [mul_pow]
        have h1 : μ ^ (d - i) * μ ^ i = μ ^ d := by rw [← pow_add, Nat.sub_add_cancel hid]
        have h2 : Fb ^ i * Fb ^ (d - i) = Fb ^ d := by rw [← pow_add, Nat.add_sub_cancel' hid]
        calc ρk * μ ^ (d - i) * (μ ^ i * Fb ^ i) * Fb ^ (d - i)
            = ρk * (μ ^ (d - i) * μ ^ i) * (Fb ^ i * Fb ^ (d - i)) := by ring
          _ = _ := by rw [h1, h2]
      rw [hG0, Nat.sub_zero, pow_zero, mul_one, ← e1]
      calc G i * Fa ^ i * Fb ^ (d - i) ≤ ρk * μ ^ (d - i) * Fa ^ i * Fb ^ (d - i) := by
            gcongr
        _ < ρk * μ ^ (d - i) * (μ * Fb) ^ i * Fb ^ (d - i) := by
            have : 0 < ρk * μ ^ (d - i) := by positivity
            have : 0 < Fb ^ (d - i) := by positivity
            gcongr
  · exact heq
  · exfalso
    refine hnd d (Finset.mem_range.2 (by omega)) ?_ fun i hi hid' => ?_
    · rw [hGd, Nat.sub_self, pow_zero, mul_one]; positivity
    · have hid : i < d := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hid'
      obtain ⟨hG1, hG2⟩ := hG i hid.le
      have hpow : (μ * Fb) ^ (d - i) < Fa ^ (d - i) := pow_lt_pow_left₀ hgt (by positivity) (by omega)
      have e1 : ρk * Fa ^ i * Fa ^ (d - i) = ρk * Fa ^ d := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hid.le]
      rw [hGd, Nat.sub_self, pow_zero, mul_one, ← e1]
      calc G i * Fa ^ i * Fb ^ (d - i) ≤ ρk * μ ^ (d - i) * Fa ^ i * Fb ^ (d - i) := by gcongr
        _ = ρk * Fa ^ i * (μ * Fb) ^ (d - i) := by rw [mul_pow]; ring
        _ < ρk * Fa ^ i * Fa ^ (d - i) := by
            have : 0 < ρk * Fa ^ i := by positivity
            gcongr

end ACris

end GroundTheory.PAdicHodge
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

open _root_.WittVector Laurent Polynomial WittTilt

variable {p : ℕ} [hp : Fact p.Prime]


set_option maxHeartbeats 4000000 in
theorem exists_norm_eq_zpow_of_iota_eq {y : PadicAlgCl p} (hy : y ≠ 0) {a b : ACris ℂ_[p] p}
    (hb : b ≠ 0) (h : iota ℂ_[p] p a = algClToBdR p y * iota ℂ_[p] p b) :
    ∃ D : ℤ, ‖y‖ = ‖(p : PadicAlgCl p)‖ ^ D := by
  set r₀ : ℝ := (p : ℝ)⁻¹ with hr₀
  have hr0 : 0 < r₀ := inv_p_pos
  have hr1 : r₀ < 1 := inv_p_lt_one
  have hnp : ‖(p : ℂ_[p])‖ = r₀ := norm_p_Cp
  have ha : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    have h1 : algClToBdR p y ≠ 0 := fun h0 => hy (injective_algClToBdR p (by rw [h0, map_zero]))
    have h2 : iota ℂ_[p] p b ≠ 0 := fun h0 => hb (iota_injective (by rw [h0, map_zero]))
    exact mul_ne_zero h1 h2 h.symm

  set q := minpoly ℚ_[p] y with hq
  set d := q.natDegree with hd_def
  have hd : 1 ≤ d := natDegree_minpoly_pos y
  have hqd : q.coeff d = 1 := (minpoly.monic (Algebra.IsIntegral.isIntegral y)).coeff_natDegree
  set Cq : ℝ := max 1 ‖y‖ ^ d with hCq
  have hCq1 : 1 ≤ Cq := one_le_pow₀ (le_max_left _ _)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (zero_lt_one.trans_le hCq1)) hr1
  have hqle : ∀ i, ‖q.coeff i‖ ≤ Cq := by
    intro i
    by_cases hi : i ≤ d
    · exact (norm_minpoly_coeff_le y hi).trans ((pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (Nat.sub_le d i)))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), norm_zero]; linarith
  have hnormc : ∀ i, ‖(p : ℚ_[p]) ^ k * q.coeff i‖ = r₀ ^ k * ‖q.coeff i‖ := by
    intro i; rw [norm_mul, norm_pow, Padic.norm_p]
  have hcoeff : ∀ i, ‖(p : ℚ_[p]) ^ k * q.coeff i‖ ≤ 1 := by
    intro i
    rw [hnormc]
    calc r₀ ^ k * ‖q.coeff i‖ ≤ r₀ ^ k * Cq := mul_le_mul_of_nonneg_left (hqle i) (pow_nonneg hr0.le k)
      _ ≤ Cq⁻¹ * Cq := mul_le_mul_of_nonneg_right hk.le (zero_le_one.trans hCq1)
      _ = 1 := inv_mul_cancel₀ (zero_lt_one.trans_le hCq1).ne'
  set c : ℕ → ℤ_[p] := fun i => ⟨(p : ℚ_[p]) ^ k * q.coeff i, hcoeff i⟩ with hc
  have hnc : ∀ i, ‖c i‖ = r₀ ^ k * ‖q.coeff i‖ := fun i => hnormc i
  set x : ℕ → AInf ℂ_[p] p := fun i => IsPerfectoidField.padicIntToWitt (K := ℂ_[p]) p (c i) with hx

  have hrel : ∑ i ∈ Finset.range (d + 1),
      algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (x i) * a ^ i * b ^ (d - i) = 0 := by
    apply iota_injective (K := ℂ_[p]) (p := p)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum]
    have e : ∀ i ∈ Finset.range (d + 1), iota ℂ_[p] p
        (algebraMap (AInf ℂ_[p] p) (ACris ℂ_[p] p) (x i) * a ^ i * b ^ (d - i)) =
        algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) ((p : ℚ_[p]) ^ k) * iota ℂ_[p] p b ^ d *
          (algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) (q.coeff i) * algClToBdR p y ^ i) := by
      intro i hi
      have hid : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
      rw [map_mul, map_mul, map_pow, map_pow, iota_padicInt, h, mul_pow]
      have hci : ((c i : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k * q.coeff i := rfl
      rw [hci, map_mul]
      have hb' : iota ℂ_[p] p b ^ i * iota ℂ_[p] p b ^ (d - i) = iota ℂ_[p] p b ^ d := by
        rw [← pow_add, Nat.add_sub_cancel' hid]
      linear_combination (algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) ((p : ℚ_[p]) ^ k) * algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) (q.coeff i) *
        algClToBdR p y ^ i) * hb'
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum]
    have haeval : ∑ i ∈ Finset.range (d + 1), algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p) (q.coeff i) * algClToBdR p y ^ i = 0 := by
      have := Polynomial.aeval_eq_sum_range (p := q) (algClToBdR p y)
      rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero] at this
      simp only [Algebra.smul_def] at this
      exact this.symm
    rw [haeval, mul_zero]

  obtain ⟨ρa, Na, ca0, hρa, hρa1, -, hgooda, hsta⟩ := exists_stable (K := ℂ_[p]) ha
  obtain ⟨ρb, Nb, cb0, hρb, hρb1, -, hgoodb, hstb⟩ := exists_stable (K := ℂ_[p]) hb
  rw [hnp] at hρa hρb hgooda hgoodb hsta hstb
  have hca0 : (ca0 : (Localization.Away (p : AInf ℂ_[p] p))) ≠ 0 := by
    intro h0
    have := hgooda r₀ ⟨le_rfl, hρa.le⟩
    rw [h0, gn_zero] at this
    linarith [pow_pos hr0 Na]
  have hcb0 : (cb0 : (Localization.Away (p : AInf ℂ_[p] p))) ≠ 0 := by
    intro h0
    have := hgoodb r₀ ⟨le_rfl, hρb.le⟩
    rw [h0, gn_zero] at this
    linarith [pow_pos hr0 Nb]
  obtain ⟨βa, ia, ρ3a, hβa, hρ3a, hρ3a1, hmona⟩ := exists_gn_eq_monomial hca0 hr0 hr1
  obtain ⟨βb, ib, ρ3b, hβb, hρ3b, hρ3b1, hmonb⟩ := exists_gn_eq_monomial hcb0 hr0 hr1
  set ρ₅ := min (min ρa ρb) (min ρ3a ρ3b) with hρ₅
  have hr₅ : r₀ < ρ₅ := lt_min (lt_min hρa hρb) (lt_min hρ3a hρ3b)
  have hmem : ∀ ρ ∈ Set.Icc r₀ ρ₅, ρ ∈ Set.Icc r₀ ρa ∧ ρ ∈ Set.Icc r₀ ρb ∧
      ρ ∈ Set.Icc r₀ ρ3a ∧ ρ ∈ Set.Icc r₀ ρ3b := by
    intro ρ hρ
    refine ⟨⟨hρ.1, ?_⟩, ⟨hρ.1, ?_⟩, ⟨hρ.1, ?_⟩, ⟨hρ.1, ?_⟩⟩
    · exact hρ.2.trans ((min_le_left _ _).trans (min_le_left _ _))
    · exact hρ.2.trans ((min_le_left _ _).trans (min_le_right _ _))
    · exact hρ.2.trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact hρ.2.trans ((min_le_right _ _).trans (min_le_right _ _))

  have hid : ∀ ρ ∈ Set.Icc r₀ ρ₅,
      gn ℂ_[p] p ρ (ca0 : (Localization.Away (p : AInf ℂ_[p] p))) = ‖y‖ ^ sig p ρ * gn ℂ_[p] p ρ (cb0 : (Localization.Away (p : AInf ℂ_[p] p))) := by
    intro ρ hρ
    obtain ⟨hρA, hρB, -, -⟩ := hmem ρ hρ
    have hρ0 : 0 < ρ := hr0.trans_le hρ.1
    have hρ1 : ρ < 1 := hρA.2.trans_lt hρa1
    have hpρ : ‖(p : ℂ_[p])‖ ≤ ρ := hnp ▸ hρ.1
    have hσ := sig_pos (p := p) hρ0 hρ1
    set Fa := gn ℂ_[p] p ρ (ca0 : (Localization.Away (p : AInf ℂ_[p] p)))
    set Fb := gn ℂ_[p] p ρ (cb0 : (Localization.Away (p : AInf ℂ_[p] p)))
    have hFa : 0 < Fa := (pow_pos hρ0 Na).trans (hgooda ρ hρA)
    have hFb : 0 < Fb := (pow_pos hρ0 Nb).trans (hgoodb ρ hρB)
    set μ := ‖y‖ ^ sig p ρ
    have hμ : 0 < μ := Real.rpow_pos_of_pos (norm_pos_iff.2 hy) _
    set G : ℕ → ℝ := fun i => gn ℂ_[p] p ρ (algebraMap (AInf ℂ_[p] p) (Localization.Away (p : AInf ℂ_[p] p)) (x i)) with hG_def
    have hGc : ∀ i, G i = ‖c i‖ ^ sig p ρ := fun i => gn_padicInt hρ0 hρ1 (c i)
    have hsig : ∀ t : ℝ, 0 ≤ t → ∀ n : ℕ, (r₀ ^ n * t) ^ sig p ρ = ρ ^ n * t ^ sig p ρ := by
      intro t ht n
      rw [Real.mul_rpow (pow_nonneg hr0.le n) ht, pow_rpow_comm hr0.le, rpow_sig hρ0]
    have hG : ∀ i ≤ d, 0 ≤ G i ∧ G i ≤ ρ ^ k * μ ^ (d - i) := by
      intro i hi
      refine ⟨hGc i ▸ Real.rpow_nonneg (norm_nonneg _) _, ?_⟩
      rw [hGc, hnc]
      calc (r₀ ^ k * ‖q.coeff i‖) ^ sig p ρ ≤ (r₀ ^ k * ‖y‖ ^ (d - i)) ^ sig p ρ :=
            Real.rpow_le_rpow (by positivity)
              (mul_le_mul_of_nonneg_left (norm_minpoly_coeff_le y hi) (pow_nonneg hr0.le k)) hσ.le
        _ = ρ ^ k * μ ^ (d - i) := by rw [hsig _ (by positivity), pow_rpow_comm (norm_nonneg _)]
    have hG0 : G 0 = ρ ^ k * μ ^ d := by
      rw [hGc, hnc, norm_minpoly_coeff_zero, hsig _ (by positivity), pow_rpow_comm (norm_nonneg _)]
    have hGd : G d = ρ ^ k := by
      rw [hGc, hnc, hqd, norm_one, mul_one, ← mul_one (r₀ ^ k), hsig _ zero_le_one, Real.one_rpow,
        mul_one]
    have hsa : ∀ N ≥ Na, ∀ c' : ACrisZero ℂ_[p] p,
        a - algebraMap _ (ACris ℂ_[p] p) c' ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} →
          gn ℂ_[p] p ρ (c' : (Localization.Away (p : AInf ℂ_[p] p))) = Fa := fun N hN c' hc' => hsta N hN c' hc' ρ hρA
    have hsb : ∀ N ≥ Nb, ∀ c' : ACrisZero ℂ_[p] p,
        b - algebraMap _ (ACris ℂ_[p] p) c' ∈ Ideal.span {(p : ACris ℂ_[p] p) ^ N} →
          gn ℂ_[p] p ρ (c' : (Localization.Away (p : AInf ℂ_[p] p))) = Fb := fun N hN c' hc' => hstb N hN c' hc' ρ hρB
    exact eq_of_no_dominant hd hFa hFb hμ (pow_pos hρ0 k) G hG hG0 hGd
      fun j hj hpos hdom => false_of_dominant hpρ hρ1 hsa hsb d x hrel hj hpos hdom

  have e1 := hid r₀ ⟨le_rfl, hr₅.le⟩
  have e2 := hid ρ₅ ⟨hr₅.le, le_rfl⟩
  obtain ⟨-, -, hA1, hB1⟩ := hmem r₀ ⟨le_rfl, hr₅.le⟩
  obtain ⟨-, -, hA2, hB2⟩ := hmem ρ₅ ⟨hr₅.le, le_rfl⟩
  rw [hmona r₀ hA1, hmonb r₀ hB1, sig_inv_p, Real.rpow_one] at e1
  rw [hmona ρ₅ hA2, hmonb ρ₅ hB2] at e2
  have hρ₅0 : 0 < ρ₅ := hr0.trans hr₅
  set D : ℤ := ia - ib
  set γ : ℝ := βa / βb with hγ
  have hγ0 : 0 < γ := div_pos hβa hβb
  have hy1 : ‖y‖ = γ * r₀ ^ D := by
    have hne : βb * r₀ ^ ib ≠ 0 := (mul_pos hβb (zpow_pos hr0 ib)).ne'
    have h0 : ‖y‖ = (βa * r₀ ^ ia) / (βb * r₀ ^ ib) := by rw [e1, mul_div_cancel_right₀ _ hne]
    rw [h0, mul_div_mul_comm, ← zpow_sub₀ hr0.ne']
  have hzr : ∀ (t : ℝ), 0 < t → (r₀ ^ D) ^ sig p t = t ^ D := by
    intro t ht
    rw [← Real.rpow_intCast, ← Real.rpow_mul hr0.le, mul_comm, Real.rpow_mul hr0.le, rpow_sig ht,
      Real.rpow_intCast]
  have hγσ : γ ^ sig p ρ₅ = γ := by
    have h2 : ‖y‖ ^ sig p ρ₅ = γ ^ sig p ρ₅ * ρ₅ ^ D := by
      rw [hy1, Real.mul_rpow hγ0.le (zpow_nonneg hr0.le D), hzr ρ₅ hρ₅0]
    have h3 : βa * ρ₅ ^ ia = γ ^ sig p ρ₅ * ρ₅ ^ D * (βb * ρ₅ ^ ib) := by rw [e2, h2]
    have h4 : ρ₅ ^ ia = ρ₅ ^ D * ρ₅ ^ ib := by
      rw [← zpow_add₀ hρ₅0.ne']
      show ρ₅ ^ ia = ρ₅ ^ (ia - ib + ib)
      rw [sub_add_cancel]
    rw [h4] at h3
    have h5 : (γ ^ sig p ρ₅ - γ) * (βb * ρ₅ ^ D * ρ₅ ^ ib) = 0 := by
      have hβ : βa = γ * βb := by rw [hγ, div_mul_cancel₀ _ hβb.ne']
      rw [hβ] at h3
      linear_combination -h3
    have h6 : βb * ρ₅ ^ D * ρ₅ ^ ib ≠ 0 := by positivity
    exact sub_eq_zero.1 ((mul_eq_zero.1 h5).resolve_right h6)
  have hσ1 : sig p ρ₅ ≠ 1 := by
    intro h1
    have : Real.log ρ₅ = Real.log r₀ := by
      unfold sig at h1
      rw [div_eq_one_iff_eq log_inv_p_neg.ne] at h1
      exact h1
    exact hr₅.ne' (Real.log_injOn_pos (Set.mem_Ioi.2 hρ₅0) (Set.mem_Ioi.2 hr0) this)
  have hγ1 : γ = 1 := by
    have h7 := congrArg Real.log hγσ
    rw [Real.log_rpow hγ0] at h7
    have h8 : (sig p ρ₅ - 1) * Real.log γ = 0 := by linear_combination h7
    have h9 := (mul_eq_zero.1 h8).resolve_left (sub_ne_zero.2 hσ1)
    exact Real.eq_one_of_pos_of_log_eq_zero hγ0 h9
  refine ⟨D, ?_⟩
  rw [hy1, hγ1, one_mul, norm_p_algCl]

end ACris

end GroundTheory.PAdicHodge
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

open _root_.WittVector Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

theorem exists_mul_pow_eq_of_away {R B : Type*} [CommRing R] [CommRing B] {r : R} (g : R →+* B)
    (f : Localization.Away r →+* B) (hfg : ∀ a, f (algebraMap R _ a) = g a)
    (x : Localization.Away r) : ∃ (w : R) (n : ℕ), f x * g r ^ n = g w := by
  obtain ⟨n, w, hw⟩ := IsLocalization.Away.surj r x
  refine ⟨w, n, ?_⟩
  have := congrArg f hw
  rwa [map_mul, map_pow, hfg, hfg] at this

def IsACrisFraction (y : PadicAlgCl p) : Prop :=
  ∃ a b : ACris ℂ_[p] p, b ≠ 0 ∧ iota ℂ_[p] p a = algClToBdR p y * iota ℂ_[p] p b

theorem iota_ne_zero {b : ACris ℂ_[p] p} (hb : b ≠ 0) : iota ℂ_[p] p b ≠ 0 :=
  fun h => hb (iota_injective (by rw [h, map_zero]))

theorem one_ne_zero_aCris : (1 : ACris ℂ_[p] p) ≠ 0 := by
  intro h
  have := congrArg (iota ℂ_[p] p) h
  rw [map_one, map_zero] at this
  exact one_ne_zero this

theorem mul_ne_zero_aCris {b c : ACris ℂ_[p] p} (hb : b ≠ 0) (hc : c ≠ 0) : b * c ≠ 0 := by
  intro h
  have := congrArg (iota ℂ_[p] p) h
  rw [map_mul, map_zero] at this
  exact mul_ne_zero (iota_ne_zero hb) (iota_ne_zero hc) this

theorem IsACrisFraction.mul {y z : PadicAlgCl p} (hy : IsACrisFraction y) (hz : IsACrisFraction z) :
    IsACrisFraction (y * z) := by
  obtain ⟨a, b, hb, h⟩ := hy
  obtain ⟨a', b', hb', h'⟩ := hz
  refine ⟨a * a', b * b', mul_ne_zero_aCris hb hb', ?_⟩
  rw [map_mul, map_mul, map_mul, h, h']
  ring

theorem IsACrisFraction.sub {y z : PadicAlgCl p} (hy : IsACrisFraction y) (hz : IsACrisFraction z) :
    IsACrisFraction (y - z) := by
  obtain ⟨a, b, hb, h⟩ := hy
  obtain ⟨a', b', hb', h'⟩ := hz
  refine ⟨a * b' - a' * b, b * b', mul_ne_zero_aCris hb hb', ?_⟩
  set_option synthInstance.maxHeartbeats 200000 in
    rw [map_sub, map_mul, map_mul, map_mul, map_sub, h, h']
  ring

theorem IsACrisFraction.pow {y : PadicAlgCl p} (hy : IsACrisFraction y) (n : ℕ) :
    IsACrisFraction (y ^ n) := by
  induction n with
  | zero => exact ⟨1, 1, one_ne_zero_aCris, by rw [pow_zero, map_one, map_one, one_mul]⟩
  | succ n ih => rw [pow_succ]; exact ih.mul hy

theorem isACrisFraction_of_mem {u : PadicAlgCl p} (hu : u ∈ unramifiedClosure p) :
    IsACrisFraction u := by
  obtain ⟨x, hx⟩ := mem_algClInBCrisPlus.1 (unramifiedClosure_le hu)
  obtain ⟨w, n, hw⟩ := exists_mul_pow_eq_of_away (iota ℂ_[p] p) (iotaPlus ℂ_[p] p)
    (fun a => iotaPlus_algebraMap a) x
  refine ⟨w, (p : ACris ℂ_[p] p) ^ n, fun h0 => ?_, ?_⟩
  · have := congrArg (iota ℂ_[p] p) h0
    rw [map_pow, map_natCast, map_zero, ← map_natCast (algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p)) p, ← map_pow] at this
    exact pow_ne_zero n (Nat.cast_ne_zero.2 hp.out.ne_zero : (p : ℚ_[p]) ≠ 0)
      ((algebraMap ℚ_[p] (BDeRhamPlus (normInteger ℂ_[p]) p)).injective (by rw [this, map_zero]))
  · rw [← hw, hx, map_pow]

theorem IsACrisFraction.exists_norm_eq_zpow {y : PadicAlgCl p} (hy : IsACrisFraction y)
    (hy0 : y ≠ 0) : ∃ D : ℤ, ‖y‖ = ‖(p : PadicAlgCl p)‖ ^ D := by
  obtain ⟨a, b, hb, h⟩ := hy
  exact exists_norm_eq_zpow_of_iota_eq hy0 hb h

theorem IsACrisFraction.norm_le {y : PadicAlgCl p} (hy : IsACrisFraction y) (h1 : ‖y‖ < 1) :
    ‖y‖ ≤ ‖(p : PadicAlgCl p)‖ := by
  by_cases hy0 : y = 0
  · rw [hy0, norm_zero]; exact norm_nonneg _
  obtain ⟨D, hD⟩ := hy.exists_norm_eq_zpow hy0
  have hp0 : 0 < ‖(p : PadicAlgCl p)‖ := by rw [norm_p_algCl]; exact inv_p_pos
  have hp1 : ‖(p : PadicAlgCl p)‖ ≤ 1 := by rw [norm_p_algCl]; exact inv_p_lt_one.le
  rw [hD]
  by_cases hD1 : 1 ≤ D
  · exact (zpow_le_zpow_right_of_le_one₀ hp0 hp1 hD1).trans_eq (zpow_one _)
  · exfalso
    have : (1 : ℝ) ≤ ‖(p : PadicAlgCl p)‖ ^ D := by
      rw [← zpow_zero ‖(p : PadicAlgCl p)‖]
      exact zpow_le_zpow_right_of_le_one₀ hp0 hp1 (by omega)
    rw [← hD] at this
    linarith

theorem norm_sub_pow_sub_le {F : Type*} [NormedField F] [IsUltrametricDist F] (hpF : ‖(p : F)‖ < 1)
    {a b : F} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (k : ℕ) :
    ‖(a - b) ^ p ^ k - (a ^ p ^ k - b ^ p ^ k)‖ ≤ ‖(p : F)‖ := by
  set O := normInteger F
  set a' : O := ⟨a, mem_normInteger.2 ha⟩
  set b' : O := ⟨b, mem_normInteger.2 hb⟩
  have hnu : (p : O) ∈ nonunits O := by
    rw [mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h1 := congrArg (fun z : O => (z : F)) u.mul_inv
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at h1
    rw [hu] at h1
    push_cast at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one] at h2
    have h3 : ‖(((u⁻¹ : Oˣ) : O) : F)‖ ≤ 1 := mem_normInteger.1 (u⁻¹ : Oˣ).val.2
    nlinarith [norm_nonneg ((p : F))]
  haveI := CharP.quotient O p hnu
  have h := sub_pow_char_pow (p := p) (n := k) (Ideal.Quotient.mk (Ideal.span {(p : O)}) a')
    (Ideal.Quotient.mk (Ideal.span {(p : O)}) b')
  rw [← map_sub, ← map_pow, ← map_pow, ← map_pow, ← map_sub, Ideal.Quotient.eq] at h
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h
  have h4 := congrArg (fun z : O => (z : F)) hc
  push_cast at h4
  rw [← h4, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (mem_normInteger.1 c.2)

theorem norm_p_algCl_lt_one : ‖(p : PadicAlgCl p)‖ < 1 := by
  rw [norm_p_algCl]; exact inv_p_lt_one

theorem exists_approx_of_isACrisFraction (m : ℕ) :
    ∀ y : PadicAlgCl p, IsACrisFraction y → ‖y‖ ≤ 1 →
      ∃ u ∈ unramifiedClosure p, ‖y - u‖ ≤ ‖(p : PadicAlgCl p)‖ ^ m := by
  induction m with
  | zero => intro y _ hy1; exact ⟨0, zero_mem _, by rw [sub_zero, pow_zero]; exact hy1⟩
  | succ m ih =>
    intro y hy hy1
    have hp1 := norm_p_algCl_lt_one (p := p)
    obtain ⟨k₀, k₁, hk, hkk⟩ := exists_lt_norm_pow_sub_lt hy1 one_pos (fun k => p ^ k)
    set r := k₁ - k₀ with hr
    have hr1 : 1 ≤ r := by omega
    set z := y ^ p ^ r - y with hz
    have hyr : ‖y ^ p ^ r‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy1
    have hbin := norm_sub_pow_sub_le hp1 hyr hy1 k₀
    have hk1 : (y ^ p ^ r) ^ p ^ k₀ = y ^ p ^ k₁ := by
      rw [← pow_mul, ← pow_add, hr, Nat.sub_add_cancel hk.le]
    rw [hk1] at hbin
    have hz1 : ‖z ^ p ^ k₀‖ < 1 := by
      have e : z ^ p ^ k₀ = (z ^ p ^ k₀ - (y ^ p ^ k₁ - y ^ p ^ k₀)) + (y ^ p ^ k₁ - y ^ p ^ k₀) := by ring
      rw [e]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hbin.trans_lt hp1) hkk)
    have hz2 : ‖z‖ < 1 := by
      rw [norm_pow] at hz1
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ hp.out.ne_zero)).1 hz1
    have hzf : IsACrisFraction z := (hy.pow _).sub hy
    have hz3 := hzf.norm_le hz2

    have hyC : ‖(y : ℂ_[p])‖ ≤ 1 := by rw [PadicComplex.norm_extends]; exact hy1
    have hzC : ‖(y : ℂ_[p]) ^ p ^ r - (y : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ 1 := by
      rw [pow_one, ← PadicComplex.coe_natCast, PadicComplex.norm_extends]
      have : (y : ℂ_[p]) ^ p ^ r - (y : ℂ_[p]) = ((y ^ p ^ r - y : PadicAlgCl p) : ℂ_[p]) := by
        simp only [PadicComplex.coe_eq, map_sub, map_pow]
      rw [this, PadicComplex.norm_extends]
      exact hz3
    obtain ⟨u₀, hu₀, hu₀y⟩ := exists_approx_of_pow_sub hyC hr1 hzC
    rw [pow_one, ← PadicComplex.coe_natCast, PadicComplex.norm_extends,
      show (y : ℂ_[p]) - (u₀ : ℂ_[p]) = ((y - u₀ : PadicAlgCl p) : ℂ_[p]) by
        simp only [PadicComplex.coe_eq, map_sub],
      PadicComplex.norm_extends] at hu₀y

    have hpne : (p : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    set y' := (y - u₀) * (p : PadicAlgCl p)⁻¹ with hy'
    have hpinv : (p : PadicAlgCl p)⁻¹ ∈ unramifiedClosure p := inv_mem (natCast_mem _ p)
    have hy'f : IsACrisFraction y' := (hy.sub (isACrisFraction_of_mem hu₀)).mul
      (isACrisFraction_of_mem hpinv)
    have hnp0 : 0 < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.2 hpne
    have hy'1 : ‖y'‖ ≤ 1 := by
      rw [hy', norm_mul, norm_inv]
      rw [← div_eq_mul_inv]
      exact (div_le_one hnp0).2 hu₀y
    obtain ⟨u', hu', hu'y⟩ := ih y' hy'f hy'1
    refine ⟨u₀ + (p : PadicAlgCl p) * u', add_mem hu₀ (mul_mem (natCast_mem _ p) hu'), ?_⟩
    have e : y - (u₀ + (p : PadicAlgCl p) * u') = (p : PadicAlgCl p) * (y' - u') := by
      rw [hy']; field_simp; ring
    rw [e, norm_mul, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_right hu'y (norm_nonneg _)

theorem IsACrisFraction.mem_unramifiedClosure {y : PadicAlgCl p} (hy : IsACrisFraction y) :
    y ∈ unramifiedClosure p := by
  have hpne : (p : PadicAlgCl p) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  have hp1 := norm_p_algCl_lt_one (p := p)
  have hnp0 : 0 < ‖(p : PadicAlgCl p)‖ := norm_pos_iff.2 hpne
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (zero_lt_one.trans_le (le_max_left 1 ‖y‖)))
    hp1
  set y' := (p : PadicAlgCl p) ^ n * y
  have hy'1 : ‖y'‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    calc ‖(p : PadicAlgCl p)‖ ^ n * ‖y‖ ≤ (max 1 ‖y‖)⁻¹ * max 1 ‖y‖ :=
          mul_le_mul hn.le (le_max_right _ _) (norm_nonneg _) (by positivity)
      _ = 1 := inv_mul_cancel₀ (zero_lt_one.trans_le (le_max_left 1 ‖y‖)).ne'
  have hy'f : IsACrisFraction y' := (isACrisFraction_of_mem (pow_mem (natCast_mem _ p) n)).mul hy
  have hy' : y' ∈ unramifiedClosure p := mem_unramifiedClosure_of_forall_approx fun m =>
    exists_approx_of_isACrisFraction m y' hy'f hy'1
  have : y = ((p : PadicAlgCl p) ^ n)⁻¹ * y' := by
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hpne), one_mul]
  rw [this]
  exact mul_mem (inv_mem (pow_mem (natCast_mem _ p) n)) hy'

end ACris

end GroundTheory.PAdicHodge
