module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorRes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootCancelPowEqSelfAcrisGaussNorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancel
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatio
open GlobalTheory.PMon.Gauss

open scoped Formalism.Per

namespace GlobalTheory.TiltRootApprox

open _root_.Ideal

variable {l : ℕ} [Fact l.Prime]

theorem pow_pow_add_mul {M : Type*} [Monoid M] {ξ : M} {o : ℕ} (h : ξ ^ (l ^ o) = ξ) (a k : ℕ) :
    ξ ^ (l ^ (a + o * k)) = ξ ^ (l ^ a) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show a + o * (k + 1) = (a + o * k) + o by ring, pow_add, mul_comm, pow_mul, h, ih]

theorem exists_pow_pow_eq {M : Type*} [Monoid M] {ξ : M} {n : ℕ} (hn : 0 < n) (hl : ¬ l ∣ n)
    (h : ξ ^ n = 1) : ∃ o : ℕ, 0 < o ∧ ξ ^ (l ^ o) = ξ := by
  have hcop : l.Coprime n := (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hl
  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have hmod : l ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop
  rw [← Nat.div_add_mod (l ^ n.totient) n, hmod, pow_add, pow_mul, h, one_pow, one_mul]
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_one]
  · have : n = 1 := by omega
    subst this
    simp only [pow_one] at h
    simp [h]

theorem exists_tilt_lift (ξ : Formalism.Per.OC l) {o : ℕ} (ho : 0 < o) (hξ : ξ ^ (l ^ o) = ξ) :
    ∃ ζ : Formalism.Per.Fl l, ζ ^ (l ^ o) = ζ ∧ ζ.untilt = ξ := by
  obtain ⟨q, rfl⟩ : ∃ q, o = q + 1 := ⟨o - 1, by omega⟩
  have hper := pow_pow_add_mul (l := l) hξ
  let s : ℕ → ModP (Formalism.Per.OC l) l := fun m =>
    Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (ξ ^ (l ^ (q * m)))
  have hs : ∀ m, s (m + 1) ^ l = s m := by
    intro m
    simp only [s, ← map_pow]
    congr 1
    rw [← pow_mul, ← pow_succ, show q * (m + 1) + 1 = q * m + (q + 1) * 1 by ring, hper]
  let ζ : Formalism.Per.Fl l := ⟨s, hs⟩
  refine ⟨ζ, ?_, ?_⟩
  · refine Perfection.ext fun m => ?_
    erw [map_pow]
    change s m ^ l ^ (q + 1) = s m
    simp only [s, ← map_pow]
    congr 1
    rw [← pow_mul, ← pow_add, show q * m + (q + 1) = q * m + (q + 1) * 1 by ring, hper]
  · refine Perfection.teichmuller_spec (I := span {((l : ℕ) : Formalism.Per.OC l)}) fun n => ?_
    refine ⟨ξ ^ (l ^ (q * n)), rfl, ?_⟩
    rw [← pow_mul, ← pow_add, show q * n + n = 0 + (q + 1) * n by ring, hper, pow_zero, pow_one]

end GlobalTheory.TiltRootApprox

namespace GlobalTheory.TiltRootApprox

open _root_.Ideal

theorem exists_root_approx : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 →
    ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ →
    ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧
      ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ <
        ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  intro l _ y y' hy' hn
  have h0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := fun h =>
    hy' (GlobalTheory.TiltAbs.eq_zero_of_untilt y' (Subtype.ext h))
  have hpos : 0 < ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := norm_pos_iff.2 h0
  have hd : y'.untilt ∣ y.untilt := by
    refine ⟨⟨((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]),
      (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, hn, div_self hpos.ne']
    · change _ = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) * (_ / _)
      field_simp
  obtain ⟨u, rfl⟩ := GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd hd
  have hmul : ∀ a b : Formalism.Per.Fl l, (((a * b).untilt : Formalism.Per.OC l) : ℂ_[l]) =
      ((a.untilt : Formalism.Per.OC l) : ℂ_[l]) * ((b.untilt : Formalism.Per.OC l) : ℂ_[l]) := by
    intro a b
    rw [map_mul]
    rfl
  have hu : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 := by
    rw [hmul, norm_mul] at hn
    have := hn
    field_simp at this
    nlinarith [this]
  obtain ⟨ξ, hξ, hclose⟩ := ReciprocityTheory.ChartRestriction.L1.res_full l _ hu.le
  have hξn : ‖ξ‖ ≤ 1 := by
    calc ‖ξ‖ = ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - (((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ)‖ := by
          rw [sub_sub_cancel]
      _ ≤ max ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ‖ := by
          have := IsUltrametricDist.norm_add_le_max (((u.untilt : Formalism.Per.OC l) : ℂ_[l]))
            (-(((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ))
          rwa [← sub_eq_add_neg, norm_neg] at this
      _ ≤ 1 := max_le hu.le hclose.le
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [sub_zero, hu] at hclose
    exact lt_irrefl _ hclose
  obtain ⟨n, hn0, hln, hξpow⟩ : ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ξ ^ n = 1 := by
    rcases Set.mem_insert_iff.1 hξ with h | h
    · exact absurd h hξ0
    · exact h
  obtain ⟨o, ho, hξo⟩ := exists_pow_pow_eq hn0 hln hξpow
  let ξ' : Formalism.Per.OC l := ⟨ξ, (GlobalTheory.RingBasics.mem_OC _).2 hξn⟩
  have hξ'o : ξ' ^ (l ^ o) = ξ' := Subtype.ext (by
    change ξ ^ (l ^ o) = ξ
    exact hξo)
  obtain ⟨ζ, hζo, hζu⟩ := exists_tilt_lift ξ' ho hξ'o
  refine ⟨ζ, o, ho, hζo, ?_, ?_⟩
  · rintro rfl
    apply hξ0
    have h00 : (0 : Formalism.Per.Fl l).untilt = 0 := Perfection.teichmuller_zero
    rw [h00] at hζu
    have := congrArg Subtype.val hζu
    exact this.symm
  · have e : y' * u - ζ * y' = (u - ζ) * y' := by ring
    rw [e, hmul, norm_mul]
    have hlt : ‖(((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l])‖ < 1 := by
      have hmk : Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) ((u - ζ).untilt) =
          Ideal.Quotient.mk (span {((l : ℕ) : Formalism.Per.OC l)}) (u.untilt - ζ.untilt) := by
        rw [PreTilt.mk_untilt_eq_coeff_zero, map_sub, map_sub, PreTilt.mk_untilt_eq_coeff_zero,
          PreTilt.mk_untilt_eq_coeff_zero]
      rw [Ideal.Quotient.eq, ← pow_one (span {((l : ℕ) : Formalism.Per.OC l)}),
        GlobalTheory.RingBasics.mem_span_pow_OC, pow_one] at hmk
      have e2 : (((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l]) =
          ((((u - ζ).untilt - (u.untilt - ζ.untilt) : Formalism.Per.OC l)) : ℂ_[l]) +
            (((u.untilt : Formalism.Per.OC l) : ℂ_[l]) - ξ) := by
        rw [hζu]
        push_cast
        ring
      rw [e2]
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hclose)
      exact lt_of_le_of_lt hmk GlobalTheory.RingBasics.norm_p_lt
    calc ‖(((u - ζ).untilt : Formalism.Per.OC l) : ℂ_[l])‖ * ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖
        < 1 * ‖((y'.untilt : Formalism.Per.OC l) : ℂ_[l])‖ := mul_lt_mul_of_pos_right hlt hpos
      _ = _ := one_mul _

end GlobalTheory.TiltRootApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatioStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 → ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ < ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  first | exact @GlobalTheory.TiltRootApprox.exists_root_approx | exact GlobalTheory.TiltRootApprox.exists_root_approx | (intros; apply GlobalTheory.TiltRootApprox.exists_root_approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupPowEqPowISupNonneg
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupPowEqPowISupNonneg
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

namespace Lead

theorem mono_lt {a C ρ₁ ρ₂ ρ : ℝ} {n : ℕ} {e : ℤ} (h1 : 0 < ρ₁) (hl : ρ₁ < ρ) (hr : ρ < ρ₂) (ha : 0 < a)
    (hne : (n : ℤ) ≠ e) (b1 : a * ρ₁ ^ n ≤ C * ρ₁ ^ e) (b2 : a * ρ₂ ^ n ≤ C * ρ₂ ^ e) :
    a * ρ ^ n < C * ρ ^ e := by
  have hρ : 0 < ρ := h1.trans hl
  have hρ2 : 0 < ρ₂ := hρ.trans hr
  set d : ℤ := (n : ℤ) - e with hd
  have key : ∀ t : ℝ, 0 < t → a * t ^ n = t ^ e * (a * t ^ d) := by
    intro t ht
    rw [← zpow_natCast, show (n : ℤ) = e + d by omega, zpow_add₀ ht.ne']
    ring
  have red : ∀ t : ℝ, 0 < t → a * t ^ n ≤ C * t ^ e → a * t ^ d ≤ C := by
    intro t ht h
    rw [key t ht, mul_comm C] at h
    exact le_of_mul_le_mul_left h (zpow_pos ht e)
  rw [key ρ hρ, mul_comm C]
  refine mul_lt_mul_of_pos_left ?_ (zpow_pos hρ e)
  rcases lt_or_gt_of_ne (show d ≠ 0 by omega) with hneg | hpos
  · have c1 := red ρ₁ h1 b1
    refine lt_of_lt_of_le (mul_lt_mul_of_pos_left ?_ ha) c1
    have e1 : ρ ^ d = (ρ ^ (-d))⁻¹ := by rw [zpow_neg, inv_inv]
    have e2 : ρ₁ ^ d = (ρ₁ ^ (-d))⁻¹ := by rw [zpow_neg, inv_inv]
    rw [e1, e2]
    exact inv_strictAnti₀ (zpow_pos h1 _) (zpow_lt_zpow_left₀ (by omega) h1.le hl)
  · have c2 := red ρ₂ hρ2 b2
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_left (zpow_lt_zpow_left₀ hpos hρ.le hr) ha) c2

theorem iSup_lt {d : ℕ → ℝ} {ρ T : ℝ} (h0 : ∀ n, 0 ≤ d n) (h1 : ∀ n, d n ≤ 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hT : 0 < T) (h : ∀ n, d n * ρ ^ n < T) : (⨆ n, d n * ρ ^ n) < T := by
  obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hT hρ1
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.range (M + 1)) (fun n => d n * ρ ^ n)
    ⟨0, by simp⟩
  refine lt_of_le_of_lt (ciSup_le fun n => ?_ : (⨆ n, d n * ρ ^ n) ≤ max (d i * ρ ^ i) (ρ ^ M))
    (max_lt (h i) hM)
  by_cases hn : n < M + 1
  · exact le_max_of_le_left (hi n (Finset.mem_range.2 hn))
  · refine le_max_of_le_right ?_
    calc d n * ρ ^ n ≤ 1 * ρ ^ n := by gcongr; exact h1 n
      _ = ρ ^ n := one_mul _
      _ ≤ ρ ^ M := pow_le_pow_of_le_one hρ.le hρ1.le (by omega)

theorem lead (c : ℕ → ℝ) (h0 : ∀ n, 0 ≤ c n) (h1 : ∀ n, c n ≤ 1) {ρ₁ ρ₂ C : ℝ} {e : ℤ} (hρ₁ : 0 < ρ₁)
    (h12 : ρ₁ < ρ₂) (hρ₂ : ρ₂ < 1) (hC : 0 < C) (hs : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, (⨆ n, c n * ρ ^ n) = C * ρ ^ e) :
    ∃ m : ℕ, (m : ℤ) = e ∧ c m = C ∧ ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, ∀ d : ℕ → ℝ, (∀ n, 0 ≤ d n) → (∀ n, d n ≤ c n) →
      d m = 0 → (⨆ n, d n * ρ ^ n) < C * ρ ^ e := by
  have hb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ∀ n, c n * ρ ^ n ≤ C * ρ ^ e := by
    intro ρ hρ n
    rw [← hs ρ hρ]
    have hρ0 : 0 ≤ ρ := hρ₁.le.trans hρ.1
    have hρ1 : ρ ≤ 1 := hρ.2.trans hρ₂.le
    refine le_ciSup (f := fun n => c n * ρ ^ n) ⟨1, Set.forall_mem_range.2 fun n => ?_⟩ n
    calc c n * ρ ^ n ≤ 1 * 1 := mul_le_mul (h1 n) (pow_le_one₀ hρ0 hρ1) (pow_nonneg hρ0 _) zero_le_one
      _ = 1 := one_mul 1
  have B : ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, ∀ d : ℕ → ℝ, (∀ n, 0 ≤ d n) → (∀ n, d n ≤ c n) →
      (∀ n : ℕ, (n : ℤ) = e → d n < C) → (⨆ n, d n * ρ ^ n) < C * ρ ^ e := by
    intro ρ hρ d hd0 hdc hde
    have hρ0 : 0 < ρ := hρ₁.trans hρ.1
    have hρ1 : ρ < 1 := hρ.2.trans hρ₂
    refine iSup_lt hd0 (fun n => (hdc n).trans (h1 n)) hρ0 hρ1 (mul_pos hC (zpow_pos hρ0 e)) fun n => ?_
    by_cases hn : (n : ℤ) = e
    · rw [← hn, zpow_natCast]
      exact mul_lt_mul_of_pos_right (hde n hn) (pow_pos hρ0 n)
    · rcases (h0 n).eq_or_lt with hc | hc
      · have : d n = 0 := le_antisymm (hc ▸ hdc n) (hd0 n)
        rw [this, zero_mul]
        exact mul_pos hC (zpow_pos hρ0 e)
      · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (hdc n) (pow_nonneg hρ0.le n))
          (mono_lt hρ₁ hρ.1 hρ.2 hc hn (hb ρ₁ ⟨le_rfl, h12.le⟩ n) (hb ρ₂ ⟨h12.le, le_rfl⟩ n))
  set ρm := (ρ₁ + ρ₂) / 2 with hρm
  have hm : ρm ∈ Set.Ioo ρ₁ ρ₂ := ⟨by rw [hρm]; linarith, by rw [hρm]; linarith⟩
  have hex : ∃ m : ℕ, (m : ℤ) = e ∧ c m = C := by
    by_contra hno
    push_neg at hno
    have hle : ∀ n : ℕ, (n : ℤ) = e → c n ≤ C := by
      intro n hn
      have := hb ρ₁ ⟨le_rfl, h12.le⟩ n
      rw [← hn, zpow_natCast] at this
      exact le_of_mul_le_mul_right this (pow_pos hρ₁ n)
    have := B ρm hm c h0 (fun _ => le_rfl) fun n hn => lt_of_le_of_ne (hle n hn) (hno n hn)
    rw [hs ρm (Set.Ioo_subset_Icc_self hm)] at this
    exact lt_irrefl _ this
  obtain ⟨m, hme, hcm⟩ := hex
  refine ⟨m, hme, hcm, fun ρ hρ d hd0 hdc hdm => B ρ hρ d hd0 hdc fun n hn => ?_⟩
  have : n = m := by omega
  subst this
  rw [hdm]
  exact hC

end Lead


open GlobalTheory.GaussSlope in
theorem lead_target : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (c ρ₁ ρ₂ : ℝ) (k : ℤ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ < ρ₂ →
    ρ₂ < 1 → 0 < c → (∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ x = c * ρ ^ k) → ∃ (y : Formalism.Per.Fl l) (j : ℕ), 0 ≤ k + j ∧
    ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c ∧ ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, gC l ρ ((l : Formalism.Per.Acris l) ^ j * x -
    (l : Formalism.Per.Acris l) ^ (k + j).toNat * tc l y) < ρ ^ j * gC l ρ x := by
  intro l _ x c ρ₁ ρ₂ k hl1 h12 h21 hc hx
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hρ₁ : 0 < ρ₁ := lt_of_lt_of_le (by positivity) hl1
  have hG : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, IsGauss l ρ (gC l ρ) := fun ρ hρ =>
    isGauss_gC_target l ρ (hl1.trans hρ.1) (hρ.2.trans_lt h21)
  have hGl : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ (l : Formalism.Per.Acris l) = ρ := by
    intro ρ hρ
    rw [← map_natCast (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)) l, (hG ρ hρ).2.2.2.2, gA,
      gauss_l l (hρ₁.le.trans hρ.1)]
  have hpm : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ∀ (n : ℕ) (w : Formalism.Per.Acris l),
      gC l ρ ((l : Formalism.Per.Acris l) ^ n * w) = ρ ^ n * gC l ρ w := by
    intro ρ hρ n w
    rw [map_pow_mul _ (hG ρ hρ).2.2.2.1, hGl ρ hρ]
  have hkb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ρ₁ ^ k.toNat ≤ ρ ^ k := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁.trans_le hρ.1
    rcases k with n | n
    · rw [Int.ofNat_eq_coe, Int.toNat_natCast, zpow_natCast]
      exact pow_le_pow_left₀ hρ₁.le hρ.1 n
    · rw [Int.toNat_negSucc, pow_zero, zpow_negSucc]
      exact (one_le_inv₀ (pow_pos hρ0 _)).2 (pow_le_one₀ hρ0.le (hρ.2.trans h21.le))
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one (mul_pos hc (pow_pos hρ₁ k.toNat)) h21
  have hrb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, ρ ^ r < c * ρ ^ k := fun ρ hρ =>
    calc ρ ^ r ≤ ρ₂ ^ r := pow_le_pow_left₀ (hρ₁.le.trans hρ.1) hρ.2 r
      _ < c * ρ₁ ^ k.toNat := hr
      _ ≤ c * ρ ^ k := mul_le_mul_of_nonneg_left (hkb ρ hρ) hc.le
  obtain ⟨s, z, hxz⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x r
  obtain ⟨j, a, ha⟩ := exists_pow_mul_eq l s
  have hjx : (l : Formalism.Per.Acris l) ^ j * x =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a + (l : Formalism.Per.Acris l) ^ (j + r) * z := by
    rw [hxz, mul_add, ha, pow_add, mul_assoc]
  have hzb : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ ((l : Formalism.Per.Acris l) ^ (j + r) * z) < ρ ^ j * (c * ρ ^ k) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁.trans_le hρ.1
    rw [hpm ρ hρ, pow_add, mul_assoc]
    refine mul_lt_mul_of_pos_left ?_ (pow_pos hρ0 j)
    exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg hρ0.le r) ((hG ρ hρ).1 z).2) (hrb ρ hρ)
  set cc : ℕ → ℝ := fun n => ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) with hcc
  have hAn : ∀ ρ ∈ Set.Icc ρ₁ ρ₂, (⨆ n, cc n * ρ ^ n) = c * ρ ^ (k + j) := by
    intro ρ hρ
    have hρ0 : 0 < ρ := hρ₁.trans_le hρ.1
    obtain ⟨e1, e2, e3, e4, e5⟩ := hG ρ hρ
    have h3 : algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a =
        (l : Formalism.Per.Acris l) ^ j * x + -((l : Formalism.Per.Acris l) ^ (j + r) * z) := by rw [hjx]; ring
    have h4 : gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) a) = ρ ^ j * (c * ρ ^ k) := by
      rw [h3, add_eq_of_lt _ e2 e3 (by rw [e3, hpm ρ hρ j x, hx ρ hρ]; exact hzb ρ hρ), hpm ρ hρ, hx ρ hρ]
    rw [e5, gA] at h4
    rw [h4, zpow_add₀ hρ0.ne', zpow_natCast]
    ring
  have hc1 : ∀ n, cc n ≤ 1 := fun n =>
    Real.rpow_le_one (norm_nonneg _) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.prop _)) (by positivity)
  obtain ⟨m, hme, hcm, hlt⟩ := Lead.lead cc (fun n => by positivity) hc1 hρ₁ h12 h21 hc hAn
  have hmt : (k + j).toNat = m := by omega
  set y := (iterateFrobeniusEquiv (Formalism.Per.Fl l) l m).symm (a.coeff m) with hy
  have hym : y ^ l ^ m = a.coeff m := by
    rw [← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply, hy, RingEquiv.apply_symm_apply]
  have hnorm : ‖((y.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c := by
    rw [← hcm, hcc]
    simp only
    rw [← hym, map_pow]
    push_cast
    rw [norm_pow, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    have : ((l ^ m : ℕ) : ℝ) * (1 / (l : ℝ) ^ m) = 1 := by
      push_cast
      field_simp
    rw [this, Real.rpow_one]
  let b : Formalism.Per.Ainf l := WittVector.mk l fun n => if n = m then 0 else a.coeff n
  have hbc : ∀ n, b.coeff n = if n = m then 0 else a.coeff n := fun n => rfl
  have hab : a = b + Formalism.Per.tm y * (l : Formalism.Per.Ainf l) ^ m := by
    ext n
    rw [WittVector.coeff_add_of_disjoint]
    · by_cases hn : n = m
      · subst hn
        rw [hbc, if_pos rfl, zero_add, WittVector.teichmuller_mul_pow_coeff, hym]
      · rw [hbc, if_neg hn, WittVector.teichmuller_mul_pow_coeff_of_ne _ hn, add_zero]
    · intro n'
      by_cases hn : n' = m
      · left
        rw [hbc, if_pos hn]
      · right
        exact WittVector.teichmuller_mul_pow_coeff_of_ne _ hn
  refine ⟨y, j, by omega, hnorm, fun ρ hρ => ?_⟩
  have hρI : ρ ∈ Set.Icc ρ₁ ρ₂ := Set.Ioo_subset_Icc_self hρ
  have hρ0 : 0 < ρ := hρ₁.trans hρ.1
  obtain ⟨e1, e2, e3, e4, e5⟩ := hG ρ hρI
  have hsplit : (l : Formalism.Per.Acris l) ^ j * x - (l : Formalism.Per.Acris l) ^ (k + j).toNat * tc l y
      = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) b + (l : Formalism.Per.Acris l) ^ (j + r) * z := by
    rw [hjx, hmt, tc]
    conv_lhs => rw [hab]
    rw [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  let d : ℕ → ℝ := fun n => if n = m then 0 else cc n
  have hbd : ∀ n, ‖(((b.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) = d n := by
    intro n
    by_cases hn : n = m
    · have : (1 : ℝ) / (l : ℝ) ^ n ≠ 0 := by positivity
      simp only [d, hbc, if_pos hn, untilt_zero, ZeroMemClass.coe_zero, norm_zero, Real.zero_rpow this]
    · simp only [d, hbc, if_neg hn, hcc]
  have hbn : gC l ρ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) b) < ρ ^ j * (c * ρ ^ k) := by
    rw [e5, gA]
    simp_rw [hbd]
    refine lt_of_lt_of_le (hlt ρ hρ d (fun n => ?_) (fun n => ?_) (by simp [d])) (le_of_eq ?_)
    · by_cases hn : n = m
      · simp [d, hn]
      · simp only [d, if_neg hn]
        positivity
    · by_cases hn : n = m
      · simp only [d, if_pos hn]
        positivity
      · simp only [d, if_neg hn, le_refl]
    · rw [zpow_add₀ hρ0.ne', zpow_natCast]
      ring
  rw [hsplit, hx ρ hρI]
  exact lt_of_le_of_lt (e2 _ _) (max_lt hbn (hzb ρ hρI))

end GlobalTheory.PMon.Gauss
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupPowEqPowISupNonnegStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial : ∀ (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (c ρ₁ ρ₂ : ℝ) (k : ℤ), (l : ℝ)⁻¹ ≤ ρ₁ → ρ₁ < ρ₂ → ρ₂ < 1 → 0 < c → (∀ ρ ∈ Set.Icc ρ₁ ρ₂, gC l ρ x = c * ρ ^ k) → ∃ (y : Formalism.Per.Fl l) (j : ℕ), 0 ≤ k + j ∧ ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c ∧ ∀ ρ ∈ Set.Ioo ρ₁ ρ₂, gC l ρ ((l : Formalism.Per.Acris l) ^ j * x - (l : Formalism.Per.Acris l) ^ (k + j).toNat * tc l y) < ρ ^ j * gC l ρ x := by
  first | exact @GlobalTheory.PMon.Gauss.lead_target | exact GlobalTheory.PMon.Gauss.lead_target | (intros; apply GlobalTheory.PMon.Gauss.lead_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancel
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem untilt_zero' : (0 : Formalism.Per.Fl l).untilt = 0 := by
  rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]

theorem isGauss_gC {ρ : ℝ} (h1 : (l : ℝ)⁻¹ ≤ ρ) (h2 : ρ < 1) : IsGauss l ρ (gC l ρ) := by
  have h : ∃ N, IsGauss l ρ N := by
    obtain ⟨N, hN⟩ := GlobalTheory.GaussExt.exists_gauss_acris l ρ h1 h2
    exact ⟨N, hN⟩
  have hfun : gC l ρ = Classical.choose h := by
    funext x
    unfold gC
    rw [dite_eq_left h]
  rw [hfun]
  exact Classical.choose_spec h

theorem gC_sub_le {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (x y : Formalism.Per.Acris l) :
    gC l ρ (x - y) ≤ max (gC l ρ x) (gC l ρ y) := by
  rw [sub_eq_add_neg]
  calc _ ≤ max (gC l ρ x) (gC l ρ (-y)) := hG.2.1 _ _
    _ = _ := by rw [hG.2.2.1]

theorem gC_pow {ρ : ℝ} (hG : IsGauss l ρ (gC l ρ)) (h1 : gC l ρ 1 = 1) (x : Formalism.Per.Acris l) (n : ℕ) :
    gC l ρ (x ^ n) = gC l ρ x ^ n := by
  induction n with
  | zero => simp [h1]
  | succ n ih => rw [pow_succ, hG.2.2.2.1, ih, pow_succ]

theorem gA_le_of_coeff_zero {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (a : Formalism.Per.Ainf l)
    (ha : a.coeff 0 = 0) : gA l ρ a ≤ ρ := by
  unfold gA
  apply ciSup_le
  intro n
  rcases n with _ | n
  · simpa [ha, untilt_zero'] using h0
  · have hn : ‖(((a.coeff (n + 1)).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ (n + 1)) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) (GlobalTheory.TiltAbs.norm_le_one _) (by positivity)
    calc _ ≤ 1 * ρ ^ (n + 1) := mul_le_mul_of_nonneg_right hn (pow_nonneg h0 _)
      _ ≤ ρ := by rw [one_mul]; exact pow_le_of_le_one h0 h1 (Nat.succ_ne_zero n)

theorem tc_mul (a b : Formalism.Per.Fl l) : tc l (a * b) = tc l a * tc l b := by
  unfold tc
  rw [Formalism.Per.tm, map_mul, map_mul]

end GlobalTheory.GaussCancel

namespace GlobalTheory.GaussCancel

variable {l : ℕ} [Fact l.Prime]

theorem equal_gauss_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 →
    (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') →
    ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧
      gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  intro l _ w w' hw' heq
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl1
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by positivity
  obtain ⟨⟨c, k, ρ₂, hc, hρ₂, hρ₂1, hm'⟩, -⟩ := GlobalTheory.T.gaussNormAcris_locally_monomial l w' hw' (l : ℝ)⁻¹ le_rfl hlinv
  have hm : ∀ ρ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂, gC l ρ w = c * ρ ^ k := fun ρ hρ => by
    rw [heq ρ hρ.1 (lt_of_le_of_lt hρ.2 hρ₂1)]; exact hm' ρ hρ
  obtain ⟨y', j', hkj', hy', hL'⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w' c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm'
  obtain ⟨y, j, hkj, hy, hL⟩ := GlobalTheory.T.exists_teichmuller_lower_gaussNorm_of_locally_monomial l w c (l : ℝ)⁻¹ ρ₂ k le_rfl hρ₂ hρ₂1 hc hm

  have hy'0 : ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hy'
    linarith
  have hdvd : y' ∣ y := by
    apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
    have hq : ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) ∈ 𝓞_ℂ_[l] := by
      rw [GlobalTheory.RingBasics.mem_OC, norm_div, hy, hy', div_self hc.ne']
    refine ⟨⟨_, hq⟩, Subtype.ext ?_⟩
    change ((y.untilt : Formalism.Per.OC l) : ℂ_[l]) = ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]) *
      (((y.untilt : Formalism.Per.OC l) : ℂ_[l]) / ((y'.untilt : Formalism.Per.OC l) : ℂ_[l]))
    field_simp
  obtain ⟨u, hu⟩ := hdvd
  have hu1 : ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((1 : Formalism.Per.Fl l).untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
    have h := hy
    rw [hu, map_mul] at h
    push_cast at h
    rw [norm_mul, hy'] at h
    rw [map_one]
    simp only [OneMemClass.coe_one, norm_one]
    have : c * ‖((u.untilt : Formalism.Per.OC l) : ℂ_[l])‖ = c * 1 := by rw [h, mul_one]
    exact mul_left_cancel₀ hc.ne' this
  obtain ⟨ζ, o, ho, hζ, hζ0, hlt⟩ := GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio l u 1 one_ne_zero hu1
  rw [mul_one, map_one] at hlt
  simp only [OneMemClass.coe_one, norm_one] at hlt

  set ρ₀ : ℝ := ((l : ℝ)⁻¹ + ρ₂) / 2 with hρ₀def
  have hρ₀a : (l : ℝ)⁻¹ < ρ₀ := by rw [hρ₀def]; linarith
  have hρ₀b : ρ₀ < ρ₂ := by rw [hρ₀def]; linarith
  have hρ₀1 : ρ₀ < 1 := lt_trans hρ₀b hρ₂1
  have hρ₀pos : 0 < ρ₀ := lt_trans hlpos hρ₀a
  have hIoo : ρ₀ ∈ Set.Ioo (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a, hρ₀b⟩
  have hIcc : ρ₀ ∈ Set.Icc (l : ℝ)⁻¹ ρ₂ := ⟨hρ₀a.le, hρ₀b.le⟩
  refine ⟨ζ, o, ρ₀, ho, hζ, hζ0, hρ₀a, hρ₀1, ?_⟩
  have hG := isGauss_gC (l := l) hρ₀a.le hρ₀1
  obtain ⟨hb1, hbl, -, hbt, -⟩ := GlobalTheory.T.gaussNormAcris_basic_values l ρ₀ hρ₀a.le hρ₀1
  have hlpow : ∀ n : ℕ, gC l ρ₀ ((l : Formalism.Per.Acris l) ^ n) = ρ₀ ^ n := fun n => by
    rw [gC_pow hG hb1, hbl]
  have hGw' : gC l ρ₀ w' = c * ρ₀ ^ k := hm' ρ₀ hIcc
  have hGw : gC l ρ₀ w = c * ρ₀ ^ k := hm ρ₀ hIcc
  set T : ℝ := ρ₀ ^ (max j j') * (c * ρ₀ ^ k) with hTdef
  set J : ℕ := max j j' with hJ
  set m : ℕ := (k + J).toNat with hmdef

  have hA : ∀ (x : Formalism.Per.Acris l) (z : Formalism.Per.Fl l) (i : ℕ), 0 ≤ k + i → i ≤ J → gC l ρ₀ x = c * ρ₀ ^ k →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ i * x - (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) < ρ₀ ^ i * gC l ρ₀ x →
      gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z) < T := by
    intro x z i hki hiJ hx hlt'
    have hmi : m = (J - i) + (k + i).toNat := by rw [hmdef]; omega
    have heqA : (l : Formalism.Per.Acris l) ^ J * x - (l : Formalism.Per.Acris l) ^ m * tc l z =
        (l : Formalism.Per.Acris l) ^ (J - i) * ((l : Formalism.Per.Acris l) ^ i * x -
          (l : Formalism.Per.Acris l) ^ (k + i).toNat * tc l z) := by
      have e : (l : Formalism.Per.Acris l) ^ J = (l : Formalism.Per.Acris l) ^ (J - i) * (l : Formalism.Per.Acris l) ^ i := by
        rw [← pow_add, Nat.sub_add_cancel hiJ]
      rw [hmi, e, pow_add]
      ring
    rw [heqA, hG.2.2.2.1, hlpow, hTdef, ← hx]
    calc ρ₀ ^ (J - i) * gC l ρ₀ _ < ρ₀ ^ (J - i) * (ρ₀ ^ i * gC l ρ₀ x) :=
          mul_lt_mul_of_pos_left hlt' (pow_pos hρ₀pos _)
      _ = ρ₀ ^ J * gC l ρ₀ x := by rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hiJ]
  have hAw := hA w y j hkj (le_max_left _ _) hGw (hL ρ₀ hIoo)
  have hAw' := hA w' y' j' hkj' (le_max_right _ _) hGw' (hL' ρ₀ hIoo)

  have hζ1 : gC l ρ₀ (tc l ζ) ≤ 1 := (hG.1 _).2
  have hdiff : gC l ρ₀ (tc l u - tc l ζ) < 1 := by
    have hsplit : tc l u - tc l ζ = tc l (u - ζ) + algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)
        (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) := by
      unfold tc
      rw [map_sub, map_sub]
      ring
    have hc0 : (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)).coeff 0 = 0 := by
      change WittVector.constantCoeff (Formalism.Per.tm u - Formalism.Per.tm ζ - Formalism.Per.tm (u - ζ)) = 0
      rw [map_sub, map_sub]
      change (Formalism.Per.tm u).coeff 0 - (Formalism.Per.tm ζ).coeff 0 - (Formalism.Per.tm (u - ζ)).coeff 0 = 0
      simp [Formalism.Per.tm, WittVector.teichmuller_coeff_zero]
    rw [hsplit]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt ?_ ?_)
    · rw [hbt]; exact hlt
    · rw [hG.2.2.2.2]
      exact lt_of_le_of_lt (gA_le_of_coeff_zero hρ₀pos.le hρ₀1.le _ hc0) hρ₀1
  have hmz : ((m : ℕ) : ℤ) = k + J := by rw [hmdef]; exact Int.toNat_of_nonneg (by omega)
  have hD : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y')) < T := by
    have : tc l y - tc l ζ * tc l y' = tc l y' * (tc l u - tc l ζ) := by
      rw [hu, tc_mul]; ring
    rw [this, hG.2.2.2.1, hG.2.2.2.1, hlpow, hbt, hy']
    have hT : ρ₀ ^ m * c = T := by
      rw [hTdef, ← zpow_natCast, hmz, zpow_add₀ hρ₀pos.ne', zpow_natCast]
      ring
    rw [← hT, ← mul_assoc]
    exact mul_lt_of_lt_one_right (mul_pos (pow_pos hρ₀pos _) hc) hdiff
  have hB : gC l ρ₀ (tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y')) < T := by
    rw [hG.2.2.2.1]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (hG.1 _).1 hζ1) hAw'
  have hid : (l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w') =
      ((l : Formalism.Per.Acris l) ^ J * w - (l : Formalism.Per.Acris l) ^ m * tc l y) -
        tc l ζ * ((l : Formalism.Per.Acris l) ^ J * w' - (l : Formalism.Per.Acris l) ^ m * tc l y') +
        (l : Formalism.Per.Acris l) ^ m * (tc l y - tc l ζ * tc l y') := by ring
  have hbig : gC l ρ₀ ((l : Formalism.Per.Acris l) ^ J * (w - tc l ζ * w')) < T := by
    rw [hid]
    refine lt_of_le_of_lt (hG.2.1 _ _) (max_lt (lt_of_le_of_lt (gC_sub_le hG _ _) (max_lt hAw hB)) ?_)
    exact hD
  rw [hG.2.2.2.1, hlpow, hTdef, ← hGw'] at hbig
  exact lt_of_mul_lt_mul_left hbig (pow_nonneg hρ₀pos.le _)

end GlobalTheory.GaussCancel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqualGaussNormTeichmullerCancelStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equal_gaussNorm_teichmuller_cancel : ∀ (l : ℕ) [Fact l.Prime] (w w' : Formalism.Per.Acris l), w' ≠ 0 → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ) (ρ₀ : ℝ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ (l : ℝ)⁻¹ < ρ₀ ∧ ρ₀ < 1 ∧ gC l ρ₀ (w - tc l ζ * w') < gC l ρ₀ w' := by
  first | exact @GlobalTheory.GaussCancel.equal_gauss_cancel | exact GlobalTheory.GaussCancel.equal_gauss_cancel | (intros; apply GlobalTheory.GaussCancel.equal_gauss_cancel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootUnityEqUnit
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss


open Polynomial in
theorem exists_zmod_of_pow_eq_self {F : Type} [CommRing F] [IsDomain F] (l : ℕ) [Fact l.Prime] [CharP F l]
    (ζ : F) (h : ζ ^ l = ζ) : ∃ a : ZMod l, ZMod.castHom (dvd_refl l) F a = ζ := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  set P : (ZMod l)[X] := X ^ l - X with hP
  have hmon : P.Monic := by
    apply Polynomial.monic_X_pow_sub
    simp [hl]
  have hroots : P.roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod l)
    rwa [ZMod.card] at this
  have hdeg : P.natDegree = l := Polynomial.natDegree_X_pow_sub_X (R := (ZMod l)) hl
  have hprod : (Multiset.map (fun a => X - C a) P.roots).prod = P :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [hroots, hdeg]; simp [ZMod.card])
  have hev := congrArg (fun Q : (ZMod l)[X] => Q.eval₂ (ZMod.castHom (dvd_refl l) F) ζ) hprod
  simp only [hP, eval₂_sub, eval₂_X_pow, eval₂_X, h, sub_self] at hev
  rw [Polynomial.eval₂_multiset_prod, Multiset.map_map] at hev
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ _, q = (0:F) := ⟨0, Multiset.prod_eq_zero_iff.1 hev, rfl⟩
  rw [Multiset.mem_map] at hq
  obtain ⟨a, -, rfl⟩ := hq
  refine ⟨a, ?_⟩
  simp only [Function.comp, eval₂_sub, eval₂_X, eval₂_C] at hq0
  exact (sub_eq_zero.1 hq0).symm

theorem padicInt_ringHom_witt_ext_pt {l : ℕ} [Fact l.Prime] {F : Type} [CommRing F] [CharP F l]
    (f g : ℤ_[l] →+* WittVector l F) : f = g := by
  ext x n
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (n + 1) x)
  have hx : x = (x.appr (n + 1) : ℤ_[l]) + y * (l : ℤ_[l]) ^ (n + 1) := by rw [hy]; ring
  have hd : f x = g x + (f y - g y) * (l : WittVector l F) ^ (n + 1) := by
    conv_lhs => rw [hx]
    conv_rhs => rw [hx]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  have ht : WittVector.truncate (n + 1) ((f y - g y) * (l : WittVector l F) ^ (n + 1)) = 0 := by
    rw [← RingHom.mem_ker, WittVector.mem_ker_truncate]
    intro i hi
    exact WittVector.mul_pow_charP_coeff_zero _ hi
  have he : WittVector.truncate (n + 1) (f x) = WittVector.truncate (n + 1) (g x) := by
    rw [hd, map_add (f := _), ht, add_zero]
  have := congrArg (fun z => TruncatedWittVector.coeff (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) z) he
  simpa only [WittVector.coeff_truncate] using this

theorem teichmuller_root_unity_eq_unit : ∀ (l : ℕ) [Fact l.Prime] (ζ : Formalism.Per.Fl l), ζ ^ l = ζ → ζ ≠ 0 →
    ∃ c : ℤ_[l], IsUnit c ∧ zc l c = tc l ζ := by
  intro l _ ζ h hne
  obtain ⟨a, rfl⟩ := exists_zmod_of_pow_eq_self l ζ h
  have ha : a ≠ 0 := by rintro rfl; exact hne (map_zero _)
  refine ⟨WittVector.toPadicInt l (WittVector.teichmuller l a), ?_, ?_⟩
  · exact ((Ne.isUnit ha).map (WittVector.teichmuller l)).map (WittVector.toPadicInt l)
  · have hz : Formalism.Per.zA l = (WittVector.map (ZMod.castHom (dvd_refl l) (Formalism.Per.Fl l))).comp
        (WittVector.fromPadicInt l) := padicInt_ringHom_witt_ext_pt _ _
    simp only [zc, tc, RingHom.comp_apply, hz, Formalism.Per.tm]
    have hft : WittVector.fromPadicInt l (WittVector.toPadicInt l (WittVector.teichmuller l a)) =
        WittVector.teichmuller l a :=
      RingHom.congr_fun (WittVector.fromPadicInt_comp_toPadicInt (p := l)) _
    rw [hft, WittVector.map_teichmuller]

end GlobalTheory.PMon.Gauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigit
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

theorem gC_zero_of_radius (l : ℕ) [Fact l.Prime] {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ (0 : Formalism.Per.Acris l) = 0 := by
  have hN := isGauss_gC_of_le l ρ h0 h1
  have hl : gC l ρ (l : Formalism.Per.Acris l) = ρ := (gC_basic_values l ρ h0 h1).2.1
  have hm := hN.2.2.2.1 ((l : Formalism.Per.Acris l)) 0
  rw [mul_zero, hl] at hm
  have : (1 - ρ) * gC l ρ 0 = 0 := by linarith
  rcases mul_eq_zero.1 this with h' | h'
  · linarith
  · exact h'

theorem gC_eq_zpow_mul_of_vr (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l) (hx : x ≠ 0) (hy : y ≠ 0) (n : ℤ)
    (hn : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r x - vr l r y = n * r) (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ x = ρ ^ n * gC l ρ y := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  set r := -Real.logb l ρ with hr
  have hρr : (l : ℝ) ^ (-r) = ρ := by
    rw [hr, neg_neg, Real.rpow_logb hl0 hl1.ne' hρ]
  have hr0 : 0 < r := by
    have := Real.logb_neg hl1 hρ h1
    linarith
  have hr1 : r ≤ 1 := by
    have h := (Real.logb_le_logb hl1 (inv_pos.2 hl0) hρ).2 h0
    rw [Real.logb_inv, Real.logb_self_eq_one hl1] at h
    linarith
  have hv := hn r ⟨hr0, hr1⟩
  simp only [vr, hρr] at hv
  have hgx := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx ρ h0 h1
  have hgy := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y hy ρ h0 h1
  apply Real.logb_injOn_pos hl1 hgx (Set.mem_Ioi.2 (mul_pos (zpow_pos hρ n) hgy))
  have hz : Real.logb l (ρ ^ n) = n * Real.logb l ρ := by
    rw [Real.logb, Real.logb, Real.log_zpow, mul_div_assoc]
  rw [Real.logb_mul (zpow_pos hρ n).ne' hgy.ne', hz]
  rw [hr] at hv
  linarith

end GlobalTheory.PMon.Gauss

theorem GlobalTheory.PMon.Gauss.one_digit : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ c : ℤ_[l], IsUnit c ∧ ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (w - zc l c * w') ≤ ρ * gC l ρ w' := by
  intro l _ h s hsh w w' hφh hw' hrat hg
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  obtain ⟨ζ, o, ρ₀, ho, hζo, hζ0, hρ₀l, hρ₀1, hlt⟩ := GlobalTheory.T.equal_gaussNorm_teichmuller_cancel l w w' hw' hg
  have hζl : ζ ^ l = ζ := GlobalTheory.T.rootCancel_pow_eq_self_acris_gaussNorm l h s hsh w w' ζ o ρ₀ hφh hw' hrat hg ho hζo hζ0 hρ₀l.le hρ₀1 hlt
  obtain ⟨c, hcu, hc⟩ := GlobalTheory.PMon.Gauss.teichmuller_root_unity_eq_unit l ζ hζl hζ0
  refine ⟨c, hcu, fun ρ h0 h1 => ?_⟩
  have hρ : 0 < ρ := (inv_pos.2 hl0).trans_le h0
  have hN := isGauss_gC_of_le l ρ h0 h1
  by_cases hw1 : w - zc l c * w' = 0
  · rw [hw1, gC_zero_of_radius l h0 h1]
    exact mul_nonneg hρ.le (hN.1 w').1
  have hφz : φc l (zc l c) = zc l c := by
    rw [hc, frob_teich, hζl]
  have hrat1 : φc l (w - zc l c * w') * w' = (w - zc l c * w') * φc l w' := by
    rw [map_sub, map_mul, hφz]
    linear_combination hrat
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hsh (w - zc l c * w') w' hφh hw1 hw' hrat1
  have hmono := gC_eq_zpow_mul_of_vr l _ w' hw1 hw' n hn
  have hρ₀ : 0 < ρ₀ := (inv_pos.2 hl0).trans hρ₀l
  have hn1 : 1 ≤ n := by
    by_contra hcon
    push_neg at hcon
    have hle : n ≤ 0 := by omega
    have e := hmono ρ₀ hρ₀l.le hρ₀1
    rw [← hc] at hlt
    rw [e] at hlt
    have hg0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l w' hw' ρ₀ hρ₀l.le hρ₀1
    have : (1 : ℝ) ≤ ρ₀ ^ n := one_le_zpow_of_nonpos₀ hρ₀ hρ₀1.le hle
    nlinarith
  rw [hmono ρ h0 h1]
  have hle : ρ ^ n ≤ ρ ^ (1 : ℤ) := zpow_le_zpow_right_of_le_one₀ hρ h1.le hn1
  rw [zpow_one] at hle
  exact mul_le_mul_of_nonneg_right hle (hN.1 w').1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigitStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussNormAcris_sub_unit_le_digit : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 → φc l w * w' = w * φc l w' → (∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = gC l ρ w') → ∃ c : ℤ_[l], IsUnit c ∧ ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (w - zc l c * w') ≤ ρ * gC l ρ w' := by
  first | exact @GlobalTheory.PMon.Gauss.one_digit | exact GlobalTheory.PMon.Gauss.one_digit | (intros; apply GlobalTheory.PMon.Gauss.one_digit <;> assumption)
end
