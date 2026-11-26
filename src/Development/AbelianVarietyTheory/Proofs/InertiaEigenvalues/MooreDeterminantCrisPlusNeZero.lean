module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisSubUnitLeDigit

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrisPlusFrobEigenvectorRatioPadic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioProportionalTarget
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.Gauss

namespace RatioProp

variable {l : ℕ} [Fact l.Prime]

theorem one_lt_l : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt

theorem inv_l_pos : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith [(one_lt_l : (1 : ℝ) < l)])

theorem inv_l_lt_one : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ one_lt_l

theorem rho_pos {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) : 0 < ρ := lt_of_lt_of_le inv_l_pos h0

theorem gauss {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : IsGauss l ρ (gC l ρ) :=
  isGauss_gC_target l ρ h0 h1

theorem phi_zc (c : ℤ_[l]) : φc l (zc l c) = zc l c :=
  (GlobalTheory.MemLoc.PhiFix.phiA_alg l _).trans (congrArg _ (GlobalTheory.MemLoc.PhiFix.φA_zA l c))

theorem iter_lpow (m j : ℕ) (x : Formalism.Per.Acris l) :
    (φc l)^[m] ((l : Formalism.Per.Acris l) ^ j * x) = (l : Formalism.Per.Acris l) ^ j * (φc l)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem gC_zero {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) : gC l ρ 0 = 0 := by
  have hm := (gauss h0 h1).2.2.2.1 0 (l : Formalism.Per.Acris l)
  rw [zero_mul, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1] at hm
  have e : gC l ρ 0 * (1 - ρ) = 0 := by linear_combination hm
  rcases mul_eq_zero.1 e with h | h
  · exact h
  · exact absurd h (by linarith)

theorem gC_lpow {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (m : ℕ) (x : Formalism.Per.Acris l) :
    gC l ρ ((l : Formalism.Per.Acris l) ^ m * x) = ρ ^ m * gC l ρ x := by
  induction m with
  | zero => rw [pow_zero, one_mul, pow_zero, one_mul]
  | succ m ih =>
    rw [pow_succ', mul_assoc, (gauss h0 h1).2.2.2.1, (GlobalTheory.T.gaussNormAcris_basic_values l ρ h0 h1).2.1, ih, pow_succ']
    ring

theorem lpow_ne_zero {x : Formalism.Per.Acris l} (hx : x ≠ 0) (m : ℕ) : (l : Formalism.Per.Acris l) ^ m * x ≠ 0 := by
  intro e
  have h := gC_lpow le_rfl inv_l_lt_one m x
  rw [e, gC_zero le_rfl inv_l_lt_one] at h
  have hp := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x hx _ le_rfl inv_l_lt_one
  have : (0 : ℝ) < (l : ℝ)⁻¹ ^ m * gC l (l : ℝ)⁻¹ x := mul_pos (pow_pos inv_l_pos m) hp
  linarith

theorem pert {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) (W W' : Formalism.Per.Acris l) (c y : ℤ_[l]) (k : ℕ) :
    gC l ρ (W - zc l (c + (l : ℤ_[l]) ^ k * y) * W') ≤ max (gC l ρ (W - zc l c * W')) (ρ ^ k * gC l ρ W') := by
  have e : W - zc l (c + (l : ℤ_[l]) ^ k * y) * W' =
      (W - zc l c * W') + -((l : Formalism.Per.Acris l) ^ k * (zc l y * W')) := by
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine ((gauss h0 h1).2.1 _ _).trans (max_le_max le_rfl ?_)
  rw [(gauss h0 h1).2.2.1, gC_lpow h0 h1, (gauss h0 h1).2.2.2.1]
  exact mul_le_mul_of_nonneg_left
    (mul_le_of_le_one_left ((gauss h0 h1).1 _).1 ((gauss h0 h1).1 _).2) (pow_nonneg (rho_pos h0).le _)

def digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : Set ℤ_[l] :=
  {c | ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') ≤ ρ ^ k * gC l ρ W'}

theorem isClosed_digitSet (W W' : Formalism.Per.Acris l) (k : ℕ) : IsClosed (digitSet W W' k) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro c hc
  simp only [digitSet, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall, not_le] at hc
  obtain ⟨ρ, h0, h1, hlt⟩ := hc
  refine ⟨(l : ℝ) ^ (-(k : ℤ)), zpow_pos (by linarith [(one_lt_l : (1 : ℝ) < l)]) _, fun c' hc' hT => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hc'
  have hmem : c - c' ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow, norm_sub_rev]
    exact hc'.le
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  have hp := pert h0 h1 W W' c' y k
  have e : c' + (l : ℤ_[l]) ^ k * y = c := by rw [mul_comm, hy]; ring
  rw [e] at hp
  exact absurd (hp.trans (max_le (hT ρ h0 h1) le_rfl)) (not_le.2 hlt)

theorem gC_eq_of_vr {V W' : Formalism.Per.Acris l} (hV : V ≠ 0) (hW' : W' ≠ 0) (n : ℤ)
    (hn : ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r V - vr l r W' = n * r) {ρ : ℝ} (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    gC l ρ V = ρ ^ n * gC l ρ W' := by
  have hl : (1 : ℝ) < l := one_lt_l
  have hρ0 : 0 < ρ := rho_pos h0
  have hr : -Real.logb l ρ ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · linarith [Real.logb_neg hl hρ0 h1]
    · have := (Real.logb_le_logb hl inv_l_pos hρ0).2 h0
      rw [Real.logb_inv, Real.logb_self_eq_one hl] at this
      linarith
  have e := hn _ hr
  have hpow : (l : ℝ) ^ (-(-Real.logb l ρ)) = ρ := by
    rw [neg_neg, Real.rpow_logb (by linarith) (ne_of_gt hl) hρ0]
  simp only [vr] at e
  rw [hpow] at e
  have hV0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l V hV ρ h0 h1
  have hW0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l W' hW' ρ h0 h1
  apply Real.logb_injOn_pos hl hV0 (mul_pos (zpow_pos hρ0 n) hW0)
  have hz : Real.logb l (ρ ^ n) = n * Real.logb l ρ := by
    simp only [Real.logb, Real.log_zpow]
    ring
  rw [Real.logb_mul (ne_of_gt (zpow_pos hρ0 n)) (ne_of_gt hW0), hz]
  linarith

theorem digit_step {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W') (k : ℕ) (c : ℤ_[l]) (hc : c ∈ digitSet W W' k) :
    (digitSet W W' (k + 1)).Nonempty := by
  have hrV : φc l (W - zc l c * W') * W' = (W - zc l c * W') * φc l W' := by
    rw [map_sub, map_mul, phi_zc]
    linear_combination hr
  by_cases hV0 : W - zc l c * W' = 0
  · refine ⟨c, fun ρ h0 h1 => ?_⟩
    rw [hV0, gC_zero h0 h1]
    exact mul_nonneg (pow_nonneg (rho_pos h0).le _) ((gauss h0 h1).1 _).1
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs _ W' he hV0 hW' hrV
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (W - zc l c * W') = ρ ^ n * gC l ρ W' :=
    fun ρ h0 h1 => gC_eq_of_vr hV0 hW' n hn h0 h1
  have hW0 := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l W' hW' _ le_rfl inv_l_lt_one
  have hk : (k : ℤ) ≤ n := by
    have a := hc _ le_rfl inv_l_lt_one
    rw [hg _ le_rfl inv_l_lt_one] at a
    have b := le_of_mul_le_mul_right a hW0
    rw [← zpow_natCast] at b
    exact (zpow_le_zpow_iff_right_of_lt_one₀ inv_l_pos inv_l_lt_one).1 b
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hkm : k ≤ m := by exact_mod_cast hk
  obtain ⟨u, -, hu⟩ := GlobalTheory.T.gaussNormAcris_sub_unit_le_digit l h s hs (W - zc l c * W') ((l : Formalism.Per.Acris l) ^ m * W')
    (by rw [iter_lpow, he]; ring) (lpow_ne_zero hW' m)
    (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hrV)
    (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
  refine ⟨c + u * (l : ℤ_[l]) ^ m, fun ρ h0 h1 => ?_⟩
  have e : W - zc l (c + u * (l : ℤ_[l]) ^ m) * W' =
      (W - zc l c * W') - zc l u * ((l : Formalism.Per.Acris l) ^ m * W') := by
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [e]
  refine (hu ρ h0 h1).trans ?_
  rw [gC_lpow h0 h1, ← mul_assoc, ← pow_succ']
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (rho_pos h0).le h1.le (by omega))
    ((gauss h0 h1).1 _).1

theorem eq_zc_mul {h s : ℕ} (hs : s < h) {W W' : Formalism.Per.Acris l}
    (he : (φc l)^[h] W' = (l : Formalism.Per.Acris l) ^ s * W') (hW' : W' ≠ 0)
    (hr : φc l W * W' = W * φc l W')
    (hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ W = gC l ρ W') :
    ∃ c : ℤ_[l], W = zc l c * W' := by
  have hmono : ∀ i, digitSet W W' (i + 1) ⊆ digitSet W W' i := fun i c hc ρ h0 h1 =>
    (hc ρ h0 h1).trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_of_le_one (rho_pos h0).le h1.le (Nat.le_succ i)) ((gauss h0 h1).1 _).1)
  have hne : ∀ i, (digitSet W W' i).Nonempty := by
    intro i
    induction i with
    | zero => exact ⟨0, fun ρ h0 h1 => by rw [map_zero, zero_mul, sub_zero, pow_zero, one_mul, hg ρ h0 h1]⟩
    | succ i ih =>
      obtain ⟨c, hc⟩ := ih
      exact digit_step hs he hW' hr i c hc
  obtain ⟨c, hc⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed _ hmono hne
    (isCompact_univ.of_isClosed_subset (isClosed_digitSet W W' 0) (Set.subset_univ _))
    (isClosed_digitSet W W')
  rw [Set.mem_iInter] at hc
  refine ⟨c, ?_⟩
  by_contra hne'
  have hpos := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l (W - zc l c * W') (sub_ne_zero.2 hne') _ le_rfl inv_l_lt_one
  have hlim : Filter.Tendsto (fun i : ℕ => (l : ℝ)⁻¹ ^ i * gC l (l : ℝ)⁻¹ W') Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one inv_l_pos.le inv_l_lt_one).mul_const
      (gC l (l : ℝ)⁻¹ W')
  have := ge_of_tendsto' hlim (fun i => hc i _ le_rfl inv_l_lt_one)
  linarith

end RatioProp


open RatioProp in
theorem ratio_proportional_target : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l,
    (φc l)^[h] w = (l : Formalism.Per.Acris l) ^ s * w → (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w' ≠ 0 →
    φc l w * w' = w * φc l w' → ∃ c d : ℤ_[l], c ≠ 0 ∧ zc l c * w = zc l d * w' := by
  intro l _ h s hs w w' _ he' hw' hr
  by_cases hw : w = 0
  · exact ⟨1, 0, one_ne_zero, by rw [hw, mul_zero, map_zero, zero_mul]⟩
  obtain ⟨n, hn⟩ := GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius l h s hs w w' he' hw hw' hr
  have hg : ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ w = ρ ^ n * gC l ρ w' :=
    fun ρ h0 h1 => gC_eq_of_vr hw hw' n hn h0 h1
  rcases le_or_gt 0 n with hn0 | hn0
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn0).symm⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := w) (W' := (l : Formalism.Per.Acris l) ^ m * w')
      (by rw [iter_lpow, he']; ring) (lpow_ne_zero hw' m)
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by rw [hg ρ h0 h1, gC_lpow h0 h1, zpow_natCast])
    refine ⟨1, c * (l : ℤ_[l]) ^ m, one_ne_zero, ?_⟩
    rw [map_one, one_mul, hc, map_mul, map_pow, map_natCast]
    ring
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -n := ⟨(-n).toNat, Int.toNat_of_nonneg (by omega)⟩
    obtain ⟨c, hc⟩ := eq_zc_mul hs (W := (l : Formalism.Per.Acris l) ^ m * w) (W' := w') he' hw'
      (by rw [map_mul, map_pow, map_natCast]; linear_combination (l : Formalism.Per.Acris l) ^ m * hr)
      (fun ρ h0 h1 => by
        rw [gC_lpow h0 h1, hg ρ h0 h1, ← mul_assoc, ← zpow_natCast, hm,
          ← zpow_add₀ (ne_of_gt (rho_pos h0)), neg_add_cancel, zpow_zero, one_mul])
    refine ⟨(l : ℤ_[l]) ^ m, c, pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero), ?_⟩
    rw [map_pow, map_natCast, hc]

end GlobalTheory.PMon.Gauss
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TmSubOneNeZeroPt
noncomputable section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Trans

variable (l : ℕ) [Fact l.Prime]

theorem map_ne_zero_pt : ∀ y : Formalism.Per.Ainf l, y ≠ 0 →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) y ≠ 0 := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hr1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  obtain ⟨N, h01, -, -, hmul, hA⟩ := GlobalTheory.GaussExt.exists_gauss_acris l _ le_rfl hr1
  have hbdd : ∀ a : Formalism.Per.Ainf l, BddAbove (Set.range fun n : ℕ =>
      ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n) := by
    intro a
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h1 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ≤ 1 :=
      (GlobalTheory.RingBasics.mem_OC _).1 ((a.coeff n).untilt).2
    have h2 : ‖(((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) h1 (by positivity)
    have h3 : ((l : ℝ)⁻¹) ^ n ≤ 1 := pow_le_one₀ (by positivity) hr1.le
    calc _ ≤ 1 * 1 := mul_le_mul h2 h3 (by positivity) zero_le_one
      _ = 1 := one_mul 1
  have hpos : ∀ a : Formalism.Per.Ainf l, a ≠ 0 → 0 < N (algebraMap _ _ a) := by
    intro a ha0
    obtain ⟨n, ha⟩ : ∃ n, a.coeff n ≠ 0 := by
      by_contra hc
      apply ha0
      refine WittVector.ext fun n => ?_
      rw [WittVector.zero_coeff]
      by_contra hn
      exact hc ⟨n, hn⟩
    rw [hA]
    refine lt_of_lt_of_le ?_ (le_ciSup (hbdd a) n)
    have hne : (((a.coeff n).untilt : Formalism.Per.OC l) : ℂ_[l]) ≠ 0 := by
      intro h
      apply ha
      refine (GlobalTheory.TiltAbs.untilt_ultrametric_definite l (a.coeff n) 0).2 ?_
      exact Subtype.ext h
    have hl0 : (0 : ℝ) < l := lt_trans one_pos hl
    exact mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hne) _) (pow_pos (inv_pos.2 hl0) _)
  have hN0 : N 0 = 0 := by
    have hz : ∀ n : ℕ, (0 : ℝ) ^ ((1 : ℝ) / (l : ℝ) ^ n) = 0 := fun n => Real.zero_rpow (by positivity)
    rw [← map_zero (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l)), hA]
    have hz' : ∀ n : ℕ, (0 : ℝ) ^ (((l : ℝ) ^ n)⁻¹) = 0 := fun n => Real.zero_rpow (by positivity)
    simp [hz, hz', GlobalTheory.GaussExt.untilt_zero]
  intro y hy h0
  have := hpos y hy
  rw [h0, hN0] at this
  exact lt_irrefl _ this

theorem tm_sub_one_ne_zero_pt (e : Formalism.Per.Fl l) (he : e ≠ 1) : (Formalism.Per.tm e - 1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  apply he
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) (sub_eq_zero.1 h)
  simpa using h'

theorem one_ne_zero_pt : (1 : Formalism.Per.Ainf l) ≠ 0 := by
  intro h
  have h' := congrArg (fun w : Formalism.Per.Ainf l => w.coeff 0) h
  simp at h'

theorem map_prod_ne_zero_pt : ∀ s : List (Formalism.Per.Fl l), (∀ e ∈ s, e ≠ 1) →
    algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (s.map fun e => Formalism.Per.tm e - 1).prod ≠ 0 := by
  intro s
  induction s with
  | nil =>
    intro _
    rw [List.map_nil, List.prod_nil]
    exact map_ne_zero_pt l 1 (one_ne_zero_pt l)
  | cons e s ih =>
    intro hs
    rw [List.map_cons, List.prod_cons, map_mul]
    intro h
    exact (GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).elim
      (map_ne_zero_pt l _ (tm_sub_one_ne_zero_pt l e (hs e List.mem_cons_self)))
      (ih fun e' he' => hs e' (List.mem_cons_of_mem _ he'))

end GlobalTheory.PMon.Trans

theorem GlobalTheory.PMon.Trans.acris_bcris : ∀ (l : ℕ) [Fact l.Prime], Function.Injective (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l)) ∧ (∀ x : Formalism.Per.Acris l, Formalism.Per.φB l (algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) x) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l x)) ∧ ∀ c : ℤ_[l], algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (zc l c) = Formalism.Per.zB l c := by
  intro l _
  refine ⟨?_, fun x => GlobalTheory.CrisMaps.φB_phiA l x, fun c => (GlobalTheory.RingIface.zB_alg l c).symm⟩
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  obtain ⟨n, h⟩ := GlobalTheory.CrisLoc.exists_pow_mul_eq_zero l e he hne hx
  refine (GlobalTheory.T.acris_eq_zero_or_eq_zero_of_mul_eq_zero l _ _ h).resolve_left ?_
  have h1 := GlobalTheory.PMon.Trans.map_prod_ne_zero_pt l (List.replicate n e)
    fun e' he' => (List.eq_of_mem_replicate he').symm ▸ hne
  rwa [List.map_replicate, List.prod_replicate, map_pow] at h1
end
end

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.RatioTransport

open GlobalTheory.PMon.Gauss

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem lift_phi {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) :
    T.eB (P.φB b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) (φc l y) := by
  rw [T.frob, h, (GlobalTheory.PMon.Trans.acris_bcris l).2.1]

theorem lift_iter {b : P.R.B} {y : Formalism.Per.Acris l}
    (h : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y) (j : ℕ) :
    T.eB (P.φB^[j] b) = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((φc l)^[j] y) := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply']; exact lift_phi T ih

theorem iter_lpow (m j : ℕ) (x : P.R.B) :
    P.φB^[m] ((l : P.R.B) ^ j * x) = (l : P.R.B) ^ j * P.φB^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast]

theorem isUnit_lpow (m : ℕ) : IsUnit ((l : P.R.B) ^ m) := by
  have h : IsUnit (l : ℚ_[l]) := (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero : (l : ℚ_[l]) ≠ 0).isUnit
  have h2 := h.map (algebraMap ℚ_[l] P.R.B)
  rw [map_natCast] at h2
  exact h2.pow m

theorem ratio_integral {h s : ℕ} (hs : s < h) {b b' : P.R.B} {y y' : Formalism.Per.Acris l}
    (hb : T.eB b = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y)
    (hb' : T.eB b' = algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) y')
    (he : P.φB^[h] b = (l : P.R.B) ^ s * b) (he' : P.φB^[h] b' = (l : P.R.B) ^ s * b')
    (h0 : b' ≠ 0) (hr : P.φB b * b' = b * P.φB b') : ∃ c : ℚ_[l], b = c • b' := by
  obtain ⟨hinj, -, hz⟩ := GlobalTheory.PMon.Trans.acris_bcris l
  have e1 : (φc l)^[h] y = (l : Formalism.Per.Acris l) ^ s * y := by
    apply hinj
    rw [← lift_iter T hb, he, map_mul, map_pow, map_natCast, hb, map_mul, map_pow, map_natCast]
  have e2 : (φc l)^[h] y' = (l : Formalism.Per.Acris l) ^ s * y' := by
    apply hinj
    rw [← lift_iter T hb', he', map_mul, map_pow, map_natCast, hb', map_mul, map_pow, map_natCast]
  have e3 : y' ≠ 0 := by
    rintro rfl
    apply h0
    apply T.eB.injective
    rw [hb', map_zero, map_zero]
  have e4 : φc l y * y' = y * φc l y' := by
    apply hinj
    rw [map_mul, map_mul, ← lift_phi T hb, ← lift_phi T hb', ← hb, ← hb', ← map_mul, ← map_mul, hr]
  obtain ⟨c, d, hc, hcd⟩ := ratio_proportional_target l h s hs y y' e1 e2 e3 e4
  have e5 : algebraMap ℚ_[l] P.R.B (c : ℚ_[l]) * b = algebraMap ℚ_[l] P.R.B (d : ℚ_[l]) * b' := by
    apply T.eB.injective
    rw [map_mul, map_mul, T.zB, T.zB, hb, hb', ← hz, ← hz, ← map_mul, ← map_mul, hcd]
  have hc' : (c : ℚ_[l]) ≠ 0 := fun e => hc (Subtype.ext e)
  refine ⟨(c : ℚ_[l])⁻¹ * d, ?_⟩
  rw [Algebra.smul_def, map_mul, mul_assoc, ← e5, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc', map_one, one_mul]

theorem ratio_of_acris : Ratio := by
  intro l _ P AI T h s hs ω ω' hω hω' he he' h0 hr
  obtain ⟨N, x, hx⟩ := hω
  obtain ⟨M, x', hx'⟩ := hω'
  have hb : T.eB ((l : P.R.B) ^ (N + M) * ω) =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ M * x) := by
    have e : (l : P.R.B) ^ (N + M) * ω = (l : P.R.B) ^ M * ((l : P.R.B) ^ N * ω) := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ M), hx]
    simp only [map_mul, map_pow, map_natCast]
  have hb' : T.eB ((l : P.R.B) ^ (N + M) * ω') =
      algebraMap (Formalism.Per.Acris l) (Formalism.Per.Bcris l) ((l : Formalism.Per.Acris l) ^ N * x') := by
    have e : (l : P.R.B) ^ (N + M) * ω' = (l : P.R.B) ^ N * ((l : P.R.B) ^ M * ω') := by ring
    rw [e, map_mul T.eB ((l : P.R.B) ^ N), hx']
    simp only [map_mul, map_pow, map_natCast]
  have hu := isUnit_lpow (P := P) (N + M)
  obtain ⟨c, hc⟩ := ratio_integral T hs hb hb'
    (by rw [iter_lpow, he]; ring) (by rw [iter_lpow, he']; ring)
    (fun e => h0 ((hu.mul_right_eq_zero).1 e))
    (by
      simp only [map_mul, map_pow, map_natCast]
      linear_combination ((l : P.R.B) ^ (N + M)) ^ 2 * hr)
  refine ⟨c, hu.mul_left_cancel ?_⟩
  rw [hc, Algebra.smul_def, Algebra.smul_def]
  ring

end GlobalTheory.PMon.RatioTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrisPlusFrobEigenvectorRatioPadic
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem ratio_holds : Ratio := GlobalTheory.PMon.RatioTransport.ratio_of_acris

end GlobalTheory.PMon

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrisPlusFrobEigenvectorRatioPadicStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crisPlus_frob_eigenvector_ratio_padic : Ratio := by
  first | exact @GlobalTheory.PMon.ratio_holds | exact GlobalTheory.PMon.ratio_holds | (intros; apply GlobalTheory.PMon.ratio_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantCrisPlusNeZero
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon.MooreDeterminant

variable {B Q : Type} [CommRing B] [IsDomain B] [Field Q] [Algebra Q B]

theorem det_mem (S : B → Prop) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι B) (hM : ∀ i j, S (M i j)) : S M.det := by
  rw [Matrix.det_apply]
  have hz : S 0 := by simpa using h0 0
  refine Finset.sum_induction _ S hadd hz ?_
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul]
  apply hmul
  · have := h0 (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Q)
    simpa using this
  · have h1 : S 1 := by simpa using h0 1
    exact Finset.prod_induction _ S hmul h1 (fun i _ => hM _ _)

theorem iter_eq (φ : B →+* B) (m : ℕ) : ⇑(φ ^ m) = (⇑φ)^[m] := RingHom.coe_pow φ m

theorem moore_core (φ : B →+* B) (S : B → Prop)
    (hφ : ∀ b, S b → S (φ b)) (h0 : ∀ q : Q, S (algebraMap Q B q))
    (hadd : ∀ a b, S a → S b → S (a + b)) (hmul : ∀ a b, S a → S b → S (a * b))
    (L : B) (hL : φ L = L) (h : ℕ)
    (ratio : ∀ s, s < h → ∀ ω ω' : B, S ω → S ω' → φ^[h] ω = L ^ s * ω → φ^[h] ω' = L ^ s * ω' → ω' ≠ 0 →
      φ ω * ω' = ω * φ ω' → ∃ c : Q, ω = c • ω') :
    ∀ (n : ℕ) (a : Fin (n + 1) → B), n + 1 ≤ h → (∀ j, S (a j)) → (∀ j, φ^[h] (a j) = L * a j) →
      LinearIndependent Q a → (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a j)).det ≠ 0 := by
  have hSit : ∀ (i : ℕ) b, S b → S (φ^[i] b) := by
    intro i
    induction i with
    | zero => intro b hb; simpa using hb
    | succ i ih => intro b hb; rw [Function.iterate_succ_apply']; exact hφ _ (ih b hb)
  intro n
  induction n with
  | zero =>
    intro a _ _ _ ha
    rw [Matrix.det_fin_one]
    simpa using ha.ne_zero 0
  | succ n ih =>
    intro a hk hSa hfa ha hdet
    set M : Matrix (Fin (n + 2)) (Fin (n + 2)) B := Matrix.of fun i j => φ^[i] (a j) with hMdef

    have hA := ih (a ∘ Fin.castSucc) (by omega) (fun j => hSa _) (fun j => hfa _)
      (ha.comp _ (Fin.castSucc_injective _))
    set ω : Fin (n + 2) → B := fun m => (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))).det with hωdef
    have hωl : ω (Fin.last _) = (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)).det := by
      simp [ω, Fin.succAbove_last]
    have hωl0 : ω (Fin.last _) ≠ 0 := by rw [hωl]; exact hA
    have hu : ∀ m, M.adjugate m (Fin.last _) = (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * ω m := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
      simp only [Fin.val_last, Fin.succAbove_last, ω]
      congr 2
    have hw : ∀ m, M.adjugate m 0 = (-1) ^ (m : ℕ) * φ (ω m) := by
      intro m
      rw [Matrix.adjugate_fin_succ_eq_det_submatrix, hωdef]
      simp only [Fin.val_zero, zero_add, Fin.succAbove_zero]
      rw [RingHom.map_det]
      congr 2
      ext i j
      simp [M, Matrix.submatrix_apply, RingHom.mapMatrix_apply, Function.iterate_succ_apply']
    have hK : M * M.adjugate = 0 := by rw [Matrix.mul_adjugate, hdet, zero_smul]
    have hker : ∀ i c, ∑ m, M i m * M.adjugate m c = 0 := fun i c => by
      have := congrFun (congrFun hK i) c
      simpa [Matrix.mul_apply] using this

    set v : Fin (n + 2) → B := fun m => M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0 -
      M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _) with hvdef
    have hv : ∀ i, ∑ m, M i m * v m = 0 := by
      intro i
      have e1 := hker i 0
      have e2 := hker i (Fin.last _)
      simp only [v, mul_sub, Finset.sum_sub_distrib]
      have : ∑ m, M i m * (M.adjugate (Fin.last _) (Fin.last _) * M.adjugate m 0) =
          M.adjugate (Fin.last _) (Fin.last _) * ∑ m, M i m * M.adjugate m 0 := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      have : ∑ m, M i m * (M.adjugate (Fin.last _) 0 * M.adjugate m (Fin.last _)) =
          M.adjugate (Fin.last _) 0 * ∑ m, M i m * M.adjugate m (Fin.last _) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
      simp_all
    have hvl : v (Fin.last _) = 0 := by simp only [v]; ring
    have hv' : Matrix.mulVec (Matrix.of fun i j : Fin (n + 1) => φ^[i] ((a ∘ Fin.castSucc) j)) (v ∘ Fin.castSucc) = 0 := by
      funext i
      have := hv (Fin.castSucc i)
      rw [Fin.sum_univ_castSucc, hvl, mul_zero, add_zero] at this
      simpa [Matrix.mulVec, dotProduct, M] using this
    have hv0 := Matrix.eq_zero_of_mulVec_eq_zero hA hv'
    have hvall : ∀ m, v m = 0 := by
      intro m
      refine Fin.lastCases hvl (fun j => ?_) m
      exact congrFun hv0 j

    have hcomm : ∀ m, φ (ω m) * ω (Fin.last _) = ω m * φ (ω (Fin.last _)) := by
      intro m
      have E := hvall m
      simp only [v, hu, hw, Fin.val_last, pow_add] at E
      have hs : ((-1 : B) ^ (m : ℕ)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      have he : ((-1 : B) ^ (n + 1)) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
      linear_combination ((-1 : B) ^ (m : ℕ)) * E
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * hs
        - (φ (ω m) * ω (Fin.last _) - ω m * φ (ω (Fin.last _))) * ((-1 : B) ^ (m : ℕ)) ^ 2 * he

    have hSω : ∀ m, S (ω m) := fun m => det_mem S h0 hadd hmul _ (fun i j => hSit _ _ (hSa _))
    have hLi : ∀ i : ℕ, φ^[i] L = L := fun i => Function.iterate_fixed hL i
    have hfω : ∀ m, φ^[h] (ω m) = L ^ (n + 1) * ω m := by
      intro m
      rw [← iter_eq, hωdef]
      simp only
      rw [RingHom.map_det]
      have : (φ ^ h).mapMatrix (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) =
          L • (Matrix.of fun i j : Fin (n + 1) => φ^[i] (a (m.succAbove j))) := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, iter_eq]
        rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, hfa, ← iter_eq, map_mul, iter_eq, hLi]
      rw [this, Matrix.det_smul, Fintype.card_fin]

    have hrat : ∀ m, ∃ c : Q, ω m = c • ω (Fin.last _) := fun m =>
      ratio (n + 1) (by omega) _ _ (hSω m) (hSω _) (hfω m) (hfω _) hωl0 (hcomm m)
    choose c hc using hrat

    have hrow := hker 0 (Fin.last _)
    set d : Fin (n + 2) → Q := fun m => (-1) ^ ((n + 1 : ℕ) + (m : ℕ)) * c m with hd
    have hsum : (∑ m, d m • a m) * ω (Fin.last _) = 0 := by
      rw [← hrow, Finset.sum_mul]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [hu, hc m]
      simp only [M, Matrix.of_apply, Fin.val_zero, Function.iterate_zero, id, hd, Algebra.smul_def, map_mul, map_pow,
        map_neg, map_one]
      ring
    have hsum0 : ∑ m, d m • a m = 0 := (mul_eq_zero.1 hsum).resolve_right hωl0
    have hdl := Fintype.linearIndependent_iff.1 ha d hsum0 (Fin.last _)
    have hcl : c (Fin.last _) = 0 := by
      simp only [hd, mul_eq_zero, pow_eq_zero_iff', neg_eq_zero, one_ne_zero, false_and, false_or] at hdl
      exact hdl
    apply hωl0
    rw [hc (Fin.last _), hcl, zero_smul]

end GlobalTheory.PMon.MooreDeterminant

namespace GlobalTheory.PMon

theorem moore_statement : Moore := by
  intro l _ P AI T h k hk a hPa hfa ha
  obtain ⟨hF, hinj, -⟩ := GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T
  obtain ⟨hpφ, -, hpR, hpQ, -⟩ := GlobalTheory.T.bcrisPlus_frobeniusStable_subring_in_filZero l P AI T
  haveI : IsDomain P.R.BdR := hF.isDomain
  haveI : IsDomain P.R.B := Function.Injective.isDomain (P.ιB : P.R.B →+* P.R.BdR) hinj
  cases k with
  | zero => simp
  | succ n =>
    exact GlobalTheory.PMon.MooreDeterminant.moore_core (Q := ℚ_[l]) (P.φB : P.R.B →+* P.R.B) (Plus T) hpφ hpQ
      (fun a b ha hb => (hpR a b ha hb).1) (fun a b ha hb => (hpR a b ha hb).2) (l : P.R.B) (map_natCast _ l) h
      (fun s hs ω ω' h1 h2 h3 h4 h5 h6 => GlobalTheory.T.crisPlus_frob_eigenvector_ratio_padic l P AI T h s hs ω ω' h1 h2 h3 h4 h5 h6)
      n a hk hPa hfa ha

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MooreDeterminantCrisPlusNeZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mooreDeterminant_crisPlus_ne_zero : Moore := by
  first | exact @GlobalTheory.PMon.moore_statement | exact GlobalTheory.PMon.moore_statement | (intros; apply GlobalTheory.PMon.moore_statement <;> assumption)
end
