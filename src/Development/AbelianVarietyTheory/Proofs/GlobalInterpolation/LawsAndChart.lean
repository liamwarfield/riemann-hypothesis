module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMultiplicativeChartAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormTranslatePowerCombLeCoprimeTranslation
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilOperatorThetaTranslateShiftPrimeToQ

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ThetaLawsUnitPeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImConjMulEqIntMulArea
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TransInv

theorem im_conj_mul_ne_zero {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 := by
  intro h0
  rw [LinearIndependent.pair_iff] at h
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im] at h0
  have h1 := h w₂.im (-w₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := h w₂.re (-w₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := h 1 0 (by
    apply Complex.ext <;> simp <;> linarith [h1.2, h2.2])
  exact one_ne_zero h3.1

theorem im_conj_mul_mem {w₁ w₂ u v : ℂ} (hu : u ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ))
    (hv : v ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ)) :
    ∃ k : ℤ, ((starRingEnd ℂ) u * v).im = k * ((starRingEnd ℂ) w₁ * w₂).im := by
  obtain ⟨a, b, rfl⟩ := AddSubgroup.mem_closure_pair.1 hu
  obtain ⟨c, d, rfl⟩ := AddSubgroup.mem_closure_pair.1 hv
  refine ⟨a * d - b * c, ?_⟩
  simp
  ring

theorem area_closure_pair {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    area (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h0 := im_conj_mul_ne_zero h
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨abs_pos.2 h0, w₁, AddSubgroup.subset_closure (by simp), w₂,
    AddSubgroup.subset_closure (by simp), rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨k, hk⟩ := im_conj_mul_mem hu hv
  rw [hk] at ha ⊢
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at ha
  have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk0
  rw [abs_mul]
  nlinarith [abs_nonneg ((starRingEnd ℂ) w₁ * w₂).im]

end GlobalTheory.TransInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedMultiplicativeChart
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedMultiplicativeChart
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.Norm

variable {q : ℕ} [hq : Fact q.Prime]

lemma cc_subst {a : ℂ_[q]⟦X⟧} (ha : constantCoeff a = 0) (f : ℂ_[q]⟦X⟧) :
    constantCoeff (f.subst a : ℂ_[q]⟦X⟧) = constantCoeff f := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' hs, finsum_eq_single _ 0]
  · simp
  · intro k hk
    simp [ha, hk]

lemma coeff_expY_subst {a : ℂ_[q]⟦X⟧} (ha : constantCoeff a = 0) (f : ℂ_[q]⟦X⟧) :
    coeff 1 (f.subst a : ℂ_[q]⟦X⟧) = coeff 1 f * coeff 1 a := by
  have hs := HasSubst.of_constantCoeff_zero' ha
  have e := congrArg constantCoeff (derivative_subst (f := f) hs)
  rw [map_mul, cc_subst ha] at e
  simpa [← coeff_zero_eq_constantCoeff_apply, coeff_derivative] using e

lemma const_log (ω : ℂ_[q]) : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := by
  have : constantCoeff (logS : ℂ_[q]⟦X⟧) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp [logS]
  simp [this]

lemma hat_scale (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (G : ℂ → ℂ) (a : ℤ_[q]) :
    hat ι (C (ω * zc a) * logS) G = (hat ι (C ω * logS) G).subst (mulS a : ℂ_[q]⟦X⟧) := by
  obtain ⟨hm, -⟩ := MulSeries.mulS_laws q
  obtain ⟨-, h0, -, hl⟩ := hm a
  have hsub : HasSubst (mulS a : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' h0
  have hs : HasSubst (C ω * logS : ℂ_[q]⟦X⟧) := HasSubst.of_constantCoeff_zero' (const_log ω)
  unfold hat
  rw [subst_comp_subst_apply hs hsub, ← smul_eq_C_mul (a := ω), subst_smul hsub, hl, smul_eq_C_mul,
    map_mul, mul_assoc]

lemma mchart_scale (M : Mdl q) {ω : ℂ_[q]} (h : M.MChart ω) {a : ℤ_[q]} (ha : ‖a‖ = 1) :
    M.MChart (ω * zc a) := by
  obtain ⟨hm, -, -, hb, -, hn⟩ := MulSeries.mulS_laws q
  obtain ⟨-, h0, h1, -⟩ := hm a
  obtain ⟨ok, -, bd, c1⟩ := h
  refine ⟨ok, const_log _, ?_, ?_⟩
  · rw [hat_scale, hb a _ _ ha]; exact bd
  · rw [hat_scale, coeff_expY_subst h0, norm_mul, c1, h1, hn, ha, one_mul]

lemma at_scale (M : Mdl q) {ω : ℂ_[q]} (h : M.MChart ω) {a : ℤ_[q]} {ξ : ℂ_[q]} {n k : ℕ} {y : ℂ}
    (hξ : ξ ^ (q ^ n) = 1) (hk : ‖a - (k : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(n : ℤ))) (hy : M.At ω (ξ ^ k) y) :
    M.At (ω * zc a) ξ y := by
  obtain ⟨hm, -⟩ := MulSeries.mulS_laws q
  obtain ⟨-, h0, -, -⟩ := hm a
  obtain ⟨h1, h2⟩ := (GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 ξ n k a _ hξ hk ⟨1, h.2.2.1⟩
  obtain ⟨s, h3, h4⟩ := hy
  refine ⟨s, h1, ?_⟩
  rw [hat_scale, ← (Shift.shift_laws q ξ h1).2.2.2.2.1, h2, cc_subst h0,
    (Shift.shift_laws q _ h3).2.2.2.2.1, h4]

lemma at_pow (M : Mdl q) {ω : ℂ_[q]} (h : M.MChart ω) {ξ : ℂ_[q]} {p : ℂ} (hp : M.At ω ξ p) (k : ℕ) :
    M.At ω (ξ ^ k) ((k : ℂ) * p) := by
  induction k with
  | zero => simpa using (GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω h).2.2.2.2
  | succ k ih =>
    have := (GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω h).1 _ _ _ _ ih hp
    rw [← pow_succ] at this
    convert this using 1
    push_cast; ring

noncomputable def rt (q n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((q ^ n : ℕ) : ℂ))

lemma rt_prim (n : ℕ) : IsPrimitiveRoot (rt q n) (q ^ n) :=
  Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hq.out.ne_zero)

lemma rt_succ (n : ℕ) : rt q (n + 1) ^ q = rt q n := by
  unfold rt
  rw [← Complex.exp_nat_mul]
  congr 1
  have : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  push_cast
  field_simp
  ring

lemma kap_eq {d : ℕ} (hd : 0 < d) (n : ℕ) (u b : ℤ) :
    kap1 d 1 (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n) = rt q n ^ b := by
  unfold kap1 rt
  rw [← Complex.exp_int_mul]
  congr 1
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have : (h1 d 1 (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n)).im = -(b : ℝ) / (q : ℝ) ^ n := by
    unfold h1
    have e : ((q : ℂ) ^ n) = (((q : ℝ) ^ n : ℝ) : ℂ) := by push_cast; rfl
    rw [e, one_mul, Complex.im_ofReal_mul, Complex.conj_im, Complex.div_ofReal_im]
    simp only [Complex.add_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re, OKArith.im_w]
    field_simp
    ring
  rw [this]
  push_cast
  ring

lemma norm_qpow (n : ℕ) : ‖(q : ℂ_[q]) ^ n‖ = (q : ℝ) ^ (-(n : ℤ)) := by
  have := OKArith.norm_zc (q := q) ((q : ℤ_[q]) ^ n)
  rw [PadicInt.norm_p_pow] at this
  simpa using this

lemma pow_le (n m : ℕ) (h : n ≤ m) : (q : ℝ) ^ (-(m : ℤ)) ≤ (q : ℝ) ^ (-(n : ℤ)) := by
  have : (1 : ℝ) ≤ q := by exact_mod_cast hq.out.one_lt.le
  exact zpow_le_zpow_right₀ this (by omega)

section
variable {d : ℕ} (hd : d.Prime) (h16 : d % 16 = 7) (hs : Split d q)
include hd h16 hs

lemma norm_le (ι : ℂ ≃+* ℂ_[q]) {α : ℂ} (h : InOK d α) : ‖ι α‖ ≤ 1 := by
  obtain ⟨⟨a, ha⟩, -⟩ := (okArith d q ι hd h16 hs).2.1 α h
  rw [ha, OKArith.zc_eq, OKArith.norm_zc]
  exact PadicInt.norm_le_one a

lemma div_ok (ι : ℂ ≃+* ℂ_[q]) (n : ℕ) (u b : ℤ) (hb : (q : ℤ) ^ n ∣ b)
    (hc : ‖ι (conj ((u : ℂ) + (b : ℂ) * wK d))‖ ≤ (q : ℝ) ^ (-(n : ℤ))) :
    InOK d (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n) := by
  refine (okArith d q ι hd h16 hs).2.2.1 _ n ⟨u, b, rfl⟩ ?_ hc
  obtain ⟨c, rfl⟩ := hb
  have h1 : ‖ι (((-c : ℤ) : ℂ) + ((2 * c : ℤ) : ℂ) * wK d)‖ ≤ 1 := norm_le hd h16 hs ι ⟨_, _, rfl⟩
  have e : (u : ℂ) + (((q : ℤ) ^ n * c : ℤ) : ℂ) * wK d =
      conj ((u : ℂ) + (((q : ℤ) ^ n * c : ℤ) : ℂ) * wK d) +
        (q : ℂ) ^ n * (((-c : ℤ) : ℂ) + ((2 * c : ℤ) : ℂ) * wK d) := by
    rw [OKArith.conj_el]; push_cast; ring
  rw [e, map_add (f := _)]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hc ?_)
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_qpow]
  exact mul_le_of_le_one_right (by positivity) h1

lemma gen (M : Mdl q) {ω : ℂ_[q]} (hL : IsOK d M.L) (h : M.MChart ω) (n : ℕ) :
    ∃ u b : ℤ, M.At ω (M.ι (rt q n)) (((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n) ∧
      ‖M.ι (conj ((u : ℂ) + (b : ℂ) * wK d))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) ∧ (n ≠ 0 → ¬ (q : ℤ) ∣ b) := by
  obtain ⟨hex, -, huq, hlat, h10⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω h
  obtain ⟨⟨-, -, hring⟩, hint, -, hid, -⟩ := okArith d q M.ι hd h16 hs
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have hη : M.ι (rt q n) ^ (q ^ n) = 1 := by rw [← map_pow, (rt_prim n).pow_eq_one, map_one]
  have hlt : ‖M.ι (rt q n) - 1‖ < 1 :=
    ((GlobalTheory.T.cpSeriesMultiplicativeShift_comp_and_subst q).2 _ n 0 0 0 hη (by simp) ⟨0, fun m => by simp⟩).1
  obtain ⟨p, hp⟩ := hex _ hlt
  have kill : ∀ z, M.At ω 1 z ↔ InOK d z := fun z => by
    rw [hlat 1 0 z h10, zero_sub, neg_mem_iff, hL]
  have h1 := at_pow M h hp (q ^ n)
  rw [hη, kill] at h1
  obtain ⟨u, b, hub⟩ := h1
  have hpe : p = ((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ n := by
    rw [← hub]; push_cast; field_simp
  have hc : ‖M.ι (conj ((u : ℂ) + (b : ℂ) * wK d))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    obtain ⟨e, he, he1, he2⟩ := hid (n + 1) 1 (by simp)
    have hce := (hring e e he he).2.2.2
    obtain ⟨⟨a, ha⟩, -⟩ := hint _ hce
    have h2 := (GlobalTheory.T.multiplicativeCoord_add_and_complexMul q M ω h).2 (conj e) a n 0 _ p
      (fun l hl => (hL _).2 (hring _ _ hce ((hL _).1 hl)).2.1) ha
      (by
        rw [Nat.cast_zero, sub_zero, ← OKArith.norm_zc, ← OKArith.zc_eq, ← ha]
        exact he2.trans (pow_le _ _ (by omega))) hη hp
    rw [pow_zero, kill] at h2
    have h3 := norm_le hd h16 hs M.ι (hring _ _ h2 h2).2.2.2
    have hne : ‖M.ι e‖ = 1 := by
      rw [Nat.cast_one, one_mul] at he1
      have : ‖M.ι e - 1‖ < ‖(1 : ℂ_[q])‖ := by
        rw [norm_one]
        exact he1.trans_lt (zpow_lt_one_of_neg₀ hq1 (by omega))
      have h5 := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm this.ne
      rw [sub_add_cancel, max_eq_right this.le, norm_one] at h5
      exact h5
    have e1 : e * conj ((u : ℂ) + (b : ℂ) * wK d) = (q : ℂ) ^ n * conj (conj e * p) := by
      rw [← hub]; simp only [map_mul, Complex.conj_conj, map_natCast]; push_cast; ring
    have e2 := congrArg (fun z => ‖M.ι z‖) e1
    simp only [map_mul M.ι, norm_mul, hne, one_mul, map_pow M.ι, map_natCast, norm_qpow] at e2
    rw [e2]
    exact mul_le_of_le_one_right (by positivity) h3
  refine ⟨u, b, hpe ▸ hp, hc, fun hn hb => ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h4 := div_ok hd h16 hs M.ι 1 u b (by simpa using hb) (hc.trans (pow_le _ _ (by omega)))
  have e3 : ((u : ℂ) + (b : ℂ) * wK d) / (q : ℂ) ^ 1 = ((q ^ m : ℕ) : ℂ) * p := by
    rw [hpe, Nat.succ_eq_add_one]; push_cast; field_simp; ring
  rw [e3, ← kill] at h4
  have h5 := huq _ _ _ (at_pow M h hp (q ^ m)) h4
  rw [← map_pow, ← map_one M.ι] at h5
  have h6 := (rt_prim (q := q) (m + 1)).dvd_of_pow_eq_one _ (M.ι.injective h5)
  have := (Nat.pow_dvd_pow_iff_le_right hq.out.one_lt).1 h6
  omega

end

theorem exists_normalised_chart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → ∃ a : ℤ_[q], ‖a‖ = 1 ∧ M.MChart (ω * zc a) ∧ ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At (ω * zc a) (M.ι (kap1 d 1 y)) y := by
  intro d q hq M ω hd h16 hs hL h
  choose u b hat hc hb using gen hd h16 hs M hL h
  obtain ⟨-, -, -, hlat, -⟩ := GlobalTheory.T.smallPoint_multiplicativeCoordinate_existsUnique q M ω h
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hdv : ∀ n, (q : ℤ) ^ n ∣ b (n + 1) - b n := fun n => by
    have h1 := at_pow M h (hat (n + 1)) q
    rw [← map_pow, rt_succ] at h1
    obtain ⟨s, t, hst⟩ := (hL _).1 ((hlat _ _ _ h1).1 (hat n))
    have : ((u (n + 1) - u n : ℤ) : ℂ) + ((b (n + 1) - b n : ℤ) : ℂ) * wK d =
        (((q : ℤ) ^ n * s : ℤ) : ℂ) + (((q : ℤ) ^ n * t : ℤ) : ℂ) * wK d := by
      push_cast
      have e : (q : ℂ) ^ n * s + (q : ℂ) ^ n * t * wK d = (q : ℂ) ^ n * ((s : ℂ) + t * wK d) := by ring
      rw [e, ← hst]
      field_simp
      ring
    exact ⟨t, (OKArith.coord_unique hd.pos this).2⟩
  set β : ℤ_[q] := PadicInt.ofIntSeq _ (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub b q hdv) with hβ
  have hβn : ∀ n, PadicInt.toZModPow n β = b n :=
    PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub b q hdv
  have hβu : IsUnit β := by
    by_contra hu
    have h1 : ‖β‖ < 1 := PadicInt.not_isUnit_iff.1 hu
    rw [PadicInt.norm_lt_one_iff_dvd] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 := hβn 1
    rw [hc, map_mul, map_natCast] at h2
    have h3 : ((q : ℕ) : ZMod (q ^ 1)) = 0 := by rw [ZMod.natCast_eq_zero_iff]; simp
    rw [h3, zero_mul, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
    exact hb 1 one_ne_zero (by simpa using h2)
  obtain ⟨a, ha⟩ := hβu.exists_left_inv
  have hna : ‖a‖ = 1 := PadicInt.isUnit_iff.1 (IsUnit.of_mul_eq_one _ ha)
  refine ⟨a, hna, mchart_scale M h hna, ?_⟩
  rintro n y ⟨v, ⟨s, t, rfl⟩, hv, rfl⟩
  rw [Nat.cast_one, one_mul, kap_eq hd.pos]
  have hqn : 0 < q ^ n := pow_pos hq.out.pos n
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = t % ((q ^ n : ℕ) : ℤ) :=
    ⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hqn.ne'))⟩
  have hrt : rt q n ^ t = rt q n ^ k := by
    have h0 : rt q n ≠ 0 := Complex.exp_ne_zero _
    conv_lhs => rw [← Int.emod_add_mul_ediv t ((q ^ n : ℕ) : ℤ), ← hk]
    rw [zpow_add₀ h0, zpow_mul, zpow_natCast, zpow_natCast, (rt_prim n).pow_eq_one, one_zpow, mul_one]
  have hξ : M.ι (rt q n ^ t) ^ (q ^ n) = 1 := by
    rw [hrt, ← map_pow, ← pow_mul, mul_comm, pow_mul, (rt_prim n).pow_eq_one, one_pow, map_one]
  refine ⟨hξ, at_scale M h (k := a.appr n) hξ ?_ ?_⟩
  · rw [PadicInt.norm_le_pow_iff_mem_span_pow]
    exact PadicInt.appr_spec n a
  · have h1 := at_pow M h (hat n) (k * a.appr n)
    rw [hrt, map_pow, ← pow_mul]
    refine (hlat _ _ _ h1).2 ((hL _).2 ?_)
    have hz : (q : ℤ) ^ n ∣ (k * a.appr n : ℕ) * b n - t := by
      have e1 : ((a.appr n : ℕ) : ZMod (q ^ n)) * (b n : ZMod (q ^ n)) = 1 := by
        rw [← hβn, show ((a.appr n : ℕ) : ZMod (q ^ n)) = PadicInt.toZModPow n a from rfl, ← map_mul, ha,
          map_one]
      have e2 : ((k : ℕ) : ZMod (q ^ n)) = (t : ZMod (q ^ n)) := by
        rw [← Int.cast_natCast, hk, ZMod.intCast_mod]
      have : ((((k * a.appr n : ℕ) : ℤ) * b n - t : ℤ) : ZMod (q ^ n)) = 0 := by
        push_cast
        rw [mul_assoc, e1, e2, mul_one, sub_self]
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
      exact_mod_cast this
    have h2 := div_ok hd h16 hs M.ι n ((k * a.appr n : ℕ) * u n - s) _ hz (by
      have e : conj (((((k * a.appr n : ℕ) : ℤ) * u n - s : ℤ) : ℂ) +
          ((((k * a.appr n : ℕ) : ℤ) * b n - t : ℤ) : ℂ) * wK d) =
          ((k * a.appr n : ℕ) : ℂ) * conj ((u n : ℂ) + (b n : ℂ) * wK d) +
            - conj ((s : ℂ) + (t : ℂ) * wK d) := by
        simp only [OKArith.conj_el]; push_cast; ring
      rw [e, map_add (f := _), map_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [map_mul, map_natCast, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)).trans (hc n)
      · rw [norm_neg]
        refine hv.trans ?_
        have := pow_le (q := q) n (2 * n) (by omega)
        simpa using this)
    convert h2 using 1
    push_cast
    ring

end GlobalTheory.MomOne.Norm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsNormalisedMultiplicativeChartStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalised_multiplicativeChart : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → ∃ a : ℤ_[q], ‖a‖ = 1 ∧ M.MChart (ω * zc a) ∧ ∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At (ω * zc a) (M.ι (kap1 d 1 y)) y := by
  first | exact @GlobalTheory.MomOne.Norm.exists_normalised_chart | exact GlobalTheory.MomOne.Norm.exists_normalised_chart | (intros; apply GlobalTheory.MomOne.Norm.exists_normalised_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsImagQuadOrderPairAndEvenTheta
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsImagQuadOrderPairAndEvenTheta
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section

namespace GlobalTheory.MomOne.ThetaZero

theorem indep {d : ℕ} (hd : 0 < d) : LinearIndependent ℝ ![(1 : ℂ), wK d] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have ht : t = 0 := by
    rcases him with h1 | h1
    · exact h1
    · exact absurd h1 (by positivity)
  subst ht
  simp at hre
  exact ⟨hre, rfl⟩

def pair {d : ℕ} (hd : 0 < d) : PeriodPair := ⟨1, wK d, indep hd⟩

theorem isOK_pair {d : ℕ} (hd : 0 < d) : IsOK d (pair hd) := by
  intro z
  rw [PeriodPair.mem_lattice]
  simp only [pair, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

theorem G_eq {d : ℕ} {L : PeriodPair} (h : IsOK d L) {k : ℕ} (hk : k ≠ 0) :
    L.G (2 * k) = eis d k := by
  unfold PeriodPair.G eis
  have e1 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  have e2 := tsum_subtype {w : ℂ | InOK d w ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  refine e1.trans (Eq.trans ?_ e2.symm)
  refine tsum_congr fun w => ?_
  by_cases h0 : w = 0
  · subst h0
    simp [Set.indicator, hk]
  · have hw : w ∈ (L.lattice : Set ℂ) ↔ w ∈ {w : ℂ | InOK d w ∧ w ≠ 0} :=
      ⟨fun a => ⟨(h w).1 a, h0⟩, fun a => (h w).2 a.1⟩
    by_cases hm : w ∈ (L.lattice : Set ℂ)
    · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hw.1 hm), one_div]
    · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (hw.not.1 hm)]

def lam (d : ℕ) : AddSubgroup ℂ := AddSubgroup.closure {1, wK d}

theorem mem_lam (d : ℕ) (z : ℂ) : z ∈ lam d ↔ InOK d z := by
  rw [lam, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul, mul_one, InOK]
  exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

theorem area_lam {d : ℕ} (hd : 0 < d) : Formalism.MainNotions.TaylorLogMetric.area (lam d) = Real.sqrt d / 2 := by
  rw [lam, GlobalTheory.TransInv.area_closure_pair (indep hd)]
  simp [wK, abs_div]

theorem thetaTranslationOperator_apply {d : ℕ} (hd : 0 < d) (x : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    Formalism.MainNotions.TaylorLogMetric.U1 (lam d) x F z = U1 d x F z := by
  simp only [Formalism.MainNotions.TaylorLogMetric.U1, U1, h1, area_lam hd]
  congr 2
  push_cast
  ring

theorem thetaTranslation_comp_eq_cocycle_mul (d : ℕ) (a b : ℂ) (F : ℂ → ℂ) (z : ℂ) :
    U1 d a (U1 d b F) z =
      Complex.exp ((Real.pi : ℂ) / 2 * (h1 d b a - h1 d a b)) * U1 d (a + b) F z := by
  simp only [U1]
  rw [mul_assoc, ← Complex.exp_add, mul_left_comm, ← Complex.exp_add, add_assoc z a b]
  congr 2
  simp only [h1, map_add (f := _)]
  ring

theorem half_not_mem {d : ℕ} (hd : 0 < d) (u v : ℤ) (h : ¬ (Odd u ∧ Even v)) :
    ((u : ℂ) + (v : ℂ) * wK d) / 2 + 1 / 2 ∉ lam d := by
  rw [mem_lam]
  rintro ⟨m, n, e⟩
  have := (LinearIndependent.pair_iff.1 (indep hd)) ((u + 1 - 2 * m : ℤ) : ℝ) ((v - 2 * n : ℤ) : ℝ) (by
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * e)
  have h1 : u + 1 - 2 * m = 0 := by exact_mod_cast this.1
  have h2 : v - 2 * n = 0 := by exact_mod_cast this.2
  exact h ⟨⟨m - 1, by omega⟩, ⟨n, by omega⟩⟩

theorem normSq_eq {d : ℕ} (c : ℤ) (hc : (d : ℤ) + 1 = 8 * c) (u v : ℤ) :
    Complex.normSq ((u : ℂ) + (v : ℂ) * wK d) = ((u ^ 2 + u * v + 2 * c * v ^ 2 : ℤ) : ℝ) := by
  have hs : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (Nat.cast_nonneg d)
  have hc' : (d : ℝ) + 1 = 8 * c := by exact_mod_cast hc
  simp [Complex.normSq_apply, wK]
  linear_combination (v : ℝ) ^ 2 / 4 * hs + (v : ℝ) ^ 2 / 4 * hc'

theorem exp_even {n : ℤ} (h : Even n) : Complex.exp ((Real.pi : ℂ) * Complex.I * (n : ℂ)) = 1 := by
  obtain ⟨k, rfl⟩ := h
  rw [← Complex.exp_int_mul_two_pi_mul_I k]
  congr 1
  push_cast
  ring

theorem comm_eq {d : ℕ} (hd : 0 < d) (u v : ℤ) :
    h1 d (wK d) ((u : ℂ) + (v : ℂ) * wK d) - h1 d ((u : ℂ) + (v : ℂ) * wK d) (wK d) =
      2 * u * Complex.I := by
  have hs : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  simp only [h1, wK, map_add (f := _), map_mul, map_div₀, map_intCast, map_one, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  push_cast
  field_simp
  ring

theorem exists_isTh {d : ℕ} (hd8 : d % 8 = 7) : ∃ θ : ℂ → ℂ, IsTh d θ := by
  have hd : 0 < d := by omega
  obtain ⟨c, hc⟩ : ∃ c : ℤ, (d : ℤ) + 1 = 8 * c := ⟨((d : ℤ) + 1) / 8, by omega⟩
  have hlat : GlobalTheory.EvenTheta.IsLat (lam d) := ⟨1, wK d, indep hd, rfl⟩
  have ht : (1 / 2 : ℂ) ∉ lam d := by
    simpa using half_not_mem hd 0 0 (by simp)
  have ht2 : 2 * (1 / 2 : ℂ) ∈ lam d := (mem_lam d _).2 ⟨1, 0, by simp⟩
  obtain ⟨b1, b2, b3, -, b5, b6⟩ := GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties (lam d) hlat (1 / 2) ht ht2
  generalize Formalism.MainNotions.GL3Theta.th0 (lam d) (1 / 2) = θ at b1 b2 b3 b5 b6
  have fix : ∀ u v : ℤ, ¬ (Odd u ∧ Even v) → U1 d ((u : ℂ) + (v : ℂ) * wK d) θ = θ := by
    intro u v h
    funext z
    rw [← thetaTranslationOperator_apply hd]
    exact b6 _ ((mem_lam d _).2 ⟨u, v, rfl⟩) (half_not_mem hd u v h) z
  refine ⟨θ, b1, b2, b3, ?_, fun z hz => ?_⟩
  · rintro x ⟨u, v, rfl⟩
    funext z
    simp only [W1]
    rw [normSq_eq c hc, Complex.ofReal_intCast]
    by_cases h : Odd u ∧ Even v
    · have f1 := fix u (v - 1) (by
        rintro ⟨-, h2⟩
        rcases h2 with ⟨a, ha⟩
        rcases h.2 with ⟨b, hb⟩
        omega)
      have f2 : U1 d (wK d) θ = θ := by simpa using fix 0 1 (by simp)
      have k := thetaTranslation_comp_eq_cocycle_mul d ((u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d) (wK d) θ z
      rw [f2, f1, comm_eq hd,
        show (u : ℂ) + ((v - 1 : ℤ) : ℂ) * wK d + wK d = (u : ℂ) + (v : ℂ) * wK d by
          push_cast; ring] at k
      have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2 - u) := by
        obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
        exact ⟨(2 * a + 1) * a + (2 * a + 1) * b + c * (b + b) ^ 2, by ring⟩
      have e := exp_even hev
      rw [k]
      congr 1
      rw [← one_mul (Complex.exp ((Real.pi : ℂ) / 2 * _)), ← e, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    · have hev : Even (u ^ 2 + u * v + 2 * c * v ^ 2) := by
        rcases Int.even_or_odd u with ⟨a, rfl⟩ | ⟨a, rfl⟩
        · exact ⟨2 * a ^ 2 + a * v + c * v ^ 2, by ring⟩
        · rcases Int.even_or_odd v with hv | ⟨b, rfl⟩
          · exact absurd ⟨⟨a, rfl⟩, hv⟩ h
          · exact ⟨(2 * a + 1) * (a + b + 1) + c * (2 * b + 1) ^ 2, by ring⟩
      rw [exp_even hev, one_mul, fix u v h]
  · obtain ⟨m, n, e⟩ := (mem_lam d _).1 ((b5 z).1 hz)
    exact ⟨m - 1, n, by push_cast; linear_combination e⟩

end GlobalTheory.MomOne.ThetaZero

namespace GlobalTheory.MomOne

theorem exists_pair_and_isTh : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  intro d hp h
  refine ⟨⟨ThetaZero.pair hp.pos, ThetaZero.isOK_pair hp.pos, ?_⟩, ThetaZero.exists_isTh (by omega)⟩
  have h2 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 2) (by norm_num)
  have h3 := ThetaZero.G_eq (ThetaZero.isOK_pair hp.pos) (k := 3) (by norm_num)
  unfold discr PeriodPair.g₂ PeriodPair.g₃
  rw [← h2, ← h3]

end GlobalTheory.MomOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsImagQuadOrderPairAndEvenThetaStatement
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  first | exact @GlobalTheory.MomOne.exists_pair_and_isTh | exact GlobalTheory.MomOne.exists_pair_and_isTh | (intros; apply GlobalTheory.MomOne.exists_pair_and_isTh <;> assumption)
end
end

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.GenusOne

variable {q : ℕ} [Fact q.Prime]

theorem norm_root_eq (M : Mdl q) (h : M.Ok) (δ : ℂ) (hδ : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2) :
    ‖M.ι δ‖ = ‖M.ι M.c‖ ∧ ‖M.ι M.c‖ ≠ 0 := by
  obtain ⟨hc, -, -, -, -, -, hΔ, h4, h6⟩ := h
  have hιc : M.ι M.c ≠ 0 := (map_ne_zero M.ι).mpr hc
  refine ⟨?_, norm_ne_zero_iff.mpr hιc⟩

  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 4 hιc)] at h4
  rw [map_div₀, map_pow, eq_div_iff (pow_ne_zero 6 hιc)] at h6
  have key : M.ι δ ^ 12 = M.ι M.c ^ 12 * M.W.Δ := by
    have e : M.ι δ ^ 12 = M.ι M.L.g₂ ^ 3 - 27 * M.ι M.L.g₃ ^ 2 := by
      rw [← map_pow, hδ]; simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e, ← h4, ← h6]
    linear_combination (-(M.ι M.c ^ 12) / 1728) * M.W.c_relation
  have hn := congrArg norm key
  rw [norm_mul, norm_pow, norm_pow, hΔ, mul_one] at hn
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp hn

theorem norm_period (M : Mdl q) (ω : ℂ_[q]) (h : M.MChart ω) : ‖ω‖ * ‖M.ι M.c‖ = 1 := by
  obtain ⟨hok, h0, -, h1⟩ := h
  obtain ⟨-, -, -, -, -, -, hdu, -, hsmall⟩ := uw_elliptic_flow q M hok
  obtain ⟨han, -⟩ := hsmall 0 (Or.inl (zero_mem _))
  obtain ⟨-, -, -, hcc, hder, -, -⟩ := TaylorRead.hat_laws q M.ι (C ω * logS) h0

  have hd0 : ∀ f : ℂ_[q]⟦X⟧, constantCoeff (PowerSeries.derivative f) = coeff 1 f := by
    intro f
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_derivative]
    simp
  have hℓ : coeff 1 (C ω * logS : ℂ_[q]⟦X⟧) = ω := by
    simp [logS, coeff_C_mul, coeff_mk]
  have e : coeff 1 (hat M.ι (C ω * logS) M.u) = ω * M.ι M.c := by
    rw [← hd0, hder M.u han, map_mul, hd0, hℓ, hcc, hdu]
  rw [e, norm_mul] at h1
  exact h1

theorem thetaLaws_unit_period : ∀ (d q : ℕ) [Fact q.Prime] (δ : ℂ), d.Prime → d % 16 = 7 → Split d q →
    δ ^ 12 = discr d → ∃ θ : ℂ → ℂ, IsTh d θ ∧ δ ≠ 0 ∧
      ∀ ι : ℂ ≃+* ℂ_[q], ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ := by
  intro d q _ δ hd h16 hsp hδ
  obtain ⟨⟨L, hL, hLd⟩, θ, hθ⟩ := GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta d hd h16
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    exact (Basic.discr_eq hL).2 (by rw [← hδ]; norm_num)
  refine ⟨θ, hθ, hδ0, fun ι => ?_⟩
  obtain ⟨M, hMι, hML, hok, a1, a2, a3, a4, a6⟩ := GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model d q ι L hd h16 hL
  subst hMι
  have hL' : IsOK d M.L := by rw [hML]; exact hL
  obtain ⟨ω₀, hω₀⟩ := GlobalTheory.T.exists_multiplicativeChart_at_splitPrime d q M hd h16 hsp hL' hok a1 a2 a3 a4 a6
  obtain ⟨a, -, hω, hgood⟩ := GlobalTheory.T.exists_normalised_multiplicativeChart d q M ω₀ hd h16 hsp hL' hω₀
  have hδM : δ ^ 12 = M.L.g₂ ^ 3 - 27 * M.L.g₃ ^ 2 := by rw [hML, hLd]; exact hδ
  obtain ⟨hn, -⟩ := norm_root_eq M hok δ hδM
  have hp := norm_period M (ω₀ * zc a) hω
  have hιδ : M.ι δ ≠ 0 := (map_ne_zero M.ι).mpr hδ0
  refine ⟨ω₀ * zc a * M.ι δ, by rw [norm_mul, hn]; exact hp, ?_⟩
  rw [mul_div_cancel_right₀ _ hιδ]
  have hU0 : U1 d 0 θ = θ := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.1 θ
  have h0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left q, 0, 0, by simp⟩
  have hB := GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ
  refine ⟨fun t ht => ?_, GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ hgood,
    GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ⟩

  have := GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M (ω₀ * zc a) θ hd h16 hsp hL' hω hθ 1 1 (fun _ => 1) (fun _ => 0) t 1
    (fun _ => h0) ht (by simpa [hU0] using hB)
  simpa [hU0] using this

end GlobalTheory.MomOne.GenusOne
end

open PowerSeries GlobalTheory.MomOne GlobalTheory.MomN
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomN.PeriodData

variable {q : ℕ} [Fact q.Prime]

theorem laws_and_chart (d : ℕ) (ι : ℂ ≃+* ℂ_[q]) (δ : ℂ) (θ : ℂ → ℂ) (L : PeriodPair)
    (hd : d.Prime) (h7 : d % 16 = 7) (hs : Split d q) (hL : IsOK d L)
    (hD : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) (hδ : δ ^ 12 = discr d) (hδ0 : δ ≠ 0) (hθ : IsTh d θ) :
    ∃ Ω : ℂ_[q], ‖Ω‖ = 1 ∧ ThetaLaws ι d (Ω / ι δ) θ ∧
      ∃ M : Mdl q, M.ι = ι ∧ IsOK d M.L ∧ M.MChart (Ω / ι δ) := by
  obtain ⟨M, rfl, rfl, hok, a1, a2, a3, a4, a6⟩ := GlobalTheory.T.exists_goodReduction_algebraic_weierstrass_model d q ι L hd h7 hL
  obtain ⟨ω₀, hω₀⟩ := GlobalTheory.T.exists_multiplicativeChart_at_splitPrime d q M hd h7 hs hL hok a1 a2 a3 a4 a6
  obtain ⟨a, -, hω, hn⟩ := GlobalTheory.T.exists_normalised_multiplicativeChart d q M ω₀ hd h7 hs hL hω₀
  set ω := ω₀ * zc a
  have hι : M.ι δ ≠ 0 := by simpa using hδ0
  refine ⟨ω * M.ι δ, ?_, ?_, M, rfl, hL, ?_⟩
  · rw [norm_mul, (GenusOne.norm_root_eq M hok δ (hδ.trans hD.symm)).1, GenusOne.norm_period M ω hω]
  · rw [mul_div_cancel_right₀ _ hι]
    have hN := GlobalTheory.T.norm_translate_powerComb_le_coprimeTranslation d q M ω θ hd h7 hs hL hω hθ
    refine ⟨fun t ht => ?_, GlobalTheory.T.weilOperator_theta_translate_shift_prime_to_q d q M ω θ hd h7 hs hL hω hθ hn, hN⟩
    have hU := (GlobalTheory.T.cmLattice_heisenberg_relations_one_variable d hd.pos).2.1
    have h0 : PrimeTo d q 0 := ⟨1, one_pos, Nat.coprime_one_left _, 0, 0, by simp⟩
    have := hN 1 1 (fun _ => 1) (fun _ => 0) t 1 (fun _ => h0) ht
      (by simpa [hU] using GlobalTheory.T.cm_even_theta_series_chart_coeff_integral d q M ω θ hd h7 hs hL hω hθ)
    simpa [hU] using this
  · rw [mul_div_cancel_right₀ _ hι]; exact hω

end GlobalTheory.MomN.PeriodData

namespace GlobalTheory.MomN

theorem exists_per : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]), d.Prime → d % 16 = 7 → Split d q →
    ∃ (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per d ι δ₀ θ Ω := by
  intro d q _ ι hd h7 hs
  obtain ⟨δ₀, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (discr d) (by norm_num : 0 < 12)
  obtain ⟨⟨L, hL, hD⟩, θ, hθ⟩ := GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta d hd h7
  have hδ0 : δ₀ ≠ 0 := (GenusOne.thetaLaws_unit_period d q δ₀ hd h7 hs hδ).choose_spec.2.1
  obtain ⟨Ω, hΩ, hT, hM⟩ := PeriodData.laws_and_chart d ι δ₀ θ L hd h7 hs hL hD hδ hδ0 hθ
  refine ⟨δ₀, θ, Ω, hθ, hδ, hδ0, fun ι' => ?_, hΩ, hT, hM⟩
  obtain ⟨Ω', h1, h2, -⟩ := PeriodData.laws_and_chart d ι' δ₀ θ L hd h7 hs hL hD hδ hδ0 hθ
  exact ⟨Ω', h1, h2⟩

end GlobalTheory.MomN
