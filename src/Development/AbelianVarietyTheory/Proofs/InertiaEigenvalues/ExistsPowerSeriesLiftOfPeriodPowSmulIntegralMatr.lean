module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralWittElementOfEvaluation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralWittElementOfEvaluation
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.HeightSInt
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem smod_iff {R : Type} [CommRing R] (p x y : R) (n : ℕ) :
    x ≡ y [SMOD (Ideal.span {p} ^ n • ⊤ : Submodule R R)] ↔ p ^ n ∣ x - y := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem l_ne_zero_WCb : ((l : ℕ) : WCb l) ≠ 0 := by
  intro h
  have := congrArg (fun x : WCb l => x.coeff 1) h
  simp only [WittVector.coeff_p_one, WittVector.zero_coeff] at this
  exact one_ne_zero this

theorem l_mul_cancel {x y : WCb l} (h : (l : WCb l) * x = (l : WCb l) * y) : x = y :=
  mul_left_cancel₀ l_ne_zero_WCb h

theorem dvd_iff_coeff {a : ℕ} [NeZero a] (w : Wq l a) : (l : Wq l a) ∣ w ↔ w.coeff 0 = 0 := by
  rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, WittVector.constantCoeff_apply]

theorem dec {a : ℕ} [NeZero a] (s : (Wq l a)⟦X⟧) :
    (∃ s', s = (l : (Wq l a)⟦X⟧) * s') ∨
      ∃ (j : ℕ) (t s' : (Wq l a)⟦X⟧), IsUnit t ∧ s = X ^ j * t + (l : (Wq l a)⟦X⟧) * s' := by
  classical
  have hl' : ((l : (Wq l a)⟦X⟧)) = C (l : Wq l a) := (map_natCast C l).symm
  by_cases h : ∀ k, (l : Wq l a) ∣ coeff k s
  · left
    choose d hd using h
    refine ⟨mk d, ?_⟩
    ext k
    rw [hl', coeff_C_mul, coeff_mk, ← hd]
  · right
    push_neg at h
    let j := Nat.find h
    have hj : ¬ (l : Wq l a) ∣ coeff j s := Nat.find_spec h
    have hlt : ∀ i < j, (l : Wq l a) ∣ coeff i s := fun i hi => by
      have := Nat.find_min h hi
      simpa using this
    let d : ℕ → Wq l a := fun i => if hd : (l : Wq l a) ∣ coeff i s then hd.choose else 0
    refine ⟨j, mk fun i => coeff (i + j) s, mk fun i => if i < j then d i else 0, ?_, ?_⟩
    · rw [isUnit_iff_constantCoeff, ← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add]
      exact WittVector.isUnit_of_coeff_zero_ne_zero _ (fun h0 => hj ((dvd_iff_coeff _).2 h0))
    · refine PowerSeries.ext fun k => ?_
      rw [map_add (f := _), coeff_X_pow_mul', hl', coeff_C_mul]
      simp only [coeff_mk]
      by_cases hk : j ≤ k
      · rw [if_pos hk, if_neg (not_lt.2 hk), mul_zero, add_zero, Nat.sub_add_cancel hk]
      · have hk' : k < j := not_le.1 hk
        rw [if_neg hk, if_pos hk', zero_add]
        have hdk : (l : Wq l a) ∣ coeff k s := hlt k hk'
        simp only [d, dif_pos hdk]
        exact hdk.choose_spec

variable (bk : BK K)

def e0 : bk.S →+* OCb l := WittVector.constantCoeff.comp bk.ev

theorem reduction_X_eq_flat : e0 bk X = bk.flat := by
  simp [e0, bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]

theorem reduction_l_mul_eq_zero (s : bk.S) : e0 bk ((l : bk.S) * s) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

theorem reduction_decomposition (s : bk.S) : (∃ s', s = (l : bk.S) * s') ∨ ∃ (j : ℕ) (t : bk.S), IsUnit (e0 bk t) ∧
    ∃ s' : bk.S, s = X ^ j * t + (l : bk.S) * s' ∧ e0 bk s = bk.flat ^ j * e0 bk t := by
  rcases dec s with h | ⟨j, t, s', ht, h⟩
  · exact Or.inl h
  · refine Or.inr ⟨j, t, ht.map _, s', h, ?_⟩
    rw [h, map_add (f := _), reduction_l_mul_eq_zero, add_zero, map_mul, map_pow, reduction_X_eq_flat]

theorem dvd_of_reduction_eq_zero {s : bk.S} (h : e0 bk s = 0) : ∃ s', s = (l : bk.S) * s' := by
  rcases reduction_decomposition bk s with h' | ⟨j, t, ht, s', -, he⟩
  · exact h'
  · rw [he] at h
    exact absurd h (mul_ne_zero (pow_ne_zero _ (FlatDisc.flat_ne_zero bk)) ht.ne_zero)

theorem exists_reduction_of_flat_pow {m : ℕ} {x : OCb l} {s : bk.S} (h : bk.flat ^ m * x = e0 bk s) : ∃ s₀ : bk.S, x = e0 bk s₀ := by
  have hf := FlatDisc.flat_ne_zero bk
  rcases reduction_decomposition bk s with ⟨s', rfl⟩ | ⟨j, t, ht, s', -, he⟩
  · rw [reduction_l_mul_eq_zero] at h
    exact ⟨0, by rw [map_zero]; exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ hf)⟩
  · rw [he] at h
    by_cases hmj : m ≤ j
    · refine ⟨X ^ (j - m) * t, ?_⟩
      rw [map_mul, map_pow, reduction_X_eq_flat]
      refine mul_left_cancel₀ (pow_ne_zero m hf) ?_
      rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hmj]
    · exfalso
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt (not_le.1 hmj)
      have h2 : bk.flat ^ (k + 1) * x = e0 bk t := by
        refine mul_left_cancel₀ (pow_ne_zero j hf) ?_
        rw [← h, ← mul_assoc, ← pow_add]; ring_nf
      rw [← h2, pow_succ, mul_assoc, mul_comm, mul_assoc] at ht
      exact FlatDisc.not_isUnit_flat bk (isUnit_of_mul_isUnit_left ht)

theorem cc_evW (s : bk.S) : WittVector.constantCoeff (bk.evW s) = algebraMap (OCb l) (Cb l) (e0 bk s) := by
  simp [BK.evW, e0, inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem cc_inclW (a : Ainf l) : WittVector.constantCoeff (inclW l a) = algebraMap (OCb l) (Cb l) (a.coeff 0) := by
  simp [inclW, WittVector.constantCoeff_apply, WittVector.map_coeff]

theorem cc_l_mul (y : WCb l) : WittVector.constantCoeff ((l : WCb l) * y) = 0 := by
  rw [map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]

end GlobalTheory.BSP.HeightSInt

namespace GlobalTheory.BSP.HeightSInt
variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K)

theorem evW_mem (s : bk.S) : bk.evW s ∈ bk.OE := fun _ => ⟨0, s, 0, by simp⟩

theorem mem_of_l_mul_mem {v : WCb l} (h : (l : WCb l) * v ∈ bk.OE) : v ∈ bk.OE := by
  intro n
  obtain ⟨m, s, y, hs⟩ := h (n + 1)
  have h0 : e0 bk s = 0 := by
    have := congrArg WittVector.constantCoeff hs
    rw [map_add (f := _), pow_succ', mul_assoc, cc_l_mul, add_zero, cc_evW, mul_left_comm, cc_l_mul] at this
    exact (IsFractionRing.injective (OCb l) (Cb l)) (by rw [← this, map_zero])
  obtain ⟨s', rfl⟩ := dvd_of_reduction_eq_zero bk h0
  refine ⟨m, s', y, l_mul_cancel ?_⟩
  rw [map_mul, map_natCast] at hs
  rw [mul_add, mul_left_comm, hs]; ring

theorem step {a : Ainf l} (h : inclW l a ∈ bk.OE) :
    ∃ (s₀ : bk.S) (a₁ : Ainf l), a = bk.ev s₀ + (l : Ainf l) * a₁ ∧ inclW l a₁ ∈ bk.OE := by
  obtain ⟨m, s, y, hs⟩ := h 1
  have h1 : bk.flat ^ m * a.coeff 0 = e0 bk s := by
    have := congrArg WittVector.constantCoeff hs
    rw [map_add (f := _), pow_one, cc_l_mul, add_zero, cc_evW, map_mul, map_pow, cc_evW, cc_inclW, reduction_X_eq_flat, ← map_pow,
      ← map_mul] at this
    exact IsFractionRing.injective (OCb l) (Cb l) this
  obtain ⟨s₀, hs₀⟩ := exists_reduction_of_flat_pow bk h1
  have h2 : a - bk.ev s₀ ∈ Ideal.span {(l : Ainf l)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, WittVector.constantCoeff_apply,
      WittVector.constantCoeff_apply, hs₀]
    simp [e0, WittVector.constantCoeff_apply]
  obtain ⟨a₁, ha₁⟩ := Ideal.mem_span_singleton.1 h2
  refine ⟨s₀, a₁, by rw [← ha₁]; ring, mem_of_l_mul_mem bk ?_⟩
  have : (l : WCb l) * inclW l a₁ = inclW l a - bk.evW s₀ := by
    rw [BK.evW, RingHom.comp_apply, ← map_sub, ha₁, map_mul, map_natCast]
  rw [this]
  exact sub_mem h (evW_mem bk s₀)

theorem exists_lim {a : ℕ} [NeZero a] (T : ℕ → (Wq l a)⟦X⟧)
    (hT : ∀ n, (l : (Wq l a)⟦X⟧) ^ n ∣ T (n + 1) - T n) :
    ∃ s : (Wq l a)⟦X⟧, ∀ n, (l : (Wq l a)⟦X⟧) ^ n ∣ T n - s := by
  classical
  have hl' : ∀ n, ((l : (Wq l a)⟦X⟧)) ^ n = C ((l : Wq l a) ^ n) := fun n => by
    rw [map_pow, map_natCast]
  have hmn : ∀ m k, (l : (Wq l a)⟦X⟧) ^ m ∣ T (m + k) - T m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have : T (m + (k + 1)) - T m = (T (m + k + 1) - T (m + k)) + (T (m + k) - T m) := by
        rw [← add_assoc]; ring
      rw [this]
      exact dvd_add ((pow_dvd_pow _ (Nat.le_add_right m k)).trans (hT (m + k))) ih
  have hc : ∀ i, ∃ L : Wq l a, ∀ n, (l : Wq l a) ^ n ∣ coeff i (T n) - L := by
    intro i
    have hpc : IsPrecomplete (Ideal.span {(l : Wq l a)}) (Wq l a) := inferInstance
    obtain ⟨L, hL⟩ := hpc.prec (f := fun n => coeff i (T n)) (fun {m n} hmn' => by
      rw [smod_iff]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn'
      obtain ⟨q, hq⟩ := hmn m k
      refine ⟨-coeff i q, ?_⟩
      have : T m - T (m + k) = -(T (m + k) - T m) := by ring
      rw [← map_sub, this, hq, hl', map_neg, coeff_C_mul]; ring)
    exact ⟨L, fun n => (smod_iff _ _ _ _).1 (hL n)⟩
  choose L hL using hc
  refine ⟨mk L, fun n => ?_⟩
  choose q hq using fun i => hL i n
  refine ⟨mk fun i => q i, PowerSeries.ext fun i => ?_⟩
  rw [map_sub, coeff_mk, hl', coeff_C_mul, coeff_mk, hq]

theorem main (w : WCb l) (hw : w ∈ bk.OE) (a : Ainf l) (ha : w = inclW l a) : ∃ s : bk.S, a = bk.ev s := by
  classical
  subst ha
  let P : Type := {a : Ainf l // inclW l a ∈ bk.OE}
  have hs : ∀ b : P, ∃ (s₀ : bk.S) (b₁ : P), b.1 = bk.ev s₀ + (l : Ainf l) * b₁.1 := fun b => by
    obtain ⟨s₀, a₁, h, h'⟩ := step bk b.2
    exact ⟨s₀, ⟨a₁, h'⟩, h⟩
  choose σ nx hσ using hs
  let A : ℕ → P := fun n => nx^[n] ⟨a, hw⟩
  have hA : ∀ n, A (n + 1) = nx (A n) := fun n => Function.iterate_succ_apply' nx n _
  let T : ℕ → bk.S := fun n => ∑ i ∈ Finset.range n, (l : bk.S) ^ i * σ (A i)
  have hTa : ∀ n, a = bk.ev (T n) + (l : Ainf l) ^ n * (A n).1 := by
    intro n
    induction n with
    | zero => simp [T, A]
    | succ n ih =>
      rw [ih, hσ (A n), ← hA n]
      simp only [T, Finset.sum_range_succ, map_add (f := _), map_mul, map_pow, map_natCast]
      ring
  obtain ⟨s, hs⟩ := exists_lim T (fun n => ⟨σ (A n), by simp [T, Finset.sum_range_succ]⟩)
  refine ⟨s, ?_⟩
  rw [← sub_eq_zero]
  refine (IsHausdorff.eq_iff_smodEq (I := Ideal.span {(l : Ainf l)})).2 fun n => (smod_iff _ _ _ _).2 ?_
  obtain ⟨q, hq⟩ := hs n
  have : T n = s + (l : bk.S) ^ n * q := by rw [← hq]; ring
  refine ⟨bk.ev q + (A n).1, ?_⟩
  rw [sub_zero]
  conv_lhs => rw [hTa n]
  rw [this, map_add (f := _), map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.BSP.HeightSInt

theorem GlobalTheory.BSP.ainf_inter_OE : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ w ∈ bk.OE, ∀ a : Ainf l,
    w = inclW l a → ∃ s : bk.S, a = bk.ev s :=
  fun _ _ _ bk w hw a ha => HeightSInt.main bk w hw a ha
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralWittElementOfEvaluationStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_witt_element_of_evaluation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ w ∈ bk.OE, ∀ a : Ainf l, w = inclW l a → ∃ s : bk.S, a = bk.ev s := by
  first | exact @GlobalTheory.BSP.ainf_inter_OE | exact GlobalTheory.BSP.ainf_inter_OE | (intros; apply GlobalTheory.BSP.ainf_inter_OE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatr
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.KisinFF

theorem exists_of_inclW_eq_pow_mul {l : ℕ} [Fact l.Prime] (n : ℕ) : ∀ (a : Ainf l) (w : WCb l),
    inclW l a = (l : WCb l) ^ n * w → ∃ a', a = (l : Ainf l) ^ n * a' ∧ inclW l a' = w := by
  induction n with
  | zero => intro a w h; exact ⟨a, by simp, by simpa using h⟩
  | succ n ih =>
    intro a w h
    obtain ⟨a₁, ha₁⟩ := GlobalTheory.HWL.TensorWitt.ainf_saturated_in_tiltWitt_prime a ((l : WCb l) ^ n * w) (by rw [h]; ring)
    obtain ⟨a', ha', hw'⟩ := ih a₁ w ha₁
    refine ⟨a', ?_, hw'⟩
    have h1 : a = (l : Ainf l) * a₁ := by
      apply GlobalTheory.HWL.TensorWitt.inclW_injective
      rw [map_mul, map_natCast, ha₁, h]; ring
    rw [h1, ha']; ring

theorem scalar {l : ℕ} [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (M : ℕ)
    (w : WCb l) (hw : w ∈ bk.OE) (a : Ainf l) (ha : inclW l a = inclW l τ ^ M * w) :
    ∃ s : bk.S, bk.evW s = w := by
  classical
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB M
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hr
  obtain ⟨v, -, hv⟩ := (GlobalTheory.T.integral_elements_unit_factorization l K bk).2.1
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : bk.S, s₀ = c.sum fun i μ => μ * TB.c i a := ⟨_, rfl⟩
  have hev : ∀ t : bk.S, inclW l (bk.ev t) = bk.evW t := fun t => rfl
  have key : ∀ n : ℕ, (l : WCb l) ^ n ∣ bk.evW s₀ - (l : WCb l) ^ r * w := by
    intro n
    obtain ⟨m, s, y, h⟩ := hw n
    have hz : inclW l (bk.ev X ^ m * a - τ ^ M * bk.ev s) = (l : WCb l) ^ n * (inclW l τ ^ M * y) := by
      rw [map_sub, map_mul, map_mul, map_pow, map_pow, hev, hev, ha]
      linear_combination (inclW l τ ^ M) * h
    obtain ⟨z', hz', -⟩ := exists_of_inclW_eq_pow_mul n _ _ hz
    have hci : ∀ i, X ^ m * TB.c i a - s * TB.c i (τ ^ M) = (l : bk.S) ^ n * TB.c i z' := by
      intro i
      have := congrArg (TB.c i) hz'
      rw [map_sub, show bk.ev X ^ m = bk.ev (X ^ m) from (map_pow _ _ _).symm, TB.c_mul, mul_comm (τ ^ M) (bk.ev s), TB.c_mul,
        show ((l : Ainf l) ^ n) = bk.ev ((l : bk.S) ^ n) by simp, TB.c_mul] at this
      exact this
    obtain ⟨t, ht⟩ : ∃ t : bk.S, t = c.sum fun i μ => μ * TB.c i z' := ⟨_, rfl⟩
    have hS : X ^ m * s₀ - s * (l : bk.S) ^ r = (l : bk.S) ^ n * t := by
      rw [← hc, hs₀, ht]
      simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul]
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by linear_combination c i * hci i
    have hW := congrArg bk.evW hS
    simp only [map_sub, map_mul, map_pow, map_natCast] at hW
    have hv' : bk.evW X ^ m * v ^ m = 1 := by rw [← mul_pow, hv, one_pow]
    refine ⟨v ^ m * (bk.evW t - (l : WCb l) ^ r * y), ?_⟩
    linear_combination v ^ m * hW - (l : WCb l) ^ r * v ^ m * h - (bk.evW s₀ - (l : WCb l) ^ r * w) * hv'
  have hd : bk.evW s₀ - (l : WCb l) ^ r * w = 0 := by
    refine IsHausdorff.haus' (I := Ideal.span {(l : WCb l)}) _ fun n => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact key n
  obtain ⟨a', -, ha'⟩ := exists_of_inclW_eq_pow_mul r (bk.ev s₀) w (by rw [hev]; linear_combination hd)
  obtain ⟨s', hs'⟩ := GlobalTheory.T.integral_witt_element_of_evaluation l K bk w hw a' ha'.symm
  exact ⟨s', by rw [← hev, ← hs', ha']⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' M : ℕ) (X : Matrix (Fin d') (Fin d) (WCb l)) (x : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, X i j ∈ bk.OE) → x.map (inclW l) = inclW l τ ^ M • X → ∃ Y : Matrix (Fin d') (Fin d) bk.S, Y.map bk.evW = X := by
  intro l _ K bk τ hτ d d' M X x hX hx
  have he : ∀ i j, inclW l (x i j) = inclW l τ ^ M * X i j := fun i j => by
    have := congrFun (congrFun hx i) j
    simpa [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] using this
  choose Y hY using fun i j => scalar K bk τ hτ M (X i j) (hX i j) (x i j) (he i j)
  exact ⟨Y, Matrix.ext fun i j => hY i j⟩

end GlobalTheory.BSP.KisinFF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatrStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_powerSeries_lift_of_period_pow_smul_integral_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d d' M : ℕ) (X : Matrix (Fin d') (Fin d) (WCb l)) (x : Matrix (Fin d') (Fin d) (Ainf l)), (∀ i j, X i j ∈ bk.OE) → x.map (inclW l) = inclW l τ ^ M • X → ∃ Y : Matrix (Fin d') (Fin d) bk.S, Y.map bk.evW = X := by
  first | exact @GlobalTheory.BSP.KisinFF.main | exact GlobalTheory.BSP.KisinFF.main | (intros; apply GlobalTheory.BSP.KisinFF.main <;> assumption)
end
