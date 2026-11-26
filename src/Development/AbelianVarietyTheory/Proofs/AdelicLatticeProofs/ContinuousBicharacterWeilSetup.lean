module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExpSeriesContDiffAndHasDerivAt
open scoped ContDiff

namespace GlobalTheory

section ExpSeries

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {I : Type}

end ExpSeries

private lemma norm_smulRight_le_opNorm_mul_norm {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] (L : V →L[ℝ] ℂ) (w : E) :
    ‖L.smulRight w‖ ≤ ‖L‖ * ‖w‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖L h‖ * ‖w‖ ≤ ‖L‖ * ‖h‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right (L.le_opNorm h) (norm_nonneg _)
    _ = ‖L‖ * ‖w‖ * ‖h‖ := by ring

private lemma mul_exp_mul_le_exp_add_one_mul (r R : ℝ) :
    r * Real.exp (R * r) ≤ Real.exp ((R + 1) * r) := by
  calc r * Real.exp (R * r) ≤ Real.exp r * Real.exp (R * r) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp r]) (Real.exp_pos _).le
    _ = Real.exp ((R + 1) * r) := by rw [← Real.exp_add]; ring_nf

private lemma summable_norm_smulRight_mul_exp {V E I : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℂ E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (R : ℝ) :
    Summable fun i => ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖) := by
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hw (R + 1))
  calc ‖(m i).smulRight (w i)‖ * Real.exp (R * ‖m i‖)
      ≤ ‖m i‖ * ‖w i‖ * Real.exp (R * ‖m i‖) :=
        mul_le_mul_of_nonneg_right (norm_smulRight_le_opNorm_mul_norm _ _) (Real.exp_pos _).le
    _ = ‖w i‖ * (‖m i‖ * Real.exp (R * ‖m i‖)) := by ring
    _ ≤ ‖w i‖ * Real.exp ((R + 1) * ‖m i‖) :=
        mul_le_mul_of_nonneg_left (mul_exp_mul_le_exp_add_one_mul _ _) (norm_nonneg _)

private lemma norm_cexp_le_exp_mul_opNorm_of_norm_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℂ) {y : V} {r : ℝ} (hy : ‖y‖ ≤ r) :
    ‖Complex.exp (L y)‖ ≤ Real.exp (r * ‖L‖) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  calc (L y).re ≤ ‖L y‖ := Complex.re_le_norm _
    _ ≤ ‖L‖ * ‖y‖ := L.le_opNorm y
    _ ≤ r * ‖L‖ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_right hy (norm_nonneg _)

private lemma hasFDerivAt_tsum_cexp_smul_of_summable_exp {V E I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (m : I → V →L[ℝ] ℂ) (w : I → E)
    (hw : ∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) (x : V) :
    HasFDerivAt (fun v => ∑' i, Complex.exp (m i v) • w i)
      (∑' i, Complex.exp (m i x) • (m i).smulRight (w i)) x := by
  set r := ‖x‖ + 1
  have hx : x ∈ Metric.ball (0 : V) r := by rw [mem_ball_zero_iff]; simp [r]
  refine hasFDerivAt_tsum_of_isPreconnected (u := fun i => ‖(m i).smulRight (w i)‖ *
      Real.exp (r * ‖m i‖)) (f := fun i v => Complex.exp (m i v) • w i)
    (f' := fun i y => Complex.exp (m i y) • (m i).smulRight (w i))
    (summable_norm_smulRight_mul_exp m w hw r) Metric.isOpen_ball
    (convex_ball _ _).isPreconnected ?_ ?_ hx ?_ hx
  · intro i y _
    refine (((m i).hasFDerivAt.cexp).smul_const (w i)).congr_fderiv ?_
    ext h
    simp [smul_smul]
  · intro i y hy
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left
      (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by rw [mem_ball_zero_iff] at hy; exact hy.le)) (norm_nonneg _)
  · refine Summable.of_norm_bounded (hw r) fun i => ?_
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left (norm_cexp_le_exp_mul_opNorm_of_norm_le _ (by simp [r])) (norm_nonneg _)

private lemma contDiff_tsum_cexp_smul_of_summable_exp {V I : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (m : I → V →L[ℝ] ℂ) (n : ℕ) :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (w : I → E),
      (∀ R : ℝ, Summable fun i => ‖w i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ n (fun v => ∑' i, Complex.exp (m i v) • w i) := by
  induction n with
  | zero =>
    intro E _ _ _ w hw
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x).continuousAt)
  | succ n ih =>
    intro E _ _ _ w hw
    have hd := fun x => hasFDerivAt_tsum_cexp_smul_of_summable_exp m w hw x
    push_cast
    refine contDiff_succ_iff_fderiv.2 ⟨fun x => (hd x).differentiableAt, fun h => by simp at h, ?_⟩
    have hfd : fderiv ℝ (fun v => ∑' i, Complex.exp (m i v) • w i) =
        fun x => ∑' i, Complex.exp (m i x) • (m i).smulRight (w i) :=
      funext fun x => (hd x).fderiv
    rw [hfd]
    exact ih (V →L[ℝ] E) (fun i => (m i).smulRight (w i))
      (summable_norm_smulRight_mul_exp m w hw)

theorem _root_.GlobalTheory.expSeries_contDiff_and_hasDerivAt :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (I : Type) (c : I → ℂ)
      (m : I → V →L[ℝ] ℂ), (∀ R : ℝ, Summable fun i => ‖c i‖ * Real.exp (R * ‖m i‖)) →
      ContDiff ℝ ∞ (fun v : V => ∑' i, c i * Complex.exp (m i v)) ∧
        ∀ z : V, Summable (fun i => c i * m i z) ∧
          HasDerivAt (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z)))
            (∑' i, c i * m i z) 0 := by
  intro V _ _ I c m hc
  have hfun : (fun v : V => ∑' i, c i * Complex.exp (m i v)) =
      fun v => ∑' i, Complex.exp (m i v) • c i :=
    funext fun v => tsum_congr fun i => by rw [smul_eq_mul, mul_comm]
  have hz : ∀ z : V, Summable fun i => c i * m i z := by
    intro z
    refine Summable.of_norm_bounded ((hc 1).mul_left ‖z‖) fun i => ?_
    rw [norm_mul, one_mul]
    have h1 : 0 ≤ ‖c i‖ * ‖z‖ * (Real.exp ‖m i‖ - ‖m i‖) :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (by linarith [Real.add_one_le_exp ‖m i‖])
    have h2 : ‖c i‖ * ‖m i z‖ ≤ ‖c i‖ * (‖m i‖ * ‖z‖) :=
      mul_le_mul_of_nonneg_left ((m i).le_opNorm z) (norm_nonneg _)
    nlinarith
  refine ⟨?_, fun z => ⟨hz z, ?_⟩⟩
  · rw [hfun]
    exact contDiff_infty.2 fun n => contDiff_tsum_cexp_smul_of_summable_exp m n ℂ c hc
  · have hF := hasFDerivAt_tsum_cexp_smul_of_summable_exp m c hc (0 : V)
    have hl := (hasDerivAt_id (0 : ℝ)).smul_const z
    have h := hF.comp_hasDerivAt_of_eq (0 : ℝ) hl (zero_smul ℝ z).symm
    have hS : Summable fun i => (m i).smulRight (c i) := by
      refine Summable.of_norm ?_
      simpa using summable_norm_smulRight_mul_exp m c hc 0
    have hS' : Summable fun i => Complex.exp (m i 0) • (m i).smulRight (c i) := by
      simpa using hS
    have hfeq : (fun t : ℝ => ∑' i, c i * Complex.exp (m i (t • z))) =
        ((fun v => ∑' i, Complex.exp (m i v) • c i) ∘ fun y => id y • z) :=
      funext fun t => tsum_congr fun i => by simp [mul_comm]
    rw [hfeq]
    refine h.congr_deriv ?_
    have happ := (hS'.hasSum.mapL (ContinuousLinearMap.apply ℝ ℂ ((1 : ℝ) • z))).tsum_eq
    simp only [ContinuousLinearMap.apply_apply] at happ
    rw [← happ]
    exact tsum_congr fun i => by simp [mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CharSeriesExistsNeZero
open scoped ContDiff

namespace GlobalTheory

theorem charSeries_kill_finset {A I : Type} [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I)
    (hmul : ∀ i a b, e i (a + b) = e i a * e i b) (hle : ∀ i a, ‖e i a‖ ≤ 1)
    (h0 : ∀ a, e i₀ a = 1) (hneg : ∀ i, i ≠ i₀ → ∃ a, e i a = -1)
    (hs : Summable (fun i => ‖c i‖)) (hF : ∀ a, ∑' i, c i * e i a = 0) (s : Finset I) :
    ∃ c' : I → ℂ, c' i₀ = c i₀ ∧ (∀ i ∈ s, i ≠ i₀ → c' i = 0) ∧ (∀ i, ‖c' i‖ ≤ ‖c i‖) ∧
      ∀ a, ∑' i, c' i * e i a = 0 := by
  classical
  refine Finset.induction_on s ⟨c, rfl, by simp, fun i => le_rfl, hF⟩ ?_
  intro j s _ ih
  obtain ⟨c', h1, h2, h3, h4⟩ := ih
  by_cases hji : j = i₀
  · subst hji
    refine ⟨c', h1, ?_, h3, h4⟩
    intro i hi hne
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact absurd rfl hne
    · exact h2 i hi hne
  · obtain ⟨b, hb⟩ := hneg j hji
    refine ⟨fun i => c' i * (1 + e i b) / 2, ?_, ?_, ?_, ?_⟩
    · show c' i₀ * (1 + e i₀ b) / 2 = c i₀
      rw [h0 b, h1]; ring
    · intro i hi hne
      show c' i * (1 + e i b) / 2 = 0
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [hb]; ring
      · rw [h2 i hi hne]; ring
    · intro i
      show ‖c' i * (1 + e i b) / 2‖ ≤ ‖c i‖
      have h2b : ‖(1 : ℂ) + e i b‖ ≤ 2 :=
        (norm_add_le _ _).trans (by rw [norm_one]; linarith [hle i b])
      rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by simp]
      calc ‖c' i‖ * ‖1 + e i b‖ / 2 ≤ ‖c' i‖ * 2 / 2 := by gcongr
        _ = ‖c' i‖ := by ring
        _ ≤ ‖c i‖ := h3 i
    · intro a
      show ∑' i, c' i * (1 + e i b) / 2 * e i a = 0
      have hsum : ∀ x, Summable (fun i => c' i * e i x) := fun x =>
        Summable.of_norm_bounded hs (fun i => by
          rw [norm_mul]
          exact (mul_le_of_le_one_right (norm_nonneg _) (hle i x)).trans (h3 i))
      have key : ∀ i, c' i * (1 + e i b) / 2 * e i a = (c' i * e i a + c' i * e i (b + a)) / 2 := by
        intro i; rw [hmul i b a]; ring
      simp only [key]
      rw [tsum_div_const, (hsum a).tsum_add (hsum (b + a)), h4 a, h4 (b + a)]
      simp

theorem charSeries_exists_ne_zero : ∀ (A I : Type) [AddCommGroup A] (e : I → A → ℂ) (c : I → ℂ) (i₀ : I), (∀ i a b, e i (a + b) = e i a * e i b) → (∀ i a, ‖e i a‖ ≤ 1) → (∀ a, e i₀ a = 1) → (∀ i, i ≠ i₀ → ∃ a, e i a = -1) → Summable (fun i => ‖c i‖) → c i₀ ≠ 0 → ∃ a, ∑' i, c i * e i a ≠ 0 := by
  intro A I _ e c i₀ hmul hle h0 hneg hs hc
  by_contra hcon
  push Not at hcon
  have he0 : ∀ i, e i 0 = 1 := by
    intro i
    by_cases hi : i = i₀
    · subst hi; exact h0 0
    · obtain ⟨a, ha⟩ := hneg i hi
      have h := hmul i a 0
      rw [add_zero, ha] at h
      linear_combination h
  have hpos : 0 < ‖c i₀‖ := norm_pos_iff.2 hc
  obtain ⟨s, hs1, hs2⟩ := (((tendsto_order.1
    (tendsto_tsum_compl_atTop_zero (fun i => ‖c i‖))).2 _ hpos).and
    (Filter.eventually_ge_atTop {i₀})).exists
  have htail : ∑' x : {x // x ∉ s}, ‖c x‖ < ‖c i₀‖ := hs1
  have hi0 : i₀ ∈ s := hs2 (Finset.mem_singleton_self i₀)
  obtain ⟨c', hc'0, hc's, hc'le, hc'F⟩ :=
    charSeries_kill_finset e c i₀ hmul hle h0 hneg hs hcon s
  have hsum' : Summable c' := Summable.of_norm_bounded hs hc'le
  have key := hc'F 0
  simp only [he0, mul_one] at key
  rw [← hsum'.sum_add_tsum_subtype_compl s] at key
  have hfin : ∑ x ∈ s, c' x = c i₀ := by
    rw [Finset.sum_eq_single i₀ (fun b hb hne => hc's b hb hne) (fun h => absurd hi0 h)]
    exact hc'0
  rw [hfin] at key
  have hbound : ‖∑' x : {x // x ∉ s}, c' x‖ ≤ ∑' x : {x // x ∉ s}, ‖c x‖ :=
    tsum_of_norm_bounded ((hs.subtype _).hasSum) (fun x => hc'le x)
  have hnorm : ‖c i₀‖ = ‖∑' x : {x // x ∉ s}, c' x‖ := by
    rw [eq_neg_of_add_eq_zero_left key, norm_neg]
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsPosMulNormSqLe
namespace GlobalTheory.IntegralPointNormSquareBound

theorem exists_pos_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (h : ∀ v : V, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : V, c * ‖v‖ ^ 2 ≤ om v (J v) := by
  have hcont : Continuous fun v : V => om v (J v) := by
    let B : V →ₗ[ℝ] V →L[ℝ] ℝ :=
      (LinearMap.toContinuousLinearMap : (V →ₗ[ℝ] ℝ) ≃ₗ[ℝ] V →L[ℝ] ℝ).toLinearMap ∘ₗ om
    have h1 : Continuous B := B.continuous_of_finiteDimensional
    have h2 : Continuous J := J.continuous_of_finiteDimensional
    exact h1.clm_apply h2
  have hcomp : IsCompact (Metric.sphere (0 : V) 1) := by
    haveI : ProperSpace V := FiniteDimensional.proper_real V
    exact isCompact_sphere 0 1
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ u ∈ Metric.sphere (0 : V) 1, c ≤ om u (J u) := by
    rcases (Metric.sphere (0 : V) 1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun u hu => by rw [he] at hu; exact hu.elim⟩
    · obtain ⟨x, hx, hmin⟩ := hcomp.exists_isMinOn hne hcont.continuousOn
      refine ⟨om x (J x), h x ?_, fun u hu => hmin hu⟩
      rintro rfl
      simp at hx
  refine ⟨c, hc, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv
    simp
  · have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : V) 1 := by
      simp [norm_smul, hn.ne']
    have h3 := hle _ hu
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
    have h4 : ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 = om v (J v) := by
      field_simp
    calc c * ‖v‖ ^ 2 ≤ ‖v‖⁻¹ * (‖v‖⁻¹ * om v (J v)) * ‖v‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = om v (J v) := h4

end GlobalTheory.IntegralPointNormSquareBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetup
open scoped ContDiff

namespace GlobalTheory.HeisenbergGaussianSeries

theorem exists_coercive {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v)) :
    ∃ c : ℝ, 0 < c ∧ ∀ v, c * ‖v‖ ^ 2 ≤ om v (J v) := by
  first
  | exact @_root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le
  | exact _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le
  | (apply _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralPointNormSquareBound.exists_pos_mul_norm_sq_le ..)

theorem exists_exponent {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) :
    ∃ M : V →L[ℝ] V →L[ℝ] ℂ, ∀ y v, M y v =
      -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)) := by
  let m : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ
    (fun y v => -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)))
    (by intro a b v; simp; ring) (by intro a b v; simp; ring)
    (by intro a b v; simp; ring) (by intro a b v; simp; ring)
  exact ⟨LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℂ)).toLinearMap ∘ₗ m),
    fun y v => rfl⟩

theorem contDiff_bilin {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) :
    ContDiff ℝ ∞ fun v : V => om v (J v) := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := ℝ)).toLinearMap ∘ₗ om)
  have h1 : ContDiff ℝ ∞ fun v : V => B v (LinearMap.toContinuousLinearMap J v) :=
    B.contDiff.clm_apply (LinearMap.toContinuousLinearMap J).contDiff
  exact h1

theorem swap_mul {G : Type} [AddCommGroup G] (β : G → G → ℂ)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (x y : G) : β x y * β y x = 1 := by
  have := hd (x + y)
  rw [hl, hr, hr, hd, hd] at this
  simpa using this

theorem summable_coeff {G V : Type} [AddCommGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (p : G →+ V) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (Γ U₀ : AddSubgroup G) (χ : G → ℂ) (hpos : ∀ v, v ≠ 0 → 0 < om v (J v))
    (hinj : ∀ g ∈ Γ, p g = 0 → g = 0)
    (hfin : ∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite)
    (hχ0 : ∀ x, x ∉ U₀ → χ x = 0) (hχ1 : ∀ x, ‖χ x‖ ≤ 1)
    (b : Γ → ℂ) (hb : ∀ g, ‖b g‖ = 1) (w : G) (y : V) (M : V →L[ℝ] V →L[ℝ] ℂ) (R : ℝ) :
    Summable fun g : Γ => ‖b g * χ (g + w) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ))‖ *
        Real.exp (R * ‖M (p g + y)‖) := by
  obtain ⟨c, hc, hq⟩ := exists_coercive om J hpos
  have hs := GlobalTheory.GaussCoset.summable_gaussian_coset G V p Γ U₀ hinj hfin (Real.pi / 2 * c) (by positivity) (|R| * ‖M‖) w y
  refine Summable.of_nonneg_of_le (fun g => by positivity) (fun g => ?_) hs
  by_cases hg : (g : G) + w ∈ U₀
  · rw [Set.indicator_of_mem (by exact hg), norm_mul, norm_mul, hb, one_mul, Complex.norm_exp,
      Real.exp_add]
    have h1 : (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ)).re
        = -(Real.pi / 2) * om (p g + y) (J (p g + y)) := by
      have : (-(Real.pi / 2 : ℂ) * (om (p g + y) (J (p g + y)) : ℝ))
        = ((-(Real.pi / 2) * om (p g + y) (J (p g + y)) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.ofReal_re]
    rw [h1]
    have h2 : -(Real.pi / 2) * om (p g + y) (J (p g + y))
        ≤ -(Real.pi / 2 * c) * ‖p g + y‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left (hq (p g + y)) (show 0 ≤ Real.pi / 2 by positivity)
      linarith
    have h3 : R * ‖M (p g + y)‖ ≤ |R| * ‖M‖ * ‖p g + y‖ := by
      rw [mul_assoc]
      exact mul_le_mul (le_abs_self R) (M.le_opNorm _) (norm_nonneg _) (abs_nonneg _)
    refine mul_le_mul ?_ (Real.exp_le_exp.mpr h3) (by positivity) (by positivity)
    exact (mul_le_of_le_one_left (by positivity) (hχ1 _)).trans (Real.exp_le_exp.mpr h2)
  · rw [Set.indicator_of_notMem (by exact hg), hχ0 _ hg]
    simp

noncomputable def series {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V)
    (Γ : AddSubgroup G) (χ : G → ℂ) (a : V) (w : G) : ℂ :=
  ∑' g : Γ, β g w * β (ι a) (g + w) * χ (g + w) *
    Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))

section
variable {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℝ V]
    {p : G →+ V} {ι : V →+ G} {β : G → G → ℂ} {om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {J : V →ₗ[ℝ] V}
    {Γ : AddSubgroup G} {χ : G → ℂ}

theorem series_quasi
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hΓ : ∀ g ∈ Γ, ∀ g' ∈ Γ, β g g' = 1) (a : V) (g₀ : G) (hg₀ : g₀ ∈ Γ) (w : G) :
    β g₀ w * series p ι β om J Γ χ a (g₀ + w) = series p ι β om J Γ χ a w := by
  unfold series
  rw [← tsum_mul_left]
  refine Eq.trans ?_ ((Equiv.addRight (⟨g₀, hg₀⟩ : Γ)).tsum_eq _)
  refine tsum_congr fun g => ?_
  have e1 : p g + (a + p (g₀ + w)) = p (g + g₀) + (a + p w) := by simp only [map_add (f := _)]; abel
  simp only [Equiv.coe_addRight, AddSubgroup.coe_add]
  rw [e1, hr g g₀ w, hΓ g g.2 g₀ hg₀, hl g g₀ w, add_assoc (g : G) g₀ w]
  ring

theorem series_inv
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (a : V) (u : G) (hu : p u = 0) (hχ : ∀ x, β x u * χ (x + u) = χ x) (w : G) :
    β w u * series p ι β om J Γ χ a (w + u) = series p ι β om J Γ χ a w := by
  unfold series
  rw [← tsum_mul_left]
  refine tsum_congr fun g => ?_
  have h1 : β (ι a) u = 1 := by
    have := swap_mul β hl hr hd (ι a) u
    rw [hβ u a, hu] at this
    simpa using this
  rw [← hχ (g + w), ← add_assoc (g : G) w u, hr (ι a) (g + w) u, h1, hr g w u, hl g w u,
    map_add p w u, hu,
    add_zero]
  ring

theorem series_expand (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (hsym : ∀ x y, om x (J y) = om y (J x)) (hχ : ∀ x v, χ (x + ι v) = χ x)
    (M : V → V → ℂ)
    (hM : ∀ y v, M y v = -(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ)))
    (a : V) (w : G) (v : V) :
    β w (ι v) * series p ι β om J Γ χ a (w + ι v) =
      Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) *
      ∑' g : Γ, (β g w * β (ι a) (g + w) * χ (g + w) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
        Complex.exp (M (p g + (a + p w)) v) := by
  unfold series
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun g => ?_
  have e1 : p g + (a + p (w + ι v)) = (p g + (a + p w)) + v := by rw [map_add (f := _), hp]; abel
  have e2 : β w (ι v) * β g (ι v) * β (ι a) (ι v) =
      Complex.exp (-(Real.pi * Complex.I) * (om (p g + (a + p w)) v : ℝ)) := by
    rw [← hl, ← hl, hβ, map_add p, map_add p, hp]
    congr 5; abel
  rw [e1, ← add_assoc (g : G) w, hχ, hr (ι a) (g + w), hr g w, hM]
  set y := p g + (a + p w)
  have e3 : Complex.exp (-(Real.pi * Complex.I) * (om y v : ℝ)) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (y + v) (J (y + v)) : ℝ)) =
      Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om y (J y) : ℝ)) *
      Complex.exp (-(Real.pi : ℂ) * (Complex.I * (om y v : ℝ) + (om y (J v) : ℝ))) := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_add (f := _), LinearMap.add_apply, hsym v y]
    push_cast; ring
  linear_combination (β g w * β (ι a) (g + w) * χ (g + w) *
      Complex.exp (-(Real.pi / 2 : ℂ) * (om (y + v) (J (y + v)) : ℝ))) * e2 +
    (β g w * β (ι a) (g + w) * χ (g + w)) * e3

theorem series_neg (hp : ∀ v, p (ι v) = v)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1)
    (hβ : ∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ)))
    (halt : ∀ v, om v v = 0) (hχ : ∀ x v, χ (x + ι v) = χ x) (a : V) :
    series p ι β om J Γ χ a (ι (-a)) =
      ∑' g : Γ, (χ g * Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g) (J (p g)) : ℝ))) *
        Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)) := by
  unfold series
  refine tsum_congr fun g => ?_
  have h1 : β (ι a) g = Complex.exp (Real.pi * Complex.I * (om (p g) a : ℝ)) := by
    have := swap_mul β hl hr hd (ι a) g
    rw [hβ g a] at this
    rw [eq_inv_of_mul_eq_one_left this, ← Complex.exp_neg]
    congr 1; ring
  have h2 : Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)) =
      Complex.exp (Real.pi * Complex.I * (om (p g) a : ℝ)) *
      Complex.exp (Real.pi * Complex.I * (om (p g) a : ℝ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hχ, hr, h1, h2, hβ, hβ, hp, hp, add_neg_cancel, add_zero]
  simp [halt]
  ring
end

theorem exists_theta : ∀ (G V : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (Γ U₀ U : AddSubgroup G) (χ : G → ℂ), Continuous p → Continuous ι → (∀ v, p (ι v) = v) → (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ x y, ‖β x y‖ = 1) → Continuous (fun q : G × G => β q.1 q.2) → (∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ))) → (∀ v, om v v = 0) → (∀ v, J (J v) = -v) → (∀ x y, om x (J y) = om y (J x)) → (∀ v, v ≠ 0 → 0 < om v (J v)) → (∀ g ∈ Γ, ∀ g' ∈ Γ, β g g' = 1) → (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ v, ι v ∈ U₀) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite) → (∀ x, x ∉ U₀ → χ x = 0) → (∀ x, ‖χ x‖ ≤ 1) → χ 0 = 1 → (∀ x v, χ (x + ι v) = χ x) → IsOpen (U : Set G) → (∀ u ∈ U, ∀ x, β x (u - ι (p u)) * χ (x + (u - ι (p u))) = χ x) → ∃ f : G → ℂ, f ≠ 0 ∧ Continuous f ∧ (∀ g ∈ Γ, ∀ w, β g w * f (g + w) = f w) ∧ (∀ u, p u = 0 → (∀ x, β x u * χ (x + u) = χ x) → ∀ w, β w u * f (w + u) = f w) ∧ (∀ w, ContDiff ℝ ∞ fun v : V => f (w + ι v)) ∧ ∀ w z, deriv (fun t : ℝ => β w (ι (t • z)) * f (w + ι (t • z))) 0 + Complex.I * deriv (fun t : ℝ => β w (ι (t • J z)) * f (w + ι (t • J z))) 0 = 0 := by
  intro G V _ _ _ _ _ _ p ι β om J Γ U₀ U χ hpc hιc hp hl hr hd hn hβc hβ halt hJ hsym hpos hΓ hinj
    _ hfin hχ0 hχ1 hχz hχι hU hUinv
  obtain ⟨M, hM⟩ := exists_exponent om J

  obtain ⟨a, ha⟩ : ∃ a : V, series p ι β om J Γ χ a (ι (-a)) ≠ 0 := by
    have hs := summable_coeff p om J Γ U₀ χ hpos hinj hfin hχ0 hχ1 (fun _ => 1) (by simp) 0 0 M 0
    simp only [one_mul, add_zero, zero_mul, Real.exp_zero, mul_one] at hs
    obtain ⟨a, ha⟩ := GlobalTheory.charSeries_exists_ne_zero V Γ
      (fun g a => Complex.exp (2 * Real.pi * Complex.I * (om (p g) a : ℝ)))
      (fun g => χ g * Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g) (J (p g)) : ℝ))) 0
      (fun g a b => by rw [← Complex.exp_add]; congr 1; simp only [map_add (f := _)]; push_cast; ring)
      (fun g a => by
        have : (2 * Real.pi * Complex.I * (om (p g) a : ℝ) : ℂ)
          = ((2 * Real.pi * om (p g) a : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [this, Complex.norm_exp_ofReal_mul_I])
      (fun a => by simp)
      (fun g hg => by
        have h1 : p g ≠ 0 := fun h => hg (Subtype.ext (hinj g g.2 h))
        have h2 := (hpos _ h1).ne'
        refine ⟨(2 * om (p g) (J (p g)))⁻¹ • J (p g), ?_⟩
        have h3 : om (p g) ((2 * om (p g) (J (p g)))⁻¹ • J (p g)) = 1 / 2 := by
          rw [map_smul, smul_eq_mul]; field_simp
        simp only [h3]
        rw [← Complex.exp_pi_mul_I]
        congr 1; push_cast; ring)
      hs (by simp [hχz])
    exact ⟨a, by rw [series_neg hp hl hr hd hβ halt hχι]; exact ha⟩
  have hexp := fun w : G => GlobalTheory.expSeries_contDiff_and_hasDerivAt V Γ
    (fun g => β g w * β (ι a) (g + w) * χ (g + w) *
        Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ)))
    (fun g => M (p g + (a + p w)))
    (summable_coeff p om J Γ U₀ χ hpos hinj hfin hχ0 hχ1 (fun g => β g w * β (ι a) (g + w))
      (fun g => by rw [norm_mul, hn, hn, one_mul]) w (a + p w) M)
  have hexpand := series_expand (Γ := Γ) hp hl hr hβ hsym hχι (fun y v => M y v) hM a
  have hne : ∀ x y, β x y ≠ 0 := fun x y h => by simpa [h] using hn x y
  have hgauss : ContDiff ℝ ∞ fun v : V => Complex.exp (-(Real.pi / 2 : ℂ) * (om v (J v) : ℝ)) :=
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_bilin om J))).cexp
  have hsmooth : ∀ w, ContDiff ℝ ∞ fun v : V => series p ι β om J Γ χ a (w + ι v) := by
    intro w
    have h1 : ContDiff ℝ ∞ fun v : V => Complex.exp (Real.pi * Complex.I * (om (p w) v : ℝ)) :=
      (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (LinearMap.toContinuousLinearMap (om (p w))).contDiff)).cexp
    have h2 := h1.mul (hgauss.mul (hexp w).1)
    refine (congrArg (ContDiff ℝ ∞) (funext fun v => ?_)).mp h2
    rw [← hexpand w v, hβ, ← mul_assoc, ← Complex.exp_add]
    simp
  refine ⟨series p ι β om J Γ χ a, fun h => ha (by rw [h]; rfl), ?_,
    fun g hg w => series_quasi hl hr hΓ a g hg w,
    fun u hu hχ w => series_inv hl hr hd hβ a u hu hχ w, hsmooth, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro w
    have hc1 : Continuous fun x : G => p (x - w) := hpc.comp (continuous_id.sub continuous_const)
    have hc2 : Continuous fun x : G => β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))) :=
      hβc.comp (f := fun x : G => (w + ι (p (x - w)), (x - w) - ι (p (x - w))))
        ((continuous_const.add (hιc.comp hc1)).prodMk
          ((continuous_id.sub continuous_const).sub (hιc.comp hc1)))
    have hc3 : Continuous fun x : G => (β (w + ι (p (x - w))) ((x - w) - ι (p (x - w))))⁻¹ *
        series p ι β om J Γ χ a (w + ι (p (x - w))) :=
      (hc2.inv₀ fun x => hne _ _).mul ((hsmooth w).continuous.comp hc1)
    refine hc3.continuousAt.congr ?_
    have hnhds : ∀ᶠ x in nhds w, x - w ∈ U := by
      have : IsOpen {x : G | x - w ∈ U} := hU.preimage (continuous_id.sub continuous_const)
      exact this.mem_nhds (by simp)
    filter_upwards [hnhds] with x hx
    have h := series_inv (Γ := Γ) (J := J) hl hr hd hβ a ((x - w) - ι (p (x - w)))
      (by rw [map_sub p, hp, sub_self]) (hUinv _ hx) (w + ι (p (x - w)))
    rw [← h, ← mul_assoc, inv_mul_cancel₀ (hne _ _), one_mul]
    congr 1; abel
  · intro w z
    have hder : ∀ z : V, HasDerivAt
        (fun t : ℝ => β w (ι (t • z)) * series p ι β om J Γ χ a (w + ι (t • z)))
        (∑' g : Γ, (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          M (p g + (a + p w)) z) 0 := by
      intro z
      have g1 : HasDerivAt (fun t : ℝ =>
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (t • z) (J (t • z)) : ℝ))) 0 0 := by
        have g0 : HasDerivAt (fun t : ℝ => om (t • z) (J (t • z))) 0 0 := by
          have := ((hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))).mul_const (om z (J z))
          refine (this.congr_deriv (by simp)).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun t => ?_)
          simp [mul_assoc]
        exact (g0.ofReal_comp.const_mul (-(Real.pi / 2 : ℂ))).cexp.congr_deriv (by simp)
      have g2 := g1.mul ((hexp w).2 z).2
      simp only [hexpand]
      exact g2.congr_deriv (by simp)
    rw [(hder z).deriv, (hder (J z)).deriv, ← tsum_mul_left,
      ← ((hexp w).2 z).1.tsum_add (((hexp w).2 (J z)).1.mul_left Complex.I)]
    refine (tsum_congr fun g => ?_).trans tsum_zero
    rw [hM, hM, hJ, map_neg]
    push_cast
    linear_combination (-(Real.pi : ℂ) * (β g w * β (ι a) (g + w) * χ (g + w) *
          Complex.exp (-(Real.pi / 2 : ℂ) * (om (p g + (a + p w)) (J (p g + (a + p w))) : ℝ))) *
          (om (p g + (a + p w)) (J z) : ℝ)) * Complex.I_mul_I

end GlobalTheory.HeisenbergGaussianSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetupStatement
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_bicharacter_weil_setup : ∀ (G V : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (Γ U₀ U : AddSubgroup G) (χ : G → ℂ), Continuous p → Continuous ι → (∀ v, p (ι v) = v) → (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ x y, ‖β x y‖ = 1) → Continuous (fun q : G × G => β q.1 q.2) → (∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ))) → (∀ v, om v v = 0) → (∀ v, J (J v) = -v) → (∀ x y, om x (J y) = om y (J x)) → (∀ v, v ≠ 0 → 0 < om v (J v)) → (∀ g ∈ Γ, ∀ g' ∈ Γ, β g g' = 1) → (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ v, ι v ∈ U₀) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite) → (∀ x, x ∉ U₀ → χ x = 0) → (∀ x, ‖χ x‖ ≤ 1) → χ 0 = 1 → (∀ x v, χ (x + ι v) = χ x) → IsOpen (U : Set G) → (∀ u ∈ U, ∀ x, β x (u - ι (p u)) * χ (x + (u - ι (p u))) = χ x) → ∃ f : G → ℂ, f ≠ 0 ∧ Continuous f ∧ (∀ g ∈ Γ, ∀ w, β g w * f (g + w) = f w) ∧ (∀ u, p u = 0 → (∀ x, β x u * χ (x + u) = χ x) → ∀ w, β w u * f (w + u) = f w) ∧ (∀ w, ContDiff ℝ ∞ fun v : V => f (w + ι v)) ∧ ∀ w z, deriv (fun t : ℝ => β w (ι (t • z)) * f (w + ι (t • z))) 0 + Complex.I * deriv (fun t : ℝ => β w (ι (t • J z)) * f (w + ι (t • J z))) 0 = 0 := by
  first | exact @GlobalTheory.HeisenbergGaussianSeries.exists_theta | exact GlobalTheory.HeisenbergGaussianSeries.exists_theta | (intros; apply GlobalTheory.HeisenbergGaussianSeries.exists_theta <;> assumption)
end
