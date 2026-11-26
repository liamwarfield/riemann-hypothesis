module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceMomentIdentity

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.TwoSidedBoundOfPointwiseBounds
open UpperTheory.V.Lit.Geo

private theorem exp_quad (x : ℝ) : Real.exp x ≤ 1 + x + x ^ 2 * Real.exp |x| := by
  rcases le_or_gt |x| 1 with h | h
  · have h1 := Real.abs_exp_sub_one_sub_id_le h
    have h2 : x ^ 2 ≤ x ^ 2 * Real.exp |x| :=
      le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (abs_nonneg x))
    have h3 := (abs_le.mp h1).2
    linarith
  · rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx] at h ⊢
      have : Real.exp x ≤ x ^ 2 * Real.exp x :=
        le_mul_of_one_le_left (Real.exp_pos x).le (by nlinarith)
      linarith
    · rw [abs_of_neg hx] at h ⊢
      have h1 : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx.le
      have h2 : x ^ 2 ≤ x ^ 2 * Real.exp (-x) :=
        le_mul_of_one_le_right (sq_nonneg x) (Real.one_le_exp (by linarith))
      nlinarith

private theorem up_pt (q u ε : ℝ) (hq : 0 ≤ q) (h0 : 0 ≤ ε) (h4 : ε ≤ 1 / 4) (hu : |u| ≤ ε * q) :
    Real.exp (-Real.pi * (q + u)) ≤ Real.exp (-Real.pi * q) + -Real.pi * (u * Real.exp (-Real.pi * q)) +
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by
  have hpi := Real.pi_pos
  have hE : Real.exp (-Real.pi * (q + u)) = Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have hx := exp_quad (-Real.pi * u)
  have habs : |-Real.pi * u| = Real.pi * |u| := by
    rw [abs_mul, abs_neg, abs_of_pos hpi]
  rw [habs] at hx
  have hu4 : |u| ≤ q / 4 := by nlinarith [abs_nonneg u, mul_nonneg (sub_nonneg.mpr h4) hq]
  have hu2 : u ^ 2 ≤ ε ^ 2 * q ^ 2 := by
    have := mul_self_le_mul_self (abs_nonneg u) hu
    nlinarith [sq_abs u]
  have hpu : Real.pi * |u| ≤ Real.pi * (q / 4) := mul_le_mul_of_nonneg_left hu4 hpi.le
  have hy0 : 0 ≤ Real.pi * q / 4 := by positivity
  have hexp1 : Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤
      Real.exp (-Real.pi * (1 / 2 * q)) * Real.exp (-(Real.pi * q / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hquad : (Real.pi * q / 4) ^ 2 ≤ 2 * Real.exp (Real.pi * q / 4) := by
    have := Real.quadratic_le_exp_of_nonneg hy0
    nlinarith
  have hey : (Real.pi * q / 4) ^ 2 * Real.exp (-(Real.pi * q / 4)) ≤ 2 := by
    have h1 : Real.exp (Real.pi * q / 4) * Real.exp (-(Real.pi * q / 4)) = 1 := by
      rw [← Real.exp_add]; simp
    have h2 := Real.exp_pos (-(Real.pi * q / 4))
    nlinarith
  have A : (-Real.pi * u) ^ 2 ≤ ε ^ 2 * (Real.pi ^ 2 * q ^ 2) := by
    have : (-Real.pi * u) ^ 2 = Real.pi ^ 2 * u ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg Real.pi]
  have hterm : (-Real.pi * u) ^ 2 * Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q) ≤
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by
    calc (-Real.pi * u) ^ 2 * Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q)
        = (-Real.pi * u) ^ 2 * (Real.exp (Real.pi * |u|) * Real.exp (-Real.pi * q)) := by ring
      _ ≤ (ε ^ 2 * (Real.pi ^ 2 * q ^ 2)) *
            (Real.exp (-Real.pi * (1 / 2 * q)) * Real.exp (-(Real.pi * q / 4))) :=
          mul_le_mul A hexp1 (by positivity) (by positivity)
      _ = 16 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) *
            ((Real.pi * q / 4) ^ 2 * Real.exp (-(Real.pi * q / 4))) := by ring
      _ ≤ 16 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) * 2 := by gcongr
      _ = 32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q)) := by ring
  rw [hE]
  have hE0 := Real.exp_pos (-Real.pi * q)
  have hm := mul_le_mul_of_nonneg_left hx hE0.le
  nlinarith

private theorem low_pt (q u m : ℝ) :
    Real.exp m * ((1 - m) * Real.exp (-Real.pi * q) + -Real.pi * (u * Real.exp (-Real.pi * q))) ≤
      Real.exp (-Real.pi * (q + u)) := by
  have h := Real.add_one_le_exp (-Real.pi * u - m)
  have hE : Real.exp (-Real.pi * (q + u)) =
      Real.exp m * Real.exp (-Real.pi * q) * Real.exp (-Real.pi * u - m) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [hE]
  have hp : 0 ≤ Real.exp m * Real.exp (-Real.pi * q) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hp]

private theorem sum_pt (q u ε : ℝ) (hq : 0 ≤ q) (h4 : ε ≤ 1 / 4) (hu : |u| ≤ ε * q) :
    ‖u * Real.exp (-Real.pi * q)‖ ≤ Real.exp (-Real.pi * (1 / 2 * q)) := by
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hu4 : |u| ≤ q / 4 := by nlinarith [mul_nonneg (sub_nonneg.mpr h4) hq]
  have hpi := Real.pi_pos
  have h1 := Real.add_one_le_exp (Real.pi * q / 2)
  have hsplit : Real.exp (-Real.pi * (1 / 2 * q)) =
      Real.exp (-Real.pi * q) * Real.exp (Real.pi * q / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hsplit]
  have hE := Real.exp_pos (-Real.pi * q)
  have h2 : q / 4 ≤ Real.exp (Real.pi * q / 2) := by nlinarith [Real.pi_gt_three]
  calc |u| * Real.exp (-Real.pi * q) ≤ q / 4 * Real.exp (-Real.pi * q) :=
        mul_le_mul_of_nonneg_right hu4 hE.le
    _ ≤ _ := by rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2 hE.le

theorem UpperTheory.two_sided_bound_of_pointwise_bounds :
    LogTaylor := by
  intro N
  refine ⟨32 * 2 ^ N, by positivity, ?_⟩
  intro ι _ q u ε hS h0 h4 hu
  obtain ⟨hq, hsc⟩ := hS
  have hsum1 := (hsc 1 1 one_pos le_rfl).1
  simp only [one_mul] at hsum1
  have hhalf := hsc (1 / 2) 1 (by norm_num) (by norm_num)
  have hsumh : Summable fun i => Real.exp (-Real.pi * (1 / 2 * q i)) := hhalf.1
  have hSle : ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) ≤
      2 ^ N * ∑' i, Real.exp (-Real.pi * q i) := by
    have h := hhalf.2
    have h2 : (1 : ℝ) / (1 / 2) = 2 := by norm_num
    rw [h2] at h
    simp only [one_mul] at h
    exact h
  set Z := ∑' i, Real.exp (-Real.pi * q i) with hZ
  set Z' := ∑' i, Real.exp (-Real.pi * (q i + u i)) with hZ'
  set M := ∑' i, u i * Real.exp (-Real.pi * q i) with hM
  set S := ∑' i, Real.exp (-Real.pi * (1 / 2 * q i)) with hS'
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hZpos : 0 < Z := hsum1.tsum_pos (fun i => (Real.exp_pos _).le) i0 (Real.exp_pos _)
  have hsumM : Summable fun i => u i * Real.exp (-Real.pi * q i) :=
    Summable.of_norm_bounded hsumh (fun i => sum_pt (q i) (u i) ε (hq i) h4 (hu i))
  have hR : HasSum (fun i => Real.exp (-Real.pi * q i) + -Real.pi * (u i * Real.exp (-Real.pi * q i)) +
      32 * ε ^ 2 * Real.exp (-Real.pi * (1 / 2 * q i))) (Z + -Real.pi * M + 32 * ε ^ 2 * S) :=
    (hsum1.hasSum.add (hsumM.hasSum.mul_left _)).add (hsumh.hasSum.mul_left _)
  have hsum' : Summable fun i => Real.exp (-Real.pi * (q i + u i)) :=
    Summable.of_nonneg_of_le (fun i => (Real.exp_pos _).le)
      (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hR.summable
  have hup : Z' ≤ Z + -Real.pi * M + 32 * ε ^ 2 * S := by
    rw [← hR.tsum_eq]
    exact Summable.tsum_le_tsum (fun i => up_pt (q i) (u i) ε (hq i) h0 h4 (hu i)) hsum' hR.summable
  set m := -Real.pi * M / Z with hm
  have hmZ : m * Z = -Real.pi * M := by rw [hm]; exact div_mul_cancel₀ _ hZpos.ne'
  have hlow : Real.exp m * Z ≤ Z' := by
    have hL : HasSum (fun i => Real.exp m * ((1 - m) * Real.exp (-Real.pi * q i) +
        -Real.pi * (u i * Real.exp (-Real.pi * q i)))) (Real.exp m * ((1 - m) * Z + -Real.pi * M)) :=
      ((hsum1.hasSum.mul_left (1 - m)).add (hsumM.hasSum.mul_left (-Real.pi))).mul_left (Real.exp m)
    have e : (1 - m) * Z + -Real.pi * M = Z := by linear_combination (-1 : ℝ) * hmZ
    rw [← e, ← hL.tsum_eq]
    exact Summable.tsum_le_tsum (fun i => low_pt (q i) (u i) m) hL.summable hsum'
  have hZ'pos : 0 < Z' := lt_of_lt_of_le (by positivity) hlow
  have hLo : m ≤ Real.log Z' - Real.log Z := by
    have := Real.log_le_log (by positivity) hlow
    rw [Real.log_mul (Real.exp_pos m).ne' hZpos.ne', Real.log_exp] at this
    linarith
  have hUp : Real.log Z' - Real.log Z ≤ m + 32 * 2 ^ N * ε ^ 2 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hZ'pos hZpos)
    rw [Real.log_div hZ'pos.ne' hZpos.ne'] at h1
    have h2 : Z' / Z - 1 ≤ m + 32 * 2 ^ N * ε ^ 2 := by
      rw [div_sub_one hZpos.ne', div_le_iff₀ hZpos]
      have h3 := mul_le_mul_of_nonneg_left hSle (by positivity : (0 : ℝ) ≤ 32 * ε ^ 2)
      nlinarith
    linarith
  have hexpr : Real.pi * (M / Z) = -m := by rw [hm]; ring
  rw [hexpr, abs_le]
  have hK : (0 : ℝ) ≤ 32 * 2 ^ N * ε ^ 2 := by positivity
  constructor <;> linarith
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.SecondOrderTaylorRemainderBound
open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Lit.Bor

private theorem taylor_two {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ} {x : V}
    (hf : ContDiffAt ℝ 2 f x) : ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧ ∀ y : V, ‖y‖ ≤ ε →
      |f (x + y) - f x - fderiv ℝ f x y| ≤ C * ‖y‖ ^ 2 := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have h2 : ∀ᶠ z in nhds x, DifferentiableAt ℝ f z :=
    (hf.eventually (by simp)).mono fun z hz => hz.differentiableAt (by simp)
  obtain ⟨ε, hε, hb⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Filter.inter_mem ht h2)
  refine ⟨K, ε, K.2, hε, fun y hy => ?_⟩
  have hsub : Metric.closedBall x ‖y‖ ⊆ Metric.closedBall x ε := Metric.closedBall_subset_closedBall hy
  have hx : x ∈ Metric.closedBall x ‖y‖ := Metric.mem_closedBall_self (norm_nonneg _)
  have key := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' (𝕜 := ℝ) (f := f) (f' := fderiv ℝ f)
    (φ := fderiv ℝ f x) (C := K * ‖y‖) (s := Metric.closedBall x ‖y‖) (x := x) (y := x + y)
    (fun z hz => (hb (hsub hz)).2.hasFDerivAt.hasFDerivWithinAt)
    (fun z hz => by
      have := hK.norm_sub_le (hb (hsub hz)).1 (hb (hsub hx)).1
      refine this.trans (mul_le_mul_of_nonneg_left ?_ K.2)
      rwa [← dist_eq_norm])
    (convex_closedBall _ _) hx (by simp)
  rw [add_sub_cancel_left, Real.norm_eq_abs] at key
  calc _ ≤ _ := key
    _ = _ := by ring

theorem UpperTheory.second_order_taylor_remainder_bound :
    ScTaylor := by
  intro E _ _ a
  obtain ⟨hs, h1, hd, -⟩ := UpperTheory.deriv_similitudeChar_at_one_eq_trace E a
  have hat : ContDiffAt ℝ 2 (fun y : Lie E a => sc (Matrix.of y)) (oneL E a) :=
    (hs.contDiffAt (isOpen_invSet.mem_nhds (val_mem_invSet 1))).of_le (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  obtain ⟨C, ε, hC, hε, h⟩ := taylor_two hat
  refine ⟨C, ε, hC, hε, fun Y hY => ?_⟩
  have := h (toL Y) hY
  rw [hd, sub_neg_eq_add] at this
  have e : sc (Matrix.of (oneL E a)) = 1 := h1
  rw [e] at this
  exact this
end

open UpperTheory.V.Lit.Geo

section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

private theorem entry_le {E : Type} [Field E] [NumberField E] {a : ℕ} (M : Matrix (Fin a) (Fin a) (Cinf E))
    (i j : Fin a) (w : InfinitePlace E) : ‖M i j w‖ ≤ ‖toL M‖ :=
  (norm_le_pi_norm (toL M i j) w).trans ((norm_le_pi_norm (toL M i) j).trans (norm_le_pi_norm (toL M) i))

private theorem abs_trF_le {E : Type} [Field E] [NumberField E] {a : ℕ} (M p : Matrix (Fin a) (Fin a) (Cinf E)) :
    |trF M p| ≤ Fintype.card (InfinitePlace E) * (a * (a * (‖toL M‖ * ‖toL p‖))) := by
  unfold trF
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (a * (‖toL M‖ * ‖toL p‖))) ?_).trans (by simp)
  intro w _
  refine (Complex.abs_re_le_norm _).trans ?_
  have h : (M * p).trace w = ∑ i, ∑ j, M i j w * p j i w := by
    simp [Matrix.trace, Matrix.mul_apply, Finset.sum_apply]
  rw [h]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (a * (‖toL M‖ * ‖toL p‖)) ?_).trans (by simp)
  intro i _
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_card_nsmul _ _ (‖toL M‖ * ‖toL p‖) ?_).trans (by simp)
  intro j _
  rw [norm_mul]
  exact mul_le_mul (entry_le M i j w) (entry_le p j i w) (norm_nonneg _) (norm_nonneg _)

private theorem trF_add_smul {E : Type} [Field E] [NumberField E] {a : ℕ} (M p p' : Matrix (Fin a) (Fin a) (Cinf E))
    (c : ℝ) : trF M (p + c • p') = trF M p + c * trF M p' := by
  unfold trF
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul]
  simp

theorem UpperTheory.hermitian_trace_form_entry_estimate :
    FnTaylor := by
  intro E _ _ _ a ha L hL
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C₁, hC₁, hT⟩ := UpperTheory.two_sided_bound_of_pointwise_bounds N
  obtain ⟨C₂, ε₂, hC₂, hε₂, hS⟩ := UpperTheory.second_order_taylor_remainder_bound E a
  obtain ⟨-, ⟨B, hB, hBd⟩, -⟩ := UpperTheory.hermitian_trace_form_estimate E a ha L hL
  obtain ⟨hq1, hqa, hqh, hqc, hqb, -⟩ := UpperTheory.geometric_side_quadraticForm_identity E a
  obtain ⟨-, -, -, hsc, -⟩ := UpperTheory.deriv_similitudeChar_at_one_eq_trace E a
  set K : ℝ := C₂ + (1 + C₂) * a with hK
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hK0 : 0 ≤ K := by positivity
  set D : ℝ := ‖toL (1 : Matrix (Fin a) (Fin a) (Cinf E))‖ + 1 with hD
  have hD0 : 0 ≤ D := by positivity
  set n : ℝ := (Fintype.card (InfinitePlace E) : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨C₁ * K ^ 2 + Real.pi * (C₂ * (n * (a * (a * (B * D))))), min ε₂ (min 1 (1 / (4 * (K + 1)))),
    by positivity, by positivity, ?_⟩
  intro g Y h hl hY hh
  set y := ‖toL Y‖ with hy
  have hy0 : 0 ≤ y := norm_nonneg _
  have hy2 : y ≤ ε₂ := hY.trans (min_le_left _ _)
  have hy1 : y ≤ 1 := hY.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hy3 : y ≤ 1 / (4 * (K + 1)) := hY.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hKy : K * y ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hy3
    nlinarith only [hy3, hy0]
  have hs := hS Y hy2
  rw [hl, add_zero, ← hy] at hs
  set s := sc (1 + Y) with hsdef
  have hs1 : |s - 1| ≤ C₂ * y := hs.trans (mul_le_mul_of_nonneg_left (by nlinarith only [hy0, hy1]) hC₂)
  have hs2 : |s - 1| ≤ C₂ := hs1.trans (by nlinarith only [hy1, hC₂])
  have hs3 : |s| ≤ 1 + C₂ := by
    have := abs_le.1 hs2
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  set p := Y + (s - 1) • (1 + Y) with hp
  have hquad : ∀ x, quad p x = (s - 1) * qf x + s * quad Y x := by
    intro x
    rw [hp, (hqa _ _ 0 x).1, (hqa _ 0 (s - 1) x).2, (hqa _ _ 0 x).1, hq1]
    ring
  have hu : ∀ x, |quad p x| ≤ K * y * qf x := by
    intro x
    have hx := qf_nonneg x
    rw [hquad]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hx]
    have h1 : |s - 1| * qf x ≤ C₂ * y * qf x := mul_le_mul_of_nonneg_right hs1 hx
    have h2 : |s| * |quad Y x| ≤ (1 + C₂) * (a * y * qf x) :=
      mul_le_mul hs3 (hqb Y x) (abs_nonneg _) (by positivity)
    calc _ ≤ C₂ * y * qf x + (1 + C₂) * (a * y * qf x) := add_le_add h1 h2
      _ = K * y * qf x := by rw [hK]; ring
  haveI : Nonempty (lat L g) := ⟨0⟩
  have key := hT (lat L g) (fun v => qf (pt (rt g) v.1)) (fun v => quad p (pt (rt g) v.1)) (K * y) (hN g)
    (by positivity) hKy (fun v => hu _)
  have e1 : fn L (g * infGL E a h) =
      Real.log (∑' v : lat L g, Real.exp (-Real.pi * (qf (pt (rt g) v.1) + quad p (pt (rt g) v.1)))) := by
    unfold fn Th
    rw [(UpperTheory.point_evaluation_multiplicative_tsum E a ha L ℝ gauss).2.1 g h]
    congr 1
    refine tsum_congr fun v => ?_
    unfold gauss
    rw [hqc, hqh, ← hsc h, hh, ← hsdef, hquad, (hqa _ _ 0 _).1, hq1]
    congr 2
    ring
  have e2 := UpperTheory.hermitian_space_moment_identity E a ha L hL g p
  have key' : |fn L (g * infGL E a h) - fn L g + Real.pi * trF (mom L g).1 p| ≤
      C₁ * (K * y) ^ 2 := by
    rw [e1, e2]
    exact key
  rw [hp, trF_add_smul] at key'
  have h1 : ‖toL (1 + Y)‖ ≤ D := by
    have : toL (1 + Y) = toL 1 + toL Y := rfl
    rw [this]
    exact (norm_add_le _ _).trans (by rw [hD]; linarith)
  have h2 : |trF (mom L g).1 (1 + Y)| ≤ n * (a * (a * (B * D))) := by
    refine (abs_trF_le _ _).trans ?_
    have := mul_le_mul (hBd g).1 h1 (norm_nonneg _) hB.le
    gcongr
  have h3 : |Real.pi * ((s - 1) * trF (mom L g).1 (1 + Y))| ≤
      Real.pi * (C₂ * y ^ 2 * (n * (a * (a * (B * D))))) := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    exact mul_le_mul_of_nonneg_left (mul_le_mul hs h2 (abs_nonneg _) (by positivity)) Real.pi_pos.le
  have h4 := abs_le.1 key'
  have h5 := abs_le.1 h3
  rw [abs_le]
  constructor <;> linarith only [h4.1, h4.2, h5.1, h5.2]

end
