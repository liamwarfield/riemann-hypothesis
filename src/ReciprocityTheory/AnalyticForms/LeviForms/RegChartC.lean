module

public import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMoll
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshExt

@[expose] public section

section -- merged from ReciprocityTheory.AnalyticForms.LeviForms.RegChartB
section -- merged from ReciprocityTheory.AnalyticForms.LeviForms.RegChartA
namespace ReciprocityTheory.AnForm.P.RegularChartScaling

open MeasureTheory Metric Filter Topology Set
open ReciprocityTheory.AnForm.A

noncomputable section

variable {D : ℕ}

lemma isPsh_mono {U V : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (h : IsPsh U φ) (hVU : V ⊆ U) :
    IsPsh V φ :=
  ⟨h.1.mono hVU, fun z w hzw => h.2 z w fun ζ hζ => hVU (hzw ζ hζ)⟩

lemma isPsh_scale {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ} (h : IsPsh U φ) (c : ℝ) :
    IsPsh {y | c • y ∈ U} (fun y => φ (c • y)) := by
  refine ⟨fun y hy t ht => ?_, fun z w hzw => ?_⟩
  · have hc : ContinuousWithinAt (fun y : Fin D → ℂ => c • y) {y | c • y ∈ U} y :=
      (continuous_const_smul c).continuousWithinAt
    exact (hc.tendsto_nhdsWithin (fun y hy => hy)).eventually (h.1 (c • y) hy t ht)
  · have e : ∀ ζ : ℂ, c • (z + ζ • w) = c • z + ζ • (c • w) := fun ζ => by
      rw [smul_add, smul_comm c ζ w]
    have := h.2 (c • z) (c • w) fun ζ hζ => by
      rw [← e]
      exact hzw ζ hζ
    simp only [e]
    exact this

lemma exists_far_point (z : Fin D → ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ x ∈ closedBall z s, (∀ i, s ≤ ‖x i‖) ∧ ‖x‖ ≤ ‖z‖ + s := by
  classical
  let u : Fin D → ℂ := fun i => if z i = 0 then 1 else z i / (‖z i‖ : ℂ)
  have hu : ∀ i, ‖u i‖ = 1 := by
    intro i
    by_cases h : z i = 0
    · simp [u, h]
    · simp only [u, if_neg h, norm_div, Complex.norm_real, norm_norm]
      exact div_self (norm_ne_zero_iff.mpr h)
  let w : Fin D → ℂ := fun i => (s : ℂ) * u i
  have hw : ‖w‖ ≤ s := by
    refine (pi_norm_le_iff_of_nonneg hs.le).mpr fun i => ?_
    simp [w, norm_mul, hu, abs_of_pos hs]
  refine ⟨z + w, ?_, fun i => ?_, (norm_add_le _ _).trans (by linarith)⟩
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hw
  · by_cases h : z i = 0
    · simp [w, u, h, abs_of_pos hs]
    · have hzi : 0 < ‖z i‖ := norm_pos_iff.mpr h
      have hc : (‖z i‖ : ℂ) ≠ 0 := by exact_mod_cast hzi.ne'
      have e : (z + w) i = ((‖z i‖ + s) / ‖z i‖ : ℝ) * z i := by
        simp only [Pi.add_apply, w, u, if_neg h]
        push_cast
        field_simp
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_cancel₀ _ hzi.ne']
      linarith

lemma not_mem_coordDiv_of {S : Finset (Fin D)} {x : Fin D → ℂ} {s : ℝ} (hs : 0 < s)
    (h : ∀ i, s ≤ ‖x i‖) : x ∉ coordDiv S := by
  rintro ⟨i, -, hi⟩
  have := h i
  rw [hi, norm_zero] at this
  linarith

lemma smul_mem_coordDiv_iff {S : Finset (Fin D)} {c : ℝ} (hc : c ≠ 0) (x : Fin D → ℂ) :
    c • x ∈ coordDiv S ↔ x ∈ coordDiv S := by
  simp only [coordDiv, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_zero, hc, false_or]

lemma mem_ball_smul_iff {R : ℝ} (hR : 0 < R) (y : Fin D → ℂ) :
    R • y ∈ ball (0 : Fin D → ℂ) R ↔ y ∈ ball (0 : Fin D → ℂ) 1 := by
  simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  exact mul_lt_iff_lt_one_right hR

lemma mem_closure_off (S : Finset (Fin D)) {R : ℝ} {y : Fin D → ℂ} (hy : y ∈ ball (0 : Fin D → ℂ) R) :
    y ∈ closure (ball (0 : Fin D → ℂ) R \ coordDiv S) := by
  classical
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hyR : ‖y‖ < R := by simpa using hy
  set m := min ε (R - ‖y‖) with hm
  have hm0 : 0 < m := lt_min hε (by linarith)
  have hfin : {t : ℝ | ∃ i, y i + (t : ℂ) = 0}.Finite := by
    have hsub : {t : ℝ | ∃ i, y i + (t : ℂ) = 0} ⊆ Set.range (fun i => -(y i).re) := by
      rintro t ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have := congrArg Complex.re hi
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
      show -(y i).re = t
      linarith
    exact (Set.finite_range _).subset hsub
  obtain ⟨t, ⟨ht0, htm⟩, htbad⟩ := ((Set.Ioo_infinite hm0).diff hfin).nonempty
  have hc : ‖fun _ : Fin D => (t : ℂ)‖ ≤ t :=
    (pi_norm_le_iff_of_nonneg ht0.le).mpr fun i => by simp [abs_of_pos ht0]
  refine ⟨y + fun _ => (t : ℂ), ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_zero_right]
    have := min_le_right ε (R - ‖y‖)
    calc ‖y + fun _ => (t : ℂ)‖ ≤ ‖y‖ + ‖fun _ : Fin D => (t : ℂ)‖ := norm_add_le _ _
      _ < R := by linarith
  · rintro ⟨i, -, hi⟩
    exact htbad ⟨i, by simpa using hi⟩
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg]
    have := min_le_left ε (R - ‖y‖)
    linarith


open Classical in
def extT (S : Finset (Fin D)) (R : ℝ) (v : (Fin D → ℂ) → ℝ) (κ : ℝ) (x : Fin D → ℂ) : ℝ :=
  limsupExt (ball (0 : Fin D → ℂ) 1) (coordDiv S) (fun y => max (v (R • y)) (-κ)) (R⁻¹ • x)

lemma ext_exists (S : Finset (Fin D)) {R : ℝ} (hR : 0 < R) {u : (Fin D → ℂ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hc : ContinuousOn u (ball 0 R \ coordDiv S))
    (hp : IsPsh (ball 0 R \ coordDiv S) u) (hub : ∀ x ∈ ball 0 R \ coordDiv S, u x ≤ B)
    (κ : ℝ) :
    ∃ w : (Fin D → ℂ) → ℝ, w = extT S R u κ ∧ IsPsh (ball 0 R) w ∧
      (∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, w x = max (u x) (-κ)) ∧
      ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0, ∃ y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ := by
  classical
  set v : (Fin D → ℂ) → ℝ := fun y => u (R • y) with hv
  have hmemR : ∀ y : Fin D → ℂ, R • y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S ↔
      y ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S := by
    intro y
    rw [Set.mem_diff, Set.mem_diff, mem_ball_smul_iff hR, smul_mem_coordDiv_iff hR.ne']
  have hset : {y : Fin D → ℂ | R • y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S} =
      ball (0 : Fin D → ℂ) 1 \ coordDiv S := by
    ext y
    exact hmemR y
  have hvc : ContinuousOn v (ball (0 : Fin D → ℂ) 1 \ coordDiv S) :=
    hc.comp (continuous_const_smul R).continuousOn fun y hy => (hmemR y).mpr hy
  have hvp : IsPsh (ball (0 : Fin D → ℂ) 1 \ coordDiv S) v := by
    have := isPsh_scale hp R
    rwa [hset] at this
  have hvb : ∀ z ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S,
      v z ≤ B * Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹) := by
    intro z hz
    have h1 : v z ≤ B := hub _ ((hmemR z).mpr hz)
    have hsum : 0 ≤ ∑ i ∈ S, Real.log ‖z i‖⁻¹ := by
      refine Finset.sum_nonneg fun i hi => ?_
      have hzi : z i ≠ 0 := fun h0 => hz.2 ⟨i, hi, h0⟩
      have hlt : ‖z i‖ ≤ 1 := by
        have h3 := norm_le_pi_norm z i
        have h2 : ‖z‖ < 1 := by simpa using hz.1
        linarith
      apply Real.log_nonneg
      rw [one_le_inv₀ (norm_pos_iff.mpr hzi)]
      exact hlt
    have hlog : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖z i‖⁻¹) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hlog hB]
  have hext := (ReciprocityTheory.AnForm.A.pshExtension_thm D S (ball 0 1) v B
    isOpen_ball subset_rfl hvc hvp hvb).2 κ
  refine ⟨extT S R u κ, rfl, ?_, ?_, ?_⟩
  · have h4 := isPsh_scale hext R⁻¹
    have hset2 : {x : Fin D → ℂ | R⁻¹ • x ∈ ball (0 : Fin D → ℂ) 1} = ball 0 R := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [← mem_ball_smul_iff hR, smul_inv_smul₀ hR.ne']
    rw [hset2] at h4
    exact h4
  · intro x hx
    have hx' : R⁻¹ • x ∉ coordDiv S := by
      rw [smul_mem_coordDiv_iff (inv_ne_zero hR.ne')]
      exact hx.2
    simp only [extT, limsupExt, if_neg hx', smul_inv_smul₀ hR.ne']
  · intro x hx δ hδ
    by_cases hxA : x ∈ coordDiv S
    · set x' := R⁻¹ • x with hx'
      have hxeq : R • x' = x := by rw [hx', smul_inv_smul₀ hR.ne']
      have hx'A : x' ∈ coordDiv S := (smul_mem_coordDiv_iff (inv_ne_zero hR.ne') x).mpr hxA
      have hx'U : x' ∈ ball (0 : Fin D → ℂ) 1 := by
        rw [← mem_ball_smul_iff hR, hxeq]
        exact hx
      set F : (Fin D → ℂ) → ℝ := fun y => max (u (R • y)) (-κ) with hF
      have hw : extT S R u κ x = limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') := by
        simp only [extT, limsupExt]
        rw [if_pos ((smul_mem_coordDiv_iff (inv_ne_zero hR.ne') x).mpr hxA)]
      haveI : (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x').NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_off S hx'U)
      have hcob : IsCoboundedUnder (· ≤ ·) (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') F :=
        isCoboundedUnder_le_of_le _ (fun y => le_max_right _ _)
      have hfreq := frequently_lt_of_lt_limsup hcob
        (show limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') - δ <
          limsup F (𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x') by linarith)
      have hev : ∀ᶠ y in 𝓝[ball (0 : Fin D → ℂ) 1 \ coordDiv S] x',
          y ∈ ball (0 : Fin D → ℂ) 1 \ coordDiv S ∧ dist y x' < δ / R :=
        Filter.Eventually.and eventually_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x' (div_pos hδ hR)))
      obtain ⟨y, hy1, hy2, hy3⟩ := (hfreq.and_eventually hev).exists
      refine ⟨R • y, (hmemR y).mpr hy2, ?_, ?_⟩
      · rw [← hxeq, dist_smul₀, Real.norm_eq_abs, abs_of_pos hR]
        calc R * dist y x' < R * (δ / R) := mul_lt_mul_of_pos_left hy3 hR
          _ = δ := by field_simp
      · have hFy : F y = max (u (R • y)) (-κ) := rfl
        rw [hw]
        linarith
    · have hx' : R⁻¹ • x ∉ coordDiv S := by
        rw [smul_mem_coordDiv_iff (inv_ne_zero hR.ne')]
        exact hxA
      have hwx : extT S R u κ x = max (u x) (-κ) := by
        simp only [extT, limsupExt, if_neg hx', smul_inv_smul₀ hR.ne']
      exact ⟨x, ⟨hx, hxA⟩, by simp [hδ], by linarith⟩

end

end ReciprocityTheory.AnForm.P.RegularChartScaling
end

namespace ReciprocityTheory.AnForm.P.RegularChartScaling

open MeasureTheory Metric Filter Topology Set
open ReciprocityTheory.AnForm.A

noncomputable section

variable {D : ℕ}

lemma log_term_nonneg {x : ℂ} (hx : ‖x‖ ≤ 2) : 0 ≤ Real.log (4 / ‖x‖ ^ 2) := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · rw [← h]; simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; nlinarith

lemma rLoc_ge (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} (hx : ∀ i, ‖x i‖ ≤ 2) :
    Real.exp 1 ≤ rLoc S m x := by
  unfold rLoc
  have : 0 ≤ ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (log_term_nonneg (hx i))
  linarith

lemma rLoc_pos (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} (hx : ∀ i, ‖x i‖ ≤ 2) :
    0 < rLoc S m x := (Real.exp_pos 1).trans_le (rLoc_ge S m hx)

lemma norm_coord_le_of_ball {R : ℝ} (hR : R ≤ 2) {x : Fin D → ℂ} (hx : x ∈ ball (0 : Fin D → ℂ) R)
    (i : Fin D) : ‖x i‖ ≤ 2 :=
  (norm_le_pi_norm x i).trans ((mem_ball_zero_iff.1 hx).le.trans hR)

def mTot (S : Finset (Fin D)) (m : Fin D → ℕ) : ℝ := ∑ i ∈ S, (m i : ℝ)

lemma mTot_nonneg (S : Finset (Fin D)) (m : Fin D → ℕ) : 0 ≤ mTot S m :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma rLoc_le_far (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} {s : ℝ} (hs : 0 < s)
    (hx : ∀ i, s ≤ ‖x i‖) : rLoc S m x ≤ Real.exp 1 + mTot S m * Real.log (4 / s ^ 2) := by
  unfold rLoc mTot
  rw [Finset.sum_mul]
  have : ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) ≤ ∑ i ∈ S, (m i : ℝ) * Real.log (4 / s ^ 2) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos (by norm_num) (pow_pos (hs.trans_le (hx i)) 2))
        (div_le_div_of_nonneg_left (by norm_num) (pow_pos hs 2) (pow_le_pow_left₀ hs.le (hx i) 2)))
      (Nat.cast_nonneg _)
  linarith

def pmoff (S : Finset (Fin D)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' (closedBall z t \ coordDiv S))

section Osc

variable {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {R C₅ : ℝ}

lemma pmo_bdd (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ} {s : ℝ}
    (hs : closedBall z s ⊆ ball 0 R) : BddAbove (u '' (closedBall z s \ coordDiv S)) :=
  ⟨C₅, by rintro _ ⟨x, hx, rfl⟩; exact hub x ⟨hs hx.1, hx.2⟩⟩

lemma pmo_nonempty (z : Fin D → ℂ) {s : ℝ} (hs : 0 < s) :
    (u '' (closedBall z s \ coordDiv S)).Nonempty := by
  obtain ⟨x, hx, hf, -⟩ := exists_far_point z hs
  exact ⟨u x, x, ⟨hx, not_mem_coordDiv_of hs hf⟩, rfl⟩

lemma le_pmo (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ} {s : ℝ}
    (hs : closedBall z s ⊆ ball 0 R) {x : Fin D → ℂ} (hx : x ∈ closedBall z s \ coordDiv S) :
    u x ≤ pmoff S u z s :=
  le_csSup (pmo_bdd hub hs) (mem_image_of_mem u hx)

lemma pmo_le (z : Fin D → ℂ) {s c : ℝ} (hs : 0 < s) (h : ∀ x ∈ closedBall z s \ coordDiv S, u x ≤ c) :
    pmoff S u z s ≤ c :=
  csSup_le (pmo_nonempty z hs) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

lemma pmo_mono (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ}
    {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') (hs' : closedBall z s' ⊆ ball 0 R) :
    pmoff S u z s ≤ pmoff S u z s' :=
  csSup_le_csSup (pmo_bdd hub hs') (pmo_nonempty z hs)
    (image_mono (sdiff_subset_sdiff_left (closedBall_subset_closedBall hss)))

lemma pmo_lower (hR : R ≤ 2) (hC₅ : 0 ≤ C₅) (m : Fin D → ℕ)
    (hb : ∀ z ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅)
    {z : Fin D → ℂ} {s : ℝ} (hs : 0 < s) (hsR : closedBall z s ⊆ ball 0 R) :
    -C₅ * Real.log (Real.exp 1 + mTot S m * Real.log (4 / s ^ 2)) ≤ pmoff S u z s := by
  obtain ⟨x, hx, hf, -⟩ := exists_far_point z hs
  have hxA : x ∉ coordDiv S := not_mem_coordDiv_of hs hf
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := hsR hx
  refine le_trans ?_ (le_pmo (fun y hy => (hb y hy).2) hsR ⟨hx, hxA⟩)
  refine le_trans ?_ (hb x ⟨hxB, hxA⟩).1
  have h1 := rLoc_pos S m (norm_coord_le_of_ball hR hxB)
  have h2 := rLoc_le_far S m hs hf
  have : Real.log (rLoc S m x) ≤ Real.log (Real.exp 1 + mTot S m * Real.log (4 / s ^ 2)) :=
    Real.log_le_log h1 h2
  nlinarith

lemma pmo_le_polyMax {w : (Fin D → ℂ) → ℝ} (hw : UpperSemicontinuousOn w (ball 0 R))
    (hwu : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ w x) {z : Fin D → ℂ} {s : ℝ}
    (hs : 0 < s) (hsR : closedBall z s ⊆ ball 0 R) :
    pmoff S u z s ≤ polyMax w z s :=
  pmo_le z hs fun x hx => (hwu x ⟨hsR hx.1, hx.2⟩).trans (le_polyMax hw hsR hx.1)

lemma polyMax_le_pmo (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅)
    {w : (Fin D → ℂ) → ℝ} {κ : ℝ}
    (hW3 : ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0, ∃ y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ)
    {z : Fin D → ℂ} {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s') (hsR : closedBall z s' ⊆ ball 0 R) :
    polyMax w z s ≤ max (pmoff S u z s') (-κ) := by
  refine polyMax_le' hs fun x hx => ?_
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := hsR (closedBall_subset_closedBall hss.le hx)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨y, hy, hyd, hwy⟩ := hW3 x hxB (min δ (s' - s)) (lt_min hδ (by linarith))
  have hyz : y ∈ closedBall z s' := by
    rw [mem_closedBall] at hx ⊢
    have := dist_triangle y x z
    linarith [min_le_right δ (s' - s)]
  have : u y ≤ pmoff S u z s' := le_pmo hub hsR ⟨hyz, hy.2⟩
  have : max (u y) (-κ) ≤ max (pmoff S u z s') (-κ) := max_le_max this le_rfl
  linarith [min_le_left δ (s' - s)]

end Osc

end

end ReciprocityTheory.AnForm.P.RegularChartScaling
end

namespace ReciprocityTheory.AnForm.P.RegularChartScaling

open MeasureTheory Metric Filter Topology Set
open ReciprocityTheory.AnForm.A

noncomputable section

variable {D : ℕ}

lemma closedBall_sub_of {z : Fin D → ℂ} {r s R : ℝ} (hz : z ∈ ball (0 : Fin D → ℂ) r)
    (hs : s ≤ R - r) : closedBall z s ⊆ ball 0 R := by
  intro x hx
  rw [mem_closedBall_iff_norm] at hx
  rw [mem_ball_zero_iff] at hz ⊢
  have := norm_sub_norm_le x z
  linarith

lemma fifth_volume_constant_nonneg {S : Finset (Fin D)} (m : Fin D → ℕ) {u : (Fin D → ℂ) → ℝ} {R C₅ : ℝ}
    (hR2 : R ≤ 2) (hR : 1 < R)
    (hb : ∀ z ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) :
    0 ≤ C₅ := by
  obtain ⟨x, hx, hf, hn⟩ := exists_far_point (0 : Fin D → ℂ) (s := 1 / 2) (by norm_num)
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := by rw [mem_ball_zero_iff]; simp at hn; linarith
  have hxA := not_mem_coordDiv_of (S := S) (by norm_num : (0 : ℝ) < 1 / 2) hf
  obtain ⟨h1, h2⟩ := hb x ⟨hxB, hxA⟩
  have h3 : 1 ≤ Real.log (rLoc S m x) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (rLoc_ge S m (norm_coord_le_of_ball hR2 hxB))
  nlinarith

theorem oscGen {S : Finset (Fin D)} (m : Fin D → ℕ) {u : (Fin D → ℂ) → ℝ} {R C₅ : ℝ}
    (hR2 : R ≤ 2) (hR : 5 / 4 < R)
    (hc : ContinuousOn u (ball 0 R \ coordDiv S)) (hp : IsPsh (ball 0 R \ coordDiv S) u)
    (hb : ∀ z ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅)
    {C₁ : ℝ} (hC₁ : 1 ≤ C₁) :
    ∃ C ℓ₀ : ℝ, 1 ≤ C ∧ ∀ t, 0 < t → ℓ₀ ≤ Real.log (1 / t) →
      Real.exp 1 ≤ Real.log (1 / t) ∧ C₁ * t ≤ (R - 5 / 4) / 2 ∧
      ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4),
        -C * Real.log (Real.log (1 / t)) ≤ pmoff S u z (t / (8 * C₁)) ∧
        pmoff S u z (C₁ * t) - pmoff S u z (t / (4 * C₁)) ≤ epsT C t := by
  have hC₅ : 0 ≤ C₅ := fifth_volume_constant_nonneg m hR2 (by linarith) hb
  have hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅ := fun x hx => (hb x hx).2
  set R' := R - 5 / 4 with hR'
  have hR'0 : 0 < R' := by linarith
  have hC0 : 0 < C₁ := by linarith
  have hlC : 0 ≤ Real.log C₁ := Real.log_nonneg hC₁
  have hl8 : 0 < Real.log (8 * C₁) := Real.log_pos (by linarith)
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set Λ := Real.log C₁ + Real.log (8 * C₁) with hΛ
  have hΛ0 : 0 < Λ := by linarith
  set K₁ := Real.exp 1 + mTot S m * (Real.log 4 + 2 * Real.log (8 * C₁) + 2) with hK₁
  have hmT := mTot_nonneg S m
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine ⟨6 * C₅ * Λ + 2 * C₅ + 1,
    max (max (Real.exp 1) K₁) (max (Real.log (2 * C₁ / R')) (2 * (Real.log C₁ - Real.log R'))),
    by have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 6) hC₅) hΛ0.le; linarith,
    fun t ht hℓ => ?_⟩
  set ℓ := Real.log (1 / t) with hℓdef
  have hℓt : Real.log t = -ℓ := by rw [hℓdef, one_div, Real.log_inv, neg_neg]
  have h1 : Real.exp 1 ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hℓ
  have h2 : K₁ ≤ ℓ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hℓ
  have h3 : Real.log (2 * C₁ / R') ≤ ℓ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hℓ
  have h4 : 2 * (Real.log C₁ - Real.log R') ≤ ℓ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hℓ
  have hℓ1 : 1 ≤ ℓ := he1.trans h1
  have hlℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) h1
  have hteq : t = Real.exp (-ℓ) := by rw [← hℓt, Real.exp_log ht]
  have hCt : C₁ * t ≤ R' / 2 := by
    have : 2 * C₁ / R' ≤ Real.exp ℓ := by
      rw [← Real.exp_log (by positivity : 0 < 2 * C₁ / R')]; exact Real.exp_le_exp.2 h3
    rw [hteq, Real.exp_neg]
    rw [div_le_iff₀ hR'0] at this
    have hE := Real.exp_pos ℓ
    rw [mul_inv_le_iff₀ hE]
    nlinarith
  refine ⟨h1, hCt, fun z hz => ?_⟩

  set κ := 2 * C₅ * Real.log ℓ + 1 with hκ
  obtain ⟨w, -, hW1, hW2, hW3⟩ := ext_exists S (by linarith : (0 : ℝ) < R) hC₅ hc hp hub κ
  have hwu : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ w x := fun x hx => by
    rw [hW2 x hx]; exact le_max_left _ _
  set s₈ := t / (8 * C₁) with hs₈
  set s₄ := t / (4 * C₁) with hs₄
  have hs₈0 : 0 < s₈ := by positivity
  have hs₄0 : 0 < s₄ := by positivity
  have hs84 : s₈ < s₄ := by
    rw [hs₈, hs₄]; exact div_lt_div_of_pos_left ht (by positivity) (by linarith)
  have hs4C : s₄ ≤ C₁ * t := by
    rw [hs₄, div_le_iff₀ (by positivity)]
    have h4c : 1 ≤ 4 * C₁ * C₁ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4c ht.le]
  have hsub : ∀ s, s ≤ R' → closedBall z s ⊆ ball 0 R := fun s hs =>
    closedBall_sub_of hz (by linarith)
  have hCtR : C₁ * t ≤ R' := by linarith

  have hlow : -C₅ * (2 * Real.log ℓ) ≤ pmoff S u z s₈ := by
    refine le_trans ?_ (pmo_lower hR2 hC₅ m hb hs₈0 (hsub _ (by linarith)))
    have hlog : Real.log (4 / s₈ ^ 2) = Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁) := by
      rw [Real.log_div (by norm_num) (by positivity), Real.log_pow, hs₈,
        Real.log_div ht.ne' (by positivity), hℓt]
      push_cast; ring
    rw [hlog]
    have hK0 : 0 < K₁ := by
      have : 0 ≤ mTot S m * (Real.log 4 + 2 * Real.log (8 * C₁) + 2) :=
        mul_nonneg hmT (by linarith)
      linarith [Real.exp_pos 1]
    have hA : Real.exp 1 + mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)) ≤ K₁ * ℓ := by
      rw [hK₁]
      have e1 : Real.exp 1 ≤ Real.exp 1 * ℓ := le_mul_of_one_le_right (Real.exp_pos 1).le hℓ1
      have e2 : mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)) ≤
          mTot S m * (Real.log 4 + 2 * Real.log (8 * C₁) + 2) * ℓ := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hmT
        nlinarith [mul_nonneg (by linarith : 0 ≤ Real.log 4 + 2 * Real.log (8 * C₁))
          (by linarith : (0:ℝ) ≤ ℓ - 1)]
      linarith
    have hApos : 0 < Real.exp 1 + mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)) := by
      have : 0 ≤ mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)) :=
        mul_nonneg hmT (by linarith)
      linarith [Real.exp_pos 1]
    have hB : Real.log (Real.exp 1 + mTot S m * (Real.log 4 + 2 * ℓ + 2 * Real.log (8 * C₁)))
        ≤ 2 * Real.log ℓ := by
      calc _ ≤ Real.log (K₁ * ℓ) := Real.log_le_log hApos hA
        _ = Real.log K₁ + Real.log ℓ := Real.log_mul hK0.ne' (by linarith)
        _ ≤ 2 * Real.log ℓ := by linarith [Real.log_le_log hK0 h2]
    have := mul_le_mul_of_nonneg_left hB hC₅
    linarith
  have hκlow : -κ < pmoff S u z s₄ := by
    have := pmo_mono hub hs₈0 hs84.le (hsub s₄ (by linarith))
    rw [hκ]; linarith

  set g : ℝ → ℝ := fun σ => polyMax w z (Real.exp σ) with hg
  have hconv := (polyMaxLogConvex_thm D (ball 0 R) w z R' isOpen_ball hW1 hR'0 (hsub R' le_rfl)).1
  set a := Real.log s₈ with ha
  set b := Real.log (C₁ * t) with hbdef
  set σ := Real.log R' with hσ
  have ha' : a = -ℓ - Real.log (8 * C₁) := by
    rw [ha, hs₈, Real.log_div ht.ne' (by positivity), hℓt]
  have hb' : b = Real.log C₁ - ℓ := by
    rw [hbdef, Real.log_mul hC0.ne' ht.ne', hℓt]; ring
  have hab : a < b := by rw [ha', hb']; linarith
  have hbσ : ℓ / 2 ≤ σ - b := by rw [hb']; linarith
  have hbσ' : b < σ := by linarith
  have hslope := hconv.slope_mono_adjacent (by simp only [Set.mem_Iic]; linarith)
    (by simp only [Set.mem_Iic]; exact le_rfl) hab hbσ'
  have hga : g a = polyMax w z s₈ := by simp only [hg, ha, Real.exp_log hs₈0]
  have hgb : g b = polyMax w z (C₁ * t) := by simp only [hg, hbdef, Real.exp_log (mul_pos hC0 ht)]
  have hgσ : g σ ≤ C₅ := by
    simp only [hg, hσ, Real.exp_log hR'0]
    refine polyMax_le' hR'0.le fun x hx => le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨y, hy, -, hwy⟩ := hW3 x (hsub R' le_rfl hx) δ hδ
    have : max (u y) (-κ) ≤ C₅ := max_le (hub y hy) (by
      have := mul_nonneg hC₅ (by linarith : (0:ℝ) ≤ Real.log ℓ); rw [hκ]; linarith)
    linarith
  have hga_low : -C₅ * (2 * Real.log ℓ) ≤ g a := by
    rw [hga]; exact hlow.trans (pmo_le_polyMax hW1.1 hwu hs₈0 (hsub _ (by linarith)))
  have hga_up : g a ≤ pmoff S u z s₄ := by
    rw [hga]
    have := polyMax_le_pmo hub hW3 hs₈0.le hs84 (hsub s₄ (by linarith))
    rwa [max_eq_left hκlow.le] at this
  have hgb_up : pmoff S u z (C₁ * t) ≤ g b := by
    rw [hgb]; exact pmo_le_polyMax hW1.1 hwu (by positivity) (hsub _ hCtR)
  have hgab : g a ≤ g b := by
    have := polyMax_mono' hW1.1 hs₈0.le (by linarith) (hsub _ hCtR) (z := z)
    rw [hga, hgb]; exact this

  have hCl : 0 ≤ C₅ * Real.log ℓ := mul_nonneg hC₅ (by linarith)
  have hN : g σ - g b ≤ C₅ + 2 * C₅ * Real.log ℓ := by linarith
  have hN0 : 0 ≤ C₅ + 2 * C₅ * Real.log ℓ := by linarith
  have hba : b - a = Λ := by rw [ha', hb', hΛ]; ring
  have hosc : g b - g a ≤ Λ * ((C₅ + 2 * C₅ * Real.log ℓ) / (ℓ / 2)) := by
    rw [hba] at hslope
    rw [div_le_iff₀ hΛ0] at hslope
    have q1 : (g σ - g b) / (σ - b) ≤ (C₅ + 2 * C₅ * Real.log ℓ) / (σ - b) :=
      div_le_div_of_nonneg_right hN (by linarith)
    have q2 : (C₅ + 2 * C₅ * Real.log ℓ) / (σ - b) ≤ (C₅ + 2 * C₅ * Real.log ℓ) / (ℓ / 2) :=
      div_le_div_of_nonneg_left hN0 (by linarith) hbσ
    have := mul_le_mul_of_nonneg_right (q1.trans q2) hΛ0.le
    linarith
  refine ⟨?_, ?_⟩
  · refine le_trans ?_ hlow
    have : 2 * C₅ ≤ 6 * C₅ * Λ + 2 * C₅ + 1 := by
      have := mul_nonneg hC₅ hΛ0.le; linarith
    have := mul_le_mul_of_nonneg_right this (by linarith : (0:ℝ) ≤ Real.log ℓ)
    linarith
  · have hℓ0 : 0 < ℓ := by linarith
    have key : Λ * ((C₅ + 2 * C₅ * Real.log ℓ) / (ℓ / 2)) ≤ epsT (6 * C₅ * Λ + 2 * C₅ + 1) t := by
      have e : Λ * ((C₅ + 2 * C₅ * Real.log ℓ) / (ℓ / 2)) =
          2 * Λ * (C₅ + 2 * C₅ * Real.log ℓ) / ℓ := by
        field_simp
      rw [e, epsT, ← hℓdef]
      refine div_le_div_of_nonneg_right ?_ hℓ0.le
      have n1 : C₅ ≤ C₅ * Real.log ℓ := le_mul_of_one_le_right hC₅ hlℓ
      have n2 : 0 ≤ Λ * (C₅ * Real.log ℓ) := mul_nonneg hΛ0.le hCl
      have n3 : Λ * C₅ ≤ Λ * (C₅ * Real.log ℓ) := mul_le_mul_of_nonneg_left n1 hΛ0.le
      have n4 : 0 ≤ (2 * C₅ + 1) * Real.log ℓ := mul_nonneg (by linarith) (by linarith)
      linarith
    linarith

end

end ReciprocityTheory.AnForm.P.RegularChartScaling
