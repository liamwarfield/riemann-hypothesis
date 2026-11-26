module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open MeasureTheory Metric Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)

noncomputable section

namespace BoundedPshData

variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (B : BoundedPshData A)

def u (j : Fin B.N) : (Fin D → ℂ) → ℝ := B.chartFun B.ph j

def smoothed (ρ : Mollifier D) (t : ℝ) (j : Fin B.N) : (Fin D → ℂ) → ℝ :=
  molli ρ t (B.u j)

def phReg (ρ : Mollifier D) (t : ℝ) (j : Fin B.N) (x : X) : ℝ :=
  B.smoothed ρ t j (B.chart j x) - B.q j (B.chart j x)

def regularised (ρ : Mollifier D) (t ε : ℝ) (η : Fin B.N → X → ℝ) : X → ℝ :=
  B.glue (fun j x => B.phReg ρ t j x + 4 * ε * η j x) ε

end BoundedPshData

def BoundedChartComparison.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (B : BoundedPshData A) (ρ : Mollifier D), ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∀ j k : Fin B.N, ∀ x ∈ B.mid j ∩ B.mid k,
        |B.phReg ρ t j x - B.phReg ρ t k x| ≤ C / Real.log t⁻¹ + C * t

def BoundedGlue.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (B : BoundedPshData A) (ρ : Mollifier D) (η : Fin B.N → X → ℝ) (Cη t ε : ℝ),
    B.IsCutoffFamily η Cη → 0 < t → 0 < ε →
    (∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ (B.chart j).target) →
    (∀ j k, ∀ x ∈ B.mid j ∩ B.mid k, |B.phReg ρ t j x - B.phReg ρ t k x| ≤ ε) →
    A.Smooth (B.regularised ρ t ε η) ∧
      ∀ k : Fin B.N, ∀ x ∈ B.mid k, ∀ w : Fin D → ℂ,
        -(4 * Cη * ε) * ‖w‖ ^ 2 ≤ levi (B.chartFun (B.regularised ρ t ε η) k) (B.chart k x) w

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PCutoffs
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Set Filter Topology
open scoped ContDiff Manifold
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas IsCompatChart)
open ReciprocityTheory.AnForm.M.PLAux (chartPush chartPush_eq_zero isCompact_symm_image smooth_chartPush
  contDiffOn_compat)

noncomputable section

theorem exists_smooth_bump_of_isCompact {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K V : Set E} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧ (∀ y ∈ K, g y = 1) ∧
      IsCompact (tsupport g) ∧ tsupport g ⊆ V := by
  obtain ⟨W, hWo, hKW, hWV, hWc⟩ := exists_open_between_and_isCompact_closure hK hV hKV
  have hd : Disjoint Wᶜ K := Set.disjoint_compl_left_iff_subset.2 hKW
  obtain ⟨f, hf, hrange, h0, h1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (I := 𝓘(ℝ, E)) (n := ⊤) hWo.isClosed_compl hK.isClosed hd
  have hsupp : tsupport f ⊆ closure W := by
    refine closure_mono fun y hy => ?_
    by_contra hyW
    exact hy ((h0 y).1 hyW)
  refine ⟨f, contMDiff_iff_contDiff.1 hf, fun y => hrange ⟨y, rfl⟩, fun y hy => (h1 y).1 hy,
    hWc.of_isClosed_subset (isClosed_tsupport f) hsupp, hsupp.trans hWV⟩

theorem levi_lower_bound_of_isCompact {D : ℕ} {f : (Fin D → ℂ) → ℝ} {U K : Set (Fin D → ℂ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ K, ∀ w, -C * ‖w‖ ^ 2 ≤ levi f y w := by
  have hS : IsCompact (K ×ˢ sphere (0 : Fin D → ℂ) 1) := hK.prod (isCompact_sphere 0 1)
  have hc : ContinuousOn (fun p : (Fin D → ℂ) × (Fin D → ℂ) => levi f p.1 p.2)
      (K ×ˢ sphere (0 : Fin D → ℂ) 1) :=
    (ReciprocityTheory.AnForm.continuousOn_levi hU hf).mono (prod_mono hKU (subset_univ _))
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, fun y hy w => ?_⟩
  by_cases hw : w = 0
  · subst hw
    simp [ReciprocityTheory.AnForm.levi_zero]
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hu : ‖‖w‖⁻¹ • w‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
  have hb := hC (y, ‖w‖⁻¹ • w) ⟨hy, by simpa using hu⟩
  have hb' : -max C 0 ≤ levi f y (‖w‖⁻¹ • w) := by
    have := (abs_le.1 (Real.norm_eq_abs _ ▸ hb)).1
    linarith [le_max_left C 0]
  have hw' : w = ‖w‖ • (‖w‖⁻¹ • w) := by
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [hw', ReciprocityTheory.AnForm.levi_smul_dir]
  have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hb' h2
  have hnn : ‖‖w‖ • (‖w‖⁻¹ • w)‖ = ‖w‖ := by rw [← hw']
  rw [hnn]
  linarith

theorem CutoffsExist.proof : CutoffsExist.Statement := by
  intro X _ _ _ D A P
  have hb : ∀ j, ∃ g : (Fin D → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ (∀ y, 0 ≤ g y ∧ g y ≤ 1) ∧
      (∀ y ∈ P.chart j '' closure (P.inner j), g y = 1) ∧ IsCompact (tsupport g) ∧
      tsupport g ⊆ P.chartMid j := by
    intro j
    have hcl : closure (P.inner j) ⊆ (P.chart j).source :=
      (P.closure_inner j).trans (P.mid_subset_source j)
    refine exists_smooth_bump_of_isCompact
      (isClosed_closure.isCompact.image_of_continuousOn ((P.chart j).continuousOn.mono hcl))
      ((P.chart j).continuousOn_symm.isOpen_inter_preimage (P.chart j).open_target
        (P.isOpen_mid j)) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨(P.chart j).map_source (hcl hx), by
      rw [mem_preimage, (P.chart j).left_inv (hcl hx)]; exact P.closure_inner j hx⟩
  choose g hgs hg01 hg1 hgc hgt using hb
  have hgt' : ∀ j, tsupport (g j) ⊆ (P.chart j).target := fun j => (hgt j).trans inter_subset_left
  have hcp : ∀ j x, 0 ≤ chartPush (P.chart j) (g j) x ∧ chartPush (P.chart j) (g j) x ≤ 1 := by
    intro j x
    unfold chartPush
    by_cases hx : x ∈ (P.chart j).source
    · rw [indicator_of_mem hx]; exact hg01 j _
    · rw [indicator_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩
  have hsm : ∀ j, A.Smooth (fun x => chartPush (P.chart j) (g j) x - 1) := by
    intro j a
    exact ContDiffOn.sub (f := chartPush (P.chart j) (g j) ∘ (A.chart a).symm)
      (smooth_chartPush (P.compat j) (hgs j) (hgc j) (hgt' j) a) contDiffOn_const
  have hC : ∀ j k, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ P.chart k '' closure (P.mid k), ∀ w,
      -C * ‖w‖ ^ 2 ≤ levi ((fun x => chartPush (P.chart j) (g j) x - 1) ∘ (P.chart k).symm) y w := by
    intro j k
    have h := contDiffOn_compat (P.compat k) isOpen_univ (hsm j)
    rw [preimage_univ, inter_univ] at h
    refine levi_lower_bound_of_isCompact (P.chart k).open_target (h.of_le (WithTop.coe_le_coe.2 le_top))
      (isClosed_closure.isCompact.image_of_continuousOn
        ((P.chart k).continuousOn.mono (P.closure_mid k))) ?_
    rintro _ ⟨x, hx, rfl⟩
    exact (P.chart k).map_source (P.closure_mid k hx)
  choose C hC0 hC using hC
  refine ⟨fun j x => chartPush (P.chart j) (g j) x - 1, ∑ j, ∑ k, C j k, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro j a
    exact (hsm j a).mono (inter_subset_inter_right _ (preimage_mono (subset_univ _)))
  · intro j x _
    constructor <;> linarith [hcp j x]
  · intro j x hx
    have hs : x ∈ (P.chart j).source := P.mid_subset_source j (P.inner_subset_mid j hx)
    have h1 : chartPush (P.chart j) (g j) x = 1 := by
      unfold chartPush
      rw [indicator_of_mem hs]
      exact hg1 j _ ⟨x, subset_closure hx, rfl⟩
    simp [h1]
  · intro j
    refine ⟨(P.chart j).symm '' tsupport (g j), (isCompact_symm_image (hgc j) (hgt' j)).isClosed,
      ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact (hgt j hy).2
    · intro x hx
      simp [chartPush_eq_zero (P.chart j) hx.2]
  · intro j k x hx w
    have h := hC j k (P.chart k x) ⟨x, subset_closure hx.2, rfl⟩ w
    have hle : C j k ≤ ∑ j, ∑ k, C j k :=
      (Finset.single_le_sum (fun k _ => hC0 j k) (Finset.mem_univ k)).trans
        (Finset.single_le_sum (f := fun j => ∑ k, C j k)
          (fun j _ => Finset.sum_nonneg fun k _ => hC0 j k) (Finset.mem_univ j))
    have h2 : 0 ≤ ‖w‖ ^ 2 := by positivity
    nlinarith

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncPsh
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (IsPsh)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

def TruncPsh.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ δ B : ℝ, 0 < δ ∧ ∀ j : Fin R.N, ∃ V : Set (Fin D → ℂ), IsOpen V ∧
      V ⊆ (R.chart j).target ∧ (∀ x ∈ R.mid j, closedBall (R.chart j x) δ ⊆ V) ∧
      ∀ K : ℝ, IsPsh V (R.trunc K j) ∧ ∀ y ∈ V, R.trunc K j y ≤ max B (-K)

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.PPolyMaxLowerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Set
open ReciprocityTheory.AnForm.A (polyMax coordDiv limsupExt)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

theorem PolyMaxLowerBound.exists_pos_le {n : ℕ} (f : Fin n → ℝ) (hf : ∀ j, 0 < f j) :
    ∃ δ, 0 < δ ∧ ∀ j, δ ≤ f j := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, one_pos, fun j => (IsEmpty.false j).elim⟩
  · obtain ⟨j₀, hj₀⟩ := Finite.exists_min f
    exact ⟨f j₀, hf j₀, hj₀⟩

theorem PolyMaxLowerBound.chart_margin {X : Type} [TopologicalSpace X] [CompactSpace X] {D : ℕ}
    {A : FinHolAtlas D X} (R : RegChartData A) (j : Fin R.N) :
    ∃ δ Q : ℝ, 0 < δ ∧ 0 ≤ Q ∧ ∀ x ∈ R.mid j, ∀ y ∈ closedBall (R.chart j x) δ,
      y ∈ (R.chart j).target ∧ |R.q j y| ≤ Q := by
  have hK : IsCompact ((R.chart j) '' closure (R.mid j)) :=
    isClosed_closure.isCompact.image_of_continuousOn
      ((R.chart j).continuousOn.mono (R.closure_mid j))
  have hKT : (R.chart j) '' closure (R.mid j) ⊆ (R.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (R.chart j).map_source (R.closure_mid j hx)
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open (R.chart j).open_target hKT
  obtain ⟨Q, hQ⟩ := (hK.cthickening (r := δ)).exists_bound_of_continuousOn
    ((R.q_smooth j).continuousOn.mono hsub)
  refine ⟨δ, max Q 0, hδ, le_max_right _ _, fun x hx y hy => ?_⟩
  have hy' : y ∈ cthickening δ ((R.chart j) '' closure (R.mid j)) :=
    closedBall_subset_cthickening (mem_image_of_mem _ (subset_closure hx)) δ hy
  refine ⟨hsub hy', ?_⟩
  have := hQ y hy'
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem PolyMaxLowerBound.exists_far_point {D : ℕ} (z : Fin D → ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ y ∈ closedBall z t, ∀ i, t / 2 ≤ ‖y i‖ := by
  classical
  refine ⟨fun i => if t / 2 ≤ ‖z i‖ then z i else z i + (t : ℂ), ?_, fun i => ?_⟩
  · rw [mem_closedBall, dist_pi_le_iff ht.le]
    intro i
    by_cases h : t / 2 ≤ ‖z i‖
    · simp only [if_pos h, dist_self]; exact ht.le
    · simp only [if_neg h, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht, le_refl]
  · by_cases h : t / 2 ≤ ‖z i‖
    · simp only [if_pos h]; exact h
    · simp only [if_neg h]
      replace h := not_le.mp h
      have h1 : ‖((t : ℝ) : ℂ)‖ ≤ ‖z i + (t : ℂ)‖ + ‖z i‖ := by
        calc ‖((t : ℝ) : ℂ)‖ = ‖(z i + (t : ℂ)) - z i‖ := by ring_nf
          _ ≤ ‖z i + (t : ℂ)‖ + ‖z i‖ := norm_sub_le _ _
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht] at h1
      linarith

theorem PolyMaxLowerBound.log_inv_half_sq {t : ℝ} (ht : 0 < t) :
    Real.log ((t / 2) ^ 2)⁻¹ = 2 * Real.log 2 + 2 * Real.log t⁻¹ := by
  have h : ((t / 2) ^ 2)⁻¹ = (2 * t⁻¹) ^ 2 := by field_simp
  rw [h, Real.log_pow, Real.log_mul (by norm_num) (inv_ne_zero ht.ne')]
  push_cast; ring

theorem PolyMaxLowerBound.proof : PolyMaxLowerBound.Statement := by
  intro X _ _ _ D A R
  obtain ⟨B, hB⟩ := R.f_bdd
  choose δf Qf hδf hQf hball using PolyMaxLowerBound.chart_margin R
  obtain ⟨δ, hδ0, hδle⟩ := PolyMaxLowerBound.exists_pos_le δf hδf
  set Q : ℝ := ∑ j, Qf j with hQdef
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun j _ => hQf j
  have hQj : ∀ j, Qf j ≤ Q := fun j =>
    Finset.single_le_sum (f := Qf) (fun k _ => hQf k) (Finset.mem_univ j)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  set Λ : ℝ := Real.exp 1 + |B| + 2 * D * Real.log 2 + 2 * D with hΛdef
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
  have hΛ1 : 1 ≤ Λ := by
    have : 0 ≤ 2 * (D : ℝ) * Real.log 2 := by positivity
    have : 0 ≤ |B| := abs_nonneg B
    linarith
  have hlogΛ : 0 ≤ Real.log Λ := Real.log_nonneg hΛ1
  set C : ℝ := Q + |R.Clog| * (Real.log Λ + 1) with hCdef
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, min δ (Real.exp (-Real.exp 1)), lt_min hδ0 (Real.exp_pos _), ?_⟩
  intro t ht htt K j x hx
  have htδ : t ≤ δ := (htt.trans_le (min_le_left _ _)).le
  have hte : t < Real.exp (-Real.exp 1) := htt.trans_le (min_le_right _ _)
  set ℓ : ℝ := Real.log t⁻¹ with hℓdef
  have hℓe : Real.exp 1 < ℓ := by
    rw [hℓdef, Real.lt_log_iff_exp_lt (inv_pos.2 ht)]
    rw [Real.exp_neg] at hte
    exact (lt_inv_comm₀ ht (Real.exp_pos _)).1 hte
  have hℓ1 : 1 ≤ ℓ := he1.trans hℓe.le
  have hlogℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hℓe.le
  obtain ⟨y, hy, hyn⟩ := PolyMaxLowerBound.exists_far_point (R.chart j x) ht
  obtain ⟨hyT, hqy⟩ := hball j x hx y (closedBall_subset_closedBall (htδ.trans (hδle j)) hy)
  have hyD : y ∉ coordDiv (R.S j) := by
    rintro ⟨i, -, hi⟩
    have := hyn i
    rw [hi, norm_zero] at this
    linarith
  have hsrc := (R.chart j).map_target hyT
  have hYo : (R.chart j).symm y ∈ R.Yo :=
    (R.mem_Yo j _ hsrc).2 (by rwa [(R.chart j).right_inv hyT])
  have hr1 := R.one_le_r _ hYo

  have hsum : ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ D * (2 * Real.log 2 + 2 * ℓ) := by
    have hterm : ∀ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ 2 * Real.log 2 + 2 * ℓ := by
      intro i _
      rw [← PolyMaxLowerBound.log_inv_half_sq ht]
      have h2 : 0 < t / 2 := by linarith
      have hyi : 0 < ‖y i‖ := h2.trans_le (hyn i)
      apply Real.log_le_log (by positivity)
      exact inv_anti₀ (by positivity) (pow_le_pow_left₀ h2.le (hyn i) 2)
    have hM : 0 ≤ 2 * Real.log 2 + 2 * ℓ := by linarith
    calc ∑ i ∈ R.S j, Real.log (‖y i‖ ^ 2)⁻¹ ≤ ∑ i ∈ R.S j, (2 * Real.log 2 + 2 * ℓ) :=
          Finset.sum_le_sum hterm
      _ = (R.S j).card * (2 * Real.log 2 + 2 * ℓ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ D * (2 * Real.log 2 + 2 * ℓ) := by
          apply mul_le_mul_of_nonneg_right _ hM
          have := Finset.card_le_univ (R.S j)
          rw [Fintype.card_fin] at this
          exact_mod_cast this
  have hrle : R.r ((R.chart j).symm y) ≤ Λ * ℓ := by
    rw [R.r_chart j y ⟨hyT, hyD⟩]
    have hf : R.f j y ≤ |B| := (le_abs_self _).trans ((hB j y hyT).trans (le_abs_self B))
    have hA : 0 ≤ Real.exp 1 + |B| + 2 * D * Real.log 2 := by
      have : 0 ≤ 2 * (D : ℝ) * Real.log 2 := by positivity
      have : 0 ≤ |B| := abs_nonneg B
      linarith
    have : Real.exp 1 + |B| + 2 * D * Real.log 2 ≤ (Real.exp 1 + |B| + 2 * D * Real.log 2) * ℓ :=
      le_mul_of_one_le_right hA hℓ1
    rw [hΛdef]
    nlinarith
  have hlogr : Real.log (R.r ((R.chart j).symm y)) ≤ Real.log Λ + Real.log ℓ := by
    rw [← Real.log_mul (by linarith) (by linarith)]
    exact Real.log_le_log (by linarith) hrle
  have hlogr0 : 0 ≤ Real.log (R.r ((R.chart j).symm y)) := Real.log_nonneg hr1
  have hph := R.ph_ge _ hYo

  have hq : -Q ≤ R.q j y := by
    have := (abs_le.1 (hqy.trans (hQj j))).1
    linarith
  have h1 : -(|R.Clog| * Real.log (R.r ((R.chart j).symm y))) ≤
      -R.Clog * Real.log (R.r ((R.chart j).symm y)) := by
    have := mul_le_mul_of_nonneg_right (le_abs_self R.Clog) hlogr0
    linarith
  have h2 : |R.Clog| * Real.log (R.r ((R.chart j).symm y)) ≤
      |R.Clog| * (Real.log Λ + 1) * Real.log ℓ := by
    have h3 : Real.log Λ + Real.log ℓ ≤ (Real.log Λ + 1) * Real.log ℓ := by nlinarith
    calc |R.Clog| * Real.log (R.r ((R.chart j).symm y)) ≤ |R.Clog| * (Real.log Λ + Real.log ℓ) :=
          mul_le_mul_of_nonneg_left hlogr (abs_nonneg _)
      _ ≤ |R.Clog| * ((Real.log Λ + 1) * Real.log ℓ) :=
          mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
      _ = _ := by ring
  have hQℓ : Q ≤ Q * Real.log ℓ := le_mul_of_one_le_right hQ0 hlogℓ
  have hu : -C * Real.log ℓ ≤ R.u j y := by
    show -C * Real.log ℓ ≤ R.q j y + R.ph ((R.chart j).symm y)
    rw [hCdef]
    nlinarith
  have htr : R.trunc K j y = max (R.u j y) (-K) := by
    simp only [RegChartData.trunc, limsupExt, if_neg hyD]

  unfold polyMax
  by_cases hb : BddAbove (R.trunc K j '' closedBall (R.chart j x) t)
  · refine le_trans ?_ (le_csSup hb (mem_image_of_mem _ hy))
    rw [htr]
    exact hu.trans (le_max_left _ _)
  · rw [Real.sSup_of_not_bddAbove hb]
    have : 0 ≤ C * Real.log ℓ := mul_nonneg hC0 (by linarith)
    linarith

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.StLogCoverDescent
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric Filter Topology

noncomputable section

def LogCoverDescent.Statement : Prop :=
  ∀ (n a : ℕ) (h : a ≤ n) (φ : (Fin n → ℂ) → ℂ), AnalyticOnNhd ℂ φ (logCover h) →
    (∀ (i : Fin a), ∀ w ∈ logCover h,
      φ (w + Pi.single (Fin.castLE h i) (2 * Real.pi * Complex.I)) = φ w) →
    AnalyticOnNhd ℂ (fun z => φ (logLift a z)) (puncturedChart h (ball 0 1)) ∧
      ∀ w ∈ logCover h, φ (logLift a (expCover a w)) = φ w

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsTruncTransfer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)

noncomputable section

def TruncTransfer.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ δ L B : ℝ, 0 < δ ∧ 1 ≤ L ∧ ∀ (K : ℝ) (j k : Fin R.N),
      ∀ x ∈ R.mid j ∩ R.mid k, ∀ t : ℝ, 0 < t → t < δ → ∀ y ∈ closedBall (R.chart j x) t,
        R.trunc K j y ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
          (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t

end

end GroundTheory.Heights₂.Heights.Regular
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Regularisation.StatementsChartBounds
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (Mollifier)

noncomputable section

def ChartMollifiedBounds.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ)
    (A : ReciprocityTheory.AnForm.M.FinHolAtlas D X) (R : RegChartData A) (ρ : Mollifier D),
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      (∀ j, ∀ x ∈ closure (R.mid j), closedBall (R.chart j x) t ⊆ (R.chart j).target) ∧
      ∀ K : ℝ, 0 ≤ K → ∀ j : Fin R.N, ∀ x ∈ R.mid j,
        -K - C ≤ R.phReg ρ K t j x ∧ R.phReg ρ K t j x ≤ C ∧
          (x ∈ R.Yo → R.ph x ≤ R.phReg ρ K t j x)

end

end GroundTheory.Heights₂.Heights.Regular
end
