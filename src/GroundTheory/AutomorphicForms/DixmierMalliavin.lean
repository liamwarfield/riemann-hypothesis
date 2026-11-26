module

public import GroundTheory.AutomorphicForms.DixmierMalliavinLine
public import GroundTheory.AutomorphicForms.TraceFormulaConvolution

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.DixmierMalliavinSeries
namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem contDiff_iteratedDeriv_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℕ) :
    ∀ {Ψ : E × ℝ → F}, ContDiff ℝ ∞ Ψ → ∀ s : ℝ,
      ContDiff ℝ ∞ (fun Y : E => iteratedDeriv p (fun t : ℝ => Ψ (Y, t)) s) := by
  induction p with
  | zero =>
    intro Ψ hΨ s
    simp only [iteratedDeriv_zero]
    exact hΨ.comp (contDiff_id.prodMk contDiff_const)
  | succ p ih =>
    intro Ψ hΨ s
    have hd : ∀ Y : E, deriv (fun t : ℝ => Ψ (Y, t)) = fun t => fderiv ℝ Ψ (Y, t) (0, 1) := by
      intro Y; funext t
      have h1 : HasFDerivAt Ψ (fderiv ℝ Ψ (Y, t)) (Y, t) :=
        (hΨ.differentiable (by simp)).differentiableAt.hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => ((Y, t) : E × ℝ)) (0, 1) t :=
        (hasDerivAt_const t Y).prodMk (hasDerivAt_id t)
      exact (h1.comp_hasDerivAt t h2).deriv
    have hΨ' : ContDiff ℝ ∞ (fun q : E × ℝ => fderiv ℝ Ψ q (0, 1)) :=
      (hΨ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
    have e : (fun Y : E => iteratedDeriv (p + 1) (fun t : ℝ => Ψ (Y, t)) s) =
        fun Y => iteratedDeriv p (fun t : ℝ => fderiv ℝ Ψ (Y, t) (0, 1)) s := by
      funext Y; rw [iteratedDeriv_succ', hd Y]
    rw [e]; exact ih hΨ' s

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

noncomputable def dirDeriv (X : 𝔤) (p : ℕ) (f : G → ℂ) (x : G) : ℂ :=
  iteratedDeriv p (fun t : ℝ => f (h.expG (t • X) * x)) 0

theorem iteratedDeriv_comp_expG_mul (X : 𝔤) (p : ℕ) (f : G → ℂ) (x : G) (s : ℝ) :
    iteratedDeriv p (fun t : ℝ => f (h.expG (t • X) * x)) s =
      h.dirDeriv X p f (h.expG (s • X) * x) := by
  have e := congrFun (iteratedDeriv_comp_add_const p (fun t : ℝ => f (h.expG (t • X) * x)) s) 0
  simp only [zero_add] at e
  rw [← e, dirDeriv]
  congr 1
  funext u
  rw [h.expG_add_smul, mul_assoc]

theorem contMDiff_expG_smul_mul (X : 𝔤) (x : G) :
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔤) ∞ (fun t : ℝ => h.expG (t • X) * x)) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  exact (h.contMDiff_expG_comp (contDiff_id.smul contDiff_const)).mul contMDiff_const

theorem contDiff_comp_expG_smul_mul {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (x : G) :
    ContDiff ℝ ∞ (fun t : ℝ => f (h.expG (t • X) * x)) := by
  let := h.chartedSpace
  exact (hf.comp (h.contMDiff_expG_smul_mul X x)).contDiff

theorem contDiff_comp_expG_smul_mul_mul_expG {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (g : G) :
    ContDiff ℝ ∞ (fun q : 𝔤 × ℝ => f (h.expG (q.2 • X) * (g * h.expG q.1))) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  have hm : ContMDiff 𝓘(ℝ, 𝔤 × ℝ) 𝓘(ℝ, 𝔤) ∞
      (fun q : 𝔤 × ℝ => h.expG (q.2 • X) * (g * h.expG q.1)) :=
    (h.contMDiff_expG_comp (contDiff_snd.smul contDiff_const)).mul
      (contMDiff_const.mul (h.contMDiff_expG_comp contDiff_fst))
  exact (hf.comp hm).contDiff

theorem dirDeriv_eq_zero_of_notMem {f : G → ℂ} (X : 𝔤) (p : ℕ) {x : G}
    (hx : x ∉ tsupport f) : h.dirDeriv X p f x = 0 := by
  have hc : Continuous (fun t : ℝ => h.expG (t • X) * x) :=
    (h.continuous_expG.comp (continuous_id.smul continuous_const)).mul continuous_const
  have h0 : h.expG ((0 : ℝ) • X) * x = x := by
    simp only [zero_smul]; rw [h.expG_zero, one_mul]
  have hev : (fun t : ℝ => f (h.expG (t • X) * x)) =ᶠ[𝓝 0] fun _ => (0 : ℂ) := by
    have := hc.continuousAt (x := 0)
    rw [ContinuousAt] at this
    simp only [h0] at this
    exact this.eventually (notMem_tsupport_iff_eventuallyEq.1 hx)
  rw [dirDeriv, hev.iteratedDeriv_eq]
  simp

theorem contDiff_dirDeriv_mul_expG {f : G → ℂ} (hf : letI := h.chartedSpace;
    ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (X : 𝔤) (p : ℕ) (g : G) :
    ContDiff ℝ ∞ (fun Y : 𝔤 => h.dirDeriv X p f (g * h.expG Y)) :=
  contDiff_iteratedDeriv_snd p (h.contDiff_comp_expG_smul_mul_mul_expG hf X g) 0

theorem mem_chart_source_self (g : G) : g ∈ (h.chart g).source := by
  let := h.chartedSpace
  exact mem_chart_source 𝔤 g

theorem chart_symm_chart {g x : G} (hx : x ∈ (h.chart g).source) :
    g * h.expG (h.chart g x) = x :=
  (h.chart g).left_inv hx

theorem exists_bound_dirDeriv {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) :
    ∃ M : ℕ → ℝ, (∀ p x, ‖h.dirDeriv X p f x‖ ≤ M p) ∧
      ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) →
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞
          (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x)) ∧
        HasCompactSupport (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) := by
  let := h.chartedSpace
  have := h.lieGroup ∞
  set K := tsupport f with hKdef
  have hK : IsCompact K := hfc
  let U : G → Set G := fun g => (h.chart g).source ∩ (h.chart g) ⁻¹' Metric.ball 0 1
  have hU : ∀ g, IsOpen (U g) := fun g =>
    (h.chart g).isOpen_inter_preimage Metric.isOpen_ball
  have hgU : ∀ g, g ∈ U g := fun g =>
    ⟨h.mem_chart_source_self g, by
      show h.chart g g ∈ Metric.ball 0 1
      rw [h.chart_self]; exact Metric.mem_ball_self one_pos⟩
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover U (fun g _ => (hU g).mem_nhds (hgU g))
  let β : ContDiffBump (0 : 𝔤) := ⟨1, 2, one_pos, one_lt_two⟩
  let Φ : G → ℕ → 𝔤 → ℂ := fun g p Y => (β Y : ℂ) * h.dirDeriv X p f (g * h.expG Y)
  have hΦ : ∀ g p, ContDiff ℝ ∞ (Φ g p) := fun g p =>
    (Complex.ofRealCLM.contDiff.comp β.contDiff).mul (h.contDiff_dirDeriv_mul_expG hf X p g)
  have hΦc : ∀ g p, HasCompactSupport (Φ g p) := fun g p =>
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  have hS : ∀ g k p, ∃ C, ∀ Y, ‖iteratedFDeriv ℝ k (Φ g p) Y‖ ≤ C := fun g k p =>
    ((hΦ g p).continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      ((hΦc g p).iteratedFDeriv k)
  choose S hS using hS
  have hS0 : ∀ g k p, 0 ≤ S g k p := fun g k p => (norm_nonneg _).trans (hS g k p 0)
  let M : ℕ → ℝ := fun p => ∑ g ∈ t, ∑ k ∈ Finset.range (p + 1), S g k p
  have hM0 : ∀ p, 0 ≤ M p := fun p =>
    Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun k _ => hS0 g k p
  have hSM : ∀ p, ∀ g ∈ t, ∀ k ≤ p, S g k p ≤ M p := by
    intro p g hg k hk
    calc S g k p ≤ ∑ k ∈ Finset.range (p + 1), S g k p :=
          Finset.single_le_sum (fun k _ => hS0 g k p) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
      _ ≤ M p := Finset.single_le_sum (f := fun g => ∑ k ∈ Finset.range (p + 1), S g k p)
          (fun g _ => Finset.sum_nonneg fun k _ => hS0 g k p) hg

  have hloc : ∀ g p x, x ∈ U g → h.dirDeriv X p f x = Φ g p (h.chart g x) := by
    intro g p x hx
    have hb : β (h.chart g x) = 1 :=
      β.one_of_mem_closedBall (Metric.ball_subset_closedBall hx.2)
    simp only [Φ, hb, Complex.ofReal_one, one_mul, h.chart_symm_chart hx.1]
  have hzero : ∀ p x, x ∉ K → h.dirDeriv X p f x = 0 := fun p x hx =>
    h.dirDeriv_eq_zero_of_notMem X p hx
  refine ⟨M, ?_, ?_⟩
  · intro p x
    by_cases hx : x ∈ K
    · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (htK hx)
      rw [hloc g p x hxg]
      calc ‖Φ g p (h.chart g x)‖ = ‖iteratedFDeriv ℝ 0 (Φ g p) (h.chart g x)‖ := by
            rw [norm_iteratedFDeriv_zero]
        _ ≤ S g 0 p := hS g 0 p _
        _ ≤ M p := hSM p g hg 0 (Nat.zero_le p)
    · rw [hzero p x hx, norm_zero]; exact hM0 p
  intro c hc

  let F : G → 𝔤 → ℂ := fun g Y => ∑' p, (c p) • Φ g p Y
  have hF : ∀ g ∈ t, ContDiff ℝ ∞ (F g) := by
    intro g hg
    refine contDiff_tsum (N := ⊤) (v := fun k p => |c p| * S g k p)
      (fun p => (hΦ g p).const_smul (c p)) ?_ ?_
    · intro k _
      rw [← summable_nat_add_iff k]
      refine Summable.of_nonneg_of_le (fun p => mul_nonneg (abs_nonneg _) (hS0 g k _))
        (fun p => mul_le_mul_of_nonneg_left (hSM (p + k) g hg k (Nat.le_add_left k p))
          (abs_nonneg _)) ?_
      exact (summable_nat_add_iff k).2 hc
    · intro k p Y _
      rw [iteratedFDeriv_const_smul_apply' ((hΦ g p).contDiffAt.of_le (by exact_mod_cast le_top)), norm_smul,
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hS g k p Y) (abs_nonneg _)
  have hsupp : ∀ x, x ∉ K → ∑' p, (c p : ℂ) * h.dirDeriv X p f x = 0 := by
    intro x hx; simp [hzero _ x hx]
  refine ⟨?_, HasCompactSupport.intro hK hsupp⟩
  intro x
  by_cases hx : x ∈ K
  · obtain ⟨g, hg, hxg⟩ := Set.mem_iUnion₂.1 (htK hx)
    have hev : (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) =ᶠ[𝓝 x]
        fun x => F g (chartAt 𝔤 g x) := by
      filter_upwards [(hU g).mem_nhds hxg] with x' hx'
      show _ = F g (h.chart g x')
      simp only [F, hloc g _ x' hx', Complex.real_smul]
    have hch : ContMDiffAt 𝓘(ℝ, 𝔤) 𝓘(ℝ, 𝔤) ∞ (chartAt 𝔤 g) x := by
      have := contMDiffAt_extChartAt' (I := 𝓘(ℝ, 𝔤)) (n := ∞) (x := g) hxg.1
      simpa [extChartAt] using this
    exact (((hF g hg).contMDiff.contMDiffAt).comp x hch).congr_of_eventuallyEq hev
  · have hev : (fun x => ∑' p, (c p : ℂ) * h.dirDeriv X p f x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx] with x' hx'
      exact hsupp x' hx'
    exact contMDiffAt_const.congr_of_eventuallyEq hev

end IsExpLieAlgebra

end GroundTheory.Automorphic
end

namespace GroundTheory.Automorphic

open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

theorem exists_decomp_direction {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f₁ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f₁) ∧
      HasCompactSupport f₁ ∧
      ∃ g k : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ k ∧ tsupport g ⊆ Icc (-ε) ε ∧
        tsupport k ⊆ Icc (-ε) ε ∧
        ∀ x, f x = (∫ t, g t * f₁ (h.expG (t • X) * x)) + ∫ t, k t * f (h.expG (t • X) * x) := by
  obtain ⟨M, hM, hser⟩ := h.exists_bound_dirDeriv hf hfc X
  obtain ⟨c, g, k, hg, hk, hgs, hks, hc, hid⟩ := exists_dixmierMalliavin_line M hε
  obtain ⟨hf₁, hf₁c⟩ := hser c hc
  refine ⟨_, hf₁, hf₁c, g, k, hg, hk, hgs, hks, fun x => ?_⟩
  set F : ℝ → ℂ := fun t => f (h.expG (t • X) * x) with hFdef
  have hF : ContDiff ℝ ∞ F := h.contDiff_comp_expG_smul_mul hf X x
  have hD : ∀ p t, iteratedDeriv p F t = h.dirDeriv X p f (h.expG (t • X) * x) :=
    fun p t => h.iteratedDeriv_comp_expG_mul X p f x t
  have key := hid F hF (fun p t _ => by rw [hD]; exact hM p _)
  have hF0 : F 0 = f x := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero, one_mul]
  rw [hF0] at key
  rw [key]
  congr 1
  · have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    have hcont : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * g t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcont p).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * ‖g t‖ := by
      intro p t
      simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_assoc (|c p|)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (c p))
      have : ‖iteratedDeriv p F t‖ ≤ M p := by rw [hD]; exact hM p _
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hgi : Integrable (fun t => ‖g t‖) :=
      (hg.continuous.integrable_of_hasCompactSupport hgc).norm
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, ‖g t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e1 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e1]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    rw [← tsum_mul_left]
    congr 1
    funext p
    simp only [T, hD]
    ring
  · congr 1; funext t; rw [mul_comm]

theorem exists_decomp_iter {ε : ℝ} (hε : 0 < ε) : ∀ {d : ℕ} (X : Fin d → 𝔤) (f : G → ℂ),
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) → HasCompactSupport f →
    ∃ (m : ℕ) (F : Fin m → G → ℂ) (K : Fin m → (Fin d → ℝ) → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (F i)) ∧
        HasCompactSupport (F i)) ∧
      (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ x, f x = ∑ i, ∫ t, K i t * F i (h.revProdExp X t * x) := by
  intro d
  induction d with
  | zero =>
    intro X f hf hfc
    refine ⟨1, fun _ => f, fun _ _ => 1, fun _ => ⟨hf, hfc⟩, fun _ => ⟨contDiff_const, ?_⟩,
      fun x => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp only [h.revProdExp_zero, one_mul, integral_const, hv, one_smul, Fin.sum_univ_one]
  | succ d ih =>
    intro X f hf hfc
    let := h.chartedSpace
    obtain ⟨f₁, hf₁, hf₁c, g, k, hg, hk, hgs, hks, hdec⟩ :=
      h.exists_decomp_direction hf hfc (X 0) hε
    obtain ⟨m₁, F₁, K₁, hF₁, hK₁, hd₁⟩ := ih (Fin.tail X) f₁ hf₁ hf₁c
    obtain ⟨m₂, F₂, K₂, hF₂, hK₂, hd₂⟩ := ih (Fin.tail X) f hf hfc
    refine ⟨m₁ + m₂, Fin.append F₁ F₂,
      Fin.append (fun i t => g (t 0) * K₁ i (Fin.tail t)) (fun i t => k (t 0) * K₂ i (Fin.tail t)),
      ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using hF₁ i
      · simpa only [Fin.append_right] using hF₂ i
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨contDiff_cons_kernel hg (hK₁ i).1, tsupport_cons_kernel hε.le hgs (hK₁ i).2⟩
      · simp only [Fin.append_right]
        exact ⟨contDiff_cons_kernel hk (hK₂ i).1, tsupport_cons_kernel hε.le hks (hK₂ i).2⟩
    · intro x
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec x]
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le hg.continuous hgs (fun i => (hK₁ i).1.continuous)
          (fun i => (hK₁ i).2) (fun i => (hF₁ i).1.continuous) hd₁ x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hk.continuous hks (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => (hF₂ i).1.continuous) hd₂ x).symm

end IsExpLieAlgebra

theorem dixmierMalliavin (h : IsExpLieAlgebra G 𝔤) [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (f : G → ℂ)
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (hfc : HasCompactSupport f) :
    ∃ (n : ℕ) (φ ψ : Fin n → G → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (φ i)) ∧
        HasCompactSupport (φ i) ∧
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧ HasCompactSupport (ψ i)) ∧
      f = ∑ i, groupConv μ (φ i) (ψ i) := by
  let := h.chartedSpace
  let b := Module.finBasis ℝ 𝔤
  obtain ⟨ε, hε, hdens⟩ := h.exists_smooth_density_prodExp μ b
  obtain ⟨m, F, K, hF, hK, hd⟩ := h.exists_decomp_iter hε (⇑b) f hf hfc
  have hK' : ∀ i, ContDiff ℝ ∞ (fun t => K i (-t)) ∧
      tsupport (fun t => K i (-t)) ⊆ Metric.closedBall 0 ε := by
    intro i
    refine ⟨(hK i).1.comp contDiff_neg, ?_⟩
    intro t ht
    have : -t ∈ tsupport (K i) := by
      have := tsupport_comp_subset_preimage (K i) (f := fun t : Fin _ → ℝ => -t) continuous_neg ht
      simpa using this
    have := (hK i).2 this
    simpa [mem_closedBall_zero_iff, norm_neg] using this
  choose κ hκs hκc hκ using fun i => hdens (fun t => K i (-t)) (hK' i).1 (hK' i).2
  refine ⟨m, κ, F, fun i => ⟨hκs i, hκc i, (hF i).1, (hF i).2⟩, ?_⟩
  funext x
  rw [hd x, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [groupConv, hκ i (fun y => F i (y⁻¹ * x))
    ((hF i).1.continuous.comp (continuous_inv.mul continuous_const))]
  have e : ∀ t : Fin (Module.finrank ℝ 𝔤) → ℝ, K i (-t) * F i ((h.prodExp (⇑b) t)⁻¹ * x) =
      (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) (-t) := by
    intro t
    have := h.revProdExp_inv (⇑b) (-t)
    rw [neg_neg] at this
    simp only [← this, inv_inv]
  simp_rw [e]
  exact (integral_neg_eq_self (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) volume).symm

end GroundTheory.Automorphic
