module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.ConvDensOfOpen
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

private theorem fderiv2_add_lemma {D : ℕ} {g₁ g₂ : (Fin D → ℂ) → ℝ} {U : Set (Fin D → ℂ)}
    {y : Fin D → ℂ} (hU : IsOpen U) (hy : y ∈ U) (h₁ : ContDiffOn ℝ 2 g₁ U) (h₂ : ContDiffOn ℝ 2 g₂ U) :
    fderiv ℝ (fderiv ℝ (fun z => g₁ z + g₂ z)) y = fderiv ℝ (fderiv ℝ g₁) y + fderiv ℝ (fderiv ℝ g₂) y := by
  have hev : fderiv ℝ (fun z => g₁ z + g₂ z) =ᶠ[𝓝 y] fun z => fderiv ℝ g₁ z + fderiv ℝ g₂ z := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact fderiv_add ((h₁.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
      ((h₂.contDiffAt (hU.mem_nhds hz)).differentiableAt (by norm_num))
  rw [hev.fderiv_eq]
  exact fderiv_add
    (((h₁.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
    (((h₂.contDiffAt (hU.mem_nhds hy)).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

private theorem hessL_add_lemma_2 {D : ℕ} (H₁ H₂ : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) :
    hessL (H₁ + H₂) = hessL H₁ + hessL H₂ := by
  funext i k
  simp only [hessL, ContinuousLinearMap.add_apply, Pi.add_apply]
  push_cast
  ring

theorem conv_dens_of_open {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (Θ : LocPot X) (V : Set X) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ)
    (phT : Fin e → ℝ → X → ℝ) (hB : IsOpen V) (hΘ : IsPotential A Θ)
    (hth : ∀ i, IsPotential A (th i)) (hph : ∀ i, A.SmoothOn V (ph i))
    (hT : ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ i, A.Smooth (phT i t))
    (hC2 : ∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V, IsCompact K' →
      TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT i t ∘ (A.chart j).symm)))
        (fderiv ℝ (fderiv ℝ (ph i ∘ (A.chart j).symm))) (nhdsWithin 0 (Set.Ioi 0)) K')
    (j : Fin A.n) (K : Set (Fin e → ℂ))
    (hK : K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' V) (hKc : IsCompact K) :
    TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
      (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (nhdsWithin 0 (Set.Ioi 0)) K := by
  classical
  have hS : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) :=
    (A.chart j).isOpen_inter_preimage_symm hB
  let a : Fin e → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k y =>
    hessC (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y
  let b : (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun y =>
    hessC (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y')) y
  let q : Fin e → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k y =>
    hessL (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) y)
  let p : Fin e → ℝ → (Fin e → ℂ) → (Fin e → Fin e → ℂ) := fun k t y =>
    hessL (fderiv ℝ (fderiv ℝ (phT k t ∘ (A.chart j).symm)) y)

  have hsplit : ∀ (k : Fin e) (u : X → ℝ) (W : Set (Fin e → ℂ)) (y : Fin e → ℂ), IsOpen W → y ∈ W →
      y ∈ (A.chart j).target → ContDiffOn ℝ 2 (u ∘ (A.chart j).symm) W →
      hessC (fun y' => (th k + LocPot.ofFun u + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
        a k y + hessL (fderiv ℝ (fderiv ℝ (u ∘ (A.chart j).symm)) y) + b y := by
    intro k u W y hW hyW hyt hu
    have h1 : ContDiffOn ℝ 2 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y'))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) :=
      contDiffOn_infty.1 ((hth k).1 ((A.chart j).symm y) j) 2
    have h3 : ContDiffOn ℝ 2 (fun y' => Θ.φ ((A.chart j).symm y) ((A.chart j).symm y'))
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y)) :=
      contDiffOn_infty.1 (hΘ.1 ((A.chart j).symm y) j) 2
    have o1 := (A.chart j).isOpen_inter_preimage_symm ((th k).isOpen_U ((A.chart j).symm y))
    have o3 := (A.chart j).isOpen_inter_preimage_symm (Θ.isOpen_U ((A.chart j).symm y))
    have oU := (o1.inter hW).inter o3
    have mU : y ∈ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) ∩ W ∩
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y)) :=
      ⟨⟨⟨hyt, (th k).mem_U _⟩, hyW⟩, ⟨hyt, Θ.mem_U _⟩⟩
    have hu' : ContDiffOn ℝ 2 (fun y' => u ((A.chart j).symm y')) W := hu
    have e12 : ContDiffOn ℝ 2 (fun y' => (th k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
        u ((A.chart j).symm y'))
        (((A.chart j).target ∩ (A.chart j).symm ⁻¹' (th k).U ((A.chart j).symm y)) ∩ W ∩
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Θ.U ((A.chart j).symm y))) :=
      (h1.mono (Set.inter_subset_left.trans Set.inter_subset_left)).add
        (hu'.mono (Set.inter_subset_left.trans Set.inter_subset_right))
    show hessL (fderiv ℝ (fderiv ℝ (fun y' => ((th k).φ ((A.chart j).symm y) ((A.chart j).symm y') +
      u ((A.chart j).symm y')) + Θ.φ ((A.chart j).symm y) ((A.chart j).symm y'))) y) = _
    rw [fderiv2_add_lemma oU mU e12 (h3.mono Set.inter_subset_right),
      fderiv2_add_lemma oU mU (h1.mono (Set.inter_subset_left.trans Set.inter_subset_left))
        (hu'.mono (Set.inter_subset_left.trans Set.inter_subset_right)),
      hessL_add_lemma_2, hessL_add_lemma_2]
    rfl

  have hq0 : ∀ k, ContinuousOn (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)))
      ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) := fun k =>
    ((contDiffOn_infty.1 (hph k j) 2).fderiv_of_isOpen hS (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen
      hS (by norm_num)
  have hq_cont : ∀ k, ContinuousOn (q k) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' V) := fun k =>
    continuous_hessL.comp_continuousOn (hq0 k)
  have hpq : ∀ k, TendstoUniformlyOn (p k) (q k) (nhdsWithin 0 (Set.Ioi 0)) K := by
    intro k
    have hbdd : Bornology.IsBounded (fderiv ℝ (fderiv ℝ (ph k ∘ (A.chart j).symm)) '' K) :=
      (hKc.image_of_continuousOn ((hq0 k).mono hK)).isBounded
    exact tendstoUniformlyOn_comp_continuous hessL continuous_hessL _ _ hbdd (hC2 k j K hK hKc)
  have hW : TendstoUniformlyOn (fun t y => fun k => a k y + p k t y + b y)
      (fun y k => a k y + q k y + b y) (nhdsWithin 0 (Set.Ioi 0)) K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hk : ∀ k, ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0), ∀ y ∈ K, dist (q k y) (p k t y) < ε :=
      fun k => Metric.tendstoUniformlyOn_iff.1 (hpq k) ε hε
    filter_upwards [Filter.eventually_all.2 hk] with t ht y hy
    rw [dist_pi_lt_iff hε]
    intro k
    rw [dist_add_right, dist_add_left]
    exact ht k y hy
  have hWc : ContinuousOn (fun y k => a k y + q k y + b y) K := by
    refine continuousOn_pi.2 fun k => ?_
    have ha : ContinuousOn (a k) (A.chart j).target := hessC_base_continuousOn A (th k) (hth k) j
    have hb : ContinuousOn b (A.chart j).target := hessC_base_continuousOn A Θ hΘ j
    exact ((ha.mono fun z hz => (hK hz).1).add ((hq_cont k).mono hK)).add (hb.mono fun z hz => (hK hz).1)
  have hG : Continuous (fun w : Fin e → Fin e → Fin e → ℂ =>
      (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => w k).re) := by
    simp only [mdisc]
    refine continuous_const.mul (Complex.continuous_re.comp ?_)
    refine continuous_const.mul (continuous_finsetSum _ fun S _ => continuous_const.mul ?_)
    exact Continuous.matrix_det (continuous_finsetSum _ fun k _ => continuous_apply k)
  have hmain := tendstoUniformlyOn_comp_continuous _ hG _ _
    (hKc.image_of_continuousOn hWc).isBounded hW
  refine (hmain.congr ?_).congr_right ?_
  · filter_upwards [hT] with t ht y hy
    have hfun : (fun k => a k y + p k t y + b y) = fun k => hessC
        (fun y' => (th k + LocPot.ofFun (phT k t) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
      funext fun k => (hsplit k (phT k t) _ y ((A.chart j).isOpen_inter_preimage_symm isOpen_univ)
        ⟨(hK hy).1, trivial⟩ (hK hy).1 (contDiffOn_infty.1 (ht k j) 2)).symm
    show (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => (fun k => a k y + p k t y + b y) k).re = _
    rw [hfun]
    rfl
  · intro y hy
    have hfun : (fun k => a k y + q k y + b y) = fun k => hessC
        (fun y' => (th k + LocPot.ofFun (ph k) + Θ).φ ((A.chart j).symm y) ((A.chart j).symm y')) y :=
      funext fun k => (hsplit k (ph k) _ y hS (hK hy) (hK hy).1 (contDiffOn_infty.1 (hph k j) 2)).symm
    show (e.factorial : ℝ) * (2 / Real.pi) ^ e * (mdisc fun k => (fun k => a k y + q k y + b y) k).re = _
    rw [hfun]
    rfl

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DominatedConvergenceExhaustion
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DominatedConvergenceExhaustion
open MeasureTheory Filter Topology

namespace GlobalTheory.CompanionTheory.Conv

lemma fatou_real {α : Type} [MeasurableSpace α] {ν : Measure α} {g : ℕ → α → ℝ} {g0 : α → ℝ}
    {c : ℝ} (hi : ∀ k, Integrable (g k) ν) (hnn : ∀ k, ∀ᵐ y ∂ν, 0 ≤ g k y)
    (hlim : ∀ᵐ y ∂ν, Tendsto (fun k => g k y) atTop (𝓝 (g0 y)))
    (hc : ∀ k, ∫ y, g k y ∂ν ≤ c) :
    Integrable g0 ν ∧ ∫ y, g0 y ∂ν ≤ c := by
  have hm : AEStronglyMeasurable g0 ν :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hi k).aestronglyMeasurable) hlim
  have hnn0 : ∀ᵐ y ∂ν, 0 ≤ g0 y := by
    filter_upwards [ae_all_iff.2 hnn, hlim] with y h1 h2
    exact ge_of_tendsto' h2 h1
  have hc0 : 0 ≤ c := (integral_nonneg_of_ae (hnn 0)).trans (hc 0)
  have hk : ∀ k, ∫⁻ y, ENNReal.ofReal (g k y) ∂ν ≤ ENNReal.ofReal c := fun k => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hi k) (hnn k)]
    exact ENNReal.ofReal_le_ofReal (hc k)
  have hle : ∫⁻ y, ENNReal.ofReal (g0 y) ∂ν ≤ ENNReal.ofReal c := by
    calc ∫⁻ y, ENNReal.ofReal (g0 y) ∂ν
        = ∫⁻ y, liminf (fun k => ENNReal.ofReal (g k y)) atTop ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hlim] with y hy
          exact ((ENNReal.continuous_ofReal.tendsto _).comp hy).liminf_eq.symm
      _ ≤ liminf (fun k => ∫⁻ y, ENNReal.ofReal (g k y) ∂ν) atTop :=
          lintegral_liminf_le' (fun k => (hi k).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal c := liminf_le_of_frequently_le' (Frequently.of_forall hk)
  have hint : Integrable g0 ν :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal hnn0).2 (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have := hle
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn0] at this
  exact (ENNReal.ofReal_le_ofReal_iff hc0).1 this

lemma tail_bound {α : Type} [MeasurableSpace α] {μ : Measure α} {S E0 : Set α}
    (hS : MeasurableSet S) (hSE : S ⊆ E0ᶜ) {L ρ Γ : α → ℝ} {a c : ℝ} (ha : 0 ≤ a)
    (hρm : AEStronglyMeasurable ρ μ) (hΓm : AEStronglyMeasurable Γ μ)
    (hρ : ∀ᵐ y ∂μ, 0 ≤ ρ y) (hΓ : ∀ᵐ y ∂μ, y ∉ E0 → |Γ y| ≤ a * L y)
    (hi : IntegrableOn (fun y => L y * ρ y) S μ) (hc : ∫ y in S, L y * ρ y ∂μ ≤ c) :
    IntegrableOn (fun y => Γ y * ρ y) S μ ∧ |∫ y in S, Γ y * ρ y ∂μ| ≤ a * c := by
  have hb : ∀ᵐ y ∂μ.restrict S, ‖Γ y * ρ y‖ ≤ a * (L y * ρ y) := by
    rw [ae_restrict_iff' hS]
    filter_upwards [hρ, hΓ] with y h1 h2 hy
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (h2 (hSE hy)) h1
  have hi' : Integrable (fun y => a * (L y * ρ y)) (μ.restrict S) := Integrable.const_mul hi a
  refine ⟨Integrable.mono' hi' (hΓm.mul hρm).restrict hb, ?_⟩
  calc |∫ y in S, Γ y * ρ y ∂μ| = ‖∫ y in S, Γ y * ρ y ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y in S, a * (L y * ρ y) ∂μ := norm_integral_le_of_norm_le hi' hb
    _ = a * ∫ y in S, L y * ρ y ∂μ := integral_const_mul _ _
    _ ≤ a * c := mul_le_mul_of_nonneg_left hc ha

theorem tendsto_integral_of_exhaustion {α : Type} [MeasurableSpace α] (μ : Measure α)
    (l : Filter ℝ) [l.NeBot] [l.IsCountablyGenerated] (E : ℕ → Set α) (L : α → ℝ)
    (ρ Γ : ℝ → α → ℝ) (ρ0 Γ0 : α → ℝ) (a : ℝ) (b : ℕ → ℝ)
    (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E) (hfin : ∀ n, μ (E n) < ⊤)
    (hcov : ∀ᵐ y ∂μ, ∃ n, y ∈ E n) (hL : ∀ᵐ y ∂μ, 0 ≤ L y) (ha : 0 ≤ a)
    (hb : Tendsto b atTop (𝓝 0))
    (hρ : ∀ n, TendstoUniformlyOn ρ ρ0 l (E n)) (hΓ : ∀ n, TendstoUniformlyOn Γ Γ0 l (E n))
    (hM : ∀ n, ∃ M : ℝ, ∀ y ∈ E n, |ρ0 y| ≤ M ∧ |Γ0 y| ≤ M)
    (hev : ∀ᶠ t in l, AEStronglyMeasurable (ρ t) μ ∧ AEStronglyMeasurable (Γ t) μ ∧
      (∀ᵐ y ∂μ, 0 ≤ ρ t y) ∧ (∀ᵐ y ∂μ, y ∉ E 0 → |Γ t y| ≤ a * L y) ∧
      ∀ n, IntegrableOn (fun y => L y * ρ t y) (E n)ᶜ μ ∧ ∫ y in (E n)ᶜ, L y * ρ t y ∂μ ≤ b n) :
    Integrable (fun y => Γ0 y * ρ0 y) μ ∧ (∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ) ∧
      Tendsto (fun t => ∫ y, Γ t y * ρ t y ∂μ) l (𝓝 (∫ y, Γ0 y * ρ0 y ∂μ)) := by
  obtain ⟨u, hu⟩ := exists_seq_tendsto l
  obtain ⟨K, hK⟩ := eventually_atTop.1 (hu.eventually hev)
  have hv : Tendsto (fun k => u (k + K)) atTop l := (tendsto_add_atTop_iff_nat K).2 hu
  have hG := fun k => hK (k + K) (Nat.le_add_left K k)
  have hpt : ∀ᵐ y ∂μ, Tendsto (fun k => ρ (u (k + K)) y) atTop (𝓝 (ρ0 y)) ∧
      Tendsto (fun k => Γ (u (k + K)) y) atTop (𝓝 (Γ0 y)) := by
    filter_upwards [hcov] with y hy
    obtain ⟨n, hn⟩ := hy
    exact ⟨((hρ n).tendsto_at hn).comp hv, ((hΓ n).tendsto_at hn).comp hv⟩
  have hρ0m : AEStronglyMeasurable ρ0 μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).1) (hpt.mono fun _ h => h.1)
  have hΓ0m : AEStronglyMeasurable Γ0 μ :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).2.1) (hpt.mono fun _ h => h.2)
  have hρ0nn : ∀ᵐ y ∂μ, 0 ≤ ρ0 y := by
    filter_upwards [ae_all_iff.2 (fun k => (hG k).2.2.1), hpt] with y h1 h2
    exact ge_of_tendsto' h2.1 h1
  have hΓ0b : ∀ᵐ y ∂μ, y ∉ E 0 → |Γ0 y| ≤ a * L y := by
    filter_upwards [ae_all_iff.2 (fun k => (hG k).2.2.2.1), hpt] with y h1 h2 hy
    exact le_of_tendsto' h2.2.abs (fun k => h1 k hy)
  have htail0 : ∀ n, IntegrableOn (fun y => L y * ρ0 y) (E n)ᶜ μ ∧
      ∫ y in (E n)ᶜ, L y * ρ0 y ∂μ ≤ b n := fun n =>
    fatou_real (g := fun k y => L y * ρ (u (k + K)) y)
      (fun k => ((hG k).2.2.2.2 n).1)
      (fun k => ae_restrict_of_ae (by
        filter_upwards [hL, (hG k).2.2.1] with y h1 h2
        exact mul_nonneg h1 h2))
      (ae_restrict_of_ae (by
        filter_upwards [hpt] with y h
        exact h.1.const_mul (L y)))
      (fun k => ((hG k).2.2.2.2 n).2)
  have hsub : ∀ n, (E n)ᶜ ⊆ (E 0)ᶜ := fun n =>
    Set.compl_subset_compl.2 (hmono (Nat.zero_le n))
  have htailLim : ∀ n, IntegrableOn (fun y => Γ0 y * ρ0 y) (E n)ᶜ μ ∧
      |∫ y in (E n)ᶜ, Γ0 y * ρ0 y ∂μ| ≤ a * b n := fun n =>
    tail_bound (hEm n).compl (hsub n) ha hρ0m hΓ0m hρ0nn hΓ0b (htail0 n).1 (htail0 n).2
  have htailT : ∀ᶠ t in l, ∀ n, IntegrableOn (fun y => Γ t y * ρ t y) (E n)ᶜ μ ∧
      |∫ y in (E n)ᶜ, Γ t y * ρ t y ∂μ| ≤ a * b n := hev.mono fun t h n =>
    tail_bound (hEm n).compl (hsub n) ha h.1 h.2.1 h.2.2.1 h.2.2.2.1
      (h.2.2.2.2 n).1 (h.2.2.2.2 n).2
  have hB : ∀ n, ∃ C : ℝ, (∀ y ∈ E n, |Γ0 y * ρ0 y| ≤ C) ∧
      ∀ᶠ t in l, ∀ y ∈ E n, |Γ t y * ρ t y| ≤ C := by
    intro n
    obtain ⟨M, hM'⟩ := hM n
    have hC : (0 : ℝ) ≤ |M| + 1 := by positivity
    have key : ∀ x z : ℝ, |x| ≤ |M| + 1 → |z| ≤ |M| + 1 → |x * z| ≤ (|M| + 1) * (|M| + 1) := by
      intro x z h1 h2
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hC
    have near : ∀ x z : ℝ, |z| ≤ M → dist z x < 1 → |x| ≤ |M| + 1 := by
      intro x z h1 h2
      rw [Real.dist_eq] at h2
      have h3 := abs_sub_abs_le_abs_sub x z
      rw [abs_sub_comm x z] at h3
      have h4 := le_abs_self M
      linarith
    refine ⟨(|M| + 1) * (|M| + 1), fun y hy => ?_, ?_⟩
    · have h4 := le_abs_self M
      exact key _ _ (by linarith [(hM' y hy).2]) (by linarith [(hM' y hy).1])
    · filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hρ n) 1 one_pos,
        Metric.tendstoUniformlyOn_iff.1 (hΓ n) 1 one_pos] with t h1 h2 y hy
      exact key _ _ (near _ _ (hM' y hy).2 (h2 y hy)) (near _ _ (hM' y hy).1 (h1 y hy))
  have hhead0 : ∀ n, IntegrableOn (fun y => Γ0 y * ρ0 y) (E n) μ := by
    intro n
    obtain ⟨C, hC, -⟩ := hB n
    exact Measure.integrableOn_of_bounded (hfin n).ne (hΓ0m.mul hρ0m) (M := C)
      (ae_restrict_of_forall_mem (hEm n) hC)
  have hheadT : ∀ n, ∀ᶠ t in l, IntegrableOn (fun y => Γ t y * ρ t y) (E n) μ := by
    intro n
    obtain ⟨C, -, hC⟩ := hB n
    filter_upwards [hev, hC] with t h1 h2
    exact Measure.integrableOn_of_bounded (hfin n).ne (h1.2.1.mul h1.1) (M := C)
      (ae_restrict_of_forall_mem (hEm n) h2)
  have hU : ∀ f : α → ℝ, IntegrableOn f (E 0) μ → IntegrableOn f (E 0)ᶜ μ → Integrable f μ := by
    intro f h1 h2
    have := h1.union h2
    rwa [Set.union_compl_self, integrableOn_univ] at this
  have hI0 : Integrable (fun y => Γ0 y * ρ0 y) μ := hU _ (hhead0 0) (htailLim 0).1
  have hIT : ∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ := by
    filter_upwards [htailT, hheadT 0] with t h1 h2
    exact hU _ h2 (h1 0).1
  refine ⟨hI0, hIT, ?_⟩
  have hconv : ∀ n, Tendsto (fun t => ∫ y in E n, Γ t y * ρ t y ∂μ) l
      (𝓝 (∫ y in E n, Γ0 y * ρ0 y ∂μ)) := by
    intro n
    obtain ⟨C, -, hC⟩ := hB n
    haveI : IsFiniteMeasure (μ.restrict (E n)) := ⟨by simpa using hfin n⟩
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
      (integrable_const C) ?_
    · exact hev.mono fun t h => (h.2.1.mul h.1).restrict
    · exact hC.mono fun t h => ae_restrict_of_forall_mem (hEm n) h
    · exact ae_restrict_of_forall_mem (hEm n) fun y hy =>
        ((hΓ n).tendsto_at hy).mul ((hρ n).tendsto_at hy)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hbn : Tendsto (fun n => a * |b n|) atTop (𝓝 0) := by
    simpa using hb.abs.const_mul a
  obtain ⟨n, hn⟩ := (hbn.eventually (Iio_mem_nhds hε3)).exists
  have hn' : a * |b n| < ε / 3 := hn
  have hab : a * b n ≤ a * |b n| := mul_le_mul_of_nonneg_left (le_abs_self _) ha
  filter_upwards [Metric.tendsto_nhds.1 (hconv n) (ε / 3) hε3, htailT, hIT] with t h1 h2 h3
  have e1 : ∫ y in E n, Γ t y * ρ t y ∂μ + ∫ y in (E n)ᶜ, Γ t y * ρ t y ∂μ =
      ∫ y, Γ t y * ρ t y ∂μ := integral_add_compl (hEm n) h3
  have e2 : ∫ y in E n, Γ0 y * ρ0 y ∂μ + ∫ y in (E n)ᶜ, Γ0 y * ρ0 y ∂μ =
      ∫ y, Γ0 y * ρ0 y ∂μ := integral_add_compl (hEm n) hI0
  have A := (h2 n).2
  have B := (htailLim n).2
  rw [Real.dist_eq] at h1 ⊢
  rw [← e1, ← e2]
  rw [abs_lt] at h1 ⊢
  rw [abs_le] at A B
  constructor <;> linarith [h1.1, h1.2, A.1, A.2, B.1, B.2]

end GlobalTheory.CompanionTheory.Conv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.DominatedConvergenceExhaustionStatement
open MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominated_convergence_exhaustion : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (l : Filter ℝ) [l.NeBot] [l.IsCountablyGenerated] (E : ℕ → Set α) (L : α → ℝ) (ρ Γ : ℝ → α → ℝ) (ρ0 Γ0 : α → ℝ) (a : ℝ) (b : ℕ → ℝ), (∀ n, MeasurableSet (E n)) → Monotone E → (∀ n, μ (E n) < ⊤) → (∀ᵐ y ∂μ, ∃ n, y ∈ E n) → (∀ᵐ y ∂μ, 0 ≤ L y) → 0 ≤ a → Tendsto b atTop (𝓝 0) → (∀ n, TendstoUniformlyOn ρ ρ0 l (E n)) → (∀ n, TendstoUniformlyOn Γ Γ0 l (E n)) → (∀ n, ∃ M : ℝ, ∀ y ∈ E n, |ρ0 y| ≤ M ∧ |Γ0 y| ≤ M) → (∀ᶠ t in l, AEStronglyMeasurable (ρ t) μ ∧ AEStronglyMeasurable (Γ t) μ ∧ (∀ᵐ y ∂μ, 0 ≤ ρ t y) ∧ (∀ᵐ y ∂μ, y ∉ E 0 → |Γ t y| ≤ a * L y) ∧ ∀ n, IntegrableOn (fun y => L y * ρ t y) (E n)ᶜ μ ∧ ∫ y in (E n)ᶜ, L y * ρ t y ∂μ ≤ b n) → Integrable (fun y => Γ0 y * ρ0 y) μ ∧ (∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ) ∧ Tendsto (fun t => ∫ y, Γ t y * ρ t y ∂μ) l (𝓝 (∫ y, Γ0 y * ρ0 y ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion | exact GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion | (intros; apply GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralRegularizedConvergence
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem tendsto_logPow_div_exp_add (CE : ℝ) (e : ℕ) :
    Tendsto (fun n : ℕ => CE * Real.log (Real.exp 1 + n) ^ (e + 1) / (Real.exp 1 + n)) atTop (𝓝 0) := by
  have h := (Real.isLittleO_pow_log_id_atTop (n := e + 1)).tendsto_div_nhds_zero
  have h2 : Tendsto (fun n : ℕ => Real.exp 1 + (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have h3 := (h.comp h2).const_mul CE
  simpa [mul_div_assoc] using h3

theorem tendstoUniformlyOn_cutoff_comp {β X : Type*} (σ : β → X) (c : X → ℝ)
    (hc : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (F : ℝ → X → ℝ) (f : X → ℝ) (l : Filter ℝ) (K : Set X)
    (E : Set β) (hE : ∀ y ∈ E, σ y ∈ K) (h : TendstoUniformlyOn F f l K) :
    TendstoUniformlyOn (fun t y => c (σ y) * F t (σ y)) (fun y => c (σ y) * f (σ y)) l E := by
  rw [Metric.tendstoUniformlyOn_iff] at h ⊢
  intro ε hε
  filter_upwards [h ε hε] with t ht y hy
  have h1 := ht (σ y) (hE y hy)
  rw [Real.dist_eq] at h1 ⊢
  calc |c (σ y) * f (σ y) - c (σ y) * F t (σ y)|
      = c (σ y) * |f (σ y) - F t (σ y)| := by
        rw [← mul_sub, abs_mul, abs_of_nonneg (hc _).1]
    _ ≤ 1 * |f (σ y) - F t (σ y)| := mul_le_mul_of_nonneg_right (hc _).2 (abs_nonneg _)
    _ < ε := by simpa using h1

theorem integrableOn_compl_of_ae_eq_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (E : Set α) (hE : MeasurableSet E) (f T : α → ℝ) (b : ℝ) (hT : Integrable T μ)
    (hT0 : ∀ᵐ y ∂μ, 0 ≤ T y) (hb : ∫ y, T y ∂μ ≤ b) (heq : ∀ᵐ y ∂μ, y ∉ E → f y = T y) :
    IntegrableOn f Eᶜ μ ∧ ∫ y in Eᶜ, f y ∂μ ≤ b := by
  have h : f =ᵐ[μ.restrict Eᶜ] T := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hE.compl]
    filter_upwards [heq] with y hy hyE using hy hyE
  refine ⟨(hT.integrableOn (s := Eᶜ)).congr h.symm, ?_⟩
  rw [integral_congr_ae h]
  exact (setIntegral_le_integral hT hT0).trans hb

theorem conv_chart_integral : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (G : X → ℝ) (GT : ℝ → X → ℝ) (C CE : ℝ), IsPotential A Θ → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn R.Yo (ph i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (phT i t)) ∧ (∀ i, IsPsh A (th i + LocPot.ofFun (phT i t) + Θ)) ∧ GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => th i + LocPot.ofFun (phT i t) + Θ) CE) → (∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT i t ∘ (A.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph i ∘ (A.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable X ℝ (borel X) _ (R.Yo.indicator (GT t)) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → ∀ (j : Fin A.n) (S : Set (Fin e → ℂ)) (c : X → ℝ), S ⊆ (A.chart j).target → IsCompact S → @Measurable X ℝ (borel X) _ c → (∀ x, 0 ≤ c x ∧ c x ≤ 1) → (∀ y ∈ (A.chart j).target, y ∉ S → c ((A.chart j).symm y) = 0) → IntegrableOn (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y) (A.chart j).target ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IntegrableOn (fun y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (A.chart j).target) ∧ Tendsto (fun t => ∫ y in (A.chart j).target, c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (𝓝[>] 0) (𝓝 (∫ y in (A.chart j).target, c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y)) := by
  intro e X _ _ _ A R Θ th ph phT G GT C CE hΘ hth hph hev hconv hGev hGconv j S c hST hS hcm hc01 hc0
  obtain ⟨hYo, hnull, -, hKc⟩ := GlobalTheory.T.regular_chart_data_properties e X A R
  have hsymmS : ContinuousOn (A.chart j).symm S := (A.chart j).continuousOn_symm.mono hST
  have hSm : MeasurableSet S := hS.measurableSet
  have hTm : MeasurableSet (A.chart j).target := (A.chart j).open_target.measurableSet
  obtain ⟨E, hEdef⟩ : ∃ E : ℕ → Set (Fin e → ℂ), ∀ n, E n = S ∩ (A.chart j).symm ⁻¹'
      {x | x ∈ R.Yo ∧ R.r x ≤ Real.exp 1 + n} := ⟨_, fun _ => rfl⟩
  have hEmem : ∀ n y, y ∈ E n ↔ y ∈ S ∧ (A.chart j).symm y ∈ R.Yo ∧
      R.r ((A.chart j).symm y) ≤ Real.exp 1 + n := by
    intro n y; rw [hEdef]; rfl
  have hEc : ∀ n, IsCompact (E n) := by
    intro n; rw [hEdef]
    exact hS.of_isClosed_subset
      (hsymmS.preimage_isClosed_of_isClosed hS.isClosed (hKc _).isClosed) Set.inter_subset_left
  have hEsub : ∀ n, E n ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo := fun n y hy => by
    have := (hEmem n y).1 hy
    exact ⟨hST this.1, this.2.1⟩
  have hEm : ∀ n, MeasurableSet (E n) := fun n => (hEc n).measurableSet
  have hEmono : Monotone E := by
    intro m n hmn y hy
    obtain ⟨h1, h2, h3⟩ := (hEmem m y).1 hy
    refine (hEmem n y).2 ⟨h1, h2, h3.trans ?_⟩
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have hEfin : ∀ n, (volume.restrict S) (E n) < ⊤ := fun n => by
    rw [Measure.restrict_apply (hEm n)]
    exact lt_of_le_of_lt (measure_mono Set.inter_subset_left) (hEc n).measure_lt_top
  have hae : ∀ᵐ y ∂(volume.restrict S), y ∈ S ∧ (A.chart j).symm y ∈ R.Yo := by
    rw [ae_restrict_iff' hSm]
    filter_upwards [compl_mem_ae_iff.2 (hnull j)] with y hy hyS
    refine ⟨hyS, ?_⟩
    by_contra h
    exact hy ⟨hST hyS, h⟩
  have hex : ∀ᵐ y ∂(volume.restrict S), ∃ n, y ∈ E n := by
    filter_upwards [hae] with y hy
    obtain ⟨n, hn⟩ := exists_nat_ge (R.r ((A.chart j).symm y))
    refine ⟨n, (hEmem n y).2 ⟨hy.1, hy.2, ?_⟩⟩
    have := Real.exp_pos 1
    linarith
  have hlog : ∀ x ∈ R.Yo, 0 ≤ Real.log (R.r x) := fun x hx => Real.log_nonneg (R.one_le_r x hx)
  have hL : ∀ᵐ y ∂(volume.restrict S), 0 ≤ Real.log (R.r ((A.chart j).symm y)) := by
    filter_upwards [hae] with y hy using hlog _ hy.2
  have hGbd : ∀ n : ℕ, ∃ M : ℝ, ∀ x, x ∈ R.Yo → R.r x ≤ Real.exp 1 + n → |G x| ≤ M := by
    intro n
    have hu := hGconv {x | x ∈ R.Yo ∧ R.r x ≤ Real.exp 1 + n}
      (fun x hx => hx.1) (hKc (Real.exp 1 + n))
    have h1 := Metric.tendstoUniformlyOn_iff.1 hu 1 one_pos
    obtain ⟨t, ht1, ht2⟩ := (h1.and hGev).exists
    refine ⟨1 + (|C| + |C| * Real.log (Real.exp 1 + n)), fun x hx hxr => ?_⟩
    have a1 := ht1 x ⟨hx, hxr⟩
    have a2 := ht2.2 x hx
    have a3 : Real.log (R.r x) ≤ Real.log (Real.exp 1 + n) :=
      Real.log_le_log (by linarith [R.one_le_r x hx]) hxr
    have a4 := hlog x hx
    rw [Real.dist_eq] at a1
    have a5 := abs_sub_abs_le_abs_sub (G x) (GT t x)
    have a6 : C * Real.log (R.r x) ≤ |C| * Real.log (R.r x) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) a4
    have a7 : |C| * Real.log (R.r x) ≤ |C| * Real.log (Real.exp 1 + n) :=
      mul_le_mul_of_nonneg_left a3 (abs_nonneg C)
    have a8 := le_abs_self C
    linarith
  have hρ : ∀ n, TendstoUniformlyOn (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
      (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j) (𝓝[>] 0) (E n) := fun n =>
    GlobalTheory.CompanionTheory.Ar.Giv.conv_dens_of_open A Θ R.Yo th ph phT hYo hΘ hth hph
      (hev.mono fun t h => h.1) hconv j (E n) (hEsub n) (hEc n)
  have hΓ : ∀ n, TendstoUniformlyOn
      (fun t y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y))
      (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y)) (𝓝[>] 0) (E n) := fun n =>
    tendstoUniformlyOn_cutoff_comp (A.chart j).symm c hc01 GT G _ {x | x ∈ R.Yo ∧ R.r x ≤ Real.exp 1 + n} (E n)
      (fun y hy => ⟨((hEmem n y).1 hy).2.1, ((hEmem n y).1 hy).2.2⟩)
      (hGconv _ (fun x hx => hx.1) (hKc (Real.exp 1 + n)))
  have hM : ∀ n, ∃ M : ℝ, ∀ y ∈ E n,
      |locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y| ≤ M ∧
      |c ((A.chart j).symm y) * G ((A.chart j).symm y)| ≤ M := by
    intro n
    obtain ⟨M1, h1⟩ := (hEc n).exists_bound_of_continuousOn
      ((GlobalTheory.CompanionTheory.Ar.Giv.locDens_add_ofFun_continuousOn A R.Yo th ph Θ hYo hth hΘ hph j).mono (hEsub n))
    obtain ⟨M2, h2⟩ := hGbd n
    refine ⟨max M1 M2, fun y hy => ⟨(h1 y hy).trans (le_max_left _ _), ?_⟩⟩
    obtain ⟨-, b2, b3⟩ := (hEmem n y).1 hy
    rw [abs_mul, abs_of_nonneg (hc01 _).1]
    exact (mul_le_of_le_one_left (abs_nonneg _) (hc01 _).2).trans ((h2 _ b2 b3).trans (le_max_right _ _))
  have hEv : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j) (volume.restrict S) ∧
      AEStronglyMeasurable (fun y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y)) (volume.restrict S) ∧
      (∀ᵐ y ∂(volume.restrict S), 0 ≤ locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) ∧
      (∀ᵐ y ∂(volume.restrict S), y ∉ E 0 →
        |c ((A.chart j).symm y) * GT t ((A.chart j).symm y)| ≤ 2 * |C| * Real.log (R.r ((A.chart j).symm y))) ∧
      ∀ n, IntegrableOn (fun y => Real.log (R.r ((A.chart j).symm y)) *
          locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (E n)ᶜ (volume.restrict S) ∧
        ∫ y in (E n)ᶜ, Real.log (R.r ((A.chart j).symm y)) *
          locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y ∂(volume.restrict S) ≤
          CE * Real.log (Real.exp 1 + n) ^ (e + 1) / (Real.exp 1 + n) := by
    filter_upwards [hev, hGev] with t ⟨hs, hp, ht⟩ ⟨hm, hb⟩
    have hpot : ∀ i, IsPotential A (th i + LocPot.ofFun (phT i t) + Θ) := fun i =>
      isPotentialAdd A _ _ (isPotentialAdd A _ _ (hth i) (isPotential_ofFun A _ (hs i))) hΘ
    have hnn : ∀ y ∈ (A.chart j).target,
        0 ≤ locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y :=
      fun y hy => locDens_nonneg_of_psh A _ hpot hp j hy
    have hlocal {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X]
        [T2Space X] (A : FinHolAtlas e X) (Yo : Set X) (r : X → ℝ) (Φ : Fin e → LocPot X) (CE : ℝ)
        (hΦ : ∀ i, IsPotential A (Φ i)) (hr : ∀ x ∈ Yo, 1 ≤ r x)
        (hdens : ∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A Φ j y)
        (hT : GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A Yo r Φ CE)
        (j : Fin A.n) (S : Set (Fin e → ℂ)) (hSt : S ⊆ (A.chart j).target) (hSc : IsCompact S)
        (R₀ : ℝ) (hR₀ : Real.exp 1 ≤ R₀) :
        IntegrableOn (fun y => (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
          (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y) S ∧
        ∫ y in S, (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
          (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y ≤
          CE * Real.log R₀ ^ (e + 1) / R₀ := by
      classical
      obtain ⟨hI, hB⟩ := hT R₀ hR₀
      set h : X → ℝ := (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator
        (fun x => Real.log (r x)) with hdef
      have hIS := hI j S hSt hSc
      refine ⟨hIS, ?_⟩
      have hh0 : ∀ x, 0 ≤ h x := by
        intro x
        refine Set.indicator_nonneg (fun x hx => ?_) x
        exact Real.log_nonneg (hr x hx.1)
      have hhYo : ∀ x, x ∉ Yo → h x = 0 := by
        intro x hx
        exact Set.indicator_of_notMem (by exact fun hm => hx hm.1) _
      have hSm : MeasurableSet S := hSc.isClosed.measurableSet
      set ch := A.chart j with hch
      set Z : Set X := ch.symm '' S with hZ
      set g : X → ℝ := Z.indicator h with hgdef
      have hg0 : ∀ x, x ∉ ch.source → g x = 0 := by
        intro x hx
        refine Set.indicator_of_notMem ?_ _
        rintro ⟨y, hy, rfl⟩
        exact hx (ch.map_target (hSt hy))
      set F : (Fin e → ℂ) → ℝ := fun y => h (ch.symm y) * locDens A Φ j y with hF
      have hgF : ∀ z ∈ ch.target, g (ch.symm z) * locDens A Φ j z = S.indicator F z := by
        intro z hz
        by_cases hzS : z ∈ S
        · rw [Set.indicator_of_mem hzS, hgdef, Set.indicator_of_mem (Set.mem_image_of_mem _ hzS)]
        · have hnZ : ch.symm z ∉ Z := by
            rintro ⟨y, hy, hyz⟩
            exact hzS ((ch.symm.injOn (by simpa using hSt hy) (by simpa using hz) hyz) ▸ hy)
          rw [Set.indicator_of_notMem hzS, hgdef, Set.indicator_of_notMem hnZ, zero_mul]
      have hFint : IntegrableOn (S.indicator F) ch.target :=
        ((integrable_indicator_iff hSm).2 hIS).integrableOn
      have hint : IntegrableOn (fun z => g (ch.symm z) * locDens A Φ j z) ch.target :=
        hFint.congr_fun (fun z hz => (hgF z hz).symm) ch.open_target.measurableSet
      have hne : Nonempty (ChartPartition A) := existsPartition A
      obtain ⟨hgt, hgI⟩ := integralWith_localize_support A hne.some Φ hΦ j g hg0 hint
      have hSint : ∫ z in ch.target, g (ch.symm z) * locDens A Φ j z = ∫ y in S, F y := by
        rw [setIntegral_congr_fun ch.open_target.measurableSet hgF,
          setIntegral_indicator hSm, Set.inter_eq_right.2 hSt]
      have hle : integralWith A hne.some Φ g ≤ integralWith A hne.some Φ h := by
        unfold integralWith
        refine Finset.sum_le_sum fun k _ => ?_
        refine setIntegral_mono_on (hgt k) (integrableOn_weight A hne.some Φ h hI k)
          (A.chart k).open_target.measurableSet fun y hy => ?_
        by_cases hx : (A.chart k).symm y ∈ Yo
        · have hd := hdens k y hy hx
          have hχ := hne.some.nonneg k ((A.chart k).symm y)
          have hgh : g ((A.chart k).symm y) ≤ h ((A.chart k).symm y) :=
            Set.indicator_le_self' (fun x _ => hh0 x) _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgh hχ) hd
        · have h1 : h ((A.chart k).symm y) = 0 := hhYo _ hx
          have h2 : g ((A.chart k).symm y) = 0 := by
            rw [hgdef]
            by_cases hz : (A.chart k).symm y ∈ Z
            · rw [Set.indicator_of_mem hz, h1]
            · rw [Set.indicator_of_notMem hz]
          rw [h1, h2]
      calc ∫ y in S, F y = integralWith A hne.some Φ g := by rw [hgI, hSint]
        _ ≤ integralWith A hne.some Φ h := hle
        _ = mInt A Φ h := by
          unfold mInt
          rw [dite_eq_left hne]
        _ ≤ _ := hB
    have htail := fun n : ℕ => hlocal A R.Yo R.r _ CE hpot R.one_le_r
      (fun j' y hy _ => locDens_nonneg_of_psh A _ hpot hp j' hy) ht j S hST hS
      (Real.exp 1 + n) (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
                           linarith)
    refine ⟨((locDensCont A _ hpot j).mono hST).aestronglyMeasurable hSm, ?_, ?_, ?_, ?_⟩
    · letI : MeasurableSpace X := borel X
      haveI : BorelSpace X := ⟨rfl⟩
      have h1 : AEMeasurable (A.chart j).symm (volume.restrict S) := hsymmS.aemeasurable hSm
      have h2 : AEMeasurable (fun y => c ((A.chart j).symm y) *
          R.Yo.indicator (GT t) ((A.chart j).symm y)) (volume.restrict S) :=
        (hcm.comp_aemeasurable h1).mul (hm.comp_aemeasurable h1)
      refine h2.aestronglyMeasurable.congr ?_
      filter_upwards [hae] with y hy
      rw [Set.indicator_of_mem hy.2]
    · filter_upwards [hae] with y hy using hnn y (hST hy.1)
    · filter_upwards [hae] with y hy hyE
      have hr : Real.exp 1 < R.r ((A.chart j).symm y) := by
        by_contra h
        exact hyE ((hEmem 0 y).2 ⟨hy.1, hy.2, by simpa using not_lt.1 h⟩)
      have hl : 1 ≤ Real.log (R.r ((A.chart j).symm y)) := by
        rw [Real.le_log_iff_exp_le (lt_trans (Real.exp_pos 1) hr)]
        exact hr.le
      have b1 := hb _ hy.2
      have b2 : C * Real.log (R.r ((A.chart j).symm y)) ≤
          |C| * Real.log (R.r ((A.chart j).symm y)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
      have b3 : |C| * 1 ≤ |C| * Real.log (R.r ((A.chart j).symm y)) :=
        mul_le_mul_of_nonneg_left hl (abs_nonneg C)
      have b4 := le_abs_self C
      rw [abs_mul, abs_of_nonneg (hc01 _).1]
      have b5 := mul_le_of_le_one_left (abs_nonneg (GT t ((A.chart j).symm y))) (hc01 ((A.chart j).symm y)).2
      linarith
    · intro n
      refine integrableOn_compl_of_ae_eq_nonneg _ (E n) (hEm n) _ _ _ (htail n).1 ?_ (htail n).2 ?_
      · filter_upwards [hae] with y hy
        exact mul_nonneg (Set.indicator_nonneg (fun x (hx : x ∈
          GroundTheory.Heights₂.Heights.AnalyticLimit.tail R.Yo R.r (Real.exp 1 + n)) => hlog x hx.1) _)
          (hnn y (hST hy.1))
      · filter_upwards [hae] with y hy hyE
        have hmem : (A.chart j).symm y ∈
            GroundTheory.Heights₂.Heights.AnalyticLimit.tail R.Yo R.r (Real.exp 1 + n) := by
          refine ⟨hy.2, ?_⟩
          by_contra h
          exact hyE ((hEmem n y).2 ⟨hy.1, hy.2, (not_le.1 h).le⟩)
        rw [Set.indicator_of_mem hmem]
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.T.dominated_convergence_exhaustion (volume.restrict S) (𝓝[>] (0 : ℝ)) E
    (fun y => Real.log (R.r ((A.chart j).symm y)))
    (fun t => locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j)
    (fun t y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y))
    (locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j)
    (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y))
    (2 * |C|) (fun n => CE * Real.log (Real.exp 1 + n) ^ (e + 1) / (Real.exp 1 + n))
    hEm hEmono hEfin hex hL (by positivity) (tendsto_logPow_div_exp_add CE e) hρ hΓ hM hEv
  have e1 : ∀ (g : X → ℝ) (d : (Fin e → ℂ) → ℝ),
      ∫ y in (A.chart j).target, c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y =
      ∫ y in S, c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y := fun g d =>
    setIntegral_eq_of_subset_of_forall_diff_eq_zero hTm hST
      (fun y hy => by simp [hc0 y hy.1 hy.2])
  have e2 : ∀ (g : X → ℝ) (d : (Fin e → ℂ) → ℝ),
      Integrable (fun y => c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y) (volume.restrict S) →
      IntegrableOn (fun y => c ((A.chart j).symm y) * g ((A.chart j).symm y) * d y) (A.chart j).target :=
    fun g d h => IntegrableOn.of_forall_diff_eq_zero h hTm
      (fun y hy => by simp [hc0 y hy.1 hy.2])
  refine ⟨e2 _ _ i1, i2.mono fun t h => e2 _ _ h, ?_⟩
  rw [e1 G]
  exact Tendsto.congr (fun t => (e1 (GT t) _).symm) i3

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedIntegralRegularizedConvergenceStatement
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_integral_regularized_convergence : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) (Θ : LocPot X) (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (G : X → ℝ) (GT : ℝ → X → ℝ) (C CE : ℝ), IsPotential A Θ → (∀ i, IsPotential A (th i)) → (∀ i, A.SmoothOn R.Yo (ph i)) → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ i, A.Smooth (phT i t)) ∧ (∀ i, IsPsh A (th i + LocPot.ofFun (phT i t) + Θ)) ∧ GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A R.Yo R.r (fun i => th i + LocPot.ofFun (phT i t) + Θ) CE) → (∀ i, ∀ j, ∀ K' ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' R.Yo, IsCompact K' → TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (phT i t ∘ (A.chart j).symm))) (fderiv ℝ (fderiv ℝ (ph i ∘ (A.chart j).symm))) (𝓝[>] 0) K') → (∀ᶠ t in 𝓝[>] (0 : ℝ), @Measurable X ℝ (borel X) _ (R.Yo.indicator (GT t)) ∧ ∀ x ∈ R.Yo, |GT t x| ≤ C + C * Real.log (R.r x)) → (∀ K' ⊆ R.Yo, IsCompact K' → TendstoUniformlyOn GT G (𝓝[>] 0) K') → ∀ (j : Fin A.n) (S : Set (Fin e → ℂ)) (c : X → ℝ), S ⊆ (A.chart j).target → IsCompact S → @Measurable X ℝ (borel X) _ c → (∀ x, 0 ≤ c x ∧ c x ≤ 1) → (∀ y ∈ (A.chart j).target, y ∉ S → c ((A.chart j).symm y) = 0) → IntegrableOn (fun y => c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y) (A.chart j).target ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), IntegrableOn (fun y => c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (A.chart j).target) ∧ Tendsto (fun t => ∫ y in (A.chart j).target, c ((A.chart j).symm y) * GT t ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (phT i t) + Θ) j y) (𝓝[>] 0) (𝓝 (∫ y in (A.chart j).target, c ((A.chart j).symm y) * G ((A.chart j).symm y) * locDens A (fun i => th i + LocPot.ofFun (ph i) + Θ) j y)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.conv_chart_integral | exact GlobalTheory.CompanionTheory.Ar.Giv.conv_chart_integral | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.conv_chart_integral <;> assumption)
end
