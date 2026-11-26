module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.MemLpBzOfSup

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.TendstoIntegralInnerGermMoving
namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

section L2m

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private lemma mul_le_young_bounds_of_le_add {nF nG g e t δ : ℝ} (ht : 0 < t) (hδ : 0 ≤ δ) (hnF : 0 ≤ nF)
    (hG : nG ≤ g + e) :
    (nF ≤ δ → nF * nG ≤ t * nF ^ 2 + (0 + e ^ 2) / (2 * t) + δ / 2 * (1 + g ^ 2)) ∧
      nF * nG ≤ t * nF ^ 2 + (g ^ 2 + e ^ 2) / (2 * t) + δ / 2 * (0 + g ^ 2) := by
  have h2t : 0 < 2 * t := by positivity
  have hGa : nF * nG ≤ nF * |g| + nF * |e| := by
    have : nG ≤ |g| + |e| := hG.trans (add_le_add (le_abs_self g) (le_abs_self e))
    nlinarith

  have hA : ∀ y : ℝ, nF * |y| ≤ t * nF ^ 2 / 2 + y ^ 2 / (2 * t) := by
    intro y
    rw [show t * nF ^ 2 / 2 + y ^ 2 / (2 * t) = (t ^ 2 * nF ^ 2 + y ^ 2) / (2 * t) by field_simp <;> ring,
      le_div_iff₀ h2t]
    nlinarith [sq_nonneg (t * nF - |y|), sq_abs y]
  have hg1 : |g| ≤ (1 + g ^ 2) / 2 := by nlinarith [sq_nonneg (|g| - 1), sq_abs g]
  refine ⟨fun hK => ?_, ?_⟩
  · have h1 : nF * |g| ≤ δ * |g| := mul_le_mul_of_nonneg_right hK (abs_nonneg g)
    have h2 : δ * |g| ≤ δ / 2 * (1 + g ^ 2) := by nlinarith
    have h3 := hA e
    have h4 : t * nF ^ 2 / 2 ≤ t * nF ^ 2 := by nlinarith [sq_nonneg nF]
    have h5 : (0 + e ^ 2) / (2 * t) = e ^ 2 / (2 * t) := by ring
    rw [h5]
    linarith
  · have h3 := hA e
    have h4 := hA g
    have h5 : (g ^ 2 + e ^ 2) / (2 * t) = g ^ 2 / (2 * t) + e ^ 2 / (2 * t) := by ring
    have h6 : 0 ≤ δ / 2 * (0 + g ^ 2) := by positivity
    rw [h5]
    linarith

private lemma exists_isCompact_integral_compl_sq_lt (μ : Measure ℂ) [NullSingletonClass μ] {g : ℂ → ℝ}
    (hg2 : Integrable (fun D => g D ^ 2) μ) {η : ℝ} (hη : 0 < η) :
    ∃ K : Set ℂ, IsCompact K ∧ (0 : ℂ) ∉ K ∧ ∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ < η := by
  let Kn : ℕ → Set ℂ := fun n => Metric.closedBall (0 : ℂ) (n + 1) \ Metric.ball 0 (1 / (n + 1))
  have hKc : ∀ n, IsCompact (Kn n) := fun n => (isCompact_closedBall 0 _).diff Metric.isOpen_ball
  have h0K : ∀ n, (0 : ℂ) ∉ Kn n := by
    intro n h
    exact h.2 (Metric.mem_ball_self (by positivity))
  have hlim : Tendsto (fun n : ℕ => ∫ D, (Kn n)ᶜ.indicator (fun D => g D ^ 2) D ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun D => g D ^ 2)
      (F := fun n D => (Kn n)ᶜ.indicator (fun D => g D ^ 2) D) (f := fun _ => (0 : ℝ))
      (fun n => (hg2.indicator (hKc n).isClosed.measurableSet.compl).aestronglyMeasurable) hg2
      (fun n => Filter.Eventually.of_forall fun D => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _)]
        exact Set.indicator_le_self' (fun _ _ => sq_nonneg _) D)
      (by
        have h0 : ∀ᵐ D ∂μ, D ≠ (0 : ℂ) := compl_mem_ae_iff.2 (measure_singleton 0)
        filter_upwards [h0] with D hD
        have hpos : 0 < ‖D‖ := norm_pos_iff.2 hD
        obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / ‖D‖) ‖D‖)
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        have ha : 1 / ‖D‖ < n + 1 := by linarith [le_max_left (1 / ‖D‖) ‖D‖]
        have hb : ‖D‖ < n + 1 := by linarith [le_max_right (1 / ‖D‖) ‖D‖]
        have hmem : D ∈ Kn n := by
          refine ⟨?_, ?_⟩
          · rw [Metric.mem_closedBall, dist_zero_right]
            exact hb.le
          · rw [Metric.mem_ball, dist_zero_right, not_lt]
            rw [div_le_iff₀ (by positivity)]
            rw [div_lt_iff₀ hpos] at ha
            linarith
        simp [Set.indicator_apply, hmem])
    simpa using h
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact ⟨Kn n, hKc n, h0K n, hn⟩

theorem tendsto_integral_inner_germ_moving {α : Type} {l : Filter α} (μ : Measure ℂ) [IsFiniteMeasureOnCompacts μ]
    [NullSingletonClass μ] (F G : α → ℂ → H) (g : ℂ → ℝ) (e : α → ℂ → ℝ) (hg : MemLp g 2 μ) (B : ℝ)
    (hF : ∀ᶠ x in l, MemLp (F x) 2 μ ∧ ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B)
    (he : ∀ᶠ x in l, MemLp (e x) 2 μ)
    (he0 : Tendsto (fun x => ∫ D, e x D ^ 2 ∂μ) l (𝓝 0))
    (hG : ∀ᶠ x in l, ∀ᵐ D ∂μ, ‖G x D‖ ≤ g D + e x D)
    (hloc : ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ x in l, ∀ᵐ D ∂μ, D ∈ K → ‖F x D‖ ≤ δ) :
    Tendsto (fun x => ∫ D, ⟪F x D, G x D⟫_ℂ ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set B' : ℝ := max B 0 + 1 with hB'
  have hB'pos : 0 < B' := by positivity
  set t : ℝ := ε / (4 * B') with ht_def
  have ht : 0 < t := by positivity
  have hg2 : Integrable (fun D => g D ^ 2) μ := hg.integrable_sq
  obtain ⟨K, hKc, h0K, hKint⟩ := exists_isCompact_integral_compl_sq_lt μ hg2 (η := ε * t / 2) (by positivity)
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  have hKfin : μ K < ⊤ := hKc.measure_lt_top
  have hI1 : Integrable (K.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_indicator_iff hKmeas).2 (integrableOn_const hKfin.ne)
  set M : ℝ := ∫ D, K.indicator (fun _ => (1 : ℝ)) D ∂μ + ∫ D, g D ^ 2 ∂μ + 1 with hM_def
  have hM : 0 < M := by
    have h1 : 0 ≤ ∫ D, K.indicator (fun _ => (1 : ℝ)) D ∂μ :=
      integral_nonneg fun D => Set.indicator_nonneg (fun _ _ => zero_le_one) D
    have h2 : 0 ≤ ∫ D, g D ^ 2 ∂μ := integral_nonneg fun D => sq_nonneg _
    linarith
  set δ : ℝ := ε / (4 * M) with hδ_def
  have hδ : 0 < δ := by positivity
  have he' : ∀ᶠ x in l, ∫ D, e x D ^ 2 ∂μ < ε * t / 2 := he0.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hF, he, he', hG, hloc K hKc h0K δ hδ] with x hFx hex he2 hGx hlx
  have hFmem : MemLp (F x) 2 μ := hFx.1
  have hFB := hFx.2
  rw [dist_zero_right]
  have hF2 : Integrable (fun D => ‖F x D‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hFmem.aestronglyMeasurable).1 hFmem
  have he2i : Integrable (fun D => e x D ^ 2) μ := hex.integrable_sq
  have hIc : Integrable (Kᶜ.indicator (fun D => g D ^ 2)) μ := hg2.indicator hKmeas.compl
  have i1 : Integrable (fun D => t * ‖F x D‖ ^ 2) μ := hF2.const_mul t
  have i2 : Integrable (fun D => (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t)) μ :=
    (hIc.add he2i).div_const _
  have i3 : Integrable (fun D => δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2)) μ :=
    (hI1.add hg2).const_mul _
  have i12 : Integrable (fun D => t * ‖F x D‖ ^ 2 +
      (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t)) μ := i1.add i2
  have hbnd : ∀ᵐ D ∂μ, ‖⟪F x D, G x D⟫_ℂ‖ ≤
      t * ‖F x D‖ ^ 2 + (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t) +
        δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2) := by
    filter_upwards [hGx, hlx] with D hGD hlD
    have h1 : ‖⟪F x D, G x D⟫_ℂ‖ ≤ ‖F x D‖ * ‖G x D‖ := norm_inner_le_norm _ _
    have hP := mul_le_young_bounds_of_le_add ht hδ.le (norm_nonneg (F x D)) hGD
    by_cases hD : D ∈ K
    · have hi1 : K.indicator (fun _ => (1 : ℝ)) D = 1 := by simp [Set.indicator_apply, hD]
      have hi2 : Kᶜ.indicator (fun D => g D ^ 2) D = 0 := by simp [Set.indicator_apply, hD]
      rw [hi1, hi2]
      exact h1.trans (hP.1 (hlD hD))
    · have hi1 : K.indicator (fun _ => (1 : ℝ)) D = 0 := by simp [Set.indicator_apply, hD]
      have hi2 : Kᶜ.indicator (fun D => g D ^ 2) D = g D ^ 2 := by simp [Set.indicator_apply, hD]
      rw [hi1, hi2]
      exact h1.trans hP.2
  have hsplit : ∫ D, (t * ‖F x D‖ ^ 2 + (Kᶜ.indicator (fun D => g D ^ 2) D + e x D ^ 2) / (2 * t) +
        δ / 2 * (K.indicator (fun _ => (1 : ℝ)) D + g D ^ 2)) ∂μ =
      t * ∫ D, ‖F x D‖ ^ 2 ∂μ + (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) +
        δ / 2 * (M - 1) := by
    rw [integral_add i12 i3, integral_add i1 i2, integral_const_mul, integral_div,
      integral_add hIc he2i, integral_const_mul, integral_add hI1 hg2]
    simp only [hM_def]
    ring
  have hle : ‖∫ D, ⟪F x D, G x D⟫_ℂ ∂μ‖ ≤ t * ∫ D, ‖F x D‖ ^ 2 ∂μ +
      (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) + δ / 2 * (M - 1) := by
    rw [← hsplit]
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) (i12.add i3) hbnd)
  have hb1 : t * ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ ε / 4 := by
    have hFB' : ∫ D, ‖F x D‖ ^ 2 ∂μ ≤ B' := by linarith [le_max_left B 0]
    have : t * B' = ε / 4 := by rw [ht_def]; field_simp <;> ring
    nlinarith
  have hb2 : (∫ D, Kᶜ.indicator (fun D => g D ^ 2) D ∂μ + ∫ D, e x D ^ 2 ∂μ) / (2 * t) ≤ ε / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hb3 : δ / 2 * (M - 1) ≤ ε / 8 := by
    have : δ * M = ε / 4 := by rw [hδ_def]; field_simp <;> ring
    nlinarith
  linarith

end L2m

end

end Formalism.FourierDecayAlt.P.PBK
end

namespace Formalism.FourierDecayAlt.P.PBK

open Formalism.FourierDecayAlt Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section propGD

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure GermD {ι : Type} (s : ℕ) (β ε : ℂ) (Y : Finset ι) (ut : ι → ℂ → ℂ → H) (bt : ι → ℂ → H) (SS : ℝ) :
    Prop where
  hs : s ≠ 0
  hβ : β ≠ 0
  hε : ‖ε‖ = 1
  memU : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (ut h x) 2 volume
  sup : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ∫ D, ‖ut h x D‖ ^ 2 ≤ SS
  meas : ∀ h ∈ Y, StronglyMeasurable (bt h)
  loc : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖bz s (bt h) z‖ ^ 2) K
  germ : ∀ h ∈ Y, ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 →
    ∀ᵐ D, D ∈ K → ‖ut h x D - mainD s β ε (bt h) x D‖ ≤ C * ‖x‖⁻¹

def Uc {ι : Type} (s : ℕ) (ut : ι → ℂ → ℂ → H) : ι × ℂ → ℂ → H := fun p => cvec s (ut p.1) p.2

def Ac {ι : Type} (s : ℕ) (β ε : ℂ) (bt : ι → ℂ → H) : ι × ℂ → ℂ → H :=
  fun p => cvec s (fun x D => mainD s β ε (bt p.1) x D) p.2

def Nhat {ι : Type} (s : ℕ) (β : ℂ) (bt : ι → ℂ → H) (σ : ℂ) (h h' : ι) : ℂ :=
  ∫ z, G.psi β (σ * z) • ⟪bz s (bt h) z, bz s (bt h') z⟫_ℂ

theorem tendsto_ratio_pow (s : ℕ) (a b : ℂ) :
    Tendsto (fun x : ℂ => (x + a) ^ (s - 1) / (x + b) ^ (s - 1)) (cocompact ℂ) (𝓝 1) := by
  have hn : Tendsto (fun x : ℂ => ‖x + b‖) (cocompact ℂ) atTop := by
    have h0 : Tendsto (fun x : ℂ => ‖x‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    refine tendsto_atTop_mono (fun x => ?_) (tendsto_atTop_add_const_right _ (-‖b‖) h0)
    have := norm_sub_norm_le x (-b)
    rw [norm_neg, sub_neg_eq_add] at this
    linarith
  have hi : Tendsto (fun x : ℂ => (x + b)⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact (tendsto_inv_atTop_zero.comp hn).congr fun x => by simp [norm_inv]
  have hne : ∀ᶠ x in cocompact ℂ, x + b ≠ 0 :=
    (hn.eventually_gt_atTop 0).mono fun x hx => norm_pos_iff.mp hx
  have hq : Tendsto (fun x : ℂ => 1 + (a - b) * (x + b)⁻¹) (cocompact ℂ) (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℂ))).add ((tendsto_const_nhds (x := a - b)).mul hi)
  have hp := hq.pow (s - 1)
  rw [one_pow] at hp
  refine hp.congr' ?_
  filter_upwards [hne] with x hx
  rw [← div_pow]
  congr 1
  first
  | (field_simp; ring)
  | field_simp

variable {ι : Type} {s : ℕ} {β ε : ℂ} {Y : Finset ι} {ut : ι → ℂ → ℂ → H} {bt : ι → ℂ → H} {SS : ℝ}

theorem GermD.memLp_bz (hG : GermD s β ε Y ut bt SS) {h : ι} (hh : h ∈ Y) :
    MemLp (bz s (bt h)) 2 volume ∧ ∫ z, ‖bz s (bt h) z‖ ^ 2 ≤ SS := memLp_bz_of_sup hG.hs hG.hβ hG.hε (ut h) (bt h) SS (hG.memU h hh) (hG.sup h hh)
    (hG.meas h hh) (hG.loc h hh) (hG.germ h hh)

theorem GermD.memLp_abar (hG : GermD s β ε Y ut bt SS) {h : ι} (hh : h ∈ Y) :
    MemLp (abar s ε (bt h)) 2 volume ∧ ∫ D, abar s ε (bt h) D ^ 2 ≤ s * SS := by
  obtain ⟨hb, hbS⟩ := hG.memLp_bz hh
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.PBK.memLp_abar hG.hs hG.hε (hG.meas h hh) hb
  exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left hbS (Nat.cast_nonneg s))⟩

theorem GermD.memLp_mainD (hG : GermD s β ε Y ut bt SS) {h : ι} (hh : h ∈ Y) (x : ℂ) :
    MemLp (mainD s β ε (bt h) x) 2 volume := Formalism.FourierDecayAlt.P.PBK.memLp_mainD hG.hs β hG.hε (hG.meas h hh) (hG.memLp_bz hh).1 x

theorem GermD.tendsto_cross (hG : GermD s β ε Y ut bt SS) {h h' : ι} (hh : h ∈ Y) (hh' : h' ∈ Y) (a b : ℂ) :
    Tendsto (fun x => ∫ c, ⟪cvec s (fun x D => ut h x D - mainD s β ε (bt h) x D) (x + a) c,
      cvec s (fun x D => mainD s β ε (bt h') x D) (x + b) c⟫_ℂ) (cocompact ℂ) (𝓝 0) := by
  obtain ⟨hab', habS'⟩ := hG.memLp_abar hh'
  obtain ⟨hab, habS⟩ := hG.memLp_abar hh
  obtain ⟨hdom1, hdom2, hdom3⟩ := dil_dominator (abar s ε (bt h')) hab'
    (fun x : ℂ => (x + a) ^ (s - 1) / (x + b) ^ (s - 1)) (tendsto_ratio_pow s a b)
  have hev : ∀ᶠ x in cocompact ℂ, x + a ≠ 0 ∧ x + b ≠ 0 := by
    filter_upwards [eventually_ne_cocompact (-a), eventually_ne_cocompact (-b)] with x ha hb
    exact ⟨fun h0 => ha (eq_neg_of_add_eq_zero_left h0), fun h0 => hb (eq_neg_of_add_eq_zero_left h0)⟩
  have key : ∀ᶠ x in cocompact ℂ,
      ∫ D, ⟪ut h (x + a) D - mainD s β ε (bt h) (x + a) D,
        ((‖(x + a) ^ (s - 1) / (x + b) ^ (s - 1)‖ : ℝ) : ℂ) •
          mainD s β ε (bt h') (x + b) ((x + a) ^ (s - 1) / (x + b) ^ (s - 1) * D)⟫_ℂ
      = ∫ c, ⟪cvec s (fun x D => ut h x D - mainD s β ε (bt h) x D) (x + a) c,
          cvec s (fun x D => mainD s β ε (bt h') x D) (x + b) c⟫_ℂ := by
    filter_upwards [hev] with x hx
    rw [cvec_inner s _ _ (x + a) (x + b) hx.1 hx.2]
  refine Tendsto.congr' key ?_
  refine tendsto_integral_inner_germ_moving volume
    (fun x D => ut h (x + a) D - mainD s β ε (bt h) (x + a) D)
    (fun x D => ((‖(x + a) ^ (s - 1) / (x + b) ^ (s - 1)‖ : ℝ) : ℂ) •
      mainD s β ε (bt h') (x + b) ((x + a) ^ (s - 1) / (x + b) ^ (s - 1) * D))
    (abar s ε (bt h'))
    (fun x D => |‖(x + a) ^ (s - 1) / (x + b) ^ (s - 1)‖ *
      abar s ε (bt h') ((x + a) ^ (s - 1) / (x + b) ^ (s - 1) * D) - abar s ε (bt h') D|)
    hab' (2 * SS + 2 * (s * SS)) ?_ hdom2 hdom3 ?_ ?_
  · filter_upwards [hev] with x hx
    have hu := hG.memU h hh _ hx.1
    have hm := hG.memLp_mainD hh (x + a)
    refine ⟨hu.sub hm, ?_⟩
    have h1 := integral_sq_sub_le hu hm hab (ae_of_all _ fun D => norm_mainD_le s β ε (bt h) (x + a) D)
    have hb := hG.sup h hh _ hx.1
    beta_reduce
    linarith
  · filter_upwards with x
    refine ae_of_all _ fun D => ?_
    beta_reduce
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact (mul_le_mul_of_nonneg_left (norm_mainD_le _ _ _ _ _ _) (norm_nonneg _)).trans (hdom1 x D)
  · intro K hK hK0 δ hδ
    obtain ⟨C, hC⟩ := hG.germ h hh K hK hK0
    filter_upwards [hev, eventually_rate_cocompact a C δ hδ] with x hx hr
    filter_upwards [hC _ hx.1] with D hD hDK
    exact (hD hDK).trans hr

theorem GermD.propG (hG : GermD s β ε Y ut bt SS) :
    (∀ h ∈ Y, MemLp (bz s (bt h)) 2 volume ∧ ∫ z, ‖bz s (bt h) z‖ ^ 2 ≤ SS) ∧
    (∀ Xs : Finset ℂ, (∀ x ∈ Xs, x ≠ 0) →
      KB.BlockPSD (Y ×ˢ Xs) (Y ×ˢ Xs) (gramL volume (Uc s ut) (Uc s ut)) (gramL volume (Uc s ut) (Ac s β ε bt))
        (gramL volume (Ac s β ε bt) (Ac s β ε bt))) ∧
    (∃ B' : ℝ, ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → ‖gramL volume (Ac s β ε bt) (Ac s β ε bt) (h, x) (h, x)‖ ≤ B') ∧
    ∀ h ∈ Y, ∀ h' ∈ Y, ∀ σ : ℂ,
      Tendsto (fun x => gramL volume (Ac s β ε bt) (Ac s β ε bt) (h, x) (h', x + σ)) (cocompact ℂ)
        (𝓝 (Nhat s β bt σ h h')) ∧
      Tendsto (fun x => gramL volume (Uc s ut) (Ac s β ε bt) (h, x) (h', x + σ)) (cocompact ℂ)
        (𝓝 (Nhat s β bt σ h h')) ∧
      Tendsto (fun x => conj (gramL volume (Uc s ut) (Ac s β ε bt) (h', x + σ) (h, x))) (cocompact ℂ)
        (𝓝 (Nhat s β bt σ h h')) := by
  have hs1 : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hG.hs
  have memUc : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (Uc s ut (h, x)) 2 volume := fun h hh x hx =>
    (memLp_cvec s (ut h) x hx).1 (hG.memU h hh x hx)
  have memAc : ∀ h ∈ Y, ∀ x : ℂ, x ≠ 0 → MemLp (Ac s β ε bt (h, x)) 2 volume := fun h hh x hx =>
    (memLp_cvec s (fun x D => mainD s β ε (bt h) x D) x hx).1 (hG.memLp_mainD hh x)
  refine ⟨fun h hh => hG.memLp_bz hh, fun Xs hXs => blockPSD_gramL volume Y _ _ memUc memAc Xs hXs, ?_, ?_⟩
  ·
    refine ⟨s * SS, fun h hh x hx => ?_⟩
    obtain ⟨hab, habS⟩ := hG.memLp_abar hh
    have hmD := hG.memLp_mainD hh x
    have i1 : Integrable (fun D => ‖mainD s β ε (bt h) x D‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm hmD.aestronglyMeasurable).1 hmD
    have i2 : Integrable (fun D => abar s ε (bt h) D ^ 2) := hab.integrable_sq
    calc ‖gramL volume (Ac s β ε bt) (Ac s β ε bt) (h, x) (h, x)‖
        ≤ ∫ c, ‖⟪Ac s β ε bt (h, x) c, Ac s β ε bt (h, x) c⟫_ℂ‖ := norm_integral_le_integral_norm _
      _ = ∫ c, ‖Ac s β ε bt (h, x) c‖ ^ 2 := by
          refine integral_congr_ae (Eventually.of_forall fun c => ?_)
          simp only
          rw [inner_self_eq_norm_sq_to_K]
          norm_cast
          exact abs_of_nonneg (sq_nonneg _)
      _ = ∫ D, ‖mainD s β ε (bt h) x D‖ ^ 2 := integral_norm_cvec_sq s _ x hx
      _ ≤ ∫ D, abar s ε (bt h) D ^ 2 := by
          refine integral_mono i1 i2 fun D => ?_
          exact pow_le_pow_left₀ (norm_nonneg _) (norm_mainD_le s β ε (bt h) x D) 2
      _ ≤ s * SS := habS
  · intro h hh h' hh' σ

    have hAA : Tendsto (fun x => gramL volume (Ac s β ε bt) (Ac s β ε bt) (h, x) (h', x + σ)) (cocompact ℂ)
        (𝓝 (Nhat s β bt σ h h')) := by
      have hρ0 : ∀ᶠ x in cocompact ℂ, rhoR s σ x ≠ 0 :=
        (tendsto_rhoR s σ).eventually_ne one_ne_zero
      have hT := tendsto_pairD hG.hs hG.hβ hG.hε (hG.memLp_bz hh).1 (hG.memLp_bz hh').1 (l := cocompact ℂ)
        id (fun x => x + σ) (rhoR s σ) σ hρ0 (tendsto_rhoR s σ) (tendsto_shift s hs1 σ)
        (fun ζ _ hζ => tendsto_shift_ne s hs1 σ ζ hζ)
      refine hT.congr' ?_
      filter_upwards [eventually_ne_zero_add σ] with x hx
      exact (pairD_of_cvec hG.hs β ε (bt h) (bt h') σ x hx.1 hx.2).symm
    refine ⟨hAA, ?_, ?_⟩
    · have hR := hG.tendsto_cross hh hh' 0 σ
      simp only [add_zero] at hR
      have hsum := hAA.add hR
      rw [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_ne_zero_add σ] with x hx
      have iA := integrable_inner_of_memLp (memAc h hh x hx.1) (memAc h' hh' _ hx.2)
      have iR : Integrable (fun c => ⟪cvec s (fun x D => ut h x D - mainD s β ε (bt h) x D) x c,
          cvec s (fun x D => mainD s β ε (bt h') x D) (x + σ) c⟫_ℂ) := by
        refine integrable_inner_of_memLp ?_ (memAc h' hh' _ hx.2)
        exact (memLp_cvec s _ x hx.1).1 ((hG.memU h hh x hx.1).sub (hG.memLp_mainD hh x))
      simp only [gramL]
      rw [← integral_add iA iR]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only [Uc, Ac]
      rw [← cvec_sub, inner_sub_left]
      ring
    · have hR := hG.tendsto_cross hh' hh σ 0
      simp only [add_zero] at hR
      have hRc := ((Complex.continuous_conj.tendsto 0).comp hR)
      simp only [map_zero] at hRc
      have hsum := hAA.add hRc
      rw [add_zero] at hsum
      refine hsum.congr' ?_
      filter_upwards [eventually_ne_zero_add σ] with x hx
      have iA := integrable_inner_of_memLp (memAc h hh x hx.1) (memAc h' hh' _ hx.2)
      have iR : Integrable (fun c => ⟪cvec s (fun x D => mainD s β ε (bt h) x D) x c,
          cvec s (fun x D => ut h' x D - mainD s β ε (bt h') x D) (x + σ) c⟫_ℂ) := by
        refine integrable_inner_of_memLp (memAc h hh x hx.1) ?_
        exact (memLp_cvec s _ _ hx.2).1 ((hG.memU h' hh' _ hx.2).sub (hG.memLp_mainD hh' _))
      simp only [gramL, Function.comp_apply]
      rw [← integral_conj, ← integral_conj]
      simp only [inner_conj_symm]
      rw [← integral_add iA iR]
      refine integral_congr_ae (Eventually.of_forall fun c => ?_)
      simp only [Uc, Ac]
      rw [← cvec_sub, inner_sub_right]
      ring

end propGD

end

end Formalism.FourierDecayAlt.P.PBK
